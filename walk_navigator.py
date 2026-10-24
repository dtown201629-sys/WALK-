# SPDX-License-Identifier: GPL-3.0-or-later
"""Walk Navigator

Walk (or fly) an Empty, and the camera parented to it, around a scene with the
keyboard, the mouse and a gamepad.

Keyboard / mouse
    W / S                  forward / backward
    A / D                  turn the Empty (and Cube, camera...) left / right
    Arrow keys             Up/Down forward/backward, Left/Right strafe
    Mouse                  look (turns the Empty, tilts the camera)
    Space                  jump (gravity on)  /  rise (gravity off)
    C                      descend (gravity off)
    G                      gravity on / off
    Shift / Ctrl           sprint / walk slowly
    Mouse wheel            change speed
    R                      reset camera tilt
    1 / 2 / 3              trigger the actions assigned to buttons A / B / X
    Esc / Right-click / Enter   stop

Gamepad
    Left stick             forward / backward, and turn (or strafe, see settings)
    D-pad                  Left/Right strafe, Up/Down forward/backward
    Right stick            look
    Y                      jump (gravity on)  /  rise (gravity off)
    Left trigger           descend (gravity off)
    Right trigger          sprint (left-stick click also sprints)
    A, B, X                assignable actions (Walk panel > Actions)
    Right-stick click      reset camera tilt
    Back / View            stop

Scripting hook
    walk_navigator.register_action_callback(fn) where fn(slot, context, rig)
    is called every time button A, B or X (or key 1, 2, 3) is pressed.
"""

bl_info = {
    "name": "Walk Navigator (Empty + Camera)",
    "author": "Claude",
    "version": (1, 2, 0),
    "blender": (4, 2, 0),
    "location": "3D Viewport > Sidebar (N) > Walk   |   Ctrl+Shift+W",
    "description": "Walk or fly an Empty and its child camera with keyboard, mouse and gamepad, with gravity and jumping",
    "category": "3D View",
}

import importlib
import importlib.util
import math
import os
import re
import subprocess
import sys
import time
import traceback

import bpy
from bpy.props import (
    BoolProperty,
    EnumProperty,
    FloatProperty,
    PointerProperty,
    StringProperty,
)
from mathutils import Matrix, Vector

_ACTIVE = None            # the running operator instance (if any)
_LAST_ERROR = ""          # traceback of the last crash in walk mode
_ACTION_CALLBACKS = []    # user hooks, see register_action_callback()


def register_action_callback(fn):
    """fn(slot, context, rig) is called whenever button A, B or X is pressed."""
    if fn not in _ACTION_CALLBACKS:
        _ACTION_CALLBACKS.append(fn)


def unregister_action_callback(fn):
    if fn in _ACTION_CALLBACKS:
        _ACTION_CALLBACKS.remove(fn)


# ----------------------------------------------------------------------------
# Gamepad input
# ----------------------------------------------------------------------------

def _radial_deadzone(x, y, dz):
    """Radial deadzone with rescaling so the stick still reaches 1.0."""
    m = math.hypot(x, y)
    if m <= dz or m == 0.0:
        return 0.0, 0.0
    k = min(1.0, (m - dz) / (1.0 - dz)) / m
    return x * k, y * k


_XINPUT_BUTTONS = {
    0x1000: 'A', 0x2000: 'B', 0x4000: 'X', 0x8000: 'Y',
    0x0100: 'LB', 0x0200: 'RB', 0x0010: 'START', 0x0020: 'BACK',
    0x0040: 'L3', 0x0080: 'R3',
}
_PYGAME_BUTTONS = {0: 'A', 1: 'B', 2: 'X', 3: 'Y', 4: 'LB', 5: 'RB', 6: 'BACK', 7: 'START', 8: 'L3', 9: 'R3'}


class _XInput:
    """Xbox / XInput controllers on Windows (ctypes, no extra packages)."""

    def __init__(self):
        self._dll = None
        self._slot = None
        self._next_scan = 0.0
        if sys.platform != "win32":
            return
        import ctypes
        from ctypes import wintypes

        class _Pad(ctypes.Structure):
            _fields_ = [
                ("buttons", wintypes.WORD),
                ("lt", ctypes.c_ubyte),
                ("rt", ctypes.c_ubyte),
                ("lx", ctypes.c_short),
                ("ly", ctypes.c_short),
                ("rx", ctypes.c_short),
                ("ry", ctypes.c_short),
            ]

        class _State(ctypes.Structure):
            _fields_ = [("packet", wintypes.DWORD), ("pad", _Pad)]

        self._ctypes = ctypes
        self._State = _State
        for name in ("xinput1_4", "xinput1_3", "xinput9_1_0"):
            try:
                dll = ctypes.WinDLL(name)
            except OSError:
                continue
            dll.XInputGetState.argtypes = [wintypes.DWORD, ctypes.POINTER(_State)]
            dll.XInputGetState.restype = wintypes.DWORD
            self._dll = dll
            break

    @property
    def available(self):
        return self._dll is not None

    def poll(self, now):
        if self._dll is None:
            return None
        if self._slot is None:
            if now < self._next_scan:      # scanning empty slots is slow: do it once a second
                return None
            slots = range(4)
        else:
            slots = (self._slot,)
        for i in slots:
            st = self._State()
            if self._dll.XInputGetState(i, self._ctypes.byref(st)) == 0:
                self._slot = i
                return self._convert(i, st.pad)
        self._slot = None
        self._next_scan = now + 1.0
        return None

    @staticmethod
    def _convert(slot, p):
        b = p.buttons
        return {
            "name": "Xbox controller #%d (XInput)" % (slot + 1),
            "lx": p.lx / 32768.0, "ly": p.ly / 32768.0,
            "rx": p.rx / 32768.0, "ry": p.ry / 32768.0,
            "lt": p.lt / 255.0, "rt": p.rt / 255.0,
            "dpad": (int(bool(b & 0x0008)) - int(bool(b & 0x0004)),
                     int(bool(b & 0x0001)) - int(bool(b & 0x0002))),
            "buttons": {name for mask, name in _XINPUT_BUTTONS.items() if b & mask},
        }


class _Pygame:
    """Any SDL-supported controller (PlayStation, Switch, generic...). Needs pygame."""

    def __init__(self):
        self._pg = None
        self._joy = None
        self._failed = False
        self._next_scan = 0.0

    def _boot(self):
        if self._pg is not None:
            return True
        if self._failed:
            return False
        old = os.environ.get("SDL_VIDEODRIVER")
        try:
            os.environ["PYGAME_HIDE_SUPPORT_PROMPT"] = "1"
            os.environ.setdefault("SDL_JOYSTICK_ALLOW_BACKGROUND_EVENTS", "1")
            os.environ["SDL_VIDEODRIVER"] = "dummy"      # never touch Blender's real window
            import pygame
            pygame.display.init()
            pygame.joystick.init()
            self._pg = pygame
        except Exception:
            self._failed = True
        finally:
            if old is None:
                os.environ.pop("SDL_VIDEODRIVER", None)
            else:
                os.environ["SDL_VIDEODRIVER"] = old
        return self._pg is not None

    def poll(self, now):
        if not self._boot():
            return None
        pg = self._pg
        try:
            pg.event.pump()
            if pg.joystick.get_count() == 0:
                self._joy = None
                return None
            if self._joy is None:
                if now < self._next_scan:
                    return None
                self._next_scan = now + 1.0
                self._joy = pg.joystick.Joystick(0)
            j = self._joy
            n = j.get_numaxes()

            def ax(i):
                return j.get_axis(i) if i < n else 0.0

            hat = j.get_hat(0) if j.get_numhats() else (0, 0)
            nb = j.get_numbuttons()
            return {
                "name": "%s (pygame)" % j.get_name(),
                "lx": ax(0), "ly": -ax(1), "rx": ax(2), "ry": -ax(3),
                "lt": (ax(4) + 1.0) * 0.5 if n > 4 else 0.0,
                "rt": (ax(5) + 1.0) * 0.5 if n > 5 else 0.0,
                "dpad": (hat[0], hat[1]),
                "buttons": {name for i, name in _PYGAME_BUTTONS.items() if i < nb and j.get_button(i)},
            }
        except Exception:
            self._joy = None
            return None


class _Gamepad:
    def __init__(self, preference):
        self.backends = []
        if preference in {'AUTO', 'XINPUT'}:
            xi = _XInput()
            if xi.available:
                self.backends.append(xi)
        if preference in {'AUTO', 'PYGAME'} and importlib.util.find_spec("pygame"):
            self.backends.append(_Pygame())
        self.status = "none found"

    def poll(self, now, deadzone):
        raw = None
        for b in self.backends:
            raw = b.poll(now)
            if raw:
                break
        if not raw:
            self.status = "none found"
            return None
        self.status = raw["name"]
        mx, my = _radial_deadzone(raw["lx"], raw["ly"], deadzone)
        lx, ly = _radial_deadzone(raw["rx"], raw["ry"], deadzone)
        btn = raw["buttons"]
        return {
            "move": (mx, my),
            "look": (lx, ly),
            "dpad": raw["dpad"],
            "lt": raw["lt"],
            "buttons": btn,
            "sprint": raw["rt"] > 0.3 or 'L3' in btn,
            "exit": 'BACK' in btn,
            "reset": 'R3' in btn,
        }


# ----------------------------------------------------------------------------
# Ground probe + rig controller (no event handling here, so it is easy to test)
# ----------------------------------------------------------------------------

class _GroundProbe:
    """Finds the ground height under the walker.

    All visible meshes except the rig itself are merged into one world-space
    BVH tree when walking starts (so flattened, zero-scale planes work too).
    The ground is therefore assumed to be static while walking.
    """

    MAX_TRIS = 2000000

    def __init__(self, context, exclude):
        import numpy as np
        from mathutils.bvhtree import BVHTree

        dg = context.evaluated_depsgraph_get()
        verts, tris = [], []
        offset = total = 0
        self.skipped = 0
        self.tree = None
        for ob in context.view_layer.objects:
            if ob.type != 'MESH' or ob.name in exclude or not ob.visible_get():
                continue
            ev = ob.evaluated_get(dg)
            me = ev.to_mesh()
            try:
                me.calc_loop_triangles()
                nv, nt = len(me.vertices), len(me.loop_triangles)
                if nv == 0 or nt == 0:
                    continue
                if total + nt > self.MAX_TRIS:
                    self.skipped += 1
                    continue
                co = np.empty(nv * 3, dtype=np.float32)
                me.vertices.foreach_get("co", co)
                tri = np.empty(nt * 3, dtype=np.int32)
                me.loop_triangles.foreach_get("vertices", tri)
            finally:
                ev.to_mesh_clear()
            m = np.array(ev.matrix_world, dtype=np.float32)
            verts.append(co.reshape(-1, 3) @ m[:3, :3].T + m[:3, 3])
            tris.append(tri.reshape(-1, 3) + offset)
            offset += nv
            total += nt
        if verts:
            self.tree = BVHTree.FromPolygons(np.concatenate(verts).tolist(),
                                             np.concatenate(tris).tolist(), all_triangles=True)
        if self.skipped:
            print("Walk Navigator: ground limited to %d triangles, %d object(s) skipped" % (self.MAX_TRIS, self.skipped))

    def height_at(self, x, y, top, bottom):
        """Highest surface between `top` and `bottom` at (x, y), or None."""
        if self.tree is None or top <= bottom:
            return None
        loc, _normal, _index, _dist = self.tree.ray_cast(Vector((x, y, top)), Vector((0.0, 0.0, -1.0)), top - bottom)
        return None if loc is None else loc.z

    def height_above(self, x, y, bottom, top):
        """Lowest surface between `bottom` and `top` at (x, y), looking upward, or None."""
        if self.tree is None or top <= bottom:
            return None
        loc, _normal, _index, _dist = self.tree.ray_cast(Vector((x, y, bottom)), Vector((0.0, 0.0, 1.0)), top - bottom)
        return None if loc is None else loc.z


class _WalkRig:
    def __init__(self, context, empty, camera, s):
        self.empty, self.camera, self.s = empty, camera, s
        self._mw = empty.matrix_world.copy()
        self._start_mw = self._mw.copy()
        self.vel = Vector((0.0, 0.0, 0.0))
        self.pitch = 0.0

        # Camera pose expressed in the Empty's own frame (what the parenting gives us).
        self._pi = camera.matrix_parent_inverse.copy()
        self._pi_inv = self._pi.inverted_safe()
        self._basis0 = camera.matrix_basis.copy()
        self._cam_rel = self._pi @ self._basis0
        self._saved = (
            camera.location.copy(), camera.rotation_euler.copy(),
            camera.rotation_quaternion.copy(), tuple(camera.rotation_axis_angle),
            camera.scale.copy(),
        )

        # "Forward" = the way the camera looks, flattened onto the Empty's ground plane.
        rot = self._cam_rel.to_3x3()
        look = rot @ Vector((0.0, 0.0, -1.0))
        look.z = 0.0
        if look.length < 1e-4:                      # top-down camera: use its screen-up instead
            look = rot @ Vector((0.0, 1.0, 0.0))
            look.z = 0.0
        if look.length < 1e-4:
            look = Vector((0.0, 1.0, 0.0))
        self.fwd_local = look.normalized()
        self.axis = self.fwd_local.cross(Vector((0.0, 0.0, 1.0))).normalized()   # camera "right"

        dist = (self._mw.to_3x3() @ self._cam_rel.translation).length
        mode = s.camera_pivot
        if mode == 'AUTO':
            mode = 'EMPTY' if dist > 1.0 else 'CAMERA'
        self.pivot = Vector((0.0, 0.0, 0.0)) if mode == 'EMPTY' else self._cam_rel.translation.copy()

        # Ground (needed for gravity). `hover` = how far the Empty's origin sits above the rig's lowest point.
        children = list(empty.children_recursive)
        exclude = {empty.name, camera.name} | {c.name for c in children}
        self.probe = _GroundProbe(context, exclude)
        p = self._mw.translation
        hover = self._rig_foot_offset(context, children)
        z = self.probe.height_at(p.x, p.y, p.z + 0.05, p.z - 1000.0)
        if z is None:                                   # started underneath the ground
            z = self.probe.height_above(p.x, p.y, p.z, p.z + 1000.0)
        self.has_ground = z is not None
        if hover is None:                               # no meshes in the rig: use the current height
            hover = max(0.0, p.z - z) if self.has_ground else 0.0
        self.hover = hover
        self._start_foot = z if self.has_ground else p.z - hover
        self.foot_z = self._start_foot
        if self.has_ground:                             # "start" always means standing on the ground
            t0 = self._start_mw.translation.copy()
            t0.z = self._start_foot + hover
            self._start_mw.translation = t0
        self.grounded = False
        self.gravity_on = False
        self._jump_buf = 0.0
        self.respawned = 0
        self.set_gravity(s.use_gravity)

    def _rig_foot_offset(self, context, children):
        """Height of the Empty's origin above the lowest point of the rig's own meshes (None if it has none)."""
        dg = context.evaluated_depsgraph_get()
        low = None
        for ob in children:
            if ob.type != 'MESH':
                continue
            ev = ob.evaluated_get(dg)
            mw = ev.matrix_world
            z = min((mw @ Vector(c)).z for c in ev.bound_box)
            low = z if low is None else min(low, z)
        if low is None:
            return None
        off = self._mw.translation.z - low
        return off if off >= 0.0 else None

    def _rescue(self):
        """Gravity was switched on underneath the ground (e.g. after flying through it): stand on top of it."""
        p = self._mw.translation
        foot = self.foot_z
        if self.probe.height_at(p.x, p.y, foot + self.s.step_height, foot - 1000.0) is not None:
            return
        g = self.probe.height_above(p.x, p.y, foot, foot + 1000.0)
        if g is not None:
            self.foot_z = g
            t = p.copy()
            t.z = g + self.hover
            self._mw.translation = t
            self.empty.matrix_world = self._mw

    # -- gravity / mode ----------------------------------------------------
    def set_gravity(self, wanted):
        on = bool(wanted) and self.has_ground
        if on == self.gravity_on:
            return
        self.gravity_on = on
        self.vel.z = 0.0
        if on:
            self.foot_z = self._mw.translation.z - self.hover
            self.grounded = False       # lands on the very next frame if there is ground below
            self._rescue()

    def return_to_start(self):
        self._mw = self._start_mw.copy()
        self.empty.matrix_world = self._mw
        self.vel.zero()
        self.foot_z = self._start_foot
        self.grounded = self.gravity_on

    def _gravity_step(self, dt, x, y, jump):
        """Advance the vertical motion with gravity. Returns the new foot height."""
        s = self.s
        step = s.step_height
        self._jump_buf = 0.15 if jump else max(0.0, self._jump_buf - dt)   # small input buffer
        foot = self.foot_z
        if self.grounded:
            g = self.probe.height_at(x, y, foot + step, foot - step)
            if g is None:                       # walked off an edge
                self.grounded = False
            else:
                foot += (g - foot) * (1.0 - math.exp(-s.ground_smoothing * dt))
                if abs(g - foot) < 1e-4:
                    foot = g
                self.vel.z = 0.0
        if self.grounded and self._jump_buf > 0.0:
            self.vel.z = math.sqrt(2.0 * s.gravity * s.jump_height)
            self.grounded = False
            self._jump_buf = 0.0
        if not self.grounded:
            self.vel.z -= s.gravity * dt
            new = foot + self.vel.z * dt
            if self.vel.z <= 0.0:               # falling: look for something to land on
                g = self.probe.height_at(x, y, max(foot, new) + step, min(foot, new) - 0.02)
                if g is not None and new <= g + 1e-4:
                    new = g
                    self.vel.z = 0.0
                    self.grounded = True
            foot = new
        self.foot_z = foot
        if foot < self._start_foot - s.void_depth:      # fell out of the world
            self.respawned += 1
            self.return_to_start()
            return None
        return foot

    # -- camera tilt -------------------------------------------------------
    def _pitch_matrix(self, angle):
        return Matrix.Translation(self.pivot) @ Matrix.Rotation(angle, 4, self.axis) @ Matrix.Translation(-self.pivot)

    def _cam_world_z(self, angle):
        return (self._mw @ self._pitch_matrix(angle) @ self._cam_rel).translation.z

    def _apply_pitch(self, angle):
        self.pitch = angle
        self.camera.matrix_basis = self._pi_inv @ self._pitch_matrix(angle) @ self._pi @ self._basis0

    def reset_pitch(self):
        if self.pitch != 0.0:
            self._apply_pitch(0.0)

    # -- per-frame update --------------------------------------------------
    def update(self, dt, strafe, forward, yaw, pitch, speed_mult, rise=0.0, jump=False):
        s = self.s
        mw = self._mw
        old_t = mw.translation.copy()
        if yaw:
            t = old_t
            mw = Matrix.Translation(t) @ Matrix.Rotation(yaw, 4, 'Z') @ Matrix.Translation(-t) @ mw

        fwd = mw.to_3x3() @ self.fwd_local
        fwd.z = 0.0
        fwd = fwd.normalized() if fwd.length > 1e-6 else Vector((0.0, 1.0, 0.0))
        right = fwd.cross(Vector((0.0, 0.0, 1.0)))

        want = fwd * forward + right * strafe
        if want.length > 1.0:
            want.normalize()
        want *= s.walk_speed * speed_mult
        k = 1.0 - math.exp(-s.acceleration * dt)
        self.vel.x += (want.x - self.vel.x) * k
        self.vel.y += (want.y - self.vel.y) * k
        if want.length == 0.0 and abs(self.vel.x) < 1e-4 and abs(self.vel.y) < 1e-4:
            self.vel.x = self.vel.y = 0.0

        pos = mw.translation.copy()
        pos.x += self.vel.x * dt
        pos.y += self.vel.y * dt
        if self.gravity_on:
            foot = self._gravity_step(dt, pos.x, pos.y, jump)
            if foot is None:                    # respawned
                return
            pos.z = foot + self.hover
        else:
            self.vel.z += (rise * s.walk_speed * speed_mult - self.vel.z) * k
            if rise == 0.0 and abs(self.vel.z) < 1e-4:
                self.vel.z = 0.0
            pos.z += self.vel.z * dt
            if s.fly_above_ground and self.has_ground:
                old_foot, new_foot = old_t.z - self.hover, pos.z - self.hover
                g = self.probe.height_at(pos.x, pos.y, max(old_foot, new_foot) + s.step_height,
                                         min(old_foot, new_foot) - 0.02)
                if g is not None and new_foot < g:
                    pos.z = g + self.hover
                    self.vel.z = max(0.0, self.vel.z)
        mw.translation = pos

        if yaw or (pos - old_t).length > 1e-7:
            self.empty.matrix_world = mw
            self._mw = mw

        if pitch:
            target = max(-s.pitch_down_limit, min(s.pitch_up_limit, self.pitch + pitch))
            if target != self.pitch and self.gravity_on:
                # Never let the camera dip under the ground: stop at the steepest allowed tilt.
                floor = self.foot_z + 0.3
                z_now = self._cam_world_z(self.pitch)

                def allowed(a):
                    z = self._cam_world_z(a)
                    return z >= floor or z >= z_now

                if not allowed(target):
                    lo, hi = self.pitch, target
                    for _ in range(10):
                        mid = (lo + hi) * 0.5
                        if allowed(mid):
                            lo = mid
                        else:
                            hi = mid
                    target = lo
            if target != self.pitch:
                self._apply_pitch(target)

    def finish(self, restore_camera):
        if restore_camera:
            cam = self.camera
            loc, eul, quat, aa, scl = self._saved
            cam.location = loc
            cam.rotation_euler = eul
            cam.rotation_quaternion = quat
            cam.rotation_axis_angle = aa
            cam.scale = scl
            self.pitch = 0.0


# ----------------------------------------------------------------------------
# Settings
# ----------------------------------------------------------------------------

_ACTION_ITEMS = [
    ('NONE', "Unassigned", "Does nothing (scripts can still react through register_action_callback)"),
    ('JUMP', "Jump", "Jump when gravity is on"),
    ('TOGGLE_GRAVITY', "Toggle Gravity", "Switch between walking with gravity and free flying"),
    ('RESET_TILT', "Reset Camera Tilt", "Put the camera back to its original angle"),
    ('RETURN_TO_START', "Return to Start", "Move the Empty back to where walking started"),
    ('SPEED_UP', "Speed Up", "Increase the walk speed by 25%"),
    ('SPEED_DOWN', "Speed Down", "Decrease the walk speed by 25%"),
    ('RUN_OPERATOR', "Run Blender Operator", "Run any Blender operator by its id, for example render.opengl"),
]


class WalkNavSettings(bpy.types.PropertyGroup):
    target_empty: PointerProperty(
        name="Empty", type=bpy.types.Object,
        poll=lambda self, obj: obj.type == 'EMPTY',
        description="The Empty that walks. Leave blank to use the camera's parent / the active Empty")
    target_camera: PointerProperty(
        name="Camera", type=bpy.types.Object,
        poll=lambda self, obj: obj.type == 'CAMERA',
        description="Camera parented to the Empty. Leave blank to use the scene camera")

    # movement
    walk_speed: FloatProperty(name="Walk Speed", default=6.0, min=0.05, soft_max=60.0, unit='VELOCITY',
                              description="Walking speed (the mouse wheel changes it while walking)")
    sprint_multiplier: FloatProperty(name="Sprint Multiplier", default=2.5, min=1.0, soft_max=10.0)
    acceleration: FloatProperty(name="Acceleration", default=10.0, min=0.5, soft_max=40.0,
                                description="How quickly you reach full speed (higher is snappier)")

    # gravity
    use_gravity: BoolProperty(name="Gravity", default=True,
                              description="On: walk on the ground and jump. Off: fly freely up, down, left, right, forwards and backwards")
    gravity: FloatProperty(name="Gravity", default=9.81, min=0.1, soft_max=60.0, unit='ACCELERATION',
                           description="Downward acceleration")
    jump_height: FloatProperty(name="Jump Height", default=1.5, min=0.05, soft_max=10.0, unit='LENGTH')
    step_height: FloatProperty(name="Step Height", default=0.6, min=0.0, soft_max=3.0, unit='LENGTH',
                               description="Highest step or curb you can walk up without jumping")
    ground_smoothing: FloatProperty(name="Ground Smoothing", default=12.0, min=1.0, soft_max=40.0)
    void_depth: FloatProperty(name="Fall Limit", default=100.0, min=1.0, soft_max=1000.0, unit='LENGTH',
                              description="Return to the start after falling this far below it")
    fly_above_ground: BoolProperty(name="Stay Above Ground When Flying", default=True,
                                   description="Stops you flying down through the floor when gravity is off")

    # look
    mouse_sensitivity: FloatProperty(name="Mouse Sensitivity", default=0.15, min=0.01, max=2.0,
                                     description="Degrees of rotation per pixel of mouse movement")
    invert_look_y: BoolProperty(name="Invert Mouse Y", default=False)
    key_turn_speed: FloatProperty(name="A/D Turn Speed", default=90.0, min=1.0, soft_max=360.0,
                                  description="Degrees per second")
    pitch_up_limit: FloatProperty(name="Look Up Limit", default=math.radians(30.0), min=0.0,
                                  max=math.radians(85.0), subtype='ANGLE')
    pitch_down_limit: FloatProperty(name="Look Down Limit", default=math.radians(75.0), min=0.0,
                                    max=math.radians(85.0), subtype='ANGLE')
    camera_pivot: EnumProperty(
        name="Camera Tilt Pivot", default='AUTO',
        items=[('AUTO', "Auto", "Orbit the Empty for a third-person camera, look in place for a first-person one"),
               ('EMPTY', "Orbit Empty", "Tilt by orbiting the camera around the Empty"),
               ('CAMERA', "Camera Position", "Tilt by turning the camera in place")])
    camera_view: BoolProperty(name="Look Through Camera", default=True,
                              description="Switch the viewport to camera view while walking")
    restore_camera: BoolProperty(name="Reset Camera Tilt On Exit", default=True)

    # gamepad
    use_gamepad: BoolProperty(name="Use Gamepad", default=True)
    gamepad_backend: EnumProperty(
        name="Backend", default='AUTO',
        items=[('AUTO', "Auto", "XInput first, then pygame"),
               ('XINPUT', "XInput", "Xbox-style controllers on Windows"),
               ('PYGAME', "pygame", "Any SDL controller (needs pygame)")])
    left_stick_x: EnumProperty(
        name="Left Stick Left/Right", default='TURN',
        items=[('TURN', "Turn", "Like the A and D keys"),
               ('STRAFE', "Strafe", "Sidestep without turning")])
    gamepad_deadzone: FloatProperty(name="Deadzone", default=0.18, min=0.0, max=0.9)
    gamepad_look_speed: FloatProperty(name="Look Speed", default=140.0, min=10.0, soft_max=360.0,
                                      description="Degrees per second with the stick fully pushed")
    gamepad_invert_y: BoolProperty(name="Invert Stick Y", default=False)

    # assignable buttons (keys 1, 2, 3 do the same on the keyboard)
    action_a: EnumProperty(name="Button A", items=_ACTION_ITEMS, default='NONE')
    action_b: EnumProperty(name="Button B", items=_ACTION_ITEMS, default='NONE')
    action_x: EnumProperty(name="Button X", items=_ACTION_ITEMS, default='NONE')
    action_a_operator: StringProperty(name="Operator ID", description="For example render.opengl")
    action_b_operator: StringProperty(name="Operator ID", description="For example render.opengl")
    action_x_operator: StringProperty(name="Operator ID", description="For example render.opengl")


def _resolve_targets(context, s):
    cam = s.target_camera or context.scene.camera
    empty = s.target_empty
    if empty is None and cam is not None and cam.parent is not None and cam.parent.type == 'EMPTY':
        empty = cam.parent
    if empty is None:
        ob = context.active_object
        if ob is not None and ob.type == 'EMPTY':
            empty = ob
    return empty, cam


# ----------------------------------------------------------------------------
# Operators
# ----------------------------------------------------------------------------

_TRACKED_KEYS = {
    'W', 'A', 'S', 'D', 'C', 'SPACE',
    'UP_ARROW', 'DOWN_ARROW', 'LEFT_ARROW', 'RIGHT_ARROW',
    'LEFT_SHIFT', 'RIGHT_SHIFT', 'LEFT_CTRL', 'RIGHT_CTRL',
}
_ACTION_KEYS = {'ONE': 'A', 'TWO': 'B', 'THREE': 'X'}


class WALK_OT_start(bpy.types.Operator):
    bl_idname = "walk_nav.start"
    bl_label = "Start Walking"
    bl_description = "Walk or fly the Empty (and its child camera) with keyboard, mouse and gamepad"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        return context.area is not None and context.area.type == 'VIEW_3D' and context.window is not None

    # -- setup ---------------------------------------------------------------
    def invoke(self, context, event):
        global _ACTIVE
        if _ACTIVE is not None:
            self.report({'WARNING'}, "Walk mode is already running")
            return {'CANCELLED'}

        s = context.scene.walk_nav
        empty, cam = _resolve_targets(context, s)
        if empty is None:
            self.report({'ERROR'}, "No Empty found: pick one in the Walk panel (N sidebar) or select it")
            return {'CANCELLED'}
        if cam is None:
            self.report({'ERROR'}, "No camera found: pick one in the Walk panel or set a scene camera")
            return {'CANCELLED'}
        if cam.parent != empty or cam.parent_type != 'OBJECT':
            self.report({'ERROR'}, "The camera must be a child of the Empty (use 'Parent Camera to Empty' in the Walk panel)")
            return {'CANCELLED'}
        region = next((r for r in context.area.regions if r.type == 'WINDOW'), None)
        if region is None:
            return {'CANCELLED'}

        s.target_empty, s.target_camera = empty, cam

        self._s = s
        self._scene = context.scene
        self._window = context.window
        self._workspace = context.workspace
        self._area = context.area
        self._region = region
        self._space = context.area.spaces.active
        self._cleaned = False
        self._stop = False
        self._down = set()
        self._mx = self._my = 0.0
        self._center = (region.x + region.width // 2, region.y + region.height // 2)
        self._last = self._center
        self._warping = False
        self._rig = None
        self._pad = None
        self._timer = None
        self._saved_view = None
        self._prev_buttons = set()
        self._jump_req = False
        self._notice = None
        self._hud_t = 0.0
        try:
            self._rig = _WalkRig(context, empty, cam, s)
            self._pad = _Gamepad(s.gamepad_backend) if s.use_gamepad else None

            r3d = getattr(self._space, "region_3d", None)
            self._saved_view = (r3d.view_perspective if r3d else None, context.scene.camera)
            if s.camera_view:
                if context.scene.camera != cam:
                    context.scene.camera = cam
                if r3d:
                    r3d.view_perspective = 'CAMERA'

            wm = context.window_manager
            self._timer = wm.event_timer_add(1.0 / 60.0, window=context.window)
            self._window.cursor_modal_set('NONE')
            self._window.cursor_warp(*self._center)
            self._warping = True            # a landing event near the centre is expected
            self._t_last = time.perf_counter()
            self._set_hud(force=True)
            wm.modal_handler_add(self)
        except Exception:
            self._remember_error()
            self._cleanup()
            self.report({'ERROR'}, "Could not start walk mode (see the system console)")
            return {'CANCELLED'}

        _ACTIVE = self
        return {'RUNNING_MODAL'}

    # -- helpers -------------------------------------------------------------
    @staticmethod
    def _remember_error():
        global _LAST_ERROR
        _LAST_ERROR = traceback.format_exc()
        print(_LAST_ERROR)

    def request_stop(self):
        self._stop = True

    def _set_hud(self, force=False):
        now = time.perf_counter()
        if not force and now - self._hud_t < 0.25:
            return
        self._hud_t = now
        rig, s = self._rig, self._s
        if rig.gravity_on:
            mode = "GRAVITY ON" + ("" if rig.grounded else " - in air")
            vert = "Space / Y: jump"
        elif s.use_gravity:
            mode = "FLYING - no ground found"
            vert = "Space / Y: up   C / LT: down"
        else:
            mode = "FLYING"
            vert = "Space / Y: up   C / LT: down"
        pad = self._pad.status if self._pad else "off"
        text = ("WALK [%s]   W/S: fwd/back   A/D: turn   Arrows: move/strafe   %s   G: gravity   "
                "Mouse / right stick: look   Shift / RT: sprint   Wheel: speed (%.1f m/s)   "
                "1/2/3 = A/B/X   Esc / RMB / Back: stop   |   Gamepad: %s"
                % (mode, vert, s.walk_speed, pad))
        if self._notice and now < self._notice[1]:
            text = ">> %s <<   %s" % (self._notice[0], text)
        self._workspace.status_text_set(text)

    def _cleanup(self):
        global _ACTIVE
        if getattr(self, "_cleaned", True):
            return
        self._cleaned = True
        try:
            if self._timer is not None:
                bpy.context.window_manager.event_timer_remove(self._timer)
        except Exception:
            pass
        try:
            self._window.cursor_modal_restore()
        except Exception:
            pass
        try:
            self._workspace.status_text_set(None)
        except Exception:
            pass
        try:
            if self._rig is not None:
                self._rig.finish(self._s.restore_camera)
        except Exception:
            pass
        try:
            if self._saved_view is not None:
                persp, scene_cam = self._saved_view
                r3d = getattr(self._space, "region_3d", None)
                if r3d and persp:
                    r3d.view_perspective = persp
                if scene_cam is not None and self._scene.camera != scene_cam:
                    self._scene.camera = scene_cam
        except Exception:
            pass
        if _ACTIVE is self:
            _ACTIVE = None
        try:
            self._area.tag_redraw()
        except Exception:
            pass

    def cancel(self, context):
        self._cleanup()

    # -- actions assigned to buttons A / B / X ---------------------------------
    def _do_action(self, context, slot):
        s = self._s
        for cb in list(_ACTION_CALLBACKS):
            try:
                cb(slot, context, self._rig)
            except Exception:
                traceback.print_exc()
        act = getattr(s, "action_" + slot.lower())
        label = None
        if act == 'JUMP':
            self._jump_req = True
            label = "Jump"
        elif act == 'TOGGLE_GRAVITY':
            s.use_gravity = not s.use_gravity
            label = "Gravity " + ("on" if s.use_gravity else "off")
        elif act == 'RESET_TILT':
            self._rig.reset_pitch()
            label = "Camera tilt reset"
        elif act == 'RETURN_TO_START':
            self._rig.return_to_start()
            label = "Back at start"
        elif act in {'SPEED_UP', 'SPEED_DOWN'}:
            f = 1.25 if act == 'SPEED_UP' else 0.8
            s.walk_speed = max(0.05, min(500.0, s.walk_speed * f))
            label = "Speed %.1f m/s" % s.walk_speed
        elif act == 'RUN_OPERATOR':
            label = self._run_operator(context, getattr(s, "action_%s_operator" % slot.lower()))
        if label:
            self._notice = ("Button %s: %s" % (slot, label), time.perf_counter() + 2.5)
            self._set_hud(force=True)

    def _run_operator(self, context, ident):
        ident = (ident or "").strip()
        if not re.fullmatch(r"[a-z0-9_]+\.[a-z0-9_]+", ident) or ident == "walk_nav.start":
            return "invalid operator id '%s'" % ident
        cat, name = ident.split(".")
        try:
            op = getattr(getattr(bpy.ops, cat), name)
            with context.temp_override(window=self._window, area=self._area, region=self._region):
                op('EXEC_DEFAULT')
        except Exception as exc:
            msg = str(exc).strip().splitlines()
            return "%s failed: %s" % (ident, msg[0] if msg else exc)
        return "ran " + ident

    # -- event loop ------------------------------------------------------------
    def modal(self, context, event):
        try:
            return self._modal(context, event)
        except Exception:
            self._remember_error()
            self._cleanup()
            self.report({'ERROR'}, "Walk mode stopped because of an error (see the system console)")
            return {'CANCELLED'}

    def _finish(self):
        self._cleanup()
        return {'FINISHED'}

    def _modal(self, context, event):
        t, v = event.type, event.value
        if t == 'TIMER':
            return self._tick(context)
        if t == 'WINDOW_DEACTIVATE':
            self._down.clear()                  # key releases are not delivered while unfocused
            return {'RUNNING_MODAL'}
        if self._stop:
            return self._finish()
        if t in {'ESC', 'RIGHTMOUSE', 'RET', 'NUMPAD_ENTER'} and v == 'PRESS':
            return self._finish()
        if t in {'MOUSEMOVE', 'INBETWEEN_MOUSEMOVE'}:
            self._mouse(event)
        elif t in {'WHEELUPMOUSE', 'WHEELDOWNMOUSE'}:
            f = 1.15 if t == 'WHEELUPMOUSE' else 1.0 / 1.15
            self._s.walk_speed = max(0.05, min(500.0, self._s.walk_speed * f))
            self._set_hud(force=True)
        elif v == 'PRESS' and not event.is_repeat and t == 'R':
            self._rig.reset_pitch()
        elif v == 'PRESS' and not event.is_repeat and t == 'G':
            self._s.use_gravity = not self._s.use_gravity
            self._notice = ("Gravity " + ("on" if self._s.use_gravity else "off"), time.perf_counter() + 2.0)
            self._set_hud(force=True)
        elif v == 'PRESS' and not event.is_repeat and t in _ACTION_KEYS:
            self._do_action(context, _ACTION_KEYS[t])
        elif t in _TRACKED_KEYS:
            if v == 'PRESS':
                if t == 'SPACE' and not event.is_repeat:
                    self._jump_req = True
                self._down.add(t)
            elif v == 'RELEASE':
                self._down.discard(t)
        return {'RUNNING_MODAL'}

    def _mouse(self, event):
        x, y = event.mouse_x, event.mouse_y
        cx, cy = self._center
        if self._warping and abs(x - cx) <= 60 and abs(y - cy) <= 60:
            self._warping = False            # the cursor landed back in the centre
            self._last = (x, y)
            return
        dx, dy = x - self._last[0], y - self._last[1]
        self._last = (x, y)
        if abs(dx) < 300 and abs(dy) < 300:
            self._mx += dx
            self._my += dy
        if not self._warping and (abs(x - cx) > 60 or abs(y - cy) > 60):
            self._window.cursor_warp(cx, cy)  # keep the cursor in the middle (endless mouse look)
            self._warping = True

    def _tick(self, context):
        s = self._s
        rig = self._rig
        now = time.perf_counter()
        dt = min(now - self._t_last, 0.1)
        self._t_last = now
        if self._stop:
            return self._finish()
        if dt <= 0.0:
            return {'RUNNING_MODAL'}

        rig.set_gravity(s.use_gravity)

        d = self._down
        forward = (('W' in d) - ('S' in d)) + (('UP_ARROW' in d) - ('DOWN_ARROW' in d))
        strafe = ('RIGHT_ARROW' in d) - ('LEFT_ARROW' in d)
        rise = ('SPACE' in d) - ('C' in d)

        k = math.radians(s.mouse_sensitivity)
        yaw = -self._mx * k
        pitch = self._my * k * (-1.0 if s.invert_look_y else 1.0)
        self._mx = self._my = 0.0
        turn_rate = math.radians(s.key_turn_speed) * dt
        yaw += turn_rate * (('A' in d) - ('D' in d))          # A = turn left, D = turn right

        mult = 1.0
        if d & {'LEFT_SHIFT', 'RIGHT_SHIFT'}:
            mult = s.sprint_multiplier
        elif d & {'LEFT_CTRL', 'RIGHT_CTRL'}:
            mult = 0.35

        jump = self._jump_req
        self._jump_req = False

        pad = self._pad.poll(now, s.gamepad_deadzone) if self._pad is not None else None
        if pad:
            if pad["exit"]:
                return self._finish()
            lx, ly = pad["move"]
            forward += ly
            if s.left_stick_x == 'TURN':
                yaw -= lx * abs(lx) * turn_rate
            else:
                strafe += lx
            dx, dy = pad["dpad"]                              # D-pad: strafe + forward/back
            strafe += dx
            forward += dy
            look_rate = math.radians(s.gamepad_look_speed) * dt
            rx, ry = pad["look"]
            yaw -= rx * abs(rx) * look_rate                   # squared response = finer aim
            pitch += ry * abs(ry) * look_rate * (-1.0 if s.gamepad_invert_y else 1.0)
            if pad["sprint"]:
                mult = s.sprint_multiplier
            buttons = pad["buttons"]
            rise += (1.0 if 'Y' in buttons else 0.0) - pad["lt"]
            new = buttons - self._prev_buttons                # buttons pressed this frame
            if 'Y' in new:
                jump = True
            if 'R3' in new:
                rig.reset_pitch()
            for slot in ('A', 'B', 'X'):
                if slot in new:
                    self._do_action(context, slot)
            self._prev_buttons = set(buttons)
        else:
            self._prev_buttons = set()

        jump = jump or self._jump_req
        self._jump_req = False
        forward = max(-1.0, min(1.0, forward))
        strafe = max(-1.0, min(1.0, strafe))
        rise = max(-1.0, min(1.0, rise))
        rig.update(dt, strafe, forward, yaw, pitch, mult, rise, jump)
        self._area.tag_redraw()
        self._set_hud()
        return {'RUNNING_MODAL'}


class WALK_OT_parent_camera(bpy.types.Operator):
    bl_idname = "walk_nav.parent_camera"
    bl_label = "Parent Camera to Empty"
    bl_description = "Make the camera a child of the Empty, keeping its current position"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        empty, cam = _resolve_targets(context, context.scene.walk_nav)
        if empty is None or cam is None:
            self.report({'ERROR'}, "Pick an Empty and a camera first")
            return {'CANCELLED'}
        cam.parent = empty
        cam.parent_type = 'OBJECT'
        cam.matrix_parent_inverse = empty.matrix_world.inverted_safe()
        return {'FINISHED'}


class WALK_OT_install_pygame(bpy.types.Operator):
    bl_idname = "walk_nav.install_pygame"
    bl_label = "Install pygame"
    bl_description = ("Download pygame into Blender's user modules folder (optional: only for non-Xbox "
                      "controllers, or macOS/Linux). Blender freezes for a few seconds")

    def execute(self, context):
        py = sys.executable
        target = bpy.utils.user_resource('SCRIPTS', path="modules", create=True)
        try:
            subprocess.run([py, "-m", "ensurepip", "--upgrade"], capture_output=True)
            proc = subprocess.run([py, "-m", "pip", "install", "--upgrade", "--target", target, "pygame"],
                                  capture_output=True, text=True)
        except Exception as exc:
            self.report({'ERROR'}, "Could not run pip: %s" % exc)
            return {'CANCELLED'}
        if proc.returncode != 0:
            print(proc.stdout, proc.stderr)
            self.report({'ERROR'}, "pip failed - see the system console")
            return {'CANCELLED'}
        if target not in sys.path:
            sys.path.append(target)
        importlib.invalidate_caches()
        self.report({'INFO'}, "pygame installed - start walking again to use it")
        return {'FINISHED'}


# ----------------------------------------------------------------------------
# UI
# ----------------------------------------------------------------------------

class WALK_PT_main(bpy.types.Panel):
    bl_idname = "WALK_PT_main"
    bl_label = "Walk Navigator"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Walk"

    def draw(self, context):
        layout = self.layout
        s = context.scene.walk_nav
        empty, cam = _resolve_targets(context, s)

        col = layout.column(align=True)
        col.prop(s, "target_empty", text="Empty")
        col.prop(s, "target_camera", text="Camera")
        if empty is not None and cam is not None:
            if cam.parent != empty:
                box = layout.box()
                box.label(text="Camera is not a child of the Empty", icon='ERROR')
                box.operator("walk_nav.parent_camera", icon='LINKED')
            else:
                layout.label(text="Walking: %s  /  %s" % (empty.name, cam.name), icon='CHECKMARK')
        else:
            layout.label(text="Select an Empty and set a scene camera", icon='ERROR')

        layout.prop(s, "use_gravity", text="Gravity (off = fly)", toggle=True,
                    icon='SORTSIZE' if s.use_gravity else 'FORCE_FORCE')
        row = layout.row()
        row.scale_y = 1.6
        row.operator("walk_nav.start", icon='PLAY')
        layout.label(text="Stop: Esc / right-click / Enter", icon='INFO')


class _SubPanel:
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Walk"
    bl_parent_id = "WALK_PT_main"
    bl_options = {'DEFAULT_CLOSED'}


class WALK_PT_movement(_SubPanel, bpy.types.Panel):
    bl_label = "Movement & Gravity"

    def draw(self, context):
        s = context.scene.walk_nav
        col = self.layout
        col.use_property_split = True
        col.use_property_decorate = False
        col.prop(s, "walk_speed")
        col.prop(s, "sprint_multiplier")
        col.prop(s, "acceleration")
        col.prop(s, "fly_above_ground")
        sub = col.column()
        sub.active = s.use_gravity
        sub.prop(s, "gravity")
        sub.prop(s, "jump_height")
        sub.prop(s, "step_height")
        sub.prop(s, "ground_smoothing")
        sub.prop(s, "void_depth")


class WALK_PT_look(_SubPanel, bpy.types.Panel):
    bl_label = "Look & Camera"

    def draw(self, context):
        s = context.scene.walk_nav
        col = self.layout
        col.use_property_split = True
        col.use_property_decorate = False
        col.prop(s, "mouse_sensitivity")
        col.prop(s, "invert_look_y")
        col.prop(s, "key_turn_speed")
        col.prop(s, "pitch_up_limit")
        col.prop(s, "pitch_down_limit")
        col.prop(s, "camera_pivot")
        col.prop(s, "camera_view")
        col.prop(s, "restore_camera")


class WALK_PT_actions(_SubPanel, bpy.types.Panel):
    bl_label = "Actions (A / B / X)"

    def draw(self, context):
        s = context.scene.walk_nav
        col = self.layout
        col.use_property_split = True
        col.use_property_decorate = False
        col.label(text="Gamepad A, B, X  (keys 1, 2, 3)")
        for slot in ("a", "b", "x"):
            col.prop(s, "action_" + slot, text="Button " + slot.upper())
            if getattr(s, "action_" + slot) == 'RUN_OPERATOR':
                col.prop(s, "action_%s_operator" % slot, text="Operator ID")
        col.label(text="Y = jump / rise (fixed)")


class WALK_PT_gamepad(_SubPanel, bpy.types.Panel):
    bl_label = "Gamepad"

    def draw(self, context):
        s = context.scene.walk_nav
        col = self.layout
        col.use_property_split = True
        col.use_property_decorate = False
        col.prop(s, "use_gamepad")
        sub = col.column()
        sub.active = s.use_gamepad
        sub.prop(s, "gamepad_backend")
        sub.prop(s, "left_stick_x")
        sub.prop(s, "gamepad_deadzone")
        sub.prop(s, "gamepad_look_speed")
        sub.prop(s, "gamepad_invert_y")

        xi = sys.platform == "win32"
        pg = importlib.util.find_spec("pygame") is not None
        box = col.box()
        box.label(text="XInput (Xbox pads): %s" % ("available" if xi else "Windows only"),
                  icon='CHECKMARK' if xi else 'X')
        box.label(text="pygame (other pads): %s" % ("installed" if pg else "not installed"),
                  icon='CHECKMARK' if pg else 'X')
        if not pg:
            box.operator("walk_nav.install_pygame", icon='IMPORT')


# ----------------------------------------------------------------------------
# Registration
# ----------------------------------------------------------------------------

_classes = (
    WalkNavSettings,
    WALK_OT_start,
    WALK_OT_parent_camera,
    WALK_OT_install_pygame,
    WALK_PT_main,
    WALK_PT_movement,
    WALK_PT_look,
    WALK_PT_actions,
    WALK_PT_gamepad,
)
_keymaps = []


def register():
    for cls in _classes:
        bpy.utils.register_class(cls)
    bpy.types.Scene.walk_nav = PointerProperty(type=WalkNavSettings)
    kc = bpy.context.window_manager.keyconfigs.addon
    if kc:
        km = kc.keymaps.new(name="3D View", space_type='VIEW_3D')
        kmi = km.keymap_items.new(WALK_OT_start.bl_idname, 'W', 'PRESS', ctrl=True, shift=True)
        _keymaps.append((km, kmi))


def unregister():
    if _ACTIVE is not None:
        _ACTIVE.request_stop()
    for km, kmi in _keymaps:
        km.keymap_items.remove(kmi)
    _keymaps.clear()
    del bpy.types.Scene.walk_nav
    for cls in reversed(_classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
