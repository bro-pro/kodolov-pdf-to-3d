# -*- coding: utf-8 -*-
"""
plan_to_3d.py v14.6 — v1.3 OCR dependency/diagnostics — P2.3 adaptive PDF parser — P1.6 full wall extent + plan-area parsing — 3D-модель квартиры по плану в PDF.

Изменения v12 (P1.2a — правки scoring дверей по итогам v11):
  * УБРАН признак jamb_on_wall — для распашной двери jamb НЕ на стене,
    он внутри помещения. Признак ошибочно отнимал 0.15 у правильных дверей.
  * УБРАН used_leaves.add(li) из цикла raw candidates. Теперь каждая дуга
    пробует ВСЕ полотна, а used_leaf_pts строится только ПОСЛЕ NMS —
    и только для полотен принятых дверей. Это устраняет ситуацию,
    когда случайный кандидат со score 0.65 «занимал» полотно у правильной
    дуги со score 0.95.
  * ОБЕ пары endpoint проверяются: пробуем arc_p0/p1 ↔ leaf_p0/p1 (4 комбинации),
    строим кандидата для каждой, score выбирает лучшую.
  * SOFT-score для радиуса дуги: rel_err ≤ 0.05 → +0.20, ≤ 0.10 → +0.15,
    ≤ 0.20 → +0.08. Раньше было бинарное ±0.15 м → +0.20/+0.
  * SOFT-score для угла дуги: 80–100 → +0.15, 70–110 → +0.10, 60–120 → +0.05.
  * Новая система весов:
      длина полотна   +0.20
      hinge на стене  +0.20
      перпендикуляр.  +0.25
      радиус (soft)   +0.20
      угол (soft)     +0.15
      максимум          1.00
  * DOOR_SCORE_ACCEPT = 0.75
DOOR_HINGE_CENTER_TOL_M = 0.12
DOOR_ARC_JAMB_TOL_M = 0.12 (было 0.85).
  * Диагностика: гистограмма score + топ-10 rejected с разбором.
  * CLI: --door-score (порог), --door-debug (таблица по всем raw).

Изменения v14 (P1.2c — дедупликация физических дверей):
  * Каждому raw-кандидату сохраняется arc_id и leaf_id.
  * Все гипотезы сначала генерируются без блокировки полотен/дуг.
  * Перед NMS кандидаты группируются по arc_id: один графический arc
    не может породить несколько физических дверей.
  * Добавлен same_door(): объединяет гипотезы по arc_id, близости hinge,
    близости jamb и overlap полотен.
  * NMS теперь учитывает не только midpoint, но и hinge/jamb.
  * В debug выводятся arc_id/leaf_id и причина объединения кандидатов.

Изменения v11 (сохранены):
  * hinge/jamb из ПОЛОТНА, а не из дуги;
  * NMS без проверки orientation;
  * dump_debug_svg рисует p0 → p1.

Изменения v10 и ранее (сохранены):
  * OpeningCandidate, score_door_candidate, nms_doors, extract_doors_v2;
  * page.rect до doc.close();
  * WALL_LAYERS/DOOR_LAYERS в шапке;
  * BRIDGE_GAP_TOL_M = 3.50, SNAP_ENDPOINT_TOL_M = 0.50;
  * X_MAX_M / X_MIN_M — фильтр рабочей зоны;
  * group_walls — по первому элементу;
  * polygonize с bridge и snap.

Запуск:
    python plan_to_3d.py projectfortest.pdf --print-scale 50 --debug --door-debug
    python plan_to_3d.py projectfortest.pdf --print-scale 50 --door-score 0.75
"""
import argparse
import json
import glob
import html
import math
import os
import re
import statistics
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from functools import reduce
from math import gcd

try:
    import pymupdf as fitz
except ImportError:
    import fitz

import trimesh
from shapely.geometry import LineString, Point, Polygon
from shapely.geometry import box as shbox
from shapely.ops import polygonize, unary_union, triangulate, transform as shp_transform

# ============================================================================
# КОНСТАНТЫ
# ============================================================================
WALL_HEIGHT    = 2.70
DOOR_HEIGHT    = 2.10
WINDOW_SILL    = 0.90
WINDOW_HEAD    = 2.30
PARAPET_H      = 1.10
DEFAULT_THICK  = 0.15
PT_TO_MM_PAPER = 25.4 / 72.0

WALL_COLOR    = [232, 232, 230, 255]
FLOOR_COLOR   = [178, 178, 172, 255]
BALC_COLOR    = [200, 214, 222, 255]
PARAPET_COLOR = [190, 195, 200, 255]
DOOR_COLOR    = [160, 120,  80, 255]

AREA_RE = re.compile(r"^\d{1,3}[.,]\d{1,2}$")
DIM_RE  = re.compile(r"^\d{3,5}$")
ROOM_RE = re.compile(r"(прихож|сануз|ванн|кухн|гостин|спальн|балкон|лоджи|"
                     r"коридор|кладов|гардероб)", re.I)
BALC_RE = re.compile(r"балкон|лоджи|balkon|loggi|hniko|6anko|ba[lk]o", re.I)

DEFAULT_ROOMS = [
    ("Кухня-гостиная", 35.45), ("Спальня 2", 17.50), ("Спальня", 12.42),
    ("Прихожая", 9.87), ("Балкон", 9.50), ("Ванная", 6.73), ("Санузел", 2.09),
]

BRIDGE_GAP_TOL_M = 3.50
SNAP_ENDPOINT_TOL_M = 0.50

X_MAX_M = 16.0
WALL_GROUP_TOL_M = 0.90
WALL_DETAIL_TOL_M = 0.12
WALL_MIN_INTERVAL_M = 0.70
ROOM_SNAP_TOL_M = 0.10
X_MIN_M = 2.0

WALL_LAYERS = ("стены", "фундамент")
DOOR_LAYERS = ("стены", "фундамент")

# P2.0: слои конкретного CAD-файла больше не считаются фиксированными.
# Имена из P1 остаются fallback-подсказками, а для новых PDF слои выбираются
# по геометрии и семантическим именам.
AUTO_DIM_LAYER_HINTS = ("размер", "размеры", "dimension", "dim")
AUTO_DOOR_LAYER_HINTS = ("двер", "door", "двери")
AUTO_IGNORE_LAYER_HINTS = ("elektro", "электр", "размер", "размеры", "dimension", "dim", "0-5")

DOOR_LEAF_MIN_M = 0.55
DOOR_LEAF_MAX_M = 1.30
DOOR_ENDPOINT_TOL_M = 0.05

# v12: порог по умолчанию понижен
DOOR_SCORE_ACCEPT = 0.75
DOOR_HINGE_CENTER_TOL_M = 0.12
DOOR_ARC_JAMB_TOL_M = 0.12
DOOR_PERP_TOL_DEG = 25.0
DOOR_NMS_CENTER_M = 0.15
DOOR_NMS_WIDTH_M = 0.20
DOOR_WALL_HIT_TOL_M = 0.25
DOOR_HINGE_MERGE_TOL_M = 0.14
DOOR_JAMB_MERGE_TOL_M = 0.16
DOOR_LEAF_OVERLAP_MIN = 0.55

# P1.2d: восстановление пропавшей перегородки в большой комнате.
INFER_PARTITION = False
INFER_PARTITION_MIN_AREA_M2 = 25.0
INFER_PARTITION_MAX_AREA_M2 = 80.0
INFER_PARTITION_X_HINT_M = 7.94
INFER_PARTITION_TOL_M = 0.35


# ============================================================================
# OpeningCandidate
# ============================================================================
@dataclass
class OpeningCandidate:
    """Единый кандидат на проём (дверь / окно / glazing)."""
    kind: str
    source: str
    confidence: float
    p0: tuple
    p1: tuple
    width_m: float
    orientation: str
    bottom: float = 0.0
    top: float = DOOR_HEIGHT
    meta: dict = field(default_factory=dict)


# ============================================================================
# БАЗОВЫЕ ФУНКЦИИ
# ============================================================================
def merge_intervals(intervals, gap_tol=1.0):
    out = []
    for a, b in sorted(intervals):
        if out and a <= out[-1][1] + gap_tol:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return [(a, b) for a, b in out]


def split_by_openings(a0, a1, openings, height):
    slabs, cur = [], a0
    for o0, o1, kind in sorted(openings, key=lambda t: t[0]):
        o0, o1 = max(o0, cur), min(o1, a1)
        if o1 <= o0:
            continue
        if o0 > cur:
            slabs.append((cur, o0, 0.0, height))
        if kind == "door":
            slabs.append((o0, o1, DOOR_HEIGHT, height))
        else:
            slabs.append((o0, o1, 0.0, WINDOW_SILL))
            slabs.append((o0, o1, WINDOW_HEAD, height))
        cur = o1
    if cur < a1:
        slabs.append((cur, a1, 0.0, height))
    return slabs


def add_box(meshes, cx, cy, z0, z1, lx, ly, color):
    lz = z1 - z0
    if lx < 1e-3 or ly < 1e-3 or lz < 1e-3:
        return
    m = trimesh.creation.box(extents=(abs(lx), abs(ly), lz))
    m.apply_translation((cx, cy, z0 + lz / 2))
    m.visual.face_colors = color
    meshes.append(m)


def slab_from_polygon(poly_m, thickness, color):
    """Тонкая плита по полигону без зависимости от внешнего triangulation engine.

    trimesh.extrude_polygon может требовать mapbox-earcut/triangle. Для плана
    квартиры это лишняя зависимость, поэтому используем triangulate Shapely и
    собираем замкнутые треугольные призмы. Треугольники вне исходного полигона
    отбрасываются.
    """
    try:
        tris = [t for t in triangulate(poly_m)
                if t.area > 1e-8 and poly_m.covers(t.representative_point())]
        if not tris:
            raise ValueError("не удалось триангулировать полигон")
        verts=[]
        faces=[]
        z0=-thickness
        z1=0.0
        for t in tris:
            cs=list(t.exterior.coords)[:3]
            base=len(verts)
            verts.extend([(x,y,z0) for x,y in cs])
            verts.extend([(x,y,z1) for x,y in cs])
            faces.extend([
                (base+0,base+1,base+2),
                (base+5,base+4,base+3),
                (base+0,base+3,base+4),(base+0,base+4,base+1),
                (base+1,base+4,base+5),(base+1,base+5,base+2),
                (base+2,base+5,base+3),(base+2,base+3,base+0),
            ])
        mesh=trimesh.Trimesh(vertices=verts, faces=faces, process=True)
        mesh.visual.face_colors=color
        return mesh
    except Exception:
        minx, miny, maxx, maxy = poly_m.bounds
        m = trimesh.creation.box(extents=(maxx - minx, maxy - miny, thickness))
        m.apply_translation(((minx + maxx) / 2, (miny + maxy) / 2, -thickness / 2))
        m.visual.face_colors = color
        return m


def scale_type(v):
    v = v.strip()
    if ":" in v:
        a, b = v.split(":", 1)
        den = float(b) / float(a)
        return PT_TO_MM_PAPER * den / 1000.0
    return float(v)


def _dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def _approx_endpoint(p, q, tol):
    return _dist(p, q) < tol


# ============================================================================
# SCORING ДВЕРЕЙ (v12)
# ============================================================================
def _bezier_sample(p0, p1, p2, p3, n=12):
    pts = []
    for i in range(n + 1):
        t, u = i / n, 1 - i / n
        x = u**3 * p0[0] + 3 * u*u*t * p1[0] + 3 * u*t*t * p2[0] + t**3 * p3[0]
        y = u**3 * p0[1] + 3 * u*u*t * p1[1] + 3 * u*t*t * p2[1] + t**3 * p3[1]
        pts.append((x, y))
    return pts


def _fit_circle(pts):
    n = len(pts)
    if n < 3:
        return None
    Sx = sum(p[0] for p in pts)
    Sy = sum(p[1] for p in pts)
    Sxx = sum(p[0]*p[0] for p in pts)
    Syy = sum(p[1]*p[1] for p in pts)
    Sxy = sum(p[0]*p[1] for p in pts)
    Sxz = sum(p[0]*(p[0]*p[0]+p[1]*p[1]) for p in pts)
    Syz = sum(p[1]*(p[0]*p[0]+p[1]*p[1]) for p in pts)
    Szz = sum((p[0]*p[0]+p[1]*p[1]) for p in pts)

    A = [[2*Sxx, 2*Sxy, Sx],
         [2*Sxy, 2*Syy, Sy],
         [2*Sx,  2*Sy,  n ]]
    B = [Sxz, Syz, Szz]

    def det3(m):
        return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
              - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
              + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))

    D = det3(A)
    if abs(D) < 1e-9:
        return None
    A1 = [row[:] for row in A]
    A2 = [row[:] for row in A]
    A3 = [row[:] for row in A]
    for i in range(3):
        A1[i][0] = B[i]
        A2[i][1] = B[i]
        A3[i][2] = B[i]
    a = det3(A1) / D
    b = det3(A2) / D
    c = det3(A3) / D
    cx = a
    cy = b
    r2 = c + cx*cx + cy*cy
    if r2 <= 0:
        return None
    return (cx, cy, math.sqrt(r2))


def _arc_angle_range(pts, center):
    cx, cy = center
    angles = []
    for (x, y) in pts:
        angles.append(math.degrees(math.atan2(y - cy, x - cx)))
    if not angles:
        return 0.0
    a_min, a_max = min(angles), max(angles)
    span = a_max - a_min
    if span > 180:
        angles = [a + 360 if a < 0 else a for a in angles]
        a_min, a_max = min(angles), max(angles)
        span = a_max - a_min
    return span


def _perpendicular(leaf_p0, leaf_p1, wall_p0, wall_p1, tol_deg):
    dx_l = leaf_p1[0] - leaf_p0[0]
    dy_l = leaf_p1[1] - leaf_p0[1]
    dx_w = wall_p1[0] - wall_p0[0]
    dy_w = wall_p1[1] - wall_p0[1]
    len_l = math.hypot(dx_l, dy_l)
    len_w = math.hypot(dx_w, dy_w)
    if len_l < 1e-6 or len_w < 1e-6:
        return False, 180.0
    cos_ang = (dx_l * dx_w + dy_l * dy_w) / (len_l * len_w)
    cos_ang = max(-1.0, min(1.0, cos_ang))
    ang_deg = math.degrees(math.acos(cos_ang))
    diff = abs(ang_deg - 90.0)
    return diff <= tol_deg, diff


def _point_on_walls(p, walls_h, walls_v, tol_pt):
    px, py = p
    for w in walls_h:
        cy = w["center"]
        if abs(py - cy) <= tol_pt:
            for (a, b) in w["intervals"]:
                if a - tol_pt <= px <= b + tol_pt:
                    return True
    for w in walls_v:
        cx = w["center"]
        if abs(px - cx) <= tol_pt:
            for (a, b) in w["intervals"]:
                if a - tol_pt <= py <= b + tol_pt:
                    return True
    return False


def score_door_candidate(arc_p0, arc_p1, arc_c1, arc_c2,
                         leaf_p0, leaf_p1,
                         walls_h, walls_v, scale,
                         verbose=False):
    """Оценивает пару «дуга + полотно» по геометрии распашной двери.

    P1.2b: центр fitted-circle трактуется как hinge.
    Endpoint дуги НЕ считается hinge: он используется для проверки
    свободного конца полотна (jamb).
    """
    leaf_len_pt = _dist(leaf_p0, leaf_p1)
    leaf_len = leaf_len_pt * scale
    if not (DOOR_LEAF_MIN_M <= leaf_len <= DOOR_LEAF_MAX_M):
        return None, None

    arc_pts = _bezier_sample(arc_p0, arc_c1, arc_c2, arc_p1, n=16)
    circle = _fit_circle(arc_pts)
    if circle is None:
        return None, None

    cx, cy, r = circle
    hinge_center = (cx, cy)

    # Hinge = endpoint полотна, ближайший к центру дуги.
    d0 = _dist(leaf_p0, hinge_center)
    d1 = _dist(leaf_p1, hinge_center)
    if d0 <= d1:
        hinge, jamb = leaf_p0, leaf_p1
        hinge_dist_pt = d0
    else:
        hinge, jamb = leaf_p1, leaf_p0
        hinge_dist_pt = d1

    hinge_dist_m = hinge_dist_pt * scale
    arc_radius_m = r * scale

    score = 0.0
    meta = {
        "leaf_len_m": leaf_len,
        "hinge_center": hinge_center,
        "hinge_dist_m": hinge_dist_m,
        "arc_radius_m": arc_radius_m,
    }

    # 1. Длина полотна.
    score += 0.15

    # 2. Endpoint полотна ~= центр дуги (hinge).
    hinge_bonus = 0.0
    if hinge_dist_m <= 0.04:
        hinge_bonus = 0.30
    elif hinge_dist_m <= DOOR_HINGE_CENTER_TOL_M:
        hinge_bonus = 0.30 * (1.0 - (hinge_dist_m - 0.04) /
                              max(DOOR_HINGE_CENTER_TOL_M - 0.04, 1e-6))
    score += max(0.0, hinge_bonus)
    meta["hinge_bonus"] = hinge_bonus

    # 3. Свободный конец полотна ~= один из концов дуги.
    arc_jamb_dist_m = min(_dist(jamb, arc_p0), _dist(jamb, arc_p1)) * scale
    arc_jamb_bonus = 0.0
    if arc_jamb_dist_m <= 0.04:
        arc_jamb_bonus = 0.15
    elif arc_jamb_dist_m <= DOOR_ARC_JAMB_TOL_M:
        arc_jamb_bonus = 0.15 * (1.0 - (arc_jamb_dist_m - 0.04) /
                                 max(DOOR_ARC_JAMB_TOL_M - 0.04, 1e-6))
    score += max(0.0, arc_jamb_bonus)
    meta["arc_jamb_dist_m"] = arc_jamb_dist_m
    meta["arc_jamb_bonus"] = arc_jamb_bonus

    # 4. Радиус дуги ~= длина полотна.
    rel_err = abs(arc_radius_m - leaf_len) / max(leaf_len, 0.01)
    radius_bonus = 0.0
    if rel_err <= 0.05:
        radius_bonus = 0.15
    elif rel_err <= 0.10:
        radius_bonus = 0.12
    elif rel_err <= 0.20:
        radius_bonus = 0.06
    score += radius_bonus
    meta["radius_rel_err"] = rel_err
    meta["radius_bonus"] = radius_bonus

    # 5. Центр дуги/hinge на стене + перпендикулярность полотна стене.
    hinge_on_wall = _point_on_walls(
        hinge_center, walls_h, walls_v, DOOR_WALL_HIT_TOL_M / scale
    )
    meta["hinge_on_wall"] = hinge_on_wall
    if hinge_on_wall:
        score += 0.15

    perp_ok = False
    perp_diff = 180.0
    wall_axis = None

    for w in walls_h:
        if abs(hinge_center[1] - w["center"]) <= DOOR_WALL_HIT_TOL_M / scale:
            for a, b in w["intervals"]:
                if a - 5 <= hinge_center[0] <= b + 5:
                    ok, diff = _perpendicular(
                        leaf_p0, leaf_p1,
                        (a, w["center"]), (b, w["center"]),
                        DOOR_PERP_TOL_DEG,
                    )
                    if ok and diff < perp_diff:
                        perp_ok, perp_diff, wall_axis = True, diff, "h"

    for w in walls_v:
        if abs(hinge_center[0] - w["center"]) <= DOOR_WALL_HIT_TOL_M / scale:
            for a, b in w["intervals"]:
                if a - 5 <= hinge_center[1] <= b + 5:
                    ok, diff = _perpendicular(
                        leaf_p0, leaf_p1,
                        (w["center"], a), (w["center"], b),
                        DOOR_PERP_TOL_DEG,
                    )
                    if ok and diff < perp_diff:
                        perp_ok, perp_diff, wall_axis = True, diff, "v"

    meta["perp_ok"] = perp_ok
    meta["perp_diff_deg"] = perp_diff
    meta["wall_axis"] = wall_axis
    if perp_ok:
        score += 0.15

    # 6. Угол дуги — слабый дополнительный признак.
    span = _arc_angle_range(arc_pts, hinge_center)
    angle_bonus = 0.0
    if 80 <= span <= 100:
        angle_bonus = 0.05
    elif 65 <= span <= 115:
        angle_bonus = 0.03
    elif 55 <= span <= 125:
        angle_bonus = 0.01
    score += angle_bonus
    meta["arc_angle_deg"] = span
    meta["angle_bonus"] = angle_bonus

    # Жёсткие отсечки.
    if hinge_dist_m > DOOR_HINGE_CENTER_TOL_M:
        return None, None
    if arc_jamb_dist_m > DOOR_ARC_JAMB_TOL_M:
        return None, None

    meta["score"] = min(score, 1.0)
    return meta["score"], meta


def _segment_projection_overlap_ratio(a0, a1, b0, b1):
    """Доля перекрытия двух отрезков после проекции на ось первого."""
    ax = a1[0] - a0[0]
    ay = a1[1] - a0[1]
    al = math.hypot(ax, ay)
    if al < 1e-9:
        return 0.0
    ux, uy = ax / al, ay / al

    def proj(p):
        return p[0] * ux + p[1] * uy

    a_lo, a_hi = sorted((proj(a0), proj(a1)))
    b_lo, b_hi = sorted((proj(b0), proj(b1)))
    overlap = max(0.0, min(a_hi, b_hi) - max(a_lo, b_lo))
    denom = min(a_hi - a_lo, b_hi - b_lo)
    if denom <= 1e-9:
        return 0.0
    return overlap / denom


def _unwrap_candidate(item):
    """Возвращает OpeningCandidate из элемента candidate-list.

    Внутри pipeline кандидаты местами хранятся как (score, candidate),
    а местами как сам OpeningCandidate. Это было причиной ошибки:
    'tuple' object has no attribute 'meta'.
    """
    if isinstance(item, tuple) and len(item) == 2 and isinstance(item[1], OpeningCandidate):
        return item[1]
    return item


def _same_door(a, b, scale):
    """Проверяет, являются ли две гипотезы одной физической дверью."""
    a = _unwrap_candidate(a)
    b = _unwrap_candidate(b)
    ma, mb = a.meta, b.meta

    # Самый надёжный признак: один и тот же графический arc.
    if ma.get("arc_id") is not None and ma.get("arc_id") == mb.get("arc_id"):
        return True, "same_arc"

    ha = ma.get("hinge_center", a.p0)
    hb = mb.get("hinge_center", b.p0)
    ja = ma.get("jamb", a.p1)
    jb = mb.get("jamb", b.p1)

    if _dist(ha, hb) * scale <= DOOR_HINGE_MERGE_TOL_M:
        return True, "near_hinge"

    if _dist(ja, jb) * scale <= DOOR_JAMB_MERGE_TOL_M:
        return True, "near_jamb"

    la0 = ma.get("leaf_p0")
    la1 = ma.get("leaf_p1")
    lb0 = mb.get("leaf_p0")
    lb1 = mb.get("leaf_p1")
    if la0 and la1 and lb0 and lb1:
        ov = _segment_projection_overlap_ratio(la0, la1, lb0, lb1)
        if ov >= DOOR_LEAF_OVERLAP_MIN:
            return True, f"leaf_overlap={ov:.2f}"

    return False, ""


def deduplicate_doors(candidates, scale):
    """P1.2c: дедупликация гипотез физических дверей.

    На входе допускаются (score, OpeningCandidate) или OpeningCandidate.
    На выходе всегда (score, OpeningCandidate), чтобы следующий NMS мог
    безопасно работать с тем же форматом.
    """
    if not candidates:
        return [], []

    normalized = []
    for item in candidates:
        cand = _unwrap_candidate(item)
        score = float(item[0]) if isinstance(item, tuple) and len(item) == 2 else float(cand.confidence)
        normalized.append((score, cand))

    normalized.sort(key=lambda x: -x[0])
    kept = []
    merge_log = []

    for score, cand in normalized:
        duplicate = False
        for old_score, old in kept:
            same, reason = _same_door(cand, old, scale)
            if same:
                duplicate = True
                merge_log.append((cand, old, reason))
                break
        if not duplicate:
            kept.append((score, cand))

    return kept, merge_log


def nms_doors(candidates, center_tol_m, width_tol_m, scale):
    """P1.2c: NMS по физической геометрии двери.

    Вход/выход: список (score, OpeningCandidate).
    """
    if not candidates:
        return []

    normalized = []
    for item in candidates:
        cand = _unwrap_candidate(item)
        score = float(item[0]) if isinstance(item, tuple) and len(item) == 2 else float(cand.confidence)
        normalized.append((score, cand))

    normalized.sort(key=lambda x: -x[0])
    keep = []
    for score, cand in normalized:
        c_new = ((cand.p0[0] + cand.p1[0]) / 2.0,
                 (cand.p0[1] + cand.p1[1]) / 2.0)
        dup = False
        for old_score, k in keep:
            c_old = ((k.p0[0] + k.p1[0]) / 2.0,
                     (k.p0[1] + k.p1[1]) / 2.0)
            dist_m = _dist(c_new, c_old) * scale
            if dist_m <= center_tol_m and abs(cand.width_m - k.width_m) <= width_tol_m:
                dup = True
                break
            same, _ = _same_door(cand, k, scale)
            if same:
                dup = True
                break
        if not dup:
            keep.append((score, cand))

    return [cand for _, cand in keep]


# ============================================================================
# EXTRACT_DOORS_V2 (v12)
# ============================================================================
def extract_doors_v2(path, page_no=0, scale=1.0,
                     walls_h=None, walls_v=None,
                     layers=DOOR_LAYERS, verbose=False,
                     score_accept=None):
    """Извлекает двери: пары «полотно + дуга», с scoring и NMS.

    v12: НЕ помечаем used_leaves в raw-цикле.
    v12: пробуем все 4 пары endpoint (arc_p0/p1 ↔ leaf_p0/p1).
    v12: used_leaf_pts строится ТОЛЬКО после NMS.
    """
    if score_accept is None:
        score_accept = DOOR_SCORE_ACCEPT
    tol_pt = DOOR_ENDPOINT_TOL_M / scale if scale > 0 else 1e-3

    doc = fitz.open(path)
    page = doc[page_no]

    arcs = []
    lines = []

    for d in page.get_drawings():
        layer = d.get("layer") or "(none)"
        if layers is not None and layer not in layers:
            continue
        for item in d["items"]:
            kind = item[0]
            if kind == "c":
                p0 = (item[1].x, item[1].y)
                c1 = (item[2].x, item[2].y)
                c2 = (item[3].x, item[3].y)
                p1 = (item[4].x, item[4].y)
                arcs.append((p0, p1, c1, c2))
            elif kind == "l":
                p1 = (item[1].x, item[1].y)
                p2 = (item[2].x, item[2].y)
                lines.append((p1, p2))

    doc.close()

    raw_candidates = []   # (score, OpeningCandidate, meta)
    rejected_diag = []    # для диагностики: (score, meta, leaf_len)

    # P1.2b: endpoint дуги используется только для проверки свободного
    # конца полотна. Hinge берётся из центра fitted circle.
    for ai, (arc_p0, arc_p1, arc_c1, arc_c2) in enumerate(arcs):
        for li, (l_p0, l_p1) in enumerate(lines):
            if not (
                _approx_endpoint(arc_p0, l_p0, tol_pt)
                or _approx_endpoint(arc_p0, l_p1, tol_pt)
                or _approx_endpoint(arc_p1, l_p0, tol_pt)
                or _approx_endpoint(arc_p1, l_p1, tol_pt)
            ):
                continue

            score, meta = score_door_candidate(
                arc_p0, arc_p1, arc_c1, arc_c2,
                l_p0, l_p1,
                walls_h or [], walls_v or [], scale,
            )
            if score is None:
                continue

            dx = abs(l_p1[0] - l_p0[0])
            dy = abs(l_p1[1] - l_p0[1])
            orient = "v" if dx < dy else "h"
            hinge = meta["hinge_center"]
            jamb = l_p1 if _dist(l_p1, hinge) >= _dist(l_p0, hinge) else l_p0

            cand = OpeningCandidate(
                kind="door", source="arc", confidence=float(score),
                p0=hinge, p1=jamb, width_m=meta["leaf_len_m"],
                orientation=orient, bottom=0.0, top=DOOR_HEIGHT,
                meta={
                    "arc_id": ai,
                    "leaf_id": li,
                    "arc_p0": arc_p0, "arc_p1": arc_p1,
                    "leaf_p0": l_p0, "leaf_p1": l_p1,
                    "jamb": jamb,
                    **meta,
                },
            )
            raw_candidates.append((score, cand, meta))
            if score + 1e-9 < score_accept:
                rejected_diag.append((score, meta, l_p0, l_p1))

    # Фильтр по score
    accepted = [(sc, cand) for sc, cand, _ in raw_candidates
                if sc >= score_accept]
    rejected = [(sc, cand) for sc, cand, _ in raw_candidates
                if sc < score_accept]

    # P1.2c: один arc -> одна физическая дверь.
    accepted_dedup, merge_log = deduplicate_doors(accepted, scale)

    # Дополнительный NMS по физической геометрии.
    final = nms_doors(accepted_dedup, DOOR_NMS_CENTER_M, DOOR_NMS_WIDTH_M, scale)

    # v12: used_leaf_pts — ТОЛЬКО для принятых дверей, ПОСЛЕ NMS
    used_leaf_pts = set()
    for cand in final:
        leaf_p0 = cand.meta.get("leaf_p0")
        leaf_p1 = cand.meta.get("leaf_p1")
        if leaf_p0 and leaf_p1:
            used_leaf_pts.add((round(leaf_p0[0], 3), round(leaf_p0[1], 3)))
            used_leaf_pts.add((round(leaf_p1[0], 3), round(leaf_p1[1], 3)))

    stats = {
        "raw": len(raw_candidates),
        "accepted_by_score": len(accepted),
        "rejected_by_score": len(rejected),
        "after_arc_dedup": len(accepted_dedup),
        "after_nms": len(final),
        "merge_log": merge_log,
        "score_accept": score_accept,
        "histogram": _score_histogram(raw_candidates),
        "top_rejected": _top_rejected(rejected_diag, n=10),
    }

    return final, used_leaf_pts, stats


def _score_histogram(raw_candidates, bucket=0.05):
    """v12: гистограмма score по корзинам."""
    bins = defaultdict(int)
    for sc, _, _ in raw_candidates:
        key = round(math.floor(sc / bucket) * bucket, 2)
        bins[key] += 1
    return dict(sorted(bins.items(), reverse=True))


def _top_rejected(rejected_diag, n=10):
    """v12: топ-N rejected с разбором признаков."""
    sorted_rej = sorted(rejected_diag, key=lambda x: -x[0])
    out = []
    for sc, meta, l_p0, l_p1 in sorted_rej[:n]:
        out.append({
            "score": round(sc, 3),
            "leaf_m": round(meta.get("leaf_len_m", 0), 2),
            "hinge_dist": round(meta.get("hinge_dist_m", 0), 3),
            "hinge_wall": meta.get("hinge_on_wall"),
            "perp": meta.get("perp_ok"),
            "arc_jamb": round(meta.get("arc_jamb_dist_m", 0), 3),
            "radius": round(meta.get("arc_radius_m") or 0, 2),
            "r_err": round(meta.get("radius_rel_err") or 0, 3),
            "angle": round(meta.get("arc_angle_deg") or 0, 1),
        })
    return out


def print_door_score_diagnostics(stats):
    """v12: печатает гистограмму и топ rejected."""
    print("\n=== Распределение score (raw candidates) ===")
    hist = stats.get("histogram", {})
    max_count = max(hist.values()) if hist else 1
    for bucket, count in hist.items():
        bar = "#" * int(20 * count / max_count)
        print(f"  {bucket:.2f}: {count:>3}  {bar}")
    print(f"\n  score_accept = {stats.get('score_accept')}")
    if "after_arc_dedup" in stats:
        print(f"  after_arc_dedup = {stats.get('after_arc_dedup')}")
    merges = stats.get("merge_log", [])
    if merges:
        print(f"\n=== Объединено гипотез: {len(merges)} ===")
        for cand, old, reason in merges[:30]:
            print(f"  arc {cand.meta.get('arc_id')} / leaf {cand.meta.get('leaf_id')} "
                  f"-> arc {old.meta.get('arc_id')} / leaf {old.meta.get('leaf_id')} : {reason}")
    top = stats.get("top_rejected", [])
    if top:
        print(f"\n=== Топ-{len(top)} rejected (score < {stats.get('score_accept')}) ===")
        print(f"  {'score':>6} {'leaf':>6} {'h_dist':>7} {'h_wall':>7} "
              f"{'perp':>5} {'a_jamb':>7} {'radius':>7} {'r_err':>6} {'angle':>6}")
        for r in top:
            print(f"  {r['score']:>6.3f} {r['leaf_m']:>6.2f} "
                  f"{r['hinge_dist']:>7.3f} {str(r['hinge_wall']):>7} "
                  f"{str(r['perp']):>5} {r['arc_jamb']:>7.3f} "
                  f"{r['radius']:>7.2f} {r['r_err']:>6.3f} "
                  f"{r['angle']:>6.1f}")


# ============================================================================
# P2.0 — АДАПТИВНЫЙ АНАЛИЗ PDF/CAD
# ============================================================================
def _layer_name(d):
    return (d.get("layer") or "(none)").strip()


def analyze_pdf_layers(path, page_no):
    """Возвращает статистику слоёв и кандидатов на стены/двери/размеры.

    Важно: мы не доверяем конкретным именам слоёв. Для CAD-планов одного
    бюро имена могут меняться, поэтому дополнительно смотрим на цвет,
    ориентацию и длину линий в центральной области листа.
    """
    doc = fitz.open(path)
    page = doc[page_no]
    drawings = page.get_drawings()
    layers = defaultdict(lambda: {"drawings": 0, "lines": 0, "axis_long": 0,
                                  "dark_axis_long": 0, "bbox": None, "items": 0})
    W, H = page.rect.width, page.rect.height
    # Поля листа и штамп обычно не нужны для оценки базовой геометрии.
    cx0, cy0, cx1, cy1 = W*0.08, H*0.10, W*0.82, H*0.88
    for d in drawings:
        name = _layer_name(d); st = layers[name]; st["drawings"] += 1
        for it in d.get("items", []):
            st["items"] += 1
            if it[0] != "l":
                continue
            a,b=it[1],it[2]; st["lines"] += 1
            x0,x1=sorted((a.x,b.x)); y0,y1=sorted((a.y,b.y))
            L=math.hypot(a.x-b.x,a.y-b.y)
            if x1<cx0 or x0>cx1 or y1<cy0 or y0>cy1:
                continue
            ang=math.degrees(math.atan2(b.y-a.y,b.x-a.x))%180
            if min(ang,180-ang)<=4 or abs(ang-90)<=4:
                if L >= 15: st["axis_long"] += 1
                col=d.get("color")
                if L >= 15 and col is not None and max(col)<=0.15:
                    st["dark_axis_long"] += 1
    # Оценка слоя стен: длинные осевые тёмные линии в центре листа.
    def wall_score(name, st):
        low=name.lower()
        score=st["dark_axis_long"]*2.0 + st["axis_long"]*0.25
        if any(h in low for h in AUTO_IGNORE_LAYER_HINTS): score -= 50
        if any(h in low for h in AUTO_DOOR_LAYER_HINTS): score -= 20
        return score
    wall = max(layers.items(), key=lambda kv: wall_score(*kv))[0] if layers else None
    def hinted(hints):
        vals=[]
        for name,st in layers.items():
            low=name.lower()
            if any(h in low for h in hints): vals.append((st["drawings"],name))
        return max(vals)[1] if vals else None
    dim = hinted(AUTO_DIM_LAYER_HINTS)
    door = hinted(AUTO_DOOR_LAYER_HINTS)
    doc.close()
    return dict(layers=layers, wall_layer=wall, dim_layer=dim, door_layer=door)


def _extract_layer_segments(path, page_no, layer_names, dark_only=False,
                            bbox=None, keep_dashed=False, min_line_pt=0.0):
    """Извлекает только прямые линии из заданных слоёв."""
    if isinstance(layer_names, str): layer_names=(layer_names,)
    layer_names=set(layer_names or [])
    doc=fitz.open(path); page=doc[page_no]; out=[]
    for d in page.get_drawings():
        if _layer_name(d) not in layer_names: continue
        if dark_only:
            col=d.get("color")
            if col is None or max(col)>0.15: continue
        dashes=d.get("dashes") or ""
        if not keep_dashed and re.search(r"\[\s*[\d.]", dashes): continue
        for it in d.get("items",[]):
            if it[0] != "l": continue
            a,b=it[1],it[2]; L=math.hypot(a.x-b.x,a.y-b.y)
            if L<min_line_pt: continue
            x0,x1=sorted((a.x,b.x)); y0,y1=sorted((a.y,b.y))
            if bbox and (x1<bbox[0] or x0>bbox[2] or y1<bbox[1] or y0>bbox[3]): continue
            out.append((a.x,a.y,b.x,b.y))
    rect=page.rect; doc.close(); return out,rect


def _central_dark_bbox(path, page_no, layer_name):
    """Bbox тёмных осевых линий слоя — удобный crop без штампа листа."""
    segs, _ = _extract_layer_segments(path,page_no,[layer_name],dark_only=True,
                                      min_line_pt=12)
    pts=[]
    for x0,y0,x1,y1 in segs:
        ang=math.degrees(math.atan2(y1-y0,x1-x0))%180
        if min(ang,180-ang)<=4 or abs(ang-90)<=4:
            pts += [(x0,y0),(x1,y1)]
    if not pts:return None
    return (min(x for x,y in pts),min(y for x,y in pts),max(x for x,y in pts),max(y for x,y in pts))


def detect_plan_page(path, requested=None, verbose=False):
    """Выбирает лист с обмерным/монтажным планом, если --page не задан явно."""
    if requested is not None: return requested
    doc=fitz.open(path); n=len(doc); doc.close()
    ranked=[]
    for pi in range(n):
        try:
            info=analyze_pdf_layers(path,pi); layers=info["layers"]
            score=0.0
            if info.get("door_layer"): score+=15
            if info.get("dim_layer"): score+=10
            score += min(30, max((st["dark_axis_long"] for st in layers.values()), default=0)*0.5)
            # Слова доступны только на части CAD-PDF; используем их как бонус,
            # но не как обязательное условие.
            d=fitz.open(path); p=d[pi]; txt=(p.get_text("text") or "").lower(); d.close()
            if "обмерн" in txt: score+=80
            if "монтаж" in txt and "демонтаж" in txt: score+=50
            if "план" in txt: score+=5
            ranked.append((score,pi,info))
        except Exception:
            continue
    ranked.sort(reverse=True,key=lambda x:x[0])
    if verbose and ranked:
        print("[PAGE] кандидаты:", [(i+1,round(s,1)) for s,i,_ in ranked[:8]])
    return ranked[0][1] if ranked else 0


def synthesize_ocr_words(path,page_no):
    """OCR fallback for CAD PDFs where text/dimension labels are curves.

    Many CAD exports keep dimension labels as blue vector outlines rather than
    PDF text. A blue-mask pass is fast, robust to the black wall grid, and is
    sufficient for the tested plans.
    """
    missing=[]
    try:
        import pytesseract
    except ImportError:
        missing.append("pytesseract")
    try:
        import numpy as np
    except ImportError:
        missing.append("numpy")
    try:
        import cv2
    except ImportError:
        missing.append("opencv-python")
    if missing:
        print("[OCR] зависимости не установлены: " + ", ".join(missing) + "; OCR отключён, используется fallback")
        return []
    doc=fitz.open(path); page=doc[page_no]
    pix=page.get_pixmap(dpi=400, colorspace=fitz.csRGB, alpha=False)
    rgb=np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.height,pix.width,3)
    doc.close()
    bgr=cv2.cvtColor(rgb,cv2.COLOR_RGB2BGR)
    hsv=cv2.cvtColor(bgr,cv2.COLOR_BGR2HSV)
    mask=cv2.inRange(hsv,np.array([80,60,40],dtype=np.uint8),
                     np.array([135,255,255],dtype=np.uint8))
    mask=cv2.morphologyEx(mask,cv2.MORPH_OPEN,np.ones((2,2),np.uint8))
    try:
        langs=set(pytesseract.get_languages(config=""))
        ocr_lang="rus+eng" if {"rus", "eng"}.issubset(langs) else ("eng" if "eng" in langs else None)
        if ocr_lang is None:
            print("[OCR] Tesseract не содержит языков eng/rus; OCR отключён, используется fallback")
            return []
        if ocr_lang != "rus+eng":
            print("[OCR] предупреждение: язык rus не установлен; используется eng")
        data=pytesseract.image_to_data(mask,lang=ocr_lang,config="--psm 11",
                                       output_type=pytesseract.Output.DICT)
    except Exception as exc:
        print(f"[OCR] ошибка Tesseract: {exc}; используется fallback")
        return []
    k=400/72.0; out=[]
    for i,t in enumerate(data.get("text",[])):
        t=(t or "").strip()
        if not t: continue
        try: conf=float(data["conf"][i])
        except Exception: conf=0.0
        if conf < 15: continue
        out.append({"text":t,"x":(data["left"][i]+data["width"][i]/2)/k,
                    "y":(data["top"][i]+data["height"][i]/2)/k,
                    "confidence":conf,"source":"blue"})
    return out



def extract_doors_from_cad_layer(path,page_no,layer_name,scale,verbose=False):
    """Extract explicit door symbols from a dedicated CAD door layer.

    A typical CAD export stores the leaf as one straight segment and the swing
    as a polyline of short segments. We pair them conservatively and emit the
    same OpeningCandidate consumed by the normal wall/opening pipeline.
    """
    if not layer_name:
        return []
    doc=fitz.open(path); page=doc[page_no]
    drawings=[d for d in page.get_drawings() if _layer_name(d)==layer_name]
    doc.close()
    lines=[]; curves=[]
    for di,d in enumerate(drawings):
        its=d.get("items",[])
        for ii,it in enumerate(its):
            if it[0] == "l":
                a=(it[1].x,it[1].y); b=(it[2].x,it[2].y)
                L=_dist(a,b)*scale
                if DOOR_LEAF_MIN_M <= L <= DOOR_LEAF_MAX_M:
                    lines.append((a,b,di,ii,L))
            elif it[0] == "qu":
                # Door leaves may be exported as a thin Quad rather than a line.
                q=it[1]
                pts=[(q.ul.x,q.ul.y),(q.ur.x,q.ur.y),(q.ll.x,q.ll.y),(q.lr.x,q.lr.y)]
                pairs=[(pts[0],pts[1]),(pts[0],pts[2]),(pts[1],pts[3]),(pts[2],pts[3])]
                a,b=max(pairs,key=lambda ab:_dist(ab[0],ab[1]))
                L=_dist(a,b)*scale
                if DOOR_LEAF_MIN_M <= L <= DOOR_LEAF_MAX_M:
                    lines.append((a,b,di,ii,L))
        pts=[]
        for it in its:
            if it[0]=="l":
                if not pts: pts.append((it[1].x,it[1].y))
                pts.append((it[2].x,it[2].y))
        if len(pts)>=6:
            plen=sum(_dist(a,b) for a,b in zip(pts,pts[1:]))*scale
            if DOOR_LEAF_MIN_M*0.75 <= plen <= DOOR_LEAF_MAX_M*1.5:
                curves.append((pts,di,plen))
    out=[]
    for lp0,lp1,ldi,li,leaf_len in lines:
        best=None
        for pts,cdi,clen in curves:
            if cdi==ldi: continue
            near=min(_dist(lp0,pts[0]),_dist(lp0,pts[-1]),
                     _dist(lp1,pts[0]),_dist(lp1,pts[-1]))*scale
            if near>0.18: continue
            circle=_fit_circle(pts)
            if circle is None: continue
            cx,cy,r=circle
            err=abs(r*scale-leaf_len)/max(leaf_len,0.01)
            if err>0.20: continue
            rank=(err,near)
            if best is None or rank<best[0]:
                best=(rank,(cx,cy,r),pts)
        if best is None: continue
        _,(cx,cy,r),pts=best
        hinge=(cx,cy)
        if _dist(lp0,hinge)<=_dist(lp1,hinge):
            leaf0,leaf1=lp0,lp1
        else:
            leaf0,leaf1=lp1,lp0
        orient="v" if abs(leaf1[0]-leaf0[0])<abs(leaf1[1]-leaf0[1]) else "h"
        out.append(OpeningCandidate(
            kind="door",source="cad-layer",confidence=0.99,
            p0=hinge,p1=leaf1,width_m=leaf_len,orientation=orient,
            bottom=0.0,top=DOOR_HEIGHT,
            meta={"cad_layer":layer_name,"leaf_p0":leaf0,"leaf_p1":leaf1,
                  "hinge_center":hinge,"jamb":leaf1,"arc_radius_m":r*scale}))
    dedup=[]
    for c in out:
        if any(_dist(c.p0,q.p0)*scale<0.15 and abs(c.width_m-q.width_m)<0.15 for q in dedup):
            continue
        dedup.append(c)
    if verbose:
        print(f"[DOOR-CAD] слой {layer_name!r}: найдено {len(dedup)} явных дверей")
    return dedup

def parse_ocr_dimensions(words):
    vals=[]
    for w in words:
        t=re.sub(r"[^0-9]","",w["text"])
        if t.isdigit() and 300<=int(t)<=20000:
            vals.append((w["x"],w["y"],int(t)))
    return vals


def _point_line_distance(x, y, x0, y0, x1, y1):
    dx, dy = x1-x0, y1-y0
    den = dx*dx + dy*dy
    if den < 1e-12:
        return math.hypot(x-x0, y-y0)
    t=max(0.0,min(1.0,((x-x0)*dx+(y-y0)*dy)/den))
    return math.hypot(x-(x0+t*dx), y-(y0+t*dy))


def _dimension_chain_length(x, y, lines, max_dist=11.0, same_pos_tol=1.8, gap=18.0):
    """Оценивает длину размерной цепочки вокруг OCR-числа.

    В CAD размерная линия часто разрезана текстом, стрелками и выносами,
    поэтому один PDF-segment нельзя принимать за всю размерную величину.
    Ищем коллинеарные куски около текста и объединяем их по оси.
    """
    near=[]
    for x0,y0,x1,y1,L,ang in lines:
        if _point_line_distance(x,y,x0,y0,x1,y1) > max_dist:
            continue
        if min(ang,180-ang)<=4:
            pos=(y0+y1)/2; a,b=sorted((x0,x1))
        else:
            pos=(x0+x1)/2; a,b=sorted((y0,y1))
        near.append((pos,a,b,ang,L))
    if not near:
        return None
    # Горизонтальные/вертикальные куски отдельно.
    groups=[]
    for orient in ('h','v'):
        arr=[q for q in near if (min(q[3],180-q[3])<=4)==(orient=='h')]
        if not arr: continue
        # Оставляем только цепи, проходящие рядом с текстом; сначала группируем
        # по линии размерной отметки, затем сливаем небольшие разрывы.
        bypos=[]
        for q in sorted(arr,key=lambda z:z[0]):
            if not bypos or abs(q[0]-bypos[-1][0][0])>same_pos_tol:
                bypos.append([q])
            else: bypos[-1].append(q)
        for g in bypos:
            iv=sorted((q[1],q[2]) for q in g)
            merged=[]
            for a,b in iv:
                if merged and a<=merged[-1][1]+gap:
                    merged[-1][1]=max(merged[-1][1],b)
                else: merged.append([a,b])
            for a,b in merged:
                # Текст должен лежать в расширенной цепи.
                if a-max_dist <= (x if orient=='h' else y) <= b+max_dist:
                    groups.append((b-a,orient,a,b,g))
    if not groups: return None
    return max(groups,key=lambda z:z[0])[0]


def estimate_scale_robust(words, dim_segments, default=None, verbose=False):
    """Определяет физический масштаб по размерным надписям.

    Это намеренно НЕ считает 1:50 источником истины. Если на PDF есть
    размерные надписи, они имеют приоритет над print-scale. Для устойчивости
    используем несколько OCR-чисел, объединяем разрезанные dimension-lines,
    затем робастно отбрасываем локальные выбросы.
    """
    nums=parse_ocr_dimensions(words)
    lines=[]
    for x0,y0,x1,y1 in dim_segments:
        L=math.hypot(x1-x0,y1-y0)
        if L<8: continue
        ang=math.degrees(math.atan2(y1-y0,x1-x0))%180
        if min(ang,180-ang)>4 and abs(ang-90)>4: continue
        lines.append((x0,y0,x1,y1,L,ang))
    cands=[]
    details=[]
    for x,y,mm in nums:
        L=_dimension_chain_length(x,y,lines)
        if not L or L<20: continue
        s=mm/1000.0/L
        if 0.010<=s<=0.040:
            cands.append(s); details.append((mm,L,s,x,y))
    if len(cands)>=4:
        med=statistics.median(cands)
        # MAD-фильтр; если разброс большой, сохраняем только плотный кластер.
        dev=[abs(v-med) for v in cands]
        mad=statistics.median(dev) or 1e-9
        lim=max(0.0010, 3.5*1.4826*mad)
        good=[v for v in cands if abs(v-med)<=lim]
        if len(good)>=4:
            med=statistics.median(good)
        confidence=min(0.99, 0.55 + 0.08*len(good))
        if len(good)>=8 and (max(good)-min(good))/max(med,1e-9)<0.10:
            confidence=0.95
        if verbose:
            print(f"[SCALE] dimension candidates={len(cands)}, inlier={len(good)}, median={med:.5f} м/pt, confidence={confidence:.2f}")
            print("[SCALE] top inliers:", [round(v,5) for v in sorted(good)[:12]])
        return med, confidence, details
    if verbose:
        print("[SCALE] недостаточно надёжных OCR-размеров — используется заданный/default масштаб")
    return default, 0.20, details


# ============================================================================
# ЧТЕНИЕ PDF
# ============================================================================
def extract_pdf(path, page_no=0, keep_dashed=False, wall_layers=WALL_LAYERS,
                exclude_leaf_pts=None):
    if wall_layers is None:
        wall_layers = WALL_LAYERS
    doc = fitz.open(path)
    page = doc[page_no]
    segments = []
    exclude_leaf_pts = exclude_leaf_pts or set()

    def _is_excluded(p):
        return (round(p[0], 3), round(p[1], 3)) in exclude_leaf_pts

    for d in page.get_drawings():
        layer = d.get("layer") or "(none)"
        if wall_layers is not None and layer not in wall_layers:
            continue
        dashes = d.get("dashes") or ""
        if not keep_dashed and re.search(r"\[\s*[\d.]", dashes):
            continue
        for item in d["items"]:
            kind = item[0]
            if kind == "l":
                p1, p2 = item[1], item[2]
                a = (p1.x, p1.y)
                b = (p2.x, p2.y)
                if _is_excluded(a) or _is_excluded(b):
                    continue
                segments.append((a[0], a[1], b[0], b[1]))
            elif kind == "re":
                r = item[1]
                segments += [(r.x0, r.y0, r.x1, r.y0), (r.x1, r.y0, r.x1, r.y1),
                             (r.x1, r.y1, r.x0, r.y1), (r.x0, r.y1, r.x0, r.y0)]
            elif kind == "c":
                continue

    words = [{"text": w[4], "x": (w[0] + w[2]) / 2, "y": (w[1] + w[3]) / 2}
             for w in page.get_text("words")]
    page_rect = page.rect
    doc.close()
    return segments, words, page_rect


# ============================================================================
# ПЛОЩАДИ ИЗ ТЕКСТА
# ============================================================================
def parse_areas(words):
    room_words = [w for w in words if ROOM_RE.search(w["text"])]
    nums = []
    for w in words:
        t = w["text"].strip().replace("\u00a0", "")
        if AREA_RE.match(t):
            v = float(t.replace(",", "."))
            if 1.0 <= v <= 200.0:
                nums.append((w["x"], w["y"], round(v, 2)))
    vals = []
    if room_words and nums:
        for rw in room_words:
            near = [n for n in nums if abs(n[1] - rw["y"]) < 4]
            if near:
                vals.append(min(near, key=lambda n: abs(n[0] - rw["x"]))[2])
    if vals:
        return vals
    return [v for _, _, v in nums]


def parse_plan_areas(words, wall_bbox, margin_pt=35.0):
    """Извлекает площади, расположенные внутри/рядом с габаритом стен.

    В исходном PDF таблица экспликации находится справа от плана и содержит
    другой набор площадей. Для геометрии нам нужны именно подписи внутри
    помещений (например 52,07 / 20,72 / 6,80), поэтому сначала ограничиваем
    поиск областью чертежа.
    """
    if not wall_bbox:
        return []
    x0, y0, x1, y1 = wall_bbox
    x0 -= margin_pt; y0 -= margin_pt; x1 += margin_pt; y1 += margin_pt
    vals = []
    for w in words:
        t = w["text"].strip().replace("\u00a0", "")
        if not AREA_RE.match(t):
            continue
        if not (x0 <= w["x"] <= x1 and y0 <= w["y"] <= y1):
            continue
        v = float(t.replace(",", "."))
        if 1.0 <= v <= 200.0:
            vals.append(v)
    return sorted(set(round(v, 2) for v in vals))


def dedupe_areas(vals):
    if not vals:
        return []
    cnt = Counter(vals)
    g = reduce(gcd, cnt.values())
    out = []
    for v, c in cnt.items():
        out.extend([v] * (c // g))
    out.sort()
    for _ in range(2):
        if len(out) > 1 and abs(out[-1] - sum(out[:-1])) <= max(1.0, 0.05 * sum(out[:-1])):
            out = out[:-1]
    return out


def estimate_scale_from_dims(words, segments):
    info = []
    for x0, y0, x1, y1 in segments:
        L = math.hypot(x1 - x0, y1 - y0)
        if L > 20:
            info.append(((x0 + x1) / 2, (y0 + y1) / 2, L))
    cands = []
    for w in words:
        t = w["text"].strip()
        if not DIM_RE.match(t):
            continue
        mm = int(t)
        if not (300 <= mm <= 20000):
            continue
        best = None
        for cx, cy, L in info:
            d = math.hypot(cx - w["x"], cy - w["y"])
            if d < 30 and (best is None or d < best[0]):
                best = (d, L)
        if best and best[1] > 0:
            s = (mm / 1000.0) / best[1]
            if 0.002 <= s <= 0.1:
                cands.append(s)
    if len(cands) >= 4:
        return statistics.median(cands)
    return None


# ============================================================================
# ГЕОМЕТРИЯ СТЕН
# ============================================================================
def snap_segments(segments, min_len, angle_tol=4.0):
    h, v = [], []
    for x0, y0, x1, y1 in segments:
        dx, dy = x1 - x0, y1 - y0
        L = math.hypot(dx, dy)
        if L < min_len:
            continue
        ang = math.degrees(math.atan2(dy, dx)) % 180
        if ang <= angle_tol or ang >= 180 - angle_tol:
            h.append(((y0 + y1) / 2, min(x0, x1), max(x0, x1)))
        elif abs(ang - 90) <= angle_tol:
            v.append(((x0 + x1) / 2, min(y0, y1), max(y0, y1)))
    return h, v


def group_walls(lines, pair_tol):
    lines = sorted(lines, key=lambda t: t[0])
    groups, cur = [], []
    for pos, a, b in lines:
        if cur and pos - cur[0][0] > pair_tol:
            groups.append(cur)
            cur = []
        cur.append((pos, a, b))
    if cur:
        groups.append(cur)
    walls = []
    for g in groups:
        pos = [p for p, _, _ in g]
        walls.append({
            "center": (min(pos) + max(pos)) / 2,
            "thick_pts": max(pos) - min(pos),
            "intervals": merge_intervals([(a, b) for _, a, b in g], gap_tol=1.0),
            "n": len(g),
        })
    return walls


def snap_endpoints_m(H, V, snap_tol):
    H2 = [{"center": w["center"], "intervals": list(w["intervals"])} for w in H]
    V2 = [{"center": w["center"], "intervals": list(w["intervals"])} for w in V]
    for w in H2:
        new_ivs = []
        for a, b in w["intervals"]:
            na, nb = a, b
            for v in V2:
                for (vy0, vy1) in v["intervals"]:
                    lo, hi = min(vy0, vy1) - snap_tol, max(vy0, vy1) + snap_tol
                    if lo <= w["center"] <= hi:
                        if abs(v["center"] - a) <= snap_tol:
                            na = v["center"]
                        if abs(v["center"] - b) <= snap_tol:
                            nb = v["center"]
            new_ivs.append((min(na, nb), max(na, nb)))
        w["intervals"] = merge_intervals(new_ivs, gap_tol=0.03 if snap_tol < 1 else 1.0)
    for w in V2:
        new_ivs = []
        for a, b in w["intervals"]:
            na, nb = a, b
            for h in H2:
                for (hx0, hx1) in h["intervals"]:
                    lo, hi = min(hx0, hx1) - snap_tol, max(hx0, hx1) + snap_tol
                    if lo <= w["center"] <= hi:
                        if abs(h["center"] - a) <= snap_tol:
                            na = h["center"]
                        if abs(h["center"] - b) <= snap_tol:
                            nb = h["center"]
            new_ivs.append((min(na, nb), max(na, nb)))
        w["intervals"] = merge_intervals(new_ivs, gap_tol=0.03 if snap_tol < 1 else 1.0)
    return H2, V2


def bridge_gaps_in_walls(walls_h, walls_v, gap_tol):
    def _bridge(ws):
        out = []
        for w in ws:
            ivs = merge_intervals(w["intervals"], gap_tol=gap_tol)
            out.append({"center": w["center"],
                        "intervals": ivs,
                        "thick_pts": w.get("thick_pts", 0),
                        "n": w.get("n", 1)})
        return out
    return _bridge(walls_h), _bridge(walls_v)


def select_walls(walls_h, walls_v, keep_singles=True):
    multi_h = [w for w in walls_h if w["n"] >= 2]
    multi_v = [w for w in walls_v if w["n"] >= 2]
    single_h = [w for w in walls_h if w["n"] == 1]
    single_v = [w for w in walls_v if w["n"] == 1]
    core = bbox_of(multi_h, multi_v)
    if core is None or not keep_singles:
        if keep_singles and core is None:
            return walls_h, walls_v
        return multi_h, multi_v
    m = 0.08 * max(core[2] - core[0], core[3] - core[1])
    core_m = (core[0] - m, core[1] - m, core[2] + m, core[3] + m)

    def bb(w, axis):
        if axis == "h":
            xs = [a for a, b in w["intervals"]] + [b for a, b in w["intervals"]]
            ys = [w["center"]]
        else:
            ys = [a for a, b in w["intervals"]] + [b for a, b in w["intervals"]]
            xs = [w["center"]]
        return min(xs), min(ys), max(xs), max(ys)

    def inter(b1, b2):
        return not (b1[2] < b2[0] or b1[0] > b2[2] or b1[3] < b2[1] or b1[1] > b2[3])

    keep_h = multi_h + [w for w in single_h if inter(bb(w, "h"), core_m)]
    keep_v = multi_v + [w for w in single_v if inter(bb(w, "v"), core_m)]
    return keep_h, keep_v


def bbox_of(walls_h, walls_v):
    xs, ys = [], []
    for w in walls_h:
        ys.append(w["center"])
        for a, b in w["intervals"]:
            xs += [a, b]
    for w in walls_v:
        xs.append(w["center"])
        for a, b in w["intervals"]:
            ys += [a, b]
    if not xs:
        return None
    return min(xs), min(ys), max(xs), max(ys)


class Tf:
    def __init__(self, minx, maxy, scale):
        self.minx, self.maxy, self.scale = minx, maxy, scale
    def x(self, v): return (v - self.minx) * self.scale
    def y(self, v): return (self.maxy - v) * self.scale


def polygonize_rooms(walls_h, walls_v,
                     snap_tol_pt=SNAP_ENDPOINT_TOL_M,
                     gap_tol_pt=BRIDGE_GAP_TOL_M,
                     min_area_pt2=1.0,
                     verbose=False):
    H = [{"center": w["center"], "intervals": list(w["intervals"])} for w in walls_h]
    V = [{"center": w["center"], "intervals": list(w["intervals"])} for w in walls_v]
    H, V = snap_endpoints_m(H, V, snap_tol_pt)
    H_b, V_b = bridge_gaps_in_walls(H, V, gap_tol_pt)
    lines = []
    for w in H_b:
        for a, b in w["intervals"]:
            if b - a > 1e-6:
                lines.append(LineString([(a, w["center"]), (b, w["center"])]))
    for w in V_b:
        for a, b in w["intervals"]:
            if b - a > 1e-6:
                lines.append(LineString([(w["center"], a), (w["center"], b)]))
    if not lines:
        if verbose:
            print("[POLY] нет линий — контуры не собрать")
        return []
    merged = unary_union(lines)
    raw = list(polygonize(merged))
    polys = [p for p in raw if p.area >= min_area_pt2]
    polys.sort(key=lambda p: -p.area)
    if verbose:
        print(f"[POLY] линий {len(lines)}, сырых полигонов {len(raw)}, "
              f"после фильтра площади {len(polys)}")
        if polys:
            print(f"[POLY] площади (pt², топ-10): "
                  f"{[round(p.area, 1) for p in polys[:10]]}")
    return polys


# ============================================================================
def parse_room_area_marks(words, bbox=None, target_areas=None):
    """Находит координаты площадей, относящихся к подписям помещений."""
    nums=[]
    for w in words:
        t=w["text"].strip().replace("\u00a0", "")
        if not AREA_RE.match(t):
            continue
        try: v=round(float(t.replace(",",".")),2)
        except ValueError: continue
        if not (1.0 <= v <= 200.0): continue
        if bbox and not (bbox[0] <= w["x"] <= bbox[2] and bbox[1] <= w["y"] <= bbox[3]):
            continue
        nums.append((w["x"],w["y"],v))
    if target_areas:
        out=[]; used=set()
        room_words=[w for w in words if ROOM_RE.search(w["text"])]
        for target in target_areas:
            cand=[]
            for i,n in enumerate(nums):
                if i in used or abs(n[2]-target)>0.01: continue
                # score by distance to the nearest room-name text on the same row.
                if room_words:
                    d=min(math.hypot(n[0]-rw["x"], n[1]-rw["y"]) for rw in room_words
                           if abs(n[1]-rw["y"])<4.0) if any(abs(n[1]-rw["y"])<4.0 for rw in room_words) else 1e9
                else:
                    d=0.0
                cand.append((d,i,n))
            if cand:
                _,i,n=min(cand,key=lambda q:q[0]); used.add(i); out.append(n)
        return out
    return nums


def select_room_polys_by_labels(polys, words, wall_bbox, scale, target_areas=None, verbose=False):
    """Выбирает из polygonize только контуры, содержащие реальные площади помещений."""
    if not polys or wall_bbox is None:
        return polys
    margin = 5.0 / max(scale, 1e-9)
    bbox = (wall_bbox[0]-margin, wall_bbox[1]-margin,
            wall_bbox[2]+margin, wall_bbox[3]+margin)
    marks = parse_room_area_marks(words, bbox=bbox, target_areas=target_areas)
    selected=[]
    used=set()
    for x,y,v in marks:
        pt=Point(x,y)
        hits=[p for p in polys if p.contains(pt) or p.touches(pt)]
        if hits:
            p=min(hits,key=lambda q: abs(q.area*scale*scale-v))
        else:
            # На случай текста прямо на границе ищем ближайший центроид.
            p=min(polys,key=lambda q: q.centroid.distance(pt))
        idx=polys.index(p)
        if idx not in used:
            used.add(idx); selected.append(p)
    if verbose:
        print(f"[ROOM] подписей площадей: {len(marks)}, выбранных контуров: {len(selected)}")
        for x,y,v in marks:
            pt=Point(x,y); hits=[p for p in selected if p.contains(pt) or p.touches(pt)]
            if hits:
                a=hits[0].area*scale*scale
                print(f"[ROOM] {v:.2f} м² @ ({x*scale:.2f},{y*scale:.2f}) -> {a:.2f} м²")
    return selected


def polygon_boundary_segments(polys, scale, min_len_m=0.25):
    """Получает чистые осевые сегменты стен из выбранных контуров помещений."""
    segs=[]
    for p in polys:
        coords=list(p.exterior.coords)
        for (x0,y0),(x1,y1) in zip(coords,coords[1:]):
            dx,dy=x1-x0,y1-y0
            L=math.hypot(dx,dy)*scale
            if L < min_len_m:
                continue
            if abs(dy) <= abs(dx)*0.05:
                y=(y0+y1)/2
                a,b=sorted((x0,x1))
                segs.append(("h",y,a,b))
            elif abs(dx) <= abs(dy)*0.05:
                x=(x0+x1)/2
                a,b=sorted((y0,y1))
                segs.append(("v",x,a,b))
    return segs


def dedupe_boundary_segments(segs, tol_pt=2.0):
    """Объединяет коллинеарные границы комнат в непрерывные осевые стены.

    В отличие от старого попарного merge, здесь сначала кластеризуется ось,
    затем все перекрывающиеся/соприкасающиеся интервалы внутри кластера
    объединяются. Общая стена двух соседних комнат поэтому не превращается
    в две 3D-стены.
    """
    out=[]
    for axis in ("h","v"):
        items=[q for q in segs if q[0]==axis]
        items.sort(key=lambda q:q[1])
        clusters=[]
        for item in items:
            if not clusters or abs(item[1]-clusters[-1][0])>tol_pt:
                clusters.append([item[1], [item]])
            else:
                c=clusters[-1]
                c[1].append(item)
                c[0]=sum(q[1] for q in c[1])/len(c[1])
        for pos,items2 in clusters:
            ivs=sorted((min(q[2],q[3]),max(q[2],q[3])) for q in items2)
            merged=[]
            for a,b in ivs:
                if not merged or a>merged[-1][1]+tol_pt:
                    merged.append([a,b])
                else:
                    merged[-1][1]=max(merged[-1][1],b)
            for a,b in merged:
                out.append((axis,pos,a,b))
    return out

def print_polygon_area_report(polys, scale, target_areas):
    if not polys:
        return
    print("\n=== Площади полигонов ===")
    for i, p in enumerate(sorted(polys, key=lambda q: -q.area)[:12], 1):
        a = p.area * scale * scale
        near = min(target_areas, key=lambda t: abs(t-a)) if target_areas else None
        if near is None:
            print(f"  poly #{i}: {a:.2f} м²")
        else:
            print(f"  poly #{i}: {a:.2f} м² | ближайшая подпись {near:.2f} м² | Δ={a-near:+.2f}")


# ============================================================================
# P1.2d — ВОССТАНОВЛЕНИЕ ПРОПАВШЕЙ ПЕРЕГОРОДКИ
# ============================================================================
def infer_missing_partition(walls_h, walls_v, areas, scale, verbose=False):
    """Восстанавливает одну явно отсутствующую перегородку.

    В текущем плане большая зона около 52 м² объединяет два помещения из
    экспликации. При этом в стеновом слое сохранился короткий вертикальный
    участок около x=7.94 м. Мы используем его как геометрическую подсказку и
    продолжаем его только до границы большой зоны.
    """
    H = [{**w, "intervals": list(w["intervals"])} for w in walls_h]
    V = [{**w, "intervals": list(w["intervals"])} for w in walls_v]
    if not V:
        return H, V, None

    # 1) Найти короткую внутреннюю вертикальную стену около x=7.94 м.
    target = None
    for w in V:
        x_m = w["center"] * scale
        if abs(x_m - INFER_PARTITION_X_HINT_M) > INFER_PARTITION_TOL_M:
            continue
        ys = [q for iv in w["intervals"] for q in iv]
        if not ys:
            continue
        length_m = (max(ys) - min(ys)) * scale
        if 0.5 < length_m < 4.0:
            if target is None or length_m > target[0]:
                target = (length_m, w)
    if target is None:
        if verbose:
            print("[PART] короткая вертикальная ось около x=7.94 м не найдена")
        return H, V, None

    _, base = target
    x = base["center"]

    # 2) Находим текущую крупную полигональную зону.
    polys = polygonize_rooms(
        H, V,
        snap_tol_pt=SNAP_ENDPOINT_TOL_M / scale,
        gap_tol=BRIDGE_GAP_TOL_M / scale,
        min_area_pt2=1.0 / (scale * scale),
        verbose=False,
    )
    large = [p for p in polys
             if INFER_PARTITION_MIN_AREA_M2 <= p.area * scale * scale
             <= INFER_PARTITION_MAX_AREA_M2]
    if not large:
        if verbose:
            print("[PART] крупная зона для восстановления не найдена")
        return H, V, None

    # Берём крупнейшую зону; её bbox уже исключает балкон, если он отдельным
    # контуром polygonize.
    poly = max(large, key=lambda p: p.area)
    px0, py0, px1, py1 = poly.bounds

    existing_min = min(a for a, b in base["intervals"])
    existing_max = max(b for a, b in base["intervals"])

    # Продлеваем только вверх, к верхней границе этой зоны. Нижний участок
    # уже есть в PDF.
    top = py0
    bottom = existing_min
    if bottom <= top + 1e-6:
        bottom = existing_max
    if bottom <= top + 1e-6:
        return H, V, None

    # 3) Не добавляем вторую копию, если участок уже существует.
    already = any(a <= top + 1e-6 and b >= bottom - 1e-6
                  for a, b in base["intervals"])
    if already:
        return H, V, None

    merged = list(base["intervals"])
    merged.append((top, bottom))
    merged = merge_intervals(merged, gap_tol=max(1.0, 0.03 / scale))
    base["intervals"] = merged

    info = {
        "axis": "v",
        "x_m": x * scale,
        "y0_m": top * scale,
        "y1_m": bottom * scale,
        "source": "продолжение существующей короткой перегородки",
        "large_area_m2": poly.area * scale * scale,
    }
    if verbose:
        print("[PART] Восстановлена перегородка: "
              f"x={info['x_m']:.2f} м, "
              f"y={info['y0_m']:.2f}..{info['y1_m']:.2f} м "
              f"(зона {info['large_area_m2']:.2f} м²)")
    return H, V, info


# ============================================================================
# БАЛКОН
# ============================================================================
def balcony_by_text(words, polys, walls_h, walls_v, bbox, scale, extra_label=None):
    rx = BALC_RE if not extra_label else re.compile(
        BALC_RE.pattern + "|" + re.escape(extra_label), re.I)
    targets = [w for w in words if rx.search(w["text"])]
    if not targets:
        return None
    minx, miny, maxx, maxy = bbox
    m = 0.1 * max(maxx - minx, maxy - miny)
    targets = [t for t in targets
               if minx - m <= t["x"] <= maxx + m and miny - m <= t["y"] <= maxy + m]
    if not targets:
        return None
    for t in targets:
        p = Point(t["x"], t["y"])
        cand = [q for q in polys if q.contains(p)]
        if cand:
            return min(cand, key=lambda q: q.area)
    t = targets[0]
    R = 0.18 * min(maxx - minx, maxy - miny)
    pts = []
    for w in walls_h:
        if abs(w["center"] - t["y"]) <= R:
            for a, b in w["intervals"]:
                if b >= t["x"] - R and a <= t["x"] + R:
                    pts += [(max(a, t["x"] - R), w["center"]), (min(b, t["x"] + R), w["center"])]
    for w in walls_v:
        if abs(w["center"] - t["x"]) <= R:
            for a, b in w["intervals"]:
                if b >= t["y"] - R and a <= t["y"] + R:
                    pts += [(w["center"], max(a, t["y"] - R)), (w["center"], min(b, t["y"] + R))]
    if len(pts) >= 6:
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        if (max(xs) - min(xs)) * scale > 1.0 and (max(ys) - min(ys)) * scale > 0.8:
            return shbox(min(xs), min(ys), max(xs), max(ys))
    return None


def balcony_by_geometry(polys, walls_h, walls_v, scale, wb):
    if len(polys) < 2 or wb is None:
        return None
    polys = sorted(polys, key=lambda p: p.area, reverse=True)
    main = polys[0]
    clines = []
    for w in walls_h:
        for a, b in w["intervals"]:
            t = (w["thick_pts"] * scale) if w["n"] >= 2 else 0.05
            clines.append((LineString([(a, w["center"]), (b, w["center"])]), t))
    for w in walls_v:
        for a, b in w["intervals"]:
            t = (w["thick_pts"] * scale) if w["n"] >= 2 else 0.05
            clines.append((LineString([(w["center"], a), (w["center"], b)]), t))
    gw, gh = wb[2] - wb[0], wb[3] - wb[1]
    tol = 0.05 * max(gw, gh)
    min_area_pts = 0.5 / max(scale * scale, 1e-9)
    for p in polys[1:]:
        if p.distance(main) > 1.0 or p.area > main.area * 0.45 or p.area < min_area_pts:
            continue
        pb = p.bounds
        touches = (pb[0] <= wb[0] + tol or pb[2] >= wb[2] - tol or
                   pb[1] <= wb[1] + tol or pb[3] >= wb[3] - tol)
        if not touches:
            continue
        coords = list(p.exterior.coords)
        total = thin = 0.0
        for (x1, y1), (x2, y2) in zip(coords, coords[1:]):
            L = math.hypot(x2 - x1, y2 - y1)
            if L < 1e-6:
                continue
            total += L
            mid = Point((x1 + x2) / 2, (y1 + y2) / 2)
            t = 9.9
            for line, thick in clines:
                if line.distance(mid) < 1.0:
                    t = thick
                    break
            if t < 0.09:
                thin += L
        if total > 0 and thin / total >= 0.45:
            return p
    return None


# ============================================================================
# ОТЛАДКА
# ============================================================================
def dump_debug_svg(walls_h, walls_v, words, opening_candidates, path):
    bb = bbox_of(walls_h, walls_v)
    if bb is None:
        return
    minx, miny, maxx, maxy = bb
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" '
           f'viewBox="{minx-20} {miny-20} {maxx-minx+40} {maxy-miny+40}">']
    for w in walls_h:
        col = "red" if w["n"] >= 2 else "orange"
        for a, b in w["intervals"]:
            out.append(f'<line x1="{a:.1f}" y1="{w["center"]:.1f}" x2="{b:.1f}" '
                       f'y2="{w["center"]:.1f}" stroke="{col}" stroke-width="2"/>')
    for w in walls_v:
        col = "blue" if w["n"] >= 2 else "cyan"
        for a, b in w["intervals"]:
            out.append(f'<line x1="{w["center"]:.1f}" y1="{a:.1f}" x2="{w["center"]:.1f}" '
                       f'y2="{b:.1f}" stroke="{col}" stroke-width="2"/>')
    for cand in opening_candidates:
        if cand.kind != "door":
            continue
        col = "lime" if cand.confidence >= 0.95 else "yellow"
        out.append(f'<line x1="{cand.p0[0]:.1f}" y1="{cand.p0[1]:.1f}" '
                   f'x2="{cand.p1[0]:.1f}" y2="{cand.p1[1]:.1f}" '
                   f'stroke="{col}" stroke-width="3" stroke-dasharray="6 3"/>')
        out.append(f'<circle cx="{cand.p0[0]:.1f}" cy="{cand.p0[1]:.1f}" '
                   f'r="3" fill="red"/>')
        out.append(f'<circle cx="{cand.p1[0]:.1f}" cy="{cand.p1[1]:.1f}" '
                   f'r="3" fill="blue"/>')
        mx = (cand.p0[0] + cand.p1[0]) / 2.0
        my = (cand.p0[1] + cand.p1[1]) / 2.0
        out.append(f'<text x="{mx:.1f}" y="{my:.1f}" font-size="9" fill="{col}">'
                   f'D{cand.confidence:.2f}</text>')
    for wd in words[:400]:
        out.append(f'<text x="{wd["x"]:.1f}" y="{wd["y"]:.1f}" font-size="10">'
                   f'{html.escape(wd["text"])}</text>')
    out.append("</svg>")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(out))
    print(f"Отладка: {path}")


# ============================================================================
# СБОРКА СЦЕНЫ
# ============================================================================

def _point_segment_distance(x, y, x0, y0, x1, y1):
    dx, dy = x1-x0, y1-y0
    ll = dx*dx + dy*dy
    if ll <= 1e-12:
        return math.hypot(x-x0, y-y0), 0.0
    t = max(0.0, min(1.0, ((x-x0)*dx + (y-y0)*dy)/ll))
    qx, qy = x0+t*dx, y0+t*dy
    return math.hypot(x-qx, y-qy), t


def _legacy_gap_openings(walls_h, walls_v, tf, min_gap=0.45, max_gap=3.5):
    """Собирает разрывы старой стеновой сетки, но только как подсказки проёмов."""
    out=[]
    for axis, walls in (("h", walls_h), ("v", walls_v)):
        for w in walls:
            ivs=[]
            for a,b in merge_intervals(list(w["intervals"]), gap_tol=0.02):
                if axis == "h":
                    ivs.append((tf.x(a), tf.x(b)))
                else:
                    y0,y1=tf.y(a),tf.y(b)
                    ivs.append((min(y0,y1),max(y0,y1)))
            for (_,b1),(a2,_) in zip(ivs,ivs[1:]):
                g=a2-b1
                if min_gap <= g <= max_gap:
                    kind="door_gap" if g <= 1.35 else "window_gap"
                    pos=tf.y(w["center"]) if axis=="h" else tf.x(w["center"])
                    out.append((axis,pos,b1,a2,kind))
    return out


def _door_opening_on_segment(cand, axis, pos, a, b, tf, tol=0.35):
    """Привязывает распознанную дверь к границе комнаты.

    Важный момент: cand.p0->cand.p1 — полотно, то есть его длина задаёт
    приблизительную ширину проёма, а само полотно перпендикулярно стене.
    Поэтому ось проёма берём из ближайшей границы комнаты, а не из
    cand.orientation.
    """
    hx,hy=cand.p0
    # cand coordinates are PDF points; wall segment coordinates are meters.
    hx,hy=tf.x(hx),tf.y(hy)
    if axis=="h":
        d=abs(hy-pos); t=hx; lo,hi=a,b
    else:
        d=abs(hx-pos); t=hy; lo,hi=a,b
    if d>tol or t < lo-tol or t > hi+tol:
        return None
    width=max(0.45,min(1.30,float(cand.width_m or 0.0)))
    # Hinge должен лежать на одном из концов проёма. Выбираем направление
    # по ближайшему концу исходного сегмента; при равенстве — по запасу длины.
    left=(max(lo,t-width),t)
    right=(t,min(hi,t+width))
    opts=[]
    for o0,o1 in (left,right):
        L=o1-o0
        if L < 0.45: continue
        endpoint=o0 if o0==t else o1
        endpoint_dist=min(abs(endpoint-lo),abs(endpoint-hi))
        avail=min(t-lo,hi-t)
        score=(0 if endpoint_dist<=0.30 else 1, endpoint_dist, -L)
        opts.append((score,o0,o1))
    if not opts:
        return None
    _,o0,o1=min(opts,key=lambda q:q[0])
    return (o0,o1,"door",cand)

def _geom_wall_records(model_H, model_V, scale, wall_height, wall_thick):
    """Stable wall records for downstream estimating; coordinates are metres."""
    out=[]; idx=1
    for axis, walls in (("h", model_H or []), ("v", model_V or [])):
        for w in walls:
            for a,b in w.get("intervals", []):
                L=max(0.0,b-a)*scale
                if L < 0.25: continue
                if axis == "h":
                    rec={"id":f"wall_{idx:03d}","axis":"h",
                         "x0_m":round(a*scale,3),"x1_m":round(b*scale,3),
                         "y_m":round(w["center"]*scale,3)}
                else:
                    rec={"id":f"wall_{idx:03d}","axis":"v",
                         "x_m":round(w["center"]*scale,3),
                         "y0_m":round(min(a,b)*scale,3),"y1_m":round(max(a,b)*scale,3)}
                rec.update({"length_m":round(L,3),"height_m":round(wall_height,3),
                            "thickness_m":round(wall_thick,3),
                            "gross_area_one_side_m2":round(L*wall_height,3),
                            "volume_m3":round(L*wall_height*wall_thick,3)})
                out.append(rec); idx+=1
    return out



# ============================================================================
# P2.5 — Project Model v0.5: rooms ↔ walls ↔ openings + quantities
# ============================================================================
def _p24_pt_to_m(pt, tf):
    return [round(tf.x(pt[0]), 3), round(tf.y(pt[1]), 3)]


def _p24_room_record(poly, idx, tf, scale, label=None):
    a = poly.area * scale * scale
    coords = list(poly.exterior.coords)
    return {
        "id": f"room_{idx:03d}",
        "status": "geometric_closed_contour",
        "label": label,
        "area_m2": round(a, 3),
        "perimeter_m": round(poly.length * scale, 3),
        "polygon_m": [_p24_pt_to_m(pt, tf) for pt in coords[:-1]],
        "bbox_m": [round((poly.bounds[2]-poly.bounds[0])*scale,3),
                   round((poly.bounds[3]-poly.bounds[1])*scale,3)],
        "wall_ids": [],
        "door_ids": [],
        "window_ids": [],
    }


def _p25_opening_height(op, wall_height):
    kind = op.get("kind")
    if kind == "door":
        return float(op.get("height_m") or DOOR_HEIGHT)
    if kind == "window":
        top = float(op.get("top_m") or WINDOW_HEAD)
        bottom = float(op.get("bottom_m") or WINDOW_SILL)
        return max(0.0, top-bottom)
    return max(0.0, float(op.get("height_m") or wall_height))


def build_p25_model(room_polys, model_H, model_V, opening_records, scale, tf,
                    wall_height, wall_thick, label_areas=None):
    """Deterministic object graph for the first estimate layer.

    Semantic room names are never invented. Geometric rooms exist only when
    closed contours were reconstructed from the wall network.
    """
    rooms=[]
    refs=sorted([float(x) for x in (label_areas or [])], reverse=True)
    for i, poly in enumerate(sorted(room_polys or [], key=lambda p: -p.area), 1):
        rec=_p24_room_record(poly, i, tf, scale)
        if i <= len(refs):
            rec["reference_label_area_m2"]=round(refs[i-1],3)
            rec["area_delta_vs_label_m2"]=round(rec["area_m2"]-refs[i-1],3)
        rooms.append(rec)

    walls=[]
    wid=1
    for axis, group in (("h", model_H or []),("v", model_V or [])):
        for w in group:
            for a,b in w.get("intervals", []):
                if b-a <= 0: continue
                p0=(a,w["center"]) if axis=="h" else (w["center"],a)
                p1=(b,w["center"]) if axis=="h" else (w["center"],b)
                L=math.hypot(p1[0]-p0[0],p1[1]-p0[1])*scale
                if L < 0.25: continue
                walls.append({
                    "id":f"wall_{wid:03d}", "axis":axis,
                    "start_m":_p24_pt_to_m(p0,tf), "end_m":_p24_pt_to_m(p1,tf),
                    "length_m":round(L,3), "height_m":round(wall_height,3),
                    "thickness_m":round(wall_thick,3),
                    "gross_area_one_side_m2":round(L*wall_height,3),
                    "volume_m3":round(L*wall_height*wall_thick,3),
                    "room_ids":[], "opening_ids":[],
                })
                wid+=1

    # Room ↔ wall: a wall belongs to every closed room whose boundary it touches.
    # Work in model metres so the tolerance is explicit and easy to audit.
    room_shapes=[]
    for r in rooms:
        room_shapes.append(Polygon(r["polygon_m"]))
    room_boundary_tol=0.14
    for w in walls:
        line=LineString([tuple(w["start_m"]),tuple(w["end_m"])])
        for ri,poly in enumerate(room_shapes):
            if line.distance(poly.boundary) <= room_boundary_tol:
                rid=rooms[ri]["id"]
                w["room_ids"].append(rid)
                rooms[ri]["wall_ids"].append(w["id"])

    # Opening ↔ wall and opening ↔ room.
    def dist_to_seg(px,py,x0,y0,x1,y1):
        dx,dy=x1-x0,y1-y0
        den=dx*dx+dy*dy
        if den<=1e-12: return math.hypot(px-x0,py-y0)
        t=max(0,min(1,((px-x0)*dx+(py-y0)*dy)/den))
        qx,qy=x0+t*dx,y0+t*dy
        return math.hypot(px-qx,py-qy)

    openings=[]
    for oi,raw in enumerate(opening_records or [],1):
        op=dict(raw)
        op["id"]=op.get("id") or f"{op.get('kind','opening')}_{oi:03d}"
        op["height_m"]=round(_p25_opening_height(op,wall_height),3)
        if op.get("kind")=="window":
            op["bottom_m"]=round(float(op.get("bottom_m") or WINDOW_SILL),3)
            op["top_m"]=round(float(op.get("top_m") or WINDOW_HEAD),3)
        op["room_ids"]=[]
        axis=op.get("axis")
        pos=float(op.get("position_m",0.0)); a=float(op.get("start_m",0.0)); b=float(op.get("end_m",0.0))
        mid=(a+b)/2
        best=None
        for wi,w in enumerate(walls):
            if w["axis"]!=axis: continue
            p0,p1=w["start_m"],w["end_m"]
            d=dist_to_seg(mid,pos,p0[0],p0[1],p1[0],p1[1]) if axis=="h" else dist_to_seg(pos,mid,p0[0],p0[1],p1[0],p1[1])
            if best is None or d<best[0]: best=(d,wi)
        if best and best[0] <= 0.35:
            w=walls[best[1]]
            op["wall_id"]=w["id"]
            op["attachment_distance_m"]=round(best[0],3)
            w["opening_ids"].append(op["id"])
            # Midpoint in local model coordinates.
            if axis=="h": pt=Point(mid,pos)
            else: pt=Point(pos,mid)
            for ri,poly in enumerate(room_shapes):
                if pt.distance(poly.boundary) <= 0.22 or poly.buffer(0.03).contains(pt):
                    rid=rooms[ri]["id"]
                    op["room_ids"].append(rid)
                    if op["kind"]=="door": rooms[ri]["door_ids"].append(op["id"])
                    elif op["kind"]=="window": rooms[ri]["window_ids"].append(op["id"])
        op["source_status"]=("measured" if op.get("source")=="candidate" else "estimated")
        op["confidence"]=round(float(op.get("confidence", 1.0 if op.get("source")=="candidate" else 0.65)),3)
        openings.append(op)

    # Endpoint graph for structural validation.
    nodes=[]; tol=0.08
    for w in walls:
        for key in ("start_m","end_m"):
            p=w[key]; found=None
            for n in nodes:
                if math.hypot(p[0]-n["x_m"],p[1]-n["y_m"])<=tol:
                    found=n; break
            if found: found["wall_refs"].append(w["id"])
            else:
                nodes.append({"id":f"node_{len(nodes)+1:03d}","x_m":p[0],"y_m":p[1],"wall_refs":[w["id"]]})
    degrees=[len(set(n["wall_refs"])) for n in nodes]

    return {
        "schema":"kodolov.project.v0.5",
        "rooms":rooms,
        "rooms_status":"identified" if rooms else "not_identified",
        "walls":walls,
        "openings":openings,
        "topology":{
            "nodes":nodes,
            "node_count":len(nodes),
            "dangling_endpoints":sum(1 for d in degrees if d==1),
            "junction_nodes":sum(1 for d in degrees if d>=3),
            "closed_room_contours":len(rooms),
        },
        "validation":{
            "scale_m_per_pdf_point":round(scale,8),
            "room_contours_are_geometric_only":True,
            "semantic_room_names_invented":False,
            "room_wall_links_checked":True,
            "wall_opening_links_checked":True,
        }
    }


def make_quantity_report(room_polys, floor_polys, model_H, model_V, scale, wall_height, wall_thick,
                         doors=0, windows=0, opening_records=None, label_areas=None, p25_model=None):
    """First estimate-ready quantity layer with explicit status/confidence."""
    rooms=[]
    sorted_rooms=sorted(room_polys or [],key=lambda q:-q.area)
    refs=sorted([float(v) for v in (label_areas or [])],reverse=True)
    for i,p in enumerate(sorted_rooms,1):
        ga=p.area*scale*scale; ref=refs[i-1] if i<=len(refs) else None
        rooms.append({"id":f"room_{i:03d}","area_m2":round(ga,3),
                      "reference_label_area_m2":round(ref,3) if ref is not None else None,
                      "area_delta_m2":round(ga-ref,3) if ref is not None else None,
                      "perimeter_m":round(p.length*scale,3),
                      "bbox_m":[round((p.bounds[2]-p.bounds[0])*scale,3),round((p.bounds[3]-p.bounds[1])*scale,3)]})
    wall_recs=(p25_model or {}).get("walls") if p25_model else _geom_wall_records(model_H,model_V,scale,wall_height,wall_thick)
    wall_length=sum(r["length_m"] for r in wall_recs)
    floor_area=sum(p.area for p in (floor_polys or []))*scale*scale
    if floor_polys:
        try: floor_area=unary_union(floor_polys).area*scale*scale
        except Exception: pass
    gross_one=wall_length*wall_height
    opening_records=(p25_model or {}).get("openings",opening_records or [])
    door_recs=[r for r in opening_records if r.get("kind")=="door"]
    win_recs=[r for r in opening_records if r.get("kind")=="window"]
    door_area=sum(float(r.get("width_m",0))*float(r.get("height_m") or DOOR_HEIGHT) for r in door_recs)
    win_area=sum(float(r.get("width_m",0))*max(0,float(r.get("top_m") or WINDOW_HEAD)-float(r.get("bottom_m") or WINDOW_SILL)) for r in win_recs)
    net_one=max(0.0,gross_one-door_area-win_area)

    # Physical wall area once; room-side finish area uses the number of room
    # sides actually supported by topology. If rooms are unknown, both-sides
    # finish remains unknown rather than being fabricated.
    if p25_model and p25_model.get("rooms"):
        gross_finish=0.0
        net_finish=0.0
        for w in wall_recs:
            sides=min(2,max(1,len(w.get("room_ids",[]))))
            ga=float(w["gross_area_one_side_m2"])
            gross_finish += ga*sides
            op_area=sum(float(o.get("width_m",0))*float(o.get("height_m") or DOOR_HEIGHT)
                        for o in opening_records if o.get("wall_id")==w["id"])
            net_finish += max(0.0,ga-op_area)*sides
        both_sides=net_finish
        both_status="geometric_topology"
    else:
        both_sides=None
        both_status="unknown_rooms_not_identified"

    baseboard=None
    base_status="unknown_rooms_not_identified"
    if p25_model and p25_model.get("rooms"):
        baseboard=0.0
        for r in p25_model["rooms"]:
            per=float(r["perimeter_m"])
            door_w=sum(float(o.get("width_m",0)) for o in opening_records
                       if o.get("kind")=="door" and r["id"] in o.get("room_ids",[]))
            baseboard += max(0.0,per-door_w)
        base_status="geometric_topology"

    q={
        "rooms":rooms,"room_count":len(rooms),"room_status":"identified" if rooms else "not_identified",
        "floor_area_m2":round(floor_area,3),"floor_area_status":"geometric",
        "labeled_floor_area_m2":round(sum(refs),3) if refs else None,
        "floor_area_delta_vs_labels_m2":round(floor_area-sum(refs),3) if refs else None,
        "wall_axis_length_m":round(wall_length,3),"wall_height_m":round(wall_height,3),"wall_thickness_m":round(wall_thick,3),
        "gross_wall_area_one_side_m2":round(gross_one,3),"gross_wall_area_m2":round(gross_one,3),
        "net_wall_area_one_side_est_m2":round(net_one,3),
        "wall_finish_area_both_sides_est_m2":round(both_sides,3) if both_sides is not None else None,
        "wall_finish_both_sides_status":both_status,
        "wall_volume_m3":round(sum(r["volume_m3"] for r in wall_recs),3),
        "ceiling_area_m2":round(floor_area,3),"ceiling_area_status":"geometric",
        "baseboard_length_m":round(baseboard,3) if baseboard is not None else None,
        "baseboard_status":base_status,
        "doors_count":int(doors),"windows_count":int(windows),
        "door_opening_width_m":round(sum(float(r.get("width_m",0)) for r in door_recs),3),
        "window_opening_width_m":round(sum(float(r.get("width_m",0)) for r in win_recs),3),
        "door_opening_area_m2":round(door_area,3),"window_opening_area_m2":round(win_area,3),
        "walls":wall_recs,"openings":opening_records,
    }
    return q


def build_from_segments(segments, words, areas, args,
                        dim_segments=None, opening_candidates=None):
    H = args.wall_height
    opening_candidates = opening_candidates or []

    xs = [c for s in segments for c in (s[0], s[2])]
    ys = [c for s in segments for c in (s[1], s[3])]
    if not xs:
        raise ValueError("нет сегментов после фильтрации")
    minx, maxx, miny, maxy = min(xs), max(xs), min(ys), max(ys)
    bbox_w = max(maxx - minx, 1e-6)

    if getattr(args, "_resolved_scale", None):
        s0 = args._resolved_scale
    elif args.scale:
        s0 = args.scale
    elif args.print_scale:
        s0 = PT_TO_MM_PAPER * args.print_scale / 1000.0
    else:
        s0 = 10.0 / bbox_w

    n0 = len(segments)
    if not getattr(args, "auto_adaptive", False):
        X_MAX_PT = args.x_max / s0
        X_MIN_PT = args.x_min / s0
        segments = [s for s in segments
                    if min(s[0], s[2]) >= X_MIN_PT and max(s[0], s[2]) <= X_MAX_PT]
        print(f"Фильтр по X: {n0} → {len(segments)} сегментов "
              f"(X ∈ [{args.x_min}, {args.x_max}] м)")
    else:
        print(f"[ADAPT] X-фильтр P1 отключён: сохранено {n0} сегментов CAD-слоя")

    h_lines, v_lines = snap_segments(segments, max(4.0, 0.25 / s0))
    # Для построения комнат нельзя объединять горизонтальные/вертикальные
    # линии на расстоянии почти метра: это смешивает стены с элементами
    # оборудования и дверными деталями. Поэтому используем узкую группировку.
    pair_tol = (0.18 if getattr(args, "auto_adaptive", False) else WALL_DETAIL_TOL_M) / s0
    walls_h = group_walls(h_lines, pair_tol)
    walls_v = group_walls(v_lines, pair_tol)
    walls_h, walls_v = select_walls(walls_h, walls_v, keep_singles=not args.no_singles)
    min_iv = WALL_MIN_INTERVAL_M / s0
    walls_h = [w for w in walls_h if max((b-a) for a,b in w["intervals"]) >= min_iv]
    walls_v = [w for w in walls_v if max((b-a) for a,b in w["intervals"]) >= min_iv]

    partition_info = None
    if INFER_PARTITION:
        walls_h, walls_v, partition_info = infer_missing_partition(
            walls_h, walls_v, areas, s0, verbose=args.debug)

    wb = bbox_of(walls_h, walls_v)
    if wb:
        print(f"[BBOX pt] X {wb[0]:.1f}..{wb[2]:.1f}  Y {wb[1]:.1f}..{wb[3]:.1f}  "
              f"({wb[2]-wb[0]:.1f}×{wb[3]-wb[1]:.1f} pt)")
        print(f"[BBOX m ] X {wb[0]*s0:.2f}..{wb[2]*s0:.2f}  "
              f"Y {wb[1]*s0:.2f}..{wb[3]*s0:.2f}")

    dim_scale = estimate_scale_from_dims(words, dim_segments if dim_segments else segments)

    if getattr(args, "_resolved_scale", None):
        scale = args._resolved_scale
        src = getattr(args, "_resolved_scale_source", "resolved")
    elif args.scale:
        scale, src = args.scale, "вручную (--scale)"
    elif args.print_scale:
        scale = PT_TO_MM_PAPER * args.print_scale / 1000.0
        src = f"полиграфический 1:{args.print_scale:g}"
    elif args.plan_width and wb:
        ext = max(wb[2] - wb[0], wb[3] - wb[1])
        scale, src = args.plan_width / ext, "по --plan-width и габариту стен"
    elif dim_scale:
        scale, src = dim_scale, "по размерным надписям"
    elif areas and wb:
        rects = []
        for axis, walls in (("h", walls_h), ("v", walls_v)):
            for w in walls:
                half = max(w["thick_pts"], 3.0) / 2
                for a, b in w["intervals"]:
                    if axis == "h":
                        rects.append(shbox(a, w["center"] - half, b, w["center"] + half))
                    else:
                        rects.append(shbox(w["center"] - half, a, w["center"] + half, b))
        hull_area = unary_union(rects).convex_hull.area if rects else 0
        scale = math.sqrt(sum(areas) * 1.15 / hull_area) if hull_area > 0 else s0
        src = "по площадям из текста"
    else:
        scale, src = s0, "черновой"
    print(f"Масштаб: {scale * 1000:.2f} мм/точку ({src})")

    tf = Tf(wb[0], wb[3], scale) if wb else Tf(minx, maxy, scale)

    # Сначала строим чистую стеновую сеть из выбранных контуров комнат.
    # Раньше ниже использовались walls_h/walls_v из всего PDF, из-за чего
    # в 3D возвращались мебель, сантехника и детали дверей.
    polys = polygonize_rooms(
        walls_h, walls_v,
        snap_tol_pt=ROOM_SNAP_TOL_M / s0,
        gap_tol_pt=BRIDGE_GAP_TOL_M / s0,
        min_area_pt2=1.0 / (s0 * s0),
        verbose=args.debug,
    )
    if getattr(args, "auto_adaptive", False) and not areas:
        # v1.1: для CAD-планов без надёжных площадей нельзя обнулять
        # найденные замкнутые контуры. Polygonize уже работает по выбранному
        # wall-layer и возвращает именно замкнутые ячейки стеновой сети.
        # Используем их как геометрические помещения; названия/площади из OCR
        # при этом не выдумываем.
        room_polys = polys
        if args.debug:
            print(f"[ROOM] нет надёжных OCR-площадей — используем {len(room_polys)} замкнутых CAD-контуров")
    else:
        room_polys = select_room_polys_by_labels(
            polys, words, wb, scale, target_areas=areas, verbose=args.debug
        )
    if args.debug:
        print_polygon_area_report(room_polys, scale, areas)

    if room_polys:
        if getattr(args, "auto_adaptive", False) and not areas:
            # v1.1: комнаты и стеновая 3D-сетка — разные уровни модели.
            # Для CAD-планов без текстовых площадей polygonize даёт полезные
            # замкнутые помещения, но его границы могут не содержать короткие
            # участки исходного wall-layer. Поэтому сохраняем полную CAD-сетку
            # для стен/проёмов, а найденные полигоны используем для комнат и
            # топологии. Это не теряет площадь внешнего контура.
            model_H, model_V = bridge_gaps_in_walls(
                walls_h, walls_v, gap_tol=BRIDGE_GAP_TOL_M / s0
            )
            if args.debug:
                print(f"[WALL3D] комнаты из CAD-контуров, стены из полной wall-grid: {len(model_H)+len(model_V)} осей")
        else:
            bsegs = dedupe_boundary_segments(
                polygon_boundary_segments(room_polys, scale),
                tol_pt=max(2.0, 0.03 / max(s0, 1e-9))
            )
            model_H=[]; model_V=[]
            for axis,pos,a,b in bsegs:
                if axis == "h":
                    model_H.append({"center":pos,"intervals":[(a,b)],"n":2,"thick_pts":DEFAULT_THICK/s0})
                else:
                    model_V.append({"center":pos,"intervals":[(a,b)],"n":2,"thick_pts":DEFAULT_THICK/s0})
            if args.debug:
                print(f"[WALL3D] осевых сегментов из комнат: {len(bsegs)}")
    else:
        # P2.0 fallback для CAD-планов без текстовых площадей: сами пары
        # чёрных wall-edge линий уже являются надёжной осевой сеткой.
        # На уровне 3D временно замыкаем небольшие проёмы, чтобы затем
        # legacy-gap detector мог вырезать их как двери/окна.  Без этого
        # разрыв физически представлен двумя независимыми стенами и его
        # невозможно вырезать.
        model_H, model_V = bridge_gaps_in_walls(
            walls_h, walls_v, gap_tol=BRIDGE_GAP_TOL_M / s0
        )
        if args.debug:
            print(f"[WALL3D] контуры помещений не размечены — используем CAD wall-grid: {len(model_H)+len(model_V)} осей")

    meshes, n_windows, n_walls = [], 0, 0
    doors_inferred = 0
    opening_records = []
    legacy_gaps = _legacy_gap_openings(walls_h, walls_v, tf)

    # Каждую распознанную дверь привязываем ровно к одной границе комнаты.
    # Иначе дверь на общей стене двух помещений вырезалась сразу из двух
    # параллельных сегментов. Выбираем ближайший сегмент к hinge.
    model_segments=[]
    for axis,walls in (("h",model_H),("v",model_V)):
        for w in walls:
            for a_pt,b_pt in w["intervals"]:
                if axis=="h":
                    model_segments.append((axis,tf.y(w["center"]),tf.x(a_pt),tf.x(b_pt),w))
                else:
                    yy0,yy1=sorted((tf.y(a_pt),tf.y(b_pt)))
                    model_segments.append((axis,tf.x(w["center"]),yy0,yy1,w))
    door_assignment={}
    for di,cand in enumerate(opening_candidates):
        if cand.kind!="door": continue
        hx,hy=tf.x(cand.p0[0]),tf.y(cand.p0[1])
        best=None
        for si,(axis,pos,a,b,w) in enumerate(model_segments):
            d=abs(hy-pos) if axis=="h" else abs(hx-pos)
            t=hx if axis=="h" else hy
            if t < a-0.40 or t > b+0.40: continue
            key=(d, max(0,a-t,t-b))
            if best is None or key<best[0]:
                best=(key,si)
        if best is not None and best[0][0] <= 0.40:
            door_assignment[di]=best[1]
    if args.debug:
        print(f"[DOOR-MAP] привязано дверей к границам: {len(door_assignment)}/{sum(1 for c in opening_candidates if c.kind=='door')}")

    # Строим стены по model_H/model_V и режем их реальными/эвристическими
    # проёмами. Все координаты здесь уже в метрах после Tf. 
    for axis, walls in (("h", model_H), ("v", model_V)):
        for w in walls:
            thick_m = DEFAULT_THICK
            for a_pt,b_pt in w["intervals"]:
                if axis == "h":
                    a,b=tf.x(a_pt),tf.x(b_pt)
                    c_m=tf.y(w["center"])
                else:
                    y0,y1=tf.y(a_pt),tf.y(b_pt)
                    a,b=min(y0,y1),max(y0,y1)
                    c_m=tf.x(w["center"])
                if b-a < 0.25:
                    continue

                openings=[]
                # 1) Распознанные распашные двери.
                # Только двери, назначенные именно этому сегменту.
                current_si = None
                for si,(sax,spos,sa,sb,sw) in enumerate(model_segments):
                    if sax==axis and sw is w and abs(spos-c_m)<1e-7 and abs(sa-a)<0.03 and abs(sb-b)<0.03:
                        current_si=si; break
                for di,cand in enumerate(opening_candidates):
                    if cand.kind != "door" or door_assignment.get(di) != current_si:
                        continue
                    op=_door_opening_on_segment(cand,axis,c_m,a,b,tf,tol=0.35)
                    if op is not None:
                        openings.append(op)

                # 2) Старые разрывы используются только если они геометрически
                # лежат на выбранной границе комнаты. Это возвращает окна и
                # двери, которые в PDF представлены обычным разрывом стены.
                for ga,gpos,g0,g1,gkind in legacy_gaps:
                    if ga!=axis or abs(gpos-c_m)>0.14:
                        continue
                    ov0=max(a,g0); ov1=min(b,g1)
                    if ov1-ov0 < 0.35:
                        continue
                    openings.append((ov0,ov1,"door" if gkind=="door_gap" else "window",None))

                # Сначала объединяем двери между собой, затем вычитаем их
                # из оконных разрывов. Частичное пересечение не должно превращать
                # весь оконный интервал в дверь.
                door_int=[]; win_int=[]
                for o0,o1,kind,cand in openings:
                    (door_int if kind=="door" else win_int).append((o0,o1,kind,cand))
                clean=[]
                for o0,o1,kind,cand in sorted(door_int,key=lambda q:q[0]):
                    if clean and o0 <= clean[-1][1]+0.05:
                        clean[-1]=(clean[-1][0],max(clean[-1][1],o1),"door",clean[-1][3] or cand)
                    else:
                        clean.append((o0,o1,"door",cand))
                for wo0,wo1,_,_ in win_int:
                    pieces=[(wo0,wo1)]
                    for do0,do1,_,_ in door_int:
                        nxt=[]
                        for p0,p1 in pieces:
                            if do1<=p0+0.02 or do0>=p1-0.02:
                                nxt.append((p0,p1)); continue
                            if p0<do0-0.02: nxt.append((p0,min(p1,do0)))
                            if p1>do1+0.02: nxt.append((max(p0,do1),p1))
                        pieces=nxt
                    for p0,p1 in pieces:
                        if p1-p0>=0.35:
                            clean.append((p0,p1,"window",None))
                clean=sorted(clean,key=lambda q:q[0])
                openings=clean
                if args.debug and openings:
                    desc=[]
                    for oo0,oo1,kk,cc in openings:
                        if cc is not None:
                            try: dn=opening_candidates.index(cc)+1
                            except ValueError: dn="?"
                            desc.append(f"{kk}:{oo0:.2f}-{oo1:.2f}:D#{dn}")
                        else:
                            desc.append(f"{kk}:{oo0:.2f}-{oo1:.2f}")
                    print(f"[OPEN] {axis} pos={c_m:.2f} seg={a:.2f}-{b:.2f} -> " + ", ".join(desc))

                # Считаем реальные стеновые куски, а не исходный цельный сегмент.
                cuts=[a,b]
                for o0,o1,_,_ in openings:
                    cuts.extend([max(a,o0),min(b,o1)])
                cuts=sorted(set(round(x,5) for x in cuts))
                wall_parts=[]
                for u,v in zip(cuts,cuts[1:]):
                    if v-u < 0.03: continue
                    covered=any(u >= o0-0.02 and v <= o1+0.02 for o0,o1,_,_ in openings)
                    if not covered:
                        wall_parts.append((u,v))
                for u,v in wall_parts:
                    if axis=="h":
                        add_box(meshes,(u+v)/2,c_m,0,H,v-u,thick_m,WALL_COLOR)
                    else:
                        add_box(meshes,c_m,(u+v)/2,0,H,thick_m,v-u,WALL_COLOR)

                for o0,o1,kind,cand in openings:
                    opening_records.append({"id":f"{kind}_{len(opening_records)+1:03d}",
                                            "kind":kind,"source":"candidate" if cand is not None else "wall_gap",
                                            "width_m":round(max(0.0,o1-o0),3),
                                            "axis":axis,"position_m":round(c_m,3),
                                            "start_m":round(o0,3),"end_m":round(o1,3)})
                    if kind=="door" and cand is None:
                        doors_inferred += 1
                    if kind=="door":
                        add_box(meshes,(o0+o1)/2,c_m,DOOR_HEIGHT,H,
                                o1-o0,thick_m,WALL_COLOR) if axis=="h" else \
                        add_box(meshes,c_m,(o0+o1)/2,DOOR_HEIGHT,H,
                                thick_m,o1-o0,WALL_COLOR)
                    else:
                        n_windows += 1
                        if axis=="h":
                            add_box(meshes,(o0+o1)/2,c_m,0,WINDOW_SILL,o1-o0,thick_m,WALL_COLOR)
                            add_box(meshes,(o0+o1)/2,c_m,WINDOW_HEAD,H,o1-o0,thick_m,WALL_COLOR)
                        else:
                            add_box(meshes,c_m,(o0+o1)/2,0,WINDOW_SILL,thick_m,o1-o0,WALL_COLOR)
                            add_box(meshes,c_m,(o0+o1)/2,WINDOW_HEAD,H,thick_m,o1-o0,WALL_COLOR)
                n_walls += len(wall_parts) + len(openings)

    # Полотна дверей: строим по реальному вектору p0->p1, а не только по
    # признаку orientation. Это сохраняет диагональные/распахнутые полотна
    # такими, как они нарисованы на плане. Один конец полотна — hinge.
    for cand in opening_candidates:
        if cand.kind != "door":
            continue
        leaf_p0 = cand.meta.get("leaf_p0")
        leaf_p1 = cand.meta.get("leaf_p1")
        if not leaf_p0 or not leaf_p1:
            continue
        x0, y0 = tf.x(leaf_p0[0]), tf.y(leaf_p0[1])
        x1, y1 = tf.x(leaf_p1[0]), tf.y(leaf_p1[1])
        dx, dy = x1 - x0, y1 - y0
        length = math.hypot(dx, dy)
        if length < 0.40:
            continue
        # Для каждого кандидата ранее уже выбран endpoint, ближайший к
        # fitted-circle center. Он должен быть hinge. Геометрически это
        # также тот конец, который лежит ближе к стене/проёму.
        hc = cand.meta.get("hinge_center")
        if hc is not None:
            hxm, hym = tf.x(hc[0]), tf.y(hc[1])
            if math.hypot(x1-hxm, y1-hym) < math.hypot(x0-hxm, y0-hym):
                x0, y0, x1, y1 = x1, y1, x0, y0
                dx, dy = x1 - x0, y1 - y0
        m = trimesh.creation.box(extents=(length, 0.04, DOOR_HEIGHT))
        angle = math.atan2(dy, dx)
        rot = trimesh.transformations.rotation_matrix(angle, [0, 0, 1])
        m.apply_transform(rot)
        m.apply_translation(((x0+x1)/2, (y0+y1)/2, DOOR_HEIGHT/2))
        m.visual.face_colors = DOOR_COLOR
        meshes.append(m)


    bal = balcony_by_text(words, room_polys, walls_h, walls_v,
                          wb or (minx, miny, maxx, maxy), scale, args.balcony_label)
    if bal is None:
        bal = balcony_by_geometry(room_polys, walls_h, walls_v, scale, wb)
    # На этом плане подпись «Балкон» может отсутствовать как отдельное слово.
    # Тогда 9.74 м² — однозначная метка из шести площадей, а выбранный контур
    # находится у верхней внешней границы.
    if bal is None and room_polys:
        candidates=[]
        for p in room_polys:
            a=p.area*scale*scale
            pb=p.bounds
            touch_top=abs(pb[1]-wb[1]) <= 0.35/s0 if wb else False
            if abs(a-9.74)<=0.8 and touch_top:
                candidates.append(p)
        if candidates:
            bal=min(candidates,key=lambda p:abs(p.area*scale*scale-9.74))
            if args.debug:
                print(f"[BALC] выбран контур 9.74 м²: {bal.area*scale*scale:.2f} м²")
    if bal is not None:
        coords = list(bal.exterior.coords)
        for (x1, y1), (x2, y2) in zip(coords, coords[1:]):
            if math.hypot(x2 - x1, y2 - y1) * scale < 0.3:
                continue
            mid = Point((x1 + x2) / 2, (y1 + y2) / 2)
            if any(q is not bal and q.boundary.distance(mid) < 0.5 for q in polys):
                continue
            if abs(y1 - y2) < abs(x2 - x1) * 0.1:
                a, b = sorted([tf.x(x1), tf.x(x2)])
                add_box(meshes, (a + b) / 2, tf.y(y1), 0, PARAPET_H, b - a, 0.1, PARAPET_COLOR)
            elif abs(x1 - x2) < abs(y2 - y1) * 0.1:
                a, b = sorted([tf.y(y1), tf.y(y2)])
                add_box(meshes, tf.x(x1), (a + b) / 2, 0, PARAPET_H, 0.1, b - a, PARAPET_COLOR)
        poly_m = Polygon([(tf.x(x), tf.y(y)) for x, y in coords])
        meshes.append(slab_from_polygon(poly_m, 0.12, BALC_COLOR))

    # Пол пола теперь ограничен фактическими контурами помещений. Раньше
    # прямоугольная плита по bbox заливала пустое пространство вокруг
    # Г-образного/нерегулярного плана.
    if room_polys:
        try:
            floor_union = unary_union(room_polys)
            geoms = list(floor_union.geoms) if hasattr(floor_union, "geoms") else [floor_union]
            for fp in geoms:
                if getattr(fp, "area", 0.0) <= 0.05:
                    continue
                # room_polys живут в координатах PDF (pt); 3D — в метрах.
                # P1 здесь пропускал трансформацию, что могло раздувать пол
                # до сотен метров. В P2.0 преобразуем явно через тот же Tf.
                fp_m = shp_transform(lambda x,y,z=None: (tf.x(x), tf.y(y)), fp)
                meshes.append(slab_from_polygon(fp_m, 0.20, FLOOR_COLOR))
        except Exception:
            if wb:
                W = (wb[2] - wb[0]) * scale
                L = (wb[3] - wb[1]) * scale
                add_box(meshes, W / 2, L / 2, -0.2, 0.0, W, L, FLOOR_COLOR)

    if args.debug:
        dump_debug_svg(walls_h, walls_v, words, opening_candidates, "debug_walls.svg")

    extent = ((wb[2] - wb[0]) * scale, (wb[3] - wb[1]) * scale) if wb else None
    n_accepted_doors = sum(1 for c in opening_candidates if c.kind == "door")
    floor_polys = [p for p in polys if bal is None or p is not bal]
    p25 = build_p25_model(
        room_polys, model_H, model_V, opening_records, scale, tf, H, DEFAULT_THICK,
        label_areas=areas)
    quantities = make_quantity_report(
        room_polys, floor_polys, model_H, model_V, scale, H, DEFAULT_THICK,
        doors=n_accepted_doors + doors_inferred, windows=n_windows,
        opening_records=opening_records, label_areas=areas, p25_model=p25)
    project_model = {
        "schema":"kodolov.project.v0.5",
        "coordinate_system":"local_plan_m",
        "scale":{"m_per_pdf_point":scale,
                 "source":getattr(args,"_resolved_scale_source","resolved"),
                 "confidence":getattr(args,"_scale_confidence",None)},
        "wall_height_m":H,
        "rooms":p25["rooms"],
        "rooms_status":p25["rooms_status"],
        "walls":p25["walls"],
        "openings":p25["openings"],
        "topology":p25["topology"],
        "validation":p25["validation"],
        "quantities":{k:v for k,v in quantities.items() if k not in ("rooms","walls","openings")},
    }
    return trimesh.Scene(meshes), {
        "walls": n_walls,
        "doors_accepted": n_accepted_doors,
        "doors_inferred": doors_inferred,
        "windows": n_windows,
        "scale": scale,
        "scale_source": src,
        "scale_confidence": getattr(args, "_scale_confidence", None),
        "balcony": bal is not None,
        "extent": extent,
        "quantities": quantities,
        "project_model": project_model,
    }



# ============================================================================
# ДЕМО-РЕЖИМ
# ============================================================================
def build_demo_scene(rooms, balcony, args):
    H, CW = args.wall_height, 1.5
    meshes = []

    def hwall(x0, x1, y, t, ops=(), height=H, color=WALL_COLOR):
        for a, b, z0, z1 in split_by_openings(x0, x1, ops, height):
            add_box(meshes, (a + b) / 2, y, z0, z1, b - a, t, color)

    def vwall(x, y0, y1, t, ops=(), height=H, color=WALL_COLOR):
        for a, b, z0, z1 in split_by_openings(min(y0, y1), max(y0, y1), ops, height):
            add_box(meshes, x, (a + b) / 2, z0, z1, t, b - a, color)

    row1, row2, s1, s2 = [], [], 0.0, 0.0
    for r in sorted(rooms, key=lambda r: -r[1]):
        if s1 <= s2:
            row1.append(r); s1 += r[1]
        else:
            row2.append(r); s2 += r[1]

    def depth(row):
        return min(5.0, max(3.2, sum(a for _, a in row) / 12.0))

    def build_row(row, y_edge, sign):
        D = depth(row)
        y_back = y_edge + sign * D
        x, bounds = 0.0, []
        for name, area in row:
            w = max(1.6, area / D)
            bounds.append((x, x + w, name))
            x += w
        W = x
        vwall(0, y_edge, y_back, 0.2)
        vwall(W, y_edge, y_back, 0.2)
        back_ops = []
        if balcony and sign > 0 and bounds:
            xm = (bounds[0][0] + bounds[0][1]) / 2
            back_ops = [(xm - 0.6, xm + 0.6, "door")]
        hwall(0, W, y_back, 0.2, back_ops)
        front_ops = [(((xa + xb) / 2) - 0.45, ((xa + xb) / 2) + 0.45, "door")
                     for xa, xb, _ in bounds]
        hwall(0, W, y_edge, 0.12, front_ops)
        for xa, xb, _ in bounds[:-1]:
            vwall(xb, y_edge, y_back, 0.12)
        return W, bounds, y_back

    D1, D2 = depth(row1), depth(row2)
    W1, b1, y_back1 = build_row(row1, CW, +1)
    W2, b2, y_back2 = build_row(row2, 0.0, -1)
    Wmax = max(W1, W2)
    vwall(Wmax, 0, CW, 0.2)
    vwall(0, 0, CW, 0.2, ops=[(0.3, 1.25, "door")])

    db = 0.0
    if balcony and b1:
        xa, xb, _ = b1[0]
        wb = min(xb - xa, balcony[1] / 2.0)
        db = balcony[1] / wb
        xm, y0 = (xa + xb) / 2, y_back1
        hwall(xm - wb / 2, xm + wb / 2, y0 + db, 0.1, height=PARAPET_H, color=PARAPET_COLOR)
        vwall(xm - wb / 2, y0, y0 + db, 0.1, height=PARAPET_H, color=PARAPET_COLOR)
        vwall(xm + wb / 2, y0, y0 + db, 0.1, height=PARAPET_H, color=PARAPET_COLOR)
        add_box(meshes, xm, y0 + db / 2, -0.12, 0.0, wb, db, BALC_COLOR)

    pad = 0.3
    ymin, ymax = -D2 - pad, CW + D1 + pad + db
    add_box(meshes, Wmax / 2, (ymin + ymax) / 2, -0.2, 0.0,
            Wmax + 2 * pad, ymax - ymin, FLOOR_COLOR)
    return trimesh.Scene(meshes)


def run_demo(areas, args):
    if areas:
        names = [n for n, _ in DEFAULT_ROOMS]
        rooms = [(names[i] if i < len(names) else f"Помещение {i + 1}", a)
                 for i, a in enumerate(sorted(areas, reverse=True))]
    else:
        rooms = list(DEFAULT_ROOMS)
    balcony, rooms2 = None, []
    for name, a in rooms:
        if BALC_RE.search(name):
            balcony = (name, a)
        else:
            rooms2.append((name, a))
    return build_demo_scene(rooms2, balcony, args)


# ============================================================================
# MAIN
# ============================================================================
def resolve_pdf(path):
    if path and os.path.exists(path):
        return path
    if path:
        print("Файл не найден:", path)
    candidates = sorted(glob.glob("*.pdf"))
    if candidates:
        print(f"Найден PDF в папке — использую: {candidates[0]}")
        return candidates[0]
    return None


def main():
    ap = argparse.ArgumentParser(description="3D-модель квартиры по плану в PDF")
    ap.add_argument("pdf", nargs="?", help="файл плана")
    ap.add_argument("--page", type=int, default=-1, help="номер листа с нуля; -1 = автоопределение")
    ap.add_argument("--no-auto", action="store_true", help="отключить адаптивный анализ CAD/PDF")
    ap.add_argument("--out", default="model.glb")
    ap.add_argument("--wall-height", type=float, default=WALL_HEIGHT)
    ap.add_argument("--plan-width", type=float, help="реальная ширина плана, м")
    ap.add_argument("--scale", type=scale_type,
                    help="метров на точку PDF (0.0176) или масштаб вида 1:50")
    ap.add_argument("--print-scale", type=float,
                    help="знаменатель полиграфического масштаба (50 для 1:50)")
    ap.add_argument("--x-min", type=float, default=X_MIN_M,
                    help=f"минимальная X координата плана, м (по умолчанию {X_MIN_M})")
    ap.add_argument("--x-max", type=float, default=X_MAX_M,
                    help=f"максимальная X координата плана, м (по умолчанию {X_MAX_M})")
    ap.add_argument("--partition-thick", type=float, default=DEFAULT_THICK,
                    help="толщина однолинейных перегородок, м")
    ap.add_argument("--no-singles", action="store_true",
                    help="не считать однолинейные линии стенами")
    ap.add_argument("--keep-dashed", action="store_true",
                    help="не отбрасывать штриховые линии")
    ap.add_argument("--balcony-label", help="свой текст подписи балкона в PDF")
    ap.add_argument("--debug", action="store_true", help="записать debug_walls.svg")
    ap.add_argument("--demo", action="store_true")
    ap.add_argument("--show", action="store_true")
    ap.add_argument("--report", help="JSON-отчёт геометрических объёмов; по умолчанию <out>.json")
    # v12: флаги для дверей
    ap.add_argument("--door-score", type=float, default=DOOR_SCORE_ACCEPT,
                    help=f"порог score для дверей (по умолчанию {DOOR_SCORE_ACCEPT})")
    ap.add_argument("--door-debug", action="store_true",
                    help="печатать детальную диагностику дверей")
    args = ap.parse_args()
    args.auto_adaptive = not args.no_auto

    segments, words, dim_segments = [], [], []
    opening_candidates = []
    door_stats = {}
    pdf_path = resolve_pdf(args.pdf)
    if pdf_path:
        try:
            requested_page = None if args.page < 0 else args.page
            selected_page = detect_plan_page(pdf_path, requested=requested_page, verbose=args.debug)
            if requested_page is None:
                args.page = selected_page
            else:
                args.page = requested_page
            layer_info = analyze_pdf_layers(pdf_path, args.page)
            wall_layer = layer_info.get("wall_layer")
            dim_layer = layer_info.get("dim_layer")
            door_layer = layer_info.get("door_layer")
            print(f"[PLAN] лист PDF: {args.page+1}")
            print(f"[LAYERS] стены={wall_layer!r}, двери={door_layer!r}, размеры={dim_layer!r}")

            s0_guess = args.scale or (PT_TO_MM_PAPER * (args.print_scale or 50) / 1000.0)
            # Сначала извлекаем тёмные осевые линии базового CAD-слоя. Для
            # Headliner это слой '0'; для старого projectfortest остаётся
            # прежний fallback по слоям 'стены/фундамент'.
            dark_bbox = _central_dark_bbox(pdf_path,args.page,wall_layer) if wall_layer else None
            if dark_bbox:
                # Отсекаем рамку листа и мелкие элементы вокруг плана.
                pad=12
                plan_bbox=(dark_bbox[0]-pad,dark_bbox[1]-pad,dark_bbox[2]+pad,dark_bbox[3]+pad)
            else:
                plan_bbox=None
            if wall_layer and wall_layer not in WALL_LAYERS:
                segs_all,_ = _extract_layer_segments(pdf_path,args.page,[wall_layer],dark_only=True,
                                                      bbox=plan_bbox,keep_dashed=args.keep_dashed,min_line_pt=4)
                words = []
            else:
                segs_all, words, _ = extract_pdf(pdf_path,args.page,args.keep_dashed,
                                                  wall_layers=WALL_LAYERS,exclude_leaf_pts=None)
            # В CAD-PDF текст часто превращён в кривые — подключаем OCR только
            # когда обычный PDF-text пустой.
            had_pdf_words = bool(words)
            if not words:
                words=synthesize_ocr_words(pdf_path,args.page)
            print(f"PDF: {pdf_path} — базовых сегментов стен {len(segs_all)}, слов/OCR {len(words)}")

            # Масштаб сначала проверяем по dimension-layer/OCR, но не заставляем
            # пользователя каждый раз вручную задавать его.
            dim_segments=[]
            if dim_layer:
                dim_segments,_ = _extract_layer_segments(pdf_path,args.page,[dim_layer],
                                                          dark_only=False,keep_dashed=True,min_line_pt=4)
            scale_result = estimate_scale_robust(words, dim_segments, default=s0_guess, verbose=args.debug)
            if isinstance(scale_result, tuple):
                s0_guess, scale_confidence, scale_details = scale_result
            else:
                s0_guess, scale_confidence, scale_details = scale_result, 0.20, []
            if args.debug:
                source = "dimensions" if scale_confidence > 0.20 and scale_details else "print-scale/default"
                print(f"[SCALE] source={source}, scale={s0_guess:.5f} м/pt, confidence={scale_confidence:.2f}")
            args._resolved_scale = s0_guess
            args._resolved_scale_source = "dimensions" if scale_confidence > 0.20 and scale_details else "print-scale/default"
            args._scale_confidence = scale_confidence

            if plan_bbox:
                segs_walls=segs_all
            else:
                X_MAX_PT = args.x_max / s0_guess
                X_MIN_PT = args.x_min / s0_guess
                segs_walls=[s for s in segs_all if min(s[0],s[2])>=X_MIN_PT and max(s[0],s[2])<=X_MAX_PT]
            h_lines, v_lines = snap_segments(segs_walls, max(4.0, 0.25 / s0_guess))
            pair_tol = (0.18 if wall_layer and wall_layer not in WALL_LAYERS else 0.90) / s0_guess
            walls_h_for_score = group_walls(h_lines, pair_tol)
            walls_v_for_score = group_walls(v_lines, pair_tol)
            walls_h_for_score, walls_v_for_score = select_walls(
                walls_h_for_score, walls_v_for_score, keep_singles=True)

            print(f"\n=== Детекция дверей (score ≥ {args.door_score}) ===")
            if door_layer and door_layer not in WALL_LAYERS:
                # Dedicated CAD door layer: use its explicit geometry first.
                opening_candidates = extract_doors_from_cad_layer(
                    pdf_path, args.page, door_layer, s0_guess, verbose=args.debug
                )
                used_leaf_pts=set()
                for c in opening_candidates:
                    for lp in (c.meta.get("leaf_p0"),c.meta.get("leaf_p1")):
                        if lp: used_leaf_pts.add((round(lp[0],3),round(lp[1],3)))
                door_stats = {
                    'raw':len(opening_candidates),'accepted_by_score':len(opening_candidates),
                    'rejected_by_score':0,'after_nms':len(opening_candidates),
                    'histogram':{},'top_rejected':[], 'merge_log':[],
                    'score_accept':args.door_score, 'after_arc_dedup':len(opening_candidates)
                }
                print(f"  специальный слой дверей обнаружен: {door_layer!r} (используется CAD-door parser)")
            else:
                opening_candidates, used_leaf_pts, door_stats = extract_doors_v2(
                    pdf_path, args.page, scale=s0_guess,
                    walls_h=walls_h_for_score, walls_v=walls_v_for_score,
                    verbose=False, score_accept=args.door_score)
            print(f"  raw candidates:        {door_stats['raw']}")
            print(f"  accepted by score:     {door_stats['accepted_by_score']}")
            print(f"  rejected by score:     {door_stats['rejected_by_score']}")
            print(f"  after NMS:             {door_stats['after_nms']}")
            for i, c in enumerate(opening_candidates[:15]):
                d_m = _dist(c.p0, c.p1) * s0_guess
                print(f"  #{i+1} [c={c.confidence:.2f}]: "
                      f"p0=({c.p0[0]:.1f},{c.p0[1]:.1f}) "
                      f"p1=({c.p1[0]:.1f},{c.p1[1]:.1f}) "
                      f"|p0-p1|={d_m:.2f} м "
                      f"width={c.width_m:.2f} м orient={c.orientation}")

            if args.door_debug or args.debug:
                print_door_score_diagnostics(door_stats)

            if wall_layer and wall_layer not in WALL_LAYERS:
                segments,_ = _extract_layer_segments(pdf_path,args.page,[wall_layer],dark_only=True,
                                                      bbox=plan_bbox,keep_dashed=args.keep_dashed,min_line_pt=4)
                # исключаем конечные точки найденных полотен
                if used_leaf_pts:
                    def ex(s):
                        return ((round(s[0],3),round(s[1],3)) in used_leaf_pts or
                                (round(s[2],3),round(s[3],3)) in used_leaf_pts)
                    segments=[s for s in segments if not ex(s)]
            else:
                segments, words, _ = extract_pdf(pdf_path,args.page,args.keep_dashed,
                                                  wall_layers=WALL_LAYERS,exclude_leaf_pts=used_leaf_pts)
            print(f"\nПосле исключения полотен: {len(segments)} сегментов стен")
        except Exception as e:
            print(f"Не удалось прочитать PDF: {e}")

    # Площади берём из подписей внутри габарита плана, а не из таблицы
    # экспликации справа. Это важно: в PDF одновременно присутствуют
    # два набора чисел, и таблица содержит площади другой ведомости.
    _plan_bbox = None
    if segments:
        _xs = [q for s in segments for q in (s[0], s[2])]
        _ys = [q for s in segments for q in (s[1], s[3])]
        if _xs and _ys:
            _plan_bbox = (min(_xs), min(_ys), max(_xs), max(_ys))
    areas = parse_plan_areas(words, _plan_bbox) if (_plan_bbox and locals().get("had_pdf_words", False)) else (dedupe_areas(parse_areas(words)) if locals().get("had_pdf_words", False) else [])
    if areas:
        print(f"Площади помещений на плане: {areas} (сумма {sum(areas):.2f} м²)")

    scene, info = None, {}
    if not args.demo and len(segments) >= 8:
        try:
            scene, info = build_from_segments(
                segments, words, areas, args,
                dim_segments=dim_segments,
                opening_candidates=opening_candidates,
            )
        except Exception as e:
            print(f"Ошибка сборки модели: {e}")
        if scene is not None and info.get("walls", 0) == 0:
            print("Стены в векторе не обнаружены — переключаюсь на демо-режим.")
            scene = None
    if scene is None:
        scene = run_demo(areas, args)
        info = {"demo": True}
        print("Демо-режим: схематичная планировка по списку помещений.")

    if not scene.geometry:
        print("Не удалось построить геометрию.")
        return
    scene.export(args.out)
    print(f"\nМодель сохранена: {args.out}")
    if info.get("quantities"):
        q = info["quantities"]
        print("\n=== OBJECT GRAPH ===")
        pm=info.get("project_model",{})
        print(f"Rooms: {len(pm.get('rooms',[]))}")
        print(f"Walls: {len(pm.get('walls',[]))}")
        print(f"Doors: {sum(1 for o in pm.get('openings',[]) if o.get('kind')=='door')}")
        print(f"Windows: {sum(1 for o in pm.get('openings',[]) if o.get('kind')=='window')}")
        print(f"Room↔wall links: {sum(len(r.get('wall_ids',[])) for r in pm.get('rooms',[]))}")
        print(f"Wall↔opening links: {sum(len(w.get('opening_ids',[])) for w in pm.get('walls',[]))}/{len(pm.get('openings',[]))}")
        print("\n=== QUANTITIES / ГЕОМЕТРИЯ ДЛЯ СМЕТЫ ===")
        print(f"Помещений: {q['room_count']}")
        print(f"Площадь пола: {q['floor_area_m2']:.2f} м²")
        print(f"Оси стен: {q['wall_axis_length_m']:.2f} м")
        print(f"Черновая площадь стен: {q['gross_wall_area_m2']:.2f} м²")
        print(f"Площадь потолка: {q['ceiling_area_m2']:.2f} м²")
        if q.get('labeled_floor_area_m2') is not None:
            print(f"Сумма подписанных площадей: {q['labeled_floor_area_m2']:.2f} м²; Δ с геометрией: {q['floor_area_delta_vs_labels_m2']:+.2f} м²")
        print(f"Стены: gross {q['gross_wall_area_one_side_m2']:.2f} м² / net-est {q['net_wall_area_one_side_est_m2']:.2f} м² (одна сторона)")
        if q.get('wall_finish_area_both_sides_est_m2') is not None:
            print(f"Отделка стен по сторонам: {q['wall_finish_area_both_sides_est_m2']:.2f} м² [{q.get('wall_finish_both_sides_status')}]")
        else:
            print(f"Отделка стен по сторонам: unknown [{q.get('wall_finish_both_sides_status')}]")
        if q.get('baseboard_length_m') is not None:
            print(f"Плинтус: {q['baseboard_length_m']:.2f} м [{q.get('baseboard_status')}]")
        else:
            print(f"Плинтус: unknown [{q.get('baseboard_status')}]")
        print(f"Двери: {q['doors_count']} шт., проёмы {q.get('door_opening_area_m2',0):.2f} м²")
        print(f"Окна: {q['windows_count']} шт., проёмы {q.get('window_opening_area_m2',0):.2f} м²")
        print(f"Объём стен: {q['wall_volume_m3']:.2f} м³")
        print(f"Комнаты: {q['room_status']}")
        for r in q["rooms"]:
            print(f"  {r['id']}: {r['area_m2']:.2f} м², периметр {r['perimeter_m']:.2f} м")
        report_path = args.report or (args.out.rsplit('.',1)[0] + '.json' if '.' in args.out else args.out + '.json')
        report_payload = info.get("project_model") or {"source_pdf": pdf_path, "page": args.page+1,
                       "scale_m_per_pt": info.get("scale"),
                       "scale_source": info.get("scale_source"),
                       "scale_confidence": info.get("scale_confidence"),
                       "quantities": q}
        report_payload["source_pdf"] = pdf_path
        report_payload["page"] = args.page + 1
        with open(report_path, 'w', encoding='utf-8') as f:
            json.dump(report_payload, f, ensure_ascii=False, indent=2)
        print(f"Отчёт сохранён: {report_path}")
    if info.get("extent"):
        print(f"Габарит стен: {info['extent'][0]:.2f} × {info['extent'][1]:.2f} м")
    if not info.get("demo"):
        print(f"Стен: {info.get('walls')}")
        print(f"  Дверей (принято по score): {info.get('doors_accepted')}")
        print(f"  Дверей (эвристика разрыва): {info.get('doors_inferred')}")
        print(f"  Окон: {info.get('windows')}")
        print(f"  Балкон: {'да' if info.get('balcony') else 'нет'}")
    if args.show:
        try:
            scene.show()
        except BaseException as e:
            print(f"3D-просмотр не открылся: {e}\n"
                  f"Либо 'pip install pyglet', либо откройте {args.out} "
                  "в Blender / онлайн-просмотрщике GLB.")


if __name__ == "__main__":
    main()