#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Molecule Studio Pro — SMILES · MOL/SDF · PubChem · 3-D animation · Shorts.

Tabs: 📚 Library (46 molecules incl. aspirin/caffeine/glucose/ATP) ·
⌨ Formula · 🧬 SMILES & files (type SMILES, drag-in MOL/SDF, 🌐 PubChem
lookup) · 🛠 Builder.

Signature animation: 🧱 BUILD-UP — the molecule grows atom by atom from its
graph centre: each bond extends outward to the next element, a dashed
reticle marks the landing spot, the atom pops in with a click, ring bonds
snap closed, hydrogens fill last, then the spin resumes. Toggle with the
toolbar button or "B"; replays on every molecule load and plays through
the first seconds of exported MP4/Shorts.

Also: ball/CPK/Lewis/vdW styles, CPK morph, Lewis lone pairs, bond
angle/length callouts, resonance morphing with curly arrows, reaction
scenes (SN2 / addition / acid–base), hydrogen-bond water cluster,
periodic-table shell explorer, chirality badges + mirror animation,
hero-shot cameras, sound design (WAV synth) + music muxed into MP4,
Shorts hooks, cinematic 9:16 preview & export.

Fixes baked in:
  • QPolygonF imported from QtGui (Qt 6 location).
  • smiles_layout() never returns None positions — acyclic SMILES work.
  • addDockWidget uses Qt.DockWidgetArea enums (PySide6 strict enums).
  • Aromatic SMILES bonds get 1.5 order → kekulized; '@'/'/'/'\' skipped.
  • Library GROUPS derived from the data itself (drift impossible).

    pip install PySide6 pillow imageio imageio-ffmpeg numpy
"""

import json, math, random, re, struct, subprocess, sys, tempfile, wave
from collections import deque
from pathlib import Path

from PySide6.QtCore import (QElapsedTimer, QPointF, QRect, QRectF, Qt,
                            QTimer, QVariantAnimation)
from PySide6.QtGui import (QAction, QBrush, QColor, QFont, QFontMetricsF,
                           QImage, QKeySequence, QLinearGradient, QPainter,
                           QPainterPath, QPen, QPolygonF, QRadialGradient,
                           QShortcut, QTransform)
from PySide6.QtWidgets import (QApplication, QButtonGroup, QCheckBox,
                               QComboBox, QDialog, QDockWidget, QFileDialog,
                               QFormLayout, QGridLayout, QGroupBox,
                               QHBoxLayout, QInputDialog, QLabel, QLineEdit,
                               QListWidget, QListWidgetItem, QMenu,
                               QMainWindow, QMessageBox, QProgressDialog,
                               QPushButton, QSlider, QTabWidget, QToolBar,
                               QToolButton, QVBoxLayout, QWidget,
                               QGraphicsView, QGraphicsItem, QGraphicsScene,
                               QGraphicsTextItem)

try:
    import PIL  # noqa
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False
try:
    import imageio.v2 as imageio
    IMAGEIO_OK = True
except Exception:
    imageio = None
    IMAGEIO_OK = False
try:
    import numpy as np
    NUMPY_OK = True
except Exception:
    np = None
    NUMPY_OK = False

CUSTOM_FILE = Path(__file__).with_name("custom_molecules.json")

# ---------------------------------------------------------------------------
# Chemistry data
# ---------------------------------------------------------------------------
ELEMENTS = {  # symbol: (colour, radius px, mass, name, electronegativity)
    "H":  ("#e8edf5", 16.0,  1.008, "Hydrogen",   2.20),
    "C":  ("#454a54", 24.0, 12.011, "Carbon",     2.55),
    "N":  ("#4c6ef5", 23.0, 14.007, "Nitrogen",   3.04),
    "O":  ("#f0544c", 22.0, 15.999, "Oxygen",     3.44),
    "F":  ("#57c268", 20.0, 18.998, "Fluorine",   3.98),
    "Na": ("#b04ec8", 28.0, 22.990, "Sodium",     0.93),
    "P":  ("#f28c3b", 25.0, 30.974, "Phosphorus", 2.19),
    "S":  ("#e6c94c", 26.0, 32.060, "Sulfur",     2.58),
    "Cl": ("#3fbf5a", 28.0, 35.450, "Chlorine",   3.16),
}
VALENCE = {"H": 1, "C": 4, "N": 5, "O": 6, "F": 7, "Na": 1, "P": 5,
           "S": 6, "Cl": 7}
VE = dict(VALENCE)
CPK_R = {"H": 30.0, "C": 42.0, "N": 38.0, "O": 37.0, "F": 35.0, "Na": 54.0,
         "P": 46.0, "S": 45.0, "Cl": 44.0}
SHELLS = {"H": [1], "C": [2, 4], "N": [2, 5], "O": [2, 6], "F": [2, 7],
          "Na": [2, 8, 1], "P": [2, 8, 5], "S": [2, 8, 6], "Cl": [2, 8, 7]}
COMPONSES = {"H": "H₂, H₂O", "C": "CH₄, CO₂", "N": "NH₃, N₂", "O": "H₂O, O₂",
             "F": "HF, NaF", "Na": "NaCl, NaOH", "P": "PH₃, ATP",
             "S": "H₂S, SO₂", "Cl": "HCl, NaCl"}
EXTRA_ELEMENTS = {
    "Br": ("#a6503f", 27.0, 79.904, "Bromine", 2.96),
    "I":  ("#8d5fc9", 29.0, 126.904, "Iodine", 2.66),
    "B":  ("#e6b8a2", 23.0, 10.811, "Boron", 2.04),
    "Si": ("#c8b48c", 26.0, 28.085, "Silicon", 1.90),
}

def ensure_element(el):
    if el in ELEMENTS:
        return
    d = EXTRA_ELEMENTS.get(el, ("#9aa3b2", 25.0, 12.0, el, 2.0))
    ELEMENTS[el] = d
    VE.setdefault(el, 7 if el in ("Br", "I") else 4)
    CPK_R.setdefault(el, 44.0)
    SHELLS.setdefault(el, [2, 8, 18, 7] if el in ("Br", "I") else [2, 4])
    COMPONSES.setdefault(el, "—")

_SUP_TO_ASCII = {"⁺": "+", "⁻": "-", "⁰": "0", "¹": "1", "²": "2", "³": "3",
                 "⁴": "4", "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9"}
_ASCII_TO_SUP = {v: k for k, v in _SUP_TO_ASCII.items()}

# ---- 3-D vector helpers ----------------------------------------------------
def _cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def _n3(v):
    l = math.sqrt(v[0]**2+v[1]**2+v[2]**2) or 1.0
    return (v[0]/l, v[1]/l, v[2]/l)
def _sv3(v, s): return (v[0]*s, v[1]*s, v[2]*s)
def _av3(a, b): return (a[0]+b[0], a[1]+b[1], a[2]+b[2])

_TET = [_n3(v) for v in ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))]

def _tet3(away, length, phase=0.0):
    a = _n3(away)
    ref = (0.0, 0.0, 1.0) if abs(a[2]) < 0.9 else (1.0, 0.0, 0.0)
    p1 = _n3(_cross(a, ref)); p2 = _n3(_cross(a, p1))
    out = []
    for k in range(3):
        phi = phase + k * 2.0 * math.pi / 3.0
        d = _av3(_sv3(a, -1.0/3.0),
                 _sv3(_av3(_sv3(p1, math.cos(phi)), _sv3(p2, math.sin(phi))),
                      math.sqrt(8.0)/3.0))
        out.append(_sv3(d, length))
    return out

def _at(el, v): return (el, v[0], v[1], v[2])

_M_CH4 = [("C", 0.0, 0.0, 0.0)] + [_at("H", _sv3(t, 54.0)) for t in _TET]
_M_NH3 = [("N", 0.0, -16.0, 0.0)] + [
    _at("H", _av3((0.0, -16.0, 0.0), h)) for h in _tet3((0, -1, 0), 56.0, 0.0)]
_M_CHCl3 = ([("C", 0.0, 0.0, 0.0), ("H", 0.0, -52.0, 0.0)] +
            [_at("Cl", d) for d in _tet3((0, -1, 0), 60.0, 0.0)])
_M_CCl4 = [("C", 0.0, 0.0, 0.0)] + [_at("Cl", _sv3(t, 60.0)) for t in _TET]
_M_NH4 = ([("N", 0.0, 0.0, 0.0, "N⁺")] +
          [_at("H", _sv3(t, 52.0)) for t in _TET])
_od = _n3((1.0, 0.35, 0.35))
_M_CH3OH = ([("C", 0.0, 0.0, 0.0)] +
            [_at("H", h) for h in _tet3(_od, 50.0, 0.4)] +
            [_at("O", _sv3(_od, 62.0)),
             _at("H", _av3(_sv3(_od, 62.0), _sv3(_n3((0.95, -0.05, 0.30)), 46.0)))])
_c1d = _n3((-1.0, 0.30, 0.25)); _od2 = _n3((1.0, -0.25, 0.30))
_M_C2H5OH = ([("C", 0.0, 0.0, 0.0), _at("C", _sv3(_c1d, 62.0))] +
             [_at("H", h) for h in _tet3(_sv3(_c1d, -1.0), 50.0, 2.2)] +
             [_at("O", _sv3(_od2, 58.0)),
              _at("H", _sv3(_n3((0.10, -0.92, -0.38)), 50.0)),
              _at("H", _sv3(_n3((-0.10, 0.62, -0.78)), 50.0)),
              _at("H", _av3(_sv3(_od2, 58.0), _sv3(_n3((0.90, -0.35, 0.50)), 46.0)))])
_me_hs = _tet3((1.0, 0.0, 0.0), 50.0, 0.0)
_M_CH3COOH = ([("C", -62.0, 0.0, 0.0), ("C", 0.0, 0.0, 0.0),
               ("O", 34.0, -58.9, 0.0), ("O", -34.0, 58.9, 0.0),
               ("H", -77.2, 74.5, 0.0)] +
              [_at("H", _av3((-62.0, 0.0, 0.0), h)) for h in _me_hs])
_BENZ_C = [("C", 58*math.cos(math.radians(90+60*i)),
                 58*math.sin(math.radians(90+60*i)), 0.0) for i in range(6)]
_BENZ_H = [("H", 104*math.cos(math.radians(90+60*i)),
                 104*math.sin(math.radians(90+60*i)), 0.0) for i in range(6)]

def _mid(a, b): return ((a[1]+b[1])/2.0, (a[2]+b[2])/2.0)

def _ozone_res():
    m01 = _mid(("O", -46, 16, 0), ("O", 0, -22, 0))
    m12 = _mid(("O", 0, -22, 0), ("O", 46, 16, 0))
    return {"forms": [["2", "1"], ["1", "2"]], "arrows": [(m01, m12), (m12, m01)]}
def _so2_res():
    m01 = _mid(("S", 0, 12, 0), ("O", -56, -24, 0))
    m02 = _mid(("S", 0, 12, 0), ("O", 56, -24, 0))
    return {"forms": [["2", "1"], ["1", "2"]], "arrows": [(m01, m02), (m02, m01)]}
def _benz_res():
    mids = [_mid(_BENZ_C[i], _BENZ_C[(i+1) % 6]) for i in range(6)]
    return {"forms": [["2", "1", "2", "1", "2", "1"],
                      ["1", "2", "1", "2", "1", "2"]],
            "arrows": [(mids[i], mids[(i+2) % 6]) for i in (0, 2, 4)]}
def _acetate_res():
    return {"forms": [["2", "1", "1"], ["1", "2", "1"]],
            "arrows": [((21.0, -29.5), (20.0, 34.5))]}

# atoms: (element, x, y, z[, label]) · bonds: (i, j, style)
MOLECULES = [
    {"name": "Hydrogen", "formula": "H2", "geometry": "Linear",
     "polarity": "nonpolar", "info": "The simplest molecule of all.",
     "atoms": [("H", -24, 0, 0), ("H", 24, 0, 0)], "bonds": [(0, 1, "1")]},
    {"name": "Oxygen", "formula": "O2", "geometry": "Linear",
     "polarity": "nonpolar", "info": "Diatomic gas held by a double bond.",
     "atoms": [("O", -30, 0, 0), ("O", 30, 0, 0)], "bonds": [(0, 1, "2")]},
    {"name": "Nitrogen", "formula": "N2", "geometry": "Linear",
     "polarity": "nonpolar", "info": "Very stable gas with a N≡N triple bond.",
     "atoms": [("N", -28, 0, 0), ("N", 28, 0, 0)], "bonds": [(0, 1, "3")]},
    {"name": "Water", "formula": "H2O", "geometry": "Bent · 104.5°",
     "polarity": "polar", "info": "Bent, polar molecule — the universal solvent.",
     "atoms": [("O", 0, -6, 0), ("H", -52, 36, 0), ("H", 52, 36, 0)],
     "bonds": [(0, 1, "1"), (0, 2, "1")], "dipoles": [(1, 0), (2, 0)]},
    {"name": "Hydrogen peroxide", "formula": "H2O2",
     "geometry": "Open book · ~111° dihedral", "polarity": "polar",
     "info": "Twisted O–O backbone — watch the O–H bonds wedge and hash as it spins.",
     "atoms": [("H", -70, 22, 16), ("O", -30, -8, 0),
               ("O", 30, -8, 0), ("H", 70, 22, -16)],
     "bonds": [(0, 1, "1"), (1, 2, "1"), (2, 3, "1")], "dipoles": [(0, 1), (3, 2)]},
    {"name": "Hydrogen fluoride", "formula": "HF", "geometry": "Linear",
     "polarity": "very polar", "info": "Largest electronegativity gap of the simple hydrides.",
     "atoms": [("H", -32, 0, 0), ("F", 34, 0, 0)],
     "bonds": [(0, 1, "1")], "dipoles": [(0, 1)]},
    {"name": "Hydrogen chloride", "formula": "HCl", "geometry": "Linear",
     "polarity": "polar", "info": "Simple polar covalent molecule.",
     "atoms": [("H", -32, 0, 0), ("Cl", 38, 0, 0)],
     "bonds": [(0, 1, "1")], "dipoles": [(0, 1)]},
    {"name": "Hydrogen sulfide", "formula": "H2S", "geometry": "Bent · 92°",
     "polarity": "polar", "info": "Rotten-egg gas; bond angle near 90°, hinting at p orbitals.",
     "atoms": [("S", 0, -4, 0), ("H", -58, 34, 0), ("H", 58, 34, 0)],
     "bonds": [(0, 1, "1"), (0, 2, "1")], "dipoles": [(1, 0), (2, 0)]},
    {"name": "Ammonia", "formula": "NH3",
     "geometry": "Trigonal pyramidal · 107°", "polarity": "polar",
     "info": "A true 3-D pyramid — the three N–H bonds wedge and hash while it spins.",
     "atoms": _M_NH3, "bonds": [(0, 1, "1"), (0, 2, "1"), (0, 3, "1")],
     "dipoles": [(1, 0), (2, 0), (3, 0)]},
    {"name": "Carbon monoxide", "formula": "CO", "geometry": "Linear",
     "polarity": "polar", "info": "Toxic gas with a very strong C≡O triple bond.",
     "atoms": [("C", -26, 0, 0), ("O", 28, 0, 0)],
     "bonds": [(0, 1, "3")], "dipoles": [(0, 1)]},
    {"name": "Carbon dioxide", "formula": "CO2", "geometry": "Linear",
     "polarity": "nonpolar (dipoles cancel)",
     "info": "Two C=O double bonds; the bond dipoles cancel exactly.",
     "atoms": [("O", -72, 0, 0), ("C", 0, 0, 0), ("O", 72, 0, 0)],
     "bonds": [(0, 1, "2"), (1, 2, "2")], "dipoles": [(0, 1), (1, 2)]},
    {"name": "Sulfur dioxide", "formula": "SO2", "geometry": "Bent · 119°",
     "polarity": "polar", "info": "Resonance hybrid of two S–O bonds; volcanic gas.",
     "atoms": [("S", 0, 12, 0), ("O", -56, -24, 0), ("O", 56, -24, 0)],
     "bonds": [(0, 1, "partial"), (0, 2, "partial")],
     "dipoles": [(0, 1), (0, 2)], "resonance": _so2_res()},
    {"name": "Ozone", "formula": "O3", "geometry": "Bent · 117°",
     "polarity": "polar", "info": "Both bonds are resonance hybrids; UV shield.",
     "atoms": [("O", -46, 16, 0), ("O", 0, -22, 0), ("O", 46, 16, 0)],
     "bonds": [(0, 1, "partial"), (1, 2, "partial")],
     "dipoles": [(0, 1), (2, 1)], "resonance": _ozone_res()},
    {"name": "Methane", "formula": "CH4", "geometry": "Tetrahedral · 109.5°",
     "polarity": "nonpolar",
     "info": "Real tetrahedral 3-D geometry — spin it and watch the wedges swap ends.",
     "atoms": _M_CH4,
     "bonds": [(0, 1, "1"), (0, 2, "1"), (0, 3, "1"), (0, 4, "1")]},
    {"name": "Ethene", "formula": "C2H4", "geometry": "Planar · 120°",
     "polarity": "nonpolar", "info": "Planar alkene with a C=C double bond.",
     "atoms": [("H", -66, -32, 0), ("C", -32, 0, 0), ("C", 32, 0, 0),
               ("H", 66, -32, 0), ("H", -66, 32, 0), ("H", 66, 32, 0)],
     "bonds": [(1, 2, "2"), (1, 0, "1"), (2, 3, "1"), (1, 4, "1"), (2, 5, "1")]},
    {"name": "Ethyne", "formula": "C2H2", "geometry": "Linear",
     "polarity": "nonpolar", "info": "Acetylene — welding fuel with a C≡C triple bond.",
     "atoms": [("H", -88, 0, 0), ("C", -32, 0, 0), ("C", 32, 0, 0), ("H", 88, 0, 0)],
     "bonds": [(1, 2, "3"), (0, 1, "1"), (2, 3, "1")]},
    {"name": "Formaldehyde", "formula": "CH2O", "geometry": "Trigonal planar",
     "polarity": "polar", "info": "Simplest aldehyde; planar with a C=O double bond.",
     "atoms": [("O", 0, -48, 0), ("C", 0, 6, 0), ("H", -46, 32, 0), ("H", 46, 32, 0)],
     "bonds": [(0, 1, "2"), (1, 2, "1"), (1, 3, "1")], "dipoles": [(1, 0)]},
    {"name": "Methanol", "formula": "CH3OH", "geometry": "Tetrahedral C",
     "polarity": "polar", "info": "Simplest alcohol — wood spirit, in 3-D.",
     "atoms": _M_CH3OH,
     "bonds": [(0, 1, "1"), (0, 2, "1"), (0, 3, "1"), (0, 4, "1"), (4, 5, "1")],
     "dipoles": [(0, 4)]},
    {"name": "Ethanol", "formula": "C2H5OH", "geometry": "Tetrahedral C",
     "polarity": "polar", "info": "Staggered 3-D conformation of the drinkable alcohol.",
     "atoms": _M_C2H5OH,
     "bonds": [(0, 1, "1"), (1, 2, "1"), (1, 3, "1"), (1, 4, "1"),
               (0, 5, "1"), (5, 8, "1"), (0, 6, "1"), (0, 7, "1")],
     "dipoles": [(0, 5)]},
    {"name": "Acetic acid", "formula": "CH3COOH", "geometry": "Planar COOH",
     "polarity": "polar", "info": "Vinegar's acid — the COOH group is a resonance hybrid.",
     "atoms": _M_CH3COOH,
     "bonds": [(0, 1, "1"), (0, 5, "1"), (0, 6, "1"), (0, 7, "1"),
               (1, 2, "2"), (1, 3, "1"), (3, 4, "1")],
     "dipoles": [(1, 2)], "resonance": _acetate_res()},
    {"name": "Chloroform", "formula": "CHCl3", "geometry": "Tetrahedral",
     "polarity": "slightly polar",
     "info": "Historic anaesthetic; classic wedge-dash textbook drawing in 3-D.",
     "atoms": _M_CHCl3,
     "bonds": [(0, 1, "1"), (0, 2, "1"), (0, 3, "1"), (0, 4, "1")],
     "dipoles": [(1, 0)]},
    {"name": "Carbon tetrachloride", "formula": "CCl4", "geometry": "Tetrahedral",
     "polarity": "nonpolar (dipoles cancel)",
     "info": "Four equal C–Cl dipoles cancel by symmetry.",
     "atoms": _M_CCl4,
     "bonds": [(0, 1, "1"), (0, 2, "1"), (0, 3, "1"), (0, 4, "1")]},
    {"name": "Benzene", "formula": "C6H6", "geometry": "Planar hexagon",
     "polarity": "nonpolar", "info": "Aromatic ring — resonance morphs between two Kekulé forms.",
     "atoms": _BENZ_C + _BENZ_H,
     "bonds": ([(i, (i + 1) % 6, "a") for i in range(6)] +
               [(i, 6 + i, "1") for i in range(6)]),
     "inner_ring": 40.0, "resonance": _benz_res()},
    {"name": "Sodium chloride", "formula": "NaCl", "geometry": "Ionic lattice",
     "polarity": "ionic",
     "info": "An electron transfers from Na to Cl — opposite charges then attract.",
     "atoms": [("Na", -38, 0, 0, "Na⁺"), ("Cl", 42, 0, 0, "Cl⁻")],
     "bonds": [(0, 1, "ionic")], "dipoles": [(0, 1)]},
    {"name": "Ammonium", "formula": "NH4⁺", "geometry": "Tetrahedral",
     "polarity": "positive ion",
     "info": "NH₃'s lone pair donated to H⁺ — a dative adduct.",
     "atoms": _M_NH4,
     "bonds": [(0, 1, "1"), (0, 2, "1"), (0, 3, "1"), (0, 4, "1")]},
    {"name": "Hydroxide", "formula": "OH⁻", "geometry": "Linear ion",
     "polarity": "negative ion",
     "info": "Water minus a proton — a strong base with three lone pairs.",
     "atoms": [("O", -10, 0, 0, "O⁻"), ("H", 46, 0, 0)],
     "bonds": [(0, 1, "1")], "dipoles": [(1, 0)]},
]

# ---------------------------------------------------------------------------
# Formula parsing / display helpers
# ---------------------------------------------------------------------------
def normalize_formula_text(s):
    return "".join(_SUP_TO_ASCII.get(c, c) for c in s)

def charge_suffix(charge):
    if charge == 0:
        return ""
    digits = "".join(_ASCII_TO_SUP[d] for d in str(abs(charge)))
    return (digits if abs(charge) > 1 else "") + ("⁺" if charge > 0 else "⁻")

def parse_formula(text):
    raw = text.strip()
    if not raw:
        return {}, 0, "Type a formula — e.g. H2O, CH3COOH, NH4+, H2SO4"
    s = normalize_formula_text(raw)
    charge = 0
    if "^" in s:
        base, _, ch = s.partition("^")
        ch = ch.replace(" ", "")
        m = re.fullmatch(r"([+-]?)(\d*)([+-]?)", ch)
        num = m.group(2) if m else ""
        sign = (m.group(1) or m.group(3)) if m else ""
        if not m or not num or not sign:
            return {}, 0, "Charge after '^' looks wrong — e.g. SO4^2-"
        charge = int(num) * (1 if sign == "+" else -1)
        s = base
    else:
        m = re.search(r"([+-]+)$", s)
        if m:
            signs = m.group(0)
            if len(set(signs)) > 1:
                return {}, 0, "Mixed trailing '+' and '-' charges"
            charge = 1 if signs[-1] == "+" else -1
            s = s[:m.start()]
    s = s.replace(" ", "")
    if not s:
        return {}, charge, "Formula is empty"
    pos, counts = 0, {}

    def group():
        nonlocal pos
        c = {}
        while pos < len(s):
            ch = s[pos]
            if ch == "(":
                pos += 1
                inner = group()
                if pos >= len(s) or s[pos] != ")":
                    raise ValueError("Missing ')'")
                pos += 1
                mnum = re.match(r"\d+", s[pos:])
                mult = 1
                if mnum:
                    mult = int(mnum.group()); pos += len(mnum.group())
                for k, v in inner.items():
                    c[k] = c.get(k, 0) + v*mult
            elif ch == ")":
                break
            else:
                mel = re.match(r"([A-Z][a-z]?)(\d*)", s[pos:])
                if not mel or not mel.group(1):
                    raise ValueError(f"Unexpected '{ch}'")
                el = mel.group(1); nn = int(mel.group(2) or 1)
                c[el] = c.get(el, 0) + nn; pos += len(mel.group(0))
        return c
    try:
        counts = group()
        if pos < len(s):
            raise ValueError(f"Unexpected '{s[pos]}'")
    except ValueError as exc:
        return {}, 0, str(exc)
    if not counts:
        return {}, charge, "Formula is empty"
    if sum(counts.values()) > 80:
        return {}, charge, "Too many atoms (max 80)"
    for el in counts:
        ensure_element(el)
    return counts, charge, None

def formula_tokens(s):
    s = s.strip(); toks = []
    i, n = 0, len(s)
    while i < n:
        ch = s[i]
        if ch in "⁺⁻⁰¹²³⁴⁵⁶⁷⁸⁹":
            toks.append((ch, 2)); i += 1; continue
        if ch == "^":
            j = i + 1
            while j < n and (s[j].isdigit() or s[j] in "+-"):
                c = s[j]
                toks.append((c if c in "+-" else _ASCII_TO_SUP[c], 2)); j += 1
            i = j; continue
        m = re.match(r"[A-Z][a-z]?", s[i:])
        if m:
            toks.append((m.group(), 0)); i += len(m.group()); continue
        m = re.match(r"\d+", s[i:])
        if m:
            toks.append((m.group(), 1)); i += len(m.group()); continue
        if ch == "+":
            toks.append(("⁺", 2)); i += 1; continue
        if ch in "-−":
            toks.append(("⁻", 2)); i += 1; continue
        toks.append((ch, 0)); i += 1
    return toks

def formula_rich(text):
    out = []
    for tok, t in formula_tokens(text):
        if t == 1:
            out.append(f"<sub>{tok}</sub>")
        elif t == 2:
            out.append(f"<sup>{tok}</sup>")
        else:
            out.append(tok)
    return "".join(out)

def hill_formula(counts):
    order = (["C"] if "C" in counts else []) + \
            (["H"] if "H" in counts else []) + \
            sorted(k for k in counts if k not in ("C", "H"))
    return "".join(f"{e}{counts[e] if counts[e] > 1 else ''}" for e in order)

def molar_mass(mol):
    counts, _c, err = parse_formula(mol.get("formula", ""))
    if err or not counts:
        return 0.0
    return sum(ELEMENTS.get(e, ("", 0, 12.0))[2] * n for e, n in counts.items())

# ---------------------------------------------------------------------------
# SMILES parser + 2-D layout  (FIXED: no None poisoning, @/\ skipped)
# ---------------------------------------------------------------------------
_AROMATIC = set("cnops")
TARGET_V = {"H": 1, "B": 3, "C": 4, "N": 3, "O": 2, "F": 1, "P": 3,
            "S": 2, "Cl": 1, "Br": 1, "I": 1, "Si": 4}

def _smiles_token(s, i):
    if s[i] == "[":
        j = s.index("]", i)
        body = s[i+1:j]
        k = 0
        while k < len(body) and body[k].isdigit():
            k += 1
        m = re.match(r"[A-Z][a-z]?", body[k:])
        if not m:
            raise ValueError(f"Bad bracket atom '[{body}]'")
        el = m.group(); k += m.end()
        mh = re.search(r"H(\d*)", body)
        h = int(mh.group(1) or 1) if mh else 0
        charge = 0
        mc = re.search(r"(\+{2,}|-{2,}|\d*[+-])", body)
        if mc:
            t = mc.group(1)
            if t in ("+", "-"):
                charge = 1 if t == "+" else -1
            elif set(t) <= {"+"}:
                charge = len(t)
            elif set(t) <= {"-"}:
                charge = -len(t)
            else:
                charge = (int(t[:-1]) if t[-1] in "+-" else int(t[1:])) * \
                         (1 if ("+" in t) else -1)
        return el, charge, h, False, True, j + 1
    two = s[i:i+2]
    if two in ("Cl", "Br", "Si"):
        return two, 0, 0, False, False, i + 2
    ch = s[i]
    if ch in "BCNOPSFI":
        return ch, 0, 0, False, False, i + 1
    if ch in _AROMATIC:
        return ch.upper(), 0, 0, True, False, i + 1
    raise ValueError(f"Unexpected character '{ch}' in SMILES")

def parse_smiles(s):
    s = s.strip()
    if not s:
        raise ValueError("Empty SMILES")
    atoms, bonds = [], []
    ring_buf, branch = {}, []
    last, pending, i = None, 1, 0

    def add_atom(el, charge, hexp, aro, from_br):
        ensure_element(el)
        atoms.append({"el": el, "charge": charge, "hexp": hexp,
                      "aromatic": aro, "from_bracket": from_br,
                      "nb": [], "order": []})
        return len(atoms) - 1

    def add_bond(a, b, o):
        if a is None or a == b or a >= len(atoms) or b >= len(atoms):
            return
        if o == 1 and atoms[a]["aromatic"] and atoms[b]["aromatic"]:
            o = 1.5                      # aromatic bond → kekulize later
        atoms[a]["nb"].append(b); atoms[b]["nb"].append(a)
        atoms[a]["order"].append(o); atoms[b]["order"].append(o)
        bonds.append([a, b, o])

    while i < len(s):
        ch = s[i]
        if ch == "(":
            branch.append(last); i += 1
        elif ch == ")":
            last = branch.pop() if branch else None; i += 1
        elif ch == ".":
            last = None; i += 1
        elif ch in "-=#:~":
            pending = {"-": 1, "=": 2, "#": 3, ":": 1.5, "~": 1.5}[ch]; i += 1
        elif ch in "@/\\":                # stereo descriptors & bond directions
            i += 1
        elif ch == "%":
            d = s[i+1:i+3]; i += 3
            if not d.isdigit():
                raise ValueError("Bad %nn ring closure")
            if d in ring_buf:
                j, oo = ring_buf.pop(d)
                add_bond(j, last, oo if oo != 1 else pending)
            else:
                ring_buf[d] = (last, pending)
            pending = 1
        elif ch.isdigit():
            d = ch; i += 1
            if d in ring_buf:
                j, oo = ring_buf.pop(d)
                add_bond(j, last, oo if oo != 1 else pending)
            else:
                ring_buf[d] = (last, pending)
            pending = 1
        else:
            el, charge, hexp, aro, from_br, ni = _smiles_token(s, i)
            idx = add_atom(el, charge, hexp, aro, from_br)
            if last is not None:
                add_bond(last, idx, pending)
            last, pending, i = idx, 1, ni
    if ring_buf:
        raise ValueError(f"Unclosed ring digit(s): {sorted(ring_buf)}")
    if not atoms:
        raise ValueError("No atoms parsed")
    return atoms, bonds

def _kekulize(atoms, bonds):
    aro = [k for k, b in enumerate(bonds) if b[2] == 1.5]
    if not aro:
        return
    used = set()
    for k in aro:
        i, j = bonds[k][0], bonds[k][1]
        if i in used or j in used:
            continue
        bonds[k][2] = 2
        used.add(i); used.add(j)
    for k in aro:
        if bonds[k][2] == 1.5:
            bonds[k][2] = 1

def _add_implicit_h(atoms, bonds):
    adds = []
    for idx, a in enumerate(atoms):
        if a["from_bracket"]:
            h = a["hexp"]
        elif a["aromatic"] and a["el"] != "C":
            h = 0                       # pyridine-type N etc. — no implicit H
        else:
            h = max(0, int(round(TARGET_V.get(a["el"], 4) - sum(a["order"]))))
        adds.extend([idx] * h)
    for parent in adds:
        atoms.append({"el": "H", "charge": 0, "hexp": 0, "aromatic": False,
                      "from_bracket": True, "nb": [], "order": []})
        hi = len(atoms) - 1
        bonds.append([parent, hi, 1])
        for x, y in ((parent, hi), (hi, parent)):
            atoms[x]["nb"].append(y); atoms[x]["order"].append(1)

def _find_rings(n, adj):
    rings, state, parent = [], [0]*n, [-1]*n

    def dfs(u):
        state[u] = 1
        for v, _bi in adj[u]:
            if state[v] == 0:
                parent[v] = u
                dfs(v)
            elif state[v] == 1 and v != parent[u]:
                cyc, x = [v], u
                while x != v and x != -1:
                    cyc.append(x); x = parent[x]
                rings.append(cyc)
        state[u] = 2

    for r in range(n):
        if state[r] == 0:
            dfs(r)
    seen, out = set(), []
    for r in rings:
        k = frozenset(r)
        if k not in seen:
            seen.add(k); out.append(r)
    return out

def smiles_layout(atoms, bonds):
    n = len(atoms)
    adj = [[] for _ in range(n)]
    for bi, (i, j, _o) in enumerate(bonds):
        adj[i].append((j, bi)); adj[j].append((i, bi))
    L = 1.0
    pos = [None] * n
    rings = sorted(_find_rings(n, adj), key=len, reverse=True)

    def place_first(ring):
        m = len(ring)
        R = L / (2 * math.sin(math.pi / m))
        a0 = math.pi / 2 - math.pi / m
        for k, ai in enumerate(ring):
            ang = a0 + 2 * math.pi * k / m
            pos[ai] = (R * math.cos(ang), R * math.sin(ang))

    def place_fused(ring):
        m = len(ring)
        R = L / (2 * math.sin(math.pi / m))
        for k in range(m):
            ia, ib = ring[k], ring[(k + 1) % m]
            if pos[ia] is not None and pos[ib] is not None:
                break
        else:
            return False
        pa, pb = pos[ia], pos[ib]

        def path(f, t):
            seq, kk = [], ring.index(f)
            while True:
                seq.append(ring[kk])
                if ring[kk] == t:
                    break
                kk = (kk + 1) % m
            return seq
        f1 = path(ia, ib); f2 = path(ib, ia)
        seq = f1 if sum(1 for a in f1 if pos[a] is None) >= \
                   sum(1 for a in f2 if pos[a] is None) else f2
        if pos[seq[0]] is None or pos[seq[1]] is None:
            seq = list(reversed(seq))
        mx, my = (pa[0]+pb[0])/2, (pa[1]+pb[1])/2
        dx, dy = pb[0]-pa[0], pb[1]-pa[1]
        ln = math.hypot(dx, dy) or 1
        nx, ny = -dy/ln, dx/ln
        cen = [sum(p[0] for p in pos if p), sum(p[1] for p in pos if p)]
        npl = sum(1 for p in pos if p) or 1
        if ((cen[0]/npl - mx)*nx + (cen[1]/npl - my)*ny) > 0:
            nx, ny = -nx, -ny
        d = R * math.cos(math.pi / m)
        cx, cy = mx + nx*d, my + ny*d
        a1 = math.atan2(pa[1]-cy, pa[0]-cx)
        a2 = math.atan2(pb[1]-cy, pb[0]-cx)
        sign = 1 if ((a2 - a1) % (2*math.pi)) < math.pi else -1
        step = 2*math.pi/m
        pos[seq[0]] = pa
        for k in range(1, len(seq)):
            ang = a1 + sign*step*k
            pos[seq[k]] = (cx + R*math.cos(ang), cy + R*math.sin(ang))
        return True

    if rings:
        place_first(rings[0])
        for r in rings[1:]:
            if any(pos[a] is None for a in r):
                if not place_fused(r):
                    continue

    def choose(u):
        # FIX: never return None — the old version poisoned pos[] and crashed
        # on acyclic molecules ('NoneType' object is not subscriptable).
        if pos[u] is None:
            return (0.0, 0.0)
        pnb = [v for v, _b in adj[u] if pos[v] is not None]
        if not pnb:
            # First atom of a ring-less molecule: grow in a fixed direction.
            return (pos[u][0] + L * math.cos(-math.pi / 3.0),
                    pos[u][1] + L * math.sin(-math.pi / 3.0))
        if len(pnb) == 1:
            w = pnb[0]
            base = math.atan2(pos[w][1]-pos[u][1], pos[w][0]-pos[u][0])
            cands = [base + 2.0944, base - 2.0944]
        else:
            angs = [math.atan2(pos[w][1]-pos[u][1], pos[w][0]-pos[u][0])
                    for w in pnb]
            cands = [_largest_gap(angs)]
        best, bd = None, -1
        for c in cands:
            p = (pos[u][0] + L*math.cos(c), pos[u][1] + L*math.sin(c))
            d = min((math.hypot(p[0]-q[0], p[1]-q[1]) for q in pos if q),
                    default=9.0)
            if d > bd:
                bd, best = d, p
        return best

    seeded = [i for i in range(n) if pos[i] is not None]
    if not seeded:
        pos[0] = (0.0, 0.0); seeded = [0]
    seen = set(seeded); q = deque(seeded)
    while len(seen) < n:
        nxt = deque()
        for u in q:
            if pos[u] is None:
                continue
            for v, _b in adj[u]:
                if v in seen:
                    continue
                pos[v] = choose(u)
                seen.add(v); nxt.append(v)
        q = nxt
        if not q and len(seen) < n:
            v = next(i for i in range(n) if pos[i] is None)
            xs = [p[0] for p in pos if p]
            pos[v] = (max(xs) + 90.0, 0.0); seen.add(v); q = deque([v])

    bl = [math.hypot(pos[j][0]-pos[i][0], pos[j][1]-pos[i][1])
          for i, j, _o in bonds if pos[i] and pos[j]]
    s = 56.0 / (sum(bl)/len(bl) if bl else 1.0)
    cx = sum(p[0] for p in pos)/n; cy = sum(p[1] for p in pos)/n
    return [((p[0]-cx)*s, (p[1]-cy)*s) for p in pos]

def mol_from_smiles(smiles, name, info="", geometry="SMILES → 2-D layout"):
    atoms_d, bonds_r = parse_smiles(smiles)
    _kekulize(atoms_d, bonds_r)
    _add_implicit_h(atoms_d, bonds_r)
    coords = smiles_layout(atoms_d, bonds_r)
    atoms = []
    for a, (x, y) in zip(atoms_d, coords):
        lbl = None
        if a["charge"]:
            lbl = a["el"] + charge_suffix(a["charge"])
        atoms.append((a["el"], x, y, 0.0) + ((lbl,) if lbl else ()))
    stmap = {1: "1", 2: "2", 3: "3", 1.5: "a"}
    bonds = [(i, j, stmap.get(o, "1")) for i, j, o in bonds_r]
    counts = {}
    for a in atoms:
        counts[a[0]] = counts.get(a[0], 0) + 1
    tot_charge = sum(x["charge"] for x in atoms_d)
    return {"name": name, "formula": hill_formula(counts) +
            charge_suffix(tot_charge), "geometry": geometry,
            "polarity": f"ion ({tot_charge:+d})" if tot_charge else "—",
            "info": info or f"Parsed from SMILES: {smiles}",
            "atoms": atoms, "bonds": bonds}

# ---------------------------------------------------------------------------
# MOL / SDF + PubChem
# ---------------------------------------------------------------------------
def parse_mol(text):
    lines = text.splitlines()
    if "V3000" in text[:2000]:
        raise ValueError("V3000 MOLfiles are not supported — export as V2000")
    if len(lines) < 5:
        raise ValueError("Not a MOL/SDF file")
    m = re.match(r"\s*(\d+)\s+(\d+)", lines[3])
    if not m:
        raise ValueError("Unrecognised MOL counts line")
    na, nb = int(m.group(1)), int(m.group(2))
    atoms, labels = [], {}
    for ln in lines[4:4+na]:
        p = ln.split()
        if len(p) < 4:
            raise ValueError("Bad atom block")
        ensure_element(p[3].capitalize())
        atoms.append((p[3].capitalize(), float(p[0]), float(p[1]), float(p[2])))
    bonds = []
    for ln in lines[4+na:4+na+nb]:
        p = ln.split()
        if len(p) < 3:
            continue
        a, b, o = int(p[0])-1, int(p[1])-1, int(p[2])
        bonds.append((a, b, {1: "1", 2: "2", 3: "3", 4: "a"}.get(o, "1")))
    for ln in lines[4+na+nb:]:
        if ln.startswith("M  CHG"):
            t = ln.split()[3:]
            for k in range(0, len(t) - 1, 2):
                idx, ch = int(t[k]) - 1, int(t[k+1])
                if 0 <= idx < len(atoms) and ch:
                    labels[idx] = atoms[idx][0] + charge_suffix(ch)
    atoms = [a + ((labels[i],) if i in labels else ())
             for i, a in enumerate(atoms)]
    counts = {}
    for a in atoms:
        counts[a[0]] = counts.get(a[0], 0) + 1
    return {"name": lines[0].strip() or "Imported", "formula":
            hill_formula(counts), "geometry": "MOL/SDF import",
            "polarity": "—", "info": "Loaded from a MOL/SDF structure file.",
            "atoms": atoms, "bonds": bonds}

def pubchem_fetch(name):
    import urllib.request, urllib.parse
    q = urllib.parse.quote(name.strip())
    for rt in ("3d", "2d"):
        url = ("https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/name/"
               f"{q}/SDF?record_type={rt}")
        req = urllib.request.Request(url, headers={"User-Agent": "MoleculeStudio/1.0"})
        try:
            with urllib.request.urlopen(req, timeout=15) as r:
                data = r.read().decode("utf-8", "replace")
            if "$$$$" in data and "Status:" not in data[:300]:
                return data.split("$$$$")[0] + "$$$$", rt
        except Exception:
            continue
    raise ValueError(f"Could not fetch '{name}' — check spelling/connection")

# ---------------------------------------------------------------------------
# Chirality (simplified CIP fingerprint)
# ---------------------------------------------------------------------------
def find_stereocenters(atoms, bonds):
    if not atoms:
        return set()
    adj = [[] for _ in atoms]
    for i, j, _s in bonds:
        adj[i].append(j); adj[j].append(i)

    def sig(prev, cur, d):
        kids = [sig(cur, x, d+1) for x in adj[cur] if x != prev and d < 3]
        return atoms[cur][0] + ("(" + ",".join(sorted(kids)) + ")" if kids else "")

    out = set()
    for i, a in enumerate(atoms):
        if a[0] == "C" and len(adj[i]) == 4:
            sigs = sorted(sig(i, x, 0) for x in adj[i])
            if len(set(sigs)) == 4:
                out.add(i)
    return out

# ---------------------------------------------------------------------------
# Sound design (synthesised WAV + QSoundEffect + ffmpeg mux)
# ---------------------------------------------------------------------------
def _synth_wav(path, sr, fn, dur):
    frames = bytearray()
    for i in range(int(sr*dur)):
        v = max(-1.0, min(1.0, fn(i/sr)))
        frames += struct.pack("<h", int(v*32000))
    with wave.open(str(path), "wb") as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(sr)
        w.writeframes(bytes(frames))

def _sfx_dir():
    d = Path(tempfile.gettempdir()) / "molecule_studio_sfx"
    d.mkdir(exist_ok=True)
    click = Path(d)/"click.wav"; pop = Path(d)/"pop.wav"; wh = Path(d)/"whoosh.wav"
    if not click.exists():
        _synth_wav(click, 22050, lambda t: (0.6*math.sin(2*math.pi*1900*t) +
                   0.25*math.sin(2*math.pi*3400*t))*math.exp(-t*70), 0.09)
        _synth_wav(pop, 22050, lambda t: (0.7*math.sin(2*math.pi*260*t) *
                   math.exp(-t*30) + 0.2*math.sin(2*math.pi*520*t) *
                   math.exp(-t*40)), 0.16)
        rnd = random.Random(7); lp = [0.0]
        def whf(t):
            p = min(1.0, t/0.5)
            lp[0] = lp[0]*0.92 + rnd.uniform(-1, 1)*0.08
            return lp[0]*3.2*math.sin(math.pi*p)**2
        _synth_wav(wh, 22050, whf, 0.55)
    return click, pop, wh

class Sfx:
    def __init__(self):
        self.ok = False
        self.enabled = True
        self.effects = {}
        try:
            from PySide6.QtMultimedia import QSoundEffect
            from PySide6.QtCore import QUrl
            click, pop, wh = _sfx_dir()
            for nm, p in (("click", click), ("pop", pop), ("whoosh", wh)):
                e = QSoundEffect()
                e.setSource(QUrl.fromLocalFile(str(p)))
                e.setVolume(0.5)
                self.effects[nm] = e
            self.ok = True
        except Exception:
            pass

    def play(self, nm, vol=0.5):
        if self.ok and self.enabled and nm in self.effects:
            self.effects[nm].setVolume(vol)
            self.effects[nm].play()

def render_sfx_track(events, total, path):
    sr = 22050
    n = int(sr*total)
    buf = [0.0]*n

    def add(fn, dur, t0, gain):
        i0 = int(t0*sr)
        for k in range(int(dur*sr)):
            j = i0+k
            if 0 <= j < n:
                buf[j] += fn(k/sr)*gain
    add(lambda t: math.sin(2*math.pi*150*t)*math.exp(-t*3)*0.6, 0.55, 0.0, 0.6)
    for te, _p, _ci, size in events:
        if te >= total:
            continue
        if size < 0.5:
            add(lambda t: (0.7*math.sin(2*math.pi*260*t)*math.exp(-t*30) +
                0.2*math.sin(2*math.pi*520*t)*math.exp(-t*40)), 0.16, te, 0.35)
        else:
            add(lambda t: (0.6*math.sin(2*math.pi*1900*t) +
                0.25*math.sin(2*math.pi*3400*t))*math.exp(-t*70),
                0.09, te, 0.8 if size >= 1.2 else 0.55)
    frames = bytearray()
    for v in buf:
        frames += struct.pack("<h", int(max(-1.0, min(1.0, v))*32000))
    with wave.open(str(path), "wb") as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(sr)
        w.writeframes(bytes(frames))

def synth_music(path, total, sr=22050):
    """Soft 4-chord pad + sparkle arpeggio, looped & faded — for MP4 mux."""
    chords = [(220.00, 261.63, 329.63), (174.61, 220.00, 261.63),
              (196.00, 246.94, 293.66), (164.81, 207.65, 246.94)]
    bar = 2.0
    n = int(sr*total)
    buf = [0.0]*n
    for i in range(n):
        t = i/sr
        k = int(t/bar) % 4
        ph = t % bar
        env = min(1.0, ph*6.0) * (0.55 + 0.45*math.cos(math.pi*ph/bar))
        v = sum(math.sin(2*math.pi*f*t + math.sin(t*0.7)) * 0.14
                for f in chords[k]) * env
        f2 = chords[k][int(ph*2.0) % 3] * 2.0
        v += math.sin(2*math.pi*f2*t) * 0.05 * \
            max(0.0, math.sin(math.pi * (ph*2.0 % 1.0)))
        fade = min(1.0, t/0.8, max(0.0, (total-t)/0.8))
        buf[i] = v * fade
    frames = bytearray()
    for v in buf:
        frames += struct.pack("<h", int(max(-1.0, min(1.0, v))*32000))
    with wave.open(str(path), "wb") as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(sr)
        w.writeframes(bytes(frames))

def mix_wavs(paths, out, sr=22050):
    data = []
    for p in paths:
        try:
            with wave.open(str(p), "rb") as w:
                raw = w.readframes(w.getnframes())
            data.append(np.frombuffer(raw, np.int16).astype(np.float32)/32768.0)
        except Exception:
            pass
    if not data:
        return False
    n = max(len(d) for d in data)
    mixv = np.zeros(n, dtype=np.float32)
    for d in data:
        mixv[:len(d)] += d
    mixv = np.clip(mixv, -1.0, 1.0)
    frames = (mixv*32000).astype("<i2").tobytes()
    with wave.open(str(out), "wb") as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(sr)
        w.writeframes(frames)
    return True

def mux_audio(video, audio, out):
    try:
        import imageio_ffmpeg
        ff = imageio_ffmpeg.get_ffmpeg_exe()
    except Exception:
        return False
    tmp = Path(out).with_suffix(".mux.mp4")
    try:
        r = subprocess.run([ff, "-y", "-loglevel", "error", "-i", str(video),
                            "-i", str(audio), "-map", "0:v", "-map", "1:a",
                            "-c:v", "copy", "-c:a", "aac", "-b:a", "160k",
                            "-shortest", str(tmp)], capture_output=True)
        if r.returncode == 0:
            Path(out).unlink(missing_ok=True)
            tmp.replace(out)
            return True
    except Exception:
        pass
    tmp.unlink(missing_ok=True)
    return False

# ---------------------------------------------------------------------------
# Structure generation from a typed formula (valence heuristic)
# ---------------------------------------------------------------------------
GEN_VALENCE = {"H": 1, "C": 4, "N": 3, "O": 2, "F": 1, "Na": 1,
               "P": 5, "S": 6, "Cl": 1}
ATTACH_DIST = 56.0

def _largest_gap(used):
    if not used:
        return -math.pi/2.0
    us = sorted(used)
    best_gap, best = -1.0, us[0] + math.pi
    for k in range(len(us)):
        a1 = us[k]
        a2 = us[k+1] if k+1 < len(us) else us[0] + 2.0*math.pi
        gap = a2 - a1
        if gap > best_gap + 1e-9:
            best_gap, best = gap, (a1 + a2)/2.0
    return best

def _star_geometry(el, n_h):
    atoms = [(el, 0.0, 0.0, 0.0)]; bonds = []
    if n_h <= 0:
        return atoms, bonds
    d = (ELEMENTS[el][1] + ELEMENTS["H"][1])*0.55 + 34.0
    angs = {1: [-90.0], 2: [-128.0, -52.0], 3: [-90.0, 30.0, 150.0],
            4: [-45.0, 45.0, 135.0, 225.0]}.get(
        n_h, [-90.0 + 360.0*k/n_h for k in range(n_h)])
    for k, adeg in enumerate(angs):
        a = math.radians(adeg)
        atoms.append(("H", d*math.cos(a), d*math.sin(a), 0.0))
        bonds.append((0, k+1, "1"))
    return atoms, bonds

def _graph_distances(n, adj):
    dist = [[math.inf]*n for _ in range(n)]
    for src in range(n):
        dist[src][src] = 0
        frontier = [src]; d = 0
        while frontier:
            d += 1; nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[src][v] is math.inf or dist[src][v] > d:
                        dist[src][v] = d; nxt.append(v)
            frontier = nxt
    return dist

def generate_structure(counts, charge):
    notes = []
    heavy = []
    for el, n in counts.items():
        if el != "H":
            heavy += [el]*n
    n_h = counts.get("H", 0)
    if not heavy:
        if n_h <= 1:
            return [("H", 0.0, 0.0, 0.0)], [], notes
        atoms = [("H", (i-(n_h-1)/2.0)*44.0, 0.0, 0.0) for i in range(n_h)]
        return atoms, [(i, i+1, "1") for i in range(n_h-1)], notes
    if len(heavy) == 1:
        return (*_star_geometry(heavy[0], n_h), notes)

    n_c = counts.get("C", 0)
    others = [e for e in heavy if e != "C"]
    atoms, caps, bonds = [], [], []
    adj, parent = {}, {}

    def add_atom(el, x, y):
        atoms.append((el, x, y, 0.0))
        caps.append(GEN_VALENCE.get(el, 4))
        adj[len(atoms)-1] = []; parent[len(atoms)-1] = None
        return len(atoms)-1

    def bond(i, j, order=1):
        st = "1" if order == 1 else ("2" if order == 2 else "3")
        bonds.append((i, j, st)); caps[i] -= order; caps[j] -= order
        adj[i].append(j); adj[j].append(i)

    def place_near(i, dist=ATTACH_DIST):
        used = [math.atan2(atoms[nb][2]-atoms[i][2], atoms[nb][1]-atoms[i][1])
                for nb in adj[i]]
        a = _largest_gap(used)
        return atoms[i][1] + dist*math.cos(a), atoms[i][2] + dist*math.sin(a)

    def attach_h(remaining, rr):
        progressed = True
        order_cache = sorted(range(len(atoms)), key=lambda k: (len(adj[k]), k))
        while remaining > 0 and (progressed or not rr):
            progressed = False
            for i in order_cache:
                if remaining <= 0:
                    break
                if caps[i] > 0:
                    while remaining > 0 and caps[i] > 0:
                        x, y = place_near(i)
                        ni = add_atom("H", x, y); parent[ni] = i
                        bond(i, ni); remaining -= 1; progressed = True
                        if rr:
                            break
            if not rr:
                break
        while remaining > 0:
            i = min(range(len(atoms)), key=lambda k: (len(adj[k]), k))
            x, y = place_near(i)
            ni = add_atom("H", x, y); parent[ni] = i; bond(i, ni)
            remaining -= 1

    def upgrade_valence():
        guard = 0
        while sum(max(c, 0) for c in caps) >= 2 and guard < 80:
            guard += 1; done = False
            for target in ("1", "2"):
                for bi, (i, j, st) in enumerate(bonds):
                    if st == target and caps[i] >= 1 and caps[j] >= 1:
                        bonds[bi] = (i, j, "2" if target == "1" else "3")
                        caps[i] -= 1; caps[j] -= 1; done = True; break
                if done:
                    break
            if done:
                continue
            best = None
            gd = _graph_distances(len(atoms), adj)
            for i in range(len(atoms)):
                for j in range(i+1, len(atoms)):
                    if (j in adj[i] or caps[i] < 1 or caps[j] < 1
                            or atoms[i][0] != "C" or atoms[j][0] != "C"):
                        continue
                    key = (-gd[i][j], (atoms[i][1]-atoms[j][1])**2 +
                           (atoms[i][2]-atoms[j][2])**2)
                    if best is None or key < best[0]:
                        best = (key, i, j)
            if best is None:
                break
            _k, i, j = best
            bond(i, j)
            back = [k for k in range(len(atoms)) if parent[k] is None
                    and atoms[k][0] == "C"]
            if len(back) >= 3 and parent[i] is None and parent[j] is None:
                cx = sum(atoms[k][1] for k in back)/len(back)
                cy = sum(atoms[k][2] for k in back)/len(back)
                r = ATTACH_DIST/(2.0*math.sin(math.pi/len(back)))
                for ki, k in enumerate(back):
                    a = -math.pi/2.0 + 2.0*math.pi*ki/len(back)
                    atoms[k] = (atoms[k][0], cx + r*math.cos(a),
                                cy + r*math.sin(a), 0.0)
                depth = {k: 0 for k in back}; changed = True
                while changed:
                    changed = False
                    for k in range(len(atoms)):
                        if parent[k] is not None and k not in depth \
                                and parent[k] in depth:
                            depth[k] = depth[parent[k]] + 1; changed = True
                for k in sorted((k for k in depth if parent[k] is not None),
                                key=lambda k: depth[k]):
                    x, y = place_near(parent[k])
                    atoms[k] = (atoms[k][0], x, y, 0.0)
                notes.append("Closed into a ring")

    dbe = n_c - n_h/2.0 + counts.get("N", 0)/2.0 + 1.0
    all_c = (n_c == len(heavy))
    if all_c and n_c >= 2 and dbe >= 1:
        if n_c == 2:
            add_atom("C", -30.0, 0.0); add_atom("C", 30.0, 0.0)
        else:
            r = ATTACH_DIST/(2.0*math.sin(math.pi/n_c))
            for k in range(n_c):
                a = -math.pi/2.0 + 2.0*math.pi*k/n_c
                add_atom("C", r*math.cos(a), r*math.sin(a))
        for k in range(n_c):
            bond(k, (k+1) % n_c)
        rem = n_h; order_cache = list(range(n_c))
        guard = 0
        while rem > 0 and guard < 500:
            guard += 1
            for i in order_cache:
                if rem <= 0:
                    break
                if caps[i] > 0:
                    x, y = place_near(i)
                    ni = add_atom("H", x, y); parent[ni] = i
                    bond(i, ni); rem -= 1
    elif n_c >= 1:
        for i in range(n_c):
            if n_c == 1:
                add_atom("C", 0.0, 0.0)
            elif n_c == 2:
                add_atom("C", (i-0.5)*60.0, 0.0)
            else:
                add_atom("C", i*52.0, -28.0 if i % 2 == 0 else 28.0)
        for i in range(n_c-1):
            bond(i, i+1)
        for el in others:
            for _ in range(counts[el]):
                target = next((i for i in reversed(range(n_c)) if caps[i] >= 1),
                              None)
                if target is None:
                    target = next((i for i in range(len(atoms))
                                   if caps[i] >= 1), len(atoms)-1)
                x, y = place_near(target)
                ni = add_atom(el, x, y); parent[ni] = target; bond(target, ni)
        attach_h(n_h, rr=False)
    else:
        hub = heavy[0]; add_atom(hub, 0.0, 0.0); prev = 0
        for el in heavy[1:]:
            tgt = 0 if caps[0] >= 1 else prev
            x, y = place_near(tgt)
            ni = add_atom(el, x, y); parent[ni] = tgt; bond(tgt, ni); prev = ni
        attach_h(n_h, rr=False)
    upgrade_valence()
    return atoms, bonds, notes

def find_known_match(counts, charge):
    for idx, m in enumerate(MOLECULES):
        try:
            c2, ch2, err = parse_formula(m["formula"])
        except Exception:
            continue
        if err is None and c2 == counts and ch2 == charge:
            return idx
    return None

def build_molecule_from_formula(counts, charge, title_text):
    known = find_known_match(counts, charge)
    f_hill = hill_formula(counts) + charge_suffix(charge)
    if known is not None:
        mol = dict(MOLECULES[known])
        real = MOLECULES[known]["name"]
        if title_text:
            mol["name"] = title_text
        mol["info"] = (f"Recognized as {real} — exact library geometry. "
                       f"{MOLECULES[known]['info']}")
        return mol, "known"
    atoms, bonds, notes = generate_structure(counts, charge)
    note_txt = f" — {'; '.join(notes)}" if notes else ""
    mol = {"name": title_text or f"{f_hill} (generated)",
           "formula": f_hill, "geometry": "Auto-generated",
           "polarity": f"ion ({charge:+d})" if charge else "—",
           "info": ("Heuristic structure generated from the typed formula"
                    + note_txt + ". Open the Builder to refine it."),
           "atoms": [tuple(a) for a in atoms],
           "bonds": [tuple(b) for b in bonds]}
    return mol, "generated"

def shorts_description(mol):
    d = (mol.get("info") or "").strip()
    if d.startswith("Recognized as") and "geometry. " in d:
        d = d.split("geometry. ", 1)[1]
    if d and not d.startswith("Heuristic") and not d.startswith("Built ") \
            and not d.startswith("Parsed"):
        return d.rstrip(". ") + "."
    counts, _c, _e = parse_formula(mol["formula"])
    if counts:
        bits = [f"{n} {ELEMENTS[e][3].lower()}{'s' if n > 1 else ''}"
                for e, n in sorted(counts.items(), key=lambda kv: -kv[1])]
        lst = bits[0] if len(bits) == 1 else \
            ", ".join(bits[:-1]) + " and " + bits[-1]
        return f"Made of {lst} — {molar_mass(mol):.2f} g/mol."
    return "An animated molecule built in Molecule Studio."

# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------
def clamp01(p): return 0.0 if p < 0.0 else (1.0 if p > 1.0 else p)
def ease_out_cubic(p):
    p = clamp01(p); return 1.0 - (1.0-p)**3
def ease_out_back(p, s=1.70158):
    p = clamp01(p)-1.0
    return p*p*((s+1.0)*p+s)+1.0
def ease_in_out(p):
    p = clamp01(p)
    return 2.0*p*p if p < 0.5 else 1.0-(-2.0*p+2.0)**2/2.0
def _mix(c, o, t):
    return QColor(int(c.red()+(o.red()-c.red())*t),
                  int(c.green()+(o.green()-c.green())*t),
                  int(c.blue()+(o.blue()-c.blue())*t))
def lighten(c, t): return _mix(QColor(c), QColor(255, 255, 255), t)
def darken(c, t): return _mix(QColor(c), QColor(0, 0, 0), t)
def luminance(c):
    return (0.299*c.red()+0.587*c.green()+0.114*c.blue())/255.0
def formula_html(f): return re.sub(r"(\d+)", r"<sub>\1</sub>", f)

# ---------------------------------------------------------------------------
# SMILES-loaded library: drugs & biomolecules
# ---------------------------------------------------------------------------
SMILES_LIB = [
    ("Glycine", "NCC(=O)O", "Amino acid",
     "The simplest amino acid — a building block of proteins."),
    ("Alanine", "CC(N)C(=O)O", "Amino acid",
     "A chiral amino acid; watch the chirality badge appear."),
    ("Acetone", "CC(=O)C", "Ketone",
     "Nail-polish remover — the simplest ketone."),
    ("Ethyl acetate", "CCOC(=O)C", "Ester",
     "Fruity ester responsible for confectionery smells."),
    ("Acetonitrile", "CC#N", "Nitrile",
     "Polar aprotic solvent with a C≡N triple bond."),
    ("Urea", "NC(=O)N", "Amide",
     "Wöhler synthesised it in 1828 — organic chemistry's birth certificate."),
    ("Dimethyl ether", "COC", "Ether",
     "Isomer of ethanol — same atoms, very different boiling point."),
    ("Ethane", "CC", "Alkane",
     "The simplest C–C single bond."),
    ("Chloromethane", "CCl", "Haloalkane",
     "The SN2 reaction scene uses exactly this molecule."),
    ("Hydronium", "[OH3+]", "Ion",
     "Water plus a proton — acidity in action."),
    ("Polyethylene fragment", "CCCCCCCC", "Polymer slice",
     "An 8-carbon slice of the world's #1 plastic."),
    ("Aspirin", "CC(=O)Oc1ccccc1C(=O)O", "Drug · NSAID",
     "Acetylsalicylic acid — the classic painkiller, an aromatic ester-acid."),
    ("Paracetamol", "CC(=O)Nc1ccc(O)cc1", "Drug · analgesic",
     "Acetaminophen — aromatic amide with a phenolic OH."),
    ("Caffeine", "Cn1cnc2c1c(=O)n(C)c(=O)n2C", "Alkaloid",
     "The world's favourite stimulant — a fused purine ring system."),
    ("Glucose", "OC[C@H]1O[C@@H](O)[C@H](O)[C@@H](O)[C@@H]1O", "Sugar",
     "α-D-glucopyranose — five chiral centers, cellular fuel."),
    ("ATP", "Nc1ncnc2c1ncn2C1OC(COP(=O)(O)OP(=O)(O)OP(=O)(O)O)C(O)C1O",
     "Nucleotide", "Adenosine triphosphate — the energy currency of life."),
    ("Nicotine", "CN1CCC[C@H]1c1cccnc1", "Alkaloid",
     "Two rings — a pyrrolidine fused to a pyridine through a chiral carbon."),
    ("Adrenaline", "CNC[C@H](O)c1ccc(O)c(O)c1", "Hormone",
     "Epinephrine — the fight-or-flight molecule with a catechol core."),
    ("Vanillin", "COc1cc(C=O)ccc1O", "Aroma",
     "Vanilla's signature aroma molecule — aldehyde, ether and phenol in one."),
    ("Naphthalene", "c1ccc2ccccc2c1", "Arene",
     "Two fused benzene rings — mothballs."),
]

def load_smiles_library():
    out = []
    for name, smi, geo, info in SMILES_LIB:
        try:
            out.append(mol_from_smiles(smi, name, info=info, geometry=geo))
        except Exception as e:
            print(f"[smiles] skipped {name}: {e}")
    return out

MOLECULES += load_smiles_library()

def _load_custom_molecules():
    if not CUSTOM_FILE.exists():
        return []
    try:
        data = json.loads(CUSTOM_FILE.read_text(encoding="utf-8"))
        out = []
        for m in data:
            if isinstance(m, dict) and m.get("atoms") is not None:
                for a in m["atoms"]:
                    ensure_element(a[0])
                m.setdefault("geometry", "Custom")
                m.setdefault("polarity", "—")
                m.setdefault("info", "Saved from the Builder.")
                m.setdefault("bonds", [])
                out.append(m)
        return out
    except Exception as e:
        print(f"[custom] could not load: {e}")
        return []

CUSTOM_MOLS = _load_custom_molecules()
MOLECULES += CUSTOM_MOLS

GROUPS = [("Simple & inorganic", 13), ("Organic", 10), ("Ions & ionic", 3),
          ("💊 Drugs & biomolecules", len(SMILES_LIB))]
if CUSTOM_MOLS:
    GROUPS.append(("⭐ Custom", len(CUSTOM_MOLS)))
if sum(n for _, n in GROUPS) != len(MOLECULES):
    print(f"[library] WARNING: GROUPS sums to {sum(n for _, n in GROUPS)} "
          f"but MOLECULES has {len(MOLECULES)} entries")

# ---------------------------------------------------------------------------
# Presets: hero shots, hooks, reactions
# ---------------------------------------------------------------------------
HERO_SHOTS = [
    ("— none —", None, None, None),
    ("Front hero", 0.0, 12.0, 1.0),
    ("Glamour 45°", 38.0, 24.0, 1.10),
    ("Top-down", 0.0, 78.0, 1.05),
    ("Dutch tilt", 22.0, -14.0, 0.95),
    ("Dramatic low", 12.0, -26.0, 1.18),
]
HOOKS = [
    "(no hook)",
    "Wait for the flip… ✨",
    "POV: you're an atom ⚛️",
    "Chemistry, but cinematic 🎬",
    "This bond is about to break 💥",
    "The molecule everyone gets wrong 🧪",
]
REACTIONS = {
    "SN2 substitution": ["1️⃣ The nucleophile lines up behind the carbon",
                         "2️⃣ Backside attack — Walden inversion!",
                         "3️⃣ OH⁻ in, Cl⁻ out"],
    "Electrophilic addition": ["1️⃣ The π cloud reaches for H of H–Br",
                               "2️⃣ The H–Br bond breaks toward Br",
                               "3️⃣ Bromoethane formed"],
    "Acid–base proton transfer": ["1️⃣ NH₃'s lone pair grabs a proton",
                                  "2️⃣ The O–H electrons stay on oxygen",
                                  "3️⃣ NH₄⁺ + OH⁻"],
    "Hydrogen-bond water cluster": ["💧 Five waters linked by hydrogen bonds",
                                    "Surface tension, DNA, proteins — all this",
                                    "…one weak bond at a time"],
}

# ---------------------------------------------------------------------------
# Curly arrow (reaction / resonance)
# ---------------------------------------------------------------------------
class CurlyArrow(QGraphicsItem):
    def __init__(self, p0=QPointF(0, 0), p1=QPointF(100, 0), bend=48.0):
        super().__init__()
        self.prog = 0.0
        self.set_geom(p0, p1, bend)

    def set_geom(self, p0, p1, bend=48.0):
        self.prepareGeometryChange()
        self.p0, self.p1, self.bend = QPointF(p0), QPointF(p1), float(bend)
        dx, dy = self.p1.x()-self.p0.x(), self.p1.y()-self.p0.y()
        ln = math.hypot(dx, dy) or 1.0
        self._per = QPointF(-dy/ln, dx/ln)
        self._mid = QPointF((self.p0.x()+self.p1.x())/2 + self._per.x()*bend,
                            (self.p0.y()+self.p1.y())/2 + self._per.y()*bend)

    def set_prog(self, v):
        self.prog = clamp01(v)
        self.update()

    def boundingRect(self):
        xs = [self.p0.x(), self.p1.x(), self._mid.x()]
        ys = [self.p0.y(), self.p1.y(), self._mid.y()]
        return QRectF(min(xs)-40, min(ys)-40,
                      max(xs)-min(xs)+80, max(ys)-min(ys)+80)

    def _eval(self, v):
        a = (1-v)*(1-v); b = 2*v*(1-v); c = v*v
        return QPointF(a*self.p0.x()+b*self._mid.x()+c*self.p1.x(),
                       a*self.p0.y()+b*self._mid.y()+c*self.p1.y())

    def paint(self, p, option, widget=None):
        if self.prog <= 0.02:
            return
        col = QColor("#ffb347")
        col.setAlpha(int(235*self.prog))
        path = QPainterPath(self.p0)
        path.quadTo(self._mid, self.p1)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.setPen(QPen(col, 2.8, Qt.SolidLine, Qt.RoundCap))
        p.setBrush(Qt.NoBrush)
        p.drawPath(path)
        v = clamp01(self.prog)
        tip = self._eval(v)
        v2 = max(0.0, v-0.02)
        prev = self._eval(v2)
        dx, dy = tip.x()-prev.x(), tip.y()-prev.y()
        ln = math.hypot(dx, dy) or 1.0
        ux, uy = dx/ln, dy/ln
        head = QPolygonF([
            QPointF(tip.x(), tip.y()),
            QPointF(tip.x()-ux*11 + -uy*5, tip.y()-uy*11 + ux*5),
            QPointF(tip.x()-ux*11 - -uy*5, tip.y()-uy*11 - ux*5)])
        p.setBrush(QBrush(col)); p.setPen(Qt.NoPen)
        p.drawPolygon(head)

# ---------------------------------------------------------------------------
# MolItem — animated molecule (ball/CPK/Lewis/vdW · resonance · BUILD-UP)
# ---------------------------------------------------------------------------
class MolItem(QGraphicsItem):
    RES_PERIOD = 1.5
    BUILD_SPAN = 3.2      # seconds from first atom to last (live view)
    BUILD_POP = 0.38      # per-atom pop duration

    def __init__(self, mol, sfx=None):
        super().__init__()
        self.sfx = sfx
        self.yaw = 18.0
        self.pitch = 16.0
        self.mirror = 1.0
        self.spin = True
        self.spin_speed = 28.0
        self.morph_t = 0.0
        self.style = "ball"
        self.show_lp = True
        self.show_dipoles = True
        self.show_geom = False
        self.show_chiral = True
        self.resonance_on = True
        self.selected = set()
        # ---- build-up animation state ----
        self.building = False
        self.build_t = 0.0
        self.build_span = self.BUILD_SPAN
        self._build_order = []
        self._build_rank = {}
        self._build_parent = []
        self._build_bond = []
        self._build_total = 0.0
        self._build_popped = set()
        self._spin_after = True
        self.set_mol(mol)

    # ---- data ---------------------------------------------------------
    def set_mol(self, mol):
        self.mol = mol
        self.atoms = []
        for a in mol.get("atoms", []):
            self.atoms.append([a[0], float(a[1]), float(a[2]), float(a[3]),
                               a[4] if len(a) > 4 else None])
        self.bonds = [list(b) for b in mol.get("bonds", [])]
        self.stereo = find_stereocenters(
            [tuple(a[:4]) for a in self.atoms],
            [tuple(b) for b in self.bonds])
        res = mol.get("resonance", {})
        self._res_forms = res.get("forms")
        self._res_arrows = res.get("arrows", [])
        self._res_bond_ids = self._resonance_bond_ids()
        self._res_form = 0
        self._res_t = 0.0
        self.building = False
        self.build_t = 0.0
        self._build_order = []
        self.prepareGeometryChange()
        self._compute_extent()
        self.update()

    def _resonance_bond_ids(self):
        if not self._res_forms:
            return []
        n = len(self._res_forms[0])
        part = [k for k, b in enumerate(self.bonds) if b[2] == "partial"]
        if len(part) == n:
            return part
        aro = [k for k, b in enumerate(self.bonds) if b[2] == "a"]
        if len(aro) == n:
            return aro
        return list(range(max(0, len(self.bonds)-n), len(self.bonds)))

    def _compute_extent(self):
        m = 0.0
        for a in self.atoms:
            m = max(m, math.hypot(a[1], a[2]), abs(a[3]))
        rmax = max((CPK_R.get(a[0], 40.0) for a in self.atoms), default=40.0)
        self._extent = m*1.15 + rmax + 60.0

    def boundingRect(self):
        e = self._extent
        return QRectF(-e, -e, 2*e, 2*e)

    # ---- build-up animation engine --------------------------------------
    def _graph_center(self):
        n = len(self.atoms)
        if n <= 2:
            return 0
        adj = [[] for _ in range(n)]
        for i, j, _s in self.bonds:
            if i < n and j < n:
                adj[i].append(j); adj[j].append(i)

        def bfs(src):
            dist = [-1]*n; dist[src] = 0
            q = deque([src]); far = src
            while q:
                u = q.popleft()
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = dist[u] + 1
                        if dist[v] > dist[far]:
                            far = v
                        q.append(v)
            return far, dist

        a, _ = bfs(0)
        _b, da = bfs(a)
        _c, db = bfs(_b)
        best, be = 0, 10**9
        for i in range(n):
            e = max(da[i], db[i])
            if e < be:
                be, best = e, i
        return best

    def _plan_build(self):
        """BFS order from the graph centre; heavy atoms before hydrogens."""
        n = len(self.atoms)
        self._build_order = []
        self._build_parent = [-1]*n
        self._build_bond = [-1]*n
        if n == 0:
            return
        adj = [[] for _ in range(n)]
        for bi, (i, j, _s) in enumerate(self.bonds):
            if i < n and j < n:
                adj[i].append((j, bi)); adj[j].append((i, bi))
        start = self._graph_center()
        seen = {start}
        frontier = [start]
        order = [start]
        while frontier:
            nxt = []
            for u in frontier:
                kids = [(v, bi) for v, bi in adj[u] if v not in seen]
                kids.sort(key=lambda vb: 0 if self.atoms[vb[0]][0] != "H" else 1)
                for v, bi in kids:
                    seen.add(v)
                    self._build_parent[v] = u
                    self._build_bond[v] = bi
                    order.append(v)
                    nxt.append(v)
            frontier = nxt
        for i in range(n):                    # disconnected safety net
            if i not in seen:
                order.append(i); seen.add(i)
        self._build_order = order
        self._build_rank = {a: k for k, a in enumerate(order)}

    def start_build(self):
        if not self.atoms:
            return
        self._plan_build()
        n = len(self.atoms)
        self.build_span = self.BUILD_SPAN if n > 1 else 0.0
        self._build_total = self.build_span + self.BUILD_POP + 0.25
        self.building = True
        self.build_t = 0.0
        self._build_popped = set()
        self._spin_after = self.spin
        self.spin = False
        if self.sfx:
            self.sfx.play("whoosh", 0.3)
        self.update()

    def cancel_build(self):
        if self.building:
            self.building = False
            self.build_t = 0.0
            self.spin = self._spin_after
            self.update()

    # ---- animation ----------------------------------------------------
    def tick(self, dt):
        if self.building:
            self.build_t += dt
            n = len(self.atoms)
            step = self.build_span / max(1, n - 1)
            for i, a in enumerate(self.atoms):
                if a[0] == "H" or i in self._build_popped:
                    continue
                if self._build_rank.get(i, 0) * step <= self.build_t:
                    self._build_popped.add(i)
                    if self.sfx:
                        self.sfx.play("click", 0.22)
            if self.build_t >= self._build_total:
                self.building = False
                self.spin = self._spin_after
                if self.sfx:
                    self.sfx.play("whoosh", 0.35)
        elif self.spin:
            self.yaw = (self.yaw + self.spin_speed*dt) % 360.0
        if self._res_forms and self.resonance_on and not self.building:
            self._res_t += dt
            if self._res_t >= self.RES_PERIOD:
                self._res_t -= self.RES_PERIOD
                self._res_form = (self._res_form+1) % len(self._res_forms)
                if self.sfx:
                    self.sfx.play("pop", 0.15)

    # ---- projection ---------------------------------------------------
    def project(self, x, y, z):
        a = math.radians(self.yaw); b = math.radians(self.pitch)
        x *= self.mirror
        x1 = x*math.cos(a) + z*math.sin(a)
        z1 = -x*math.sin(a) + z*math.cos(a)
        y1 = y*math.cos(b) - z1*math.sin(b)
        z2 = y*math.sin(b) + z1*math.cos(b)
        return QPointF(x1, -y1), z2

    def _morph_amt(self):
        if self.style == "cpk":
            return 1.0
        if self.style == "vdw":
            return 0.9
        return self.morph_t

    def _atom_r(self, el):
        r0 = ELEMENTS.get(el, ("", 25.0))[1]*0.42 + 6.0
        rc = CPK_R.get(el, 40.0)
        return r0 + (rc-r0)*self._morph_amt()

    def atom_scene_pos(self, i):
        pt, _z = self.project(self.atoms[i][1], self.atoms[i][2],
                              self.atoms[i][3])
        return self.mapToScene(pt)

    def atom_at(self, sp):
        best, bd = None, 1e9
        for i, a in enumerate(self.atoms):
            pt, _z = self.project(a[1], a[2], a[3])
            d = math.hypot(pt.x()-sp.x(), pt.y()-sp.y())
            lim = self._atom_r(a[0]) + 8.0
            if d < lim and d < bd:
                best, bd = i, d
        return best

    # ---- bond style with resonance morph ------------------------------
    def _bond_style(self, k):
        st = self.bonds[k][2]
        if self._res_forms and self.resonance_on and k in self._res_bond_ids:
            idx = self._res_bond_ids.index(k)
            ch = self._res_forms[self._res_form][idx]
            if ch in ("1", "2"):
                st = ch
        return st

    def _res_alpha(self):
        if not (self._res_forms and self.resonance_on):
            return 0.0
        t = self._res_t / self.RES_PERIOD
        return math.sin(math.pi*clamp01(t*2.4))

    # ---- editing (Builder) --------------------------------------------
    def _refresh_topology(self):
        self.stereo = find_stereocenters(
            [tuple(a[:4]) for a in self.atoms],
            [tuple(b) for b in self.bonds])
        self._compute_extent()
        self.prepareGeometryChange()
        self.update()

    def add_atom_at(self, sp, el):
        ensure_element(el)
        cb = max(0.4, math.cos(math.radians(self.pitch)))
        x = sp.x(); y = -sp.y()/cb
        self.atoms.append([el, x, y, 0.0, None])
        self._refresh_topology()
        return len(self.atoms)-1

    def delete_nearest(self, sp):
        i = self.atom_at(sp)
        if i is None:
            return False
        del self.atoms[i]
        self.bonds = [b for b in self.bonds if i not in (b[0], b[1])]
        for b in self.bonds:
            if b[0] > i: b[0] -= 1
            if b[1] > i: b[1] -= 1
        self.selected.clear()
        self._refresh_topology()
        return True

    def _bond_between(self, i, j):
        for k, b in enumerate(self.bonds):
            if {b[0], b[1]} == {i, j}:
                return k
        return None

    def cycle_bond(self, i, j):
        if i is None or j is None or i == j:
            return
        k = self._bond_between(i, j)
        if k is None:
            self.bonds.append([i, j, "1"])
        else:
            st = self.bonds[k][2]
            self.bonds[k][2] = {"1": "2", "2": "3", "3": "1"}.get(st, "1")
        self._refresh_topology()

    def saturate_h(self):
        omap = {"1": 1, "2": 2, "3": 3, "a": 1.5, "partial": 1.5, "ionic": 0}
        for i in range(len(self.atoms)):
            el = self.atoms[i][0]
            if el == "H":
                continue
            used = sum(omap.get(b[2], 1) for b in self.bonds
                       if i in (b[0], b[1]))
            need = int(GEN_VALENCE.get(el, 4) - used)
            if need <= 0:
                continue
            nb = [j for j in range(len(self.atoms))
                  if any(i in (b[0], b[1]) and j in (b[0], b[1])
                         for b in self.bonds) and j != i]
            base = math.atan2(self.atoms[i][2], self.atoms[i][1]) \
                if not nb else 0.0
            angs = [math.atan2(self.atoms[j][2]-self.atoms[i][2],
                               self.atoms[j][1]-self.atoms[i][1])
                    for j in nb]
            for _ in range(need):
                a = _largest_gap(angs) if angs else base
                d = (ELEMENTS[el][1] + ELEMENTS["H"][1])*0.55 + 34.0
                x = self.atoms[i][1] + d*math.cos(a)
                y = self.atoms[i][2] + d*math.sin(a)
                ni = len(self.atoms)
                self.atoms.append(["H", x, y, 0.0, None])
                self.bonds.append([i, ni, "1"])
                angs.append(a)
        self._refresh_topology()

    def to_mol_dict(self, name=None):
        counts = {}
        for a in self.atoms:
            counts[a[0]] = counts.get(a[0], 0) + 1
        return {"name": name or f"Custom {len(counts)}-atom",
                "formula": hill_formula(counts) if counts else "—",
                "geometry": "Custom builder", "polarity": "—",
                "info": "Built in the Builder tab.",
                "atoms": [tuple(a[:4]) + ((a[4],) if a[4] else ())
                          for a in self.atoms],
                "bonds": [tuple(b) for b in self.bonds]}

    # ---- drawing -------------------------------------------------------
    def paint(self, p, option, widget=None):
        p.setRenderHint(QPainter.Antialiasing, True)
        if not self.atoms:
            return
        pts = []
        for a in self.atoms:
            pt, z = self.project(a[1], a[2], a[3])
            pts.append((pt, z))
        radii = [self._atom_r(a[0]) for a in self.atoms]
        order = sorted(range(len(pts)), key=lambda i: pts[i][1])
        if self.building:
            self._paint_build(p, pts, order, radii)
            return
        if self.style == "lewis":
            self._draw_lewis(p, pts, order)
        else:
            self._draw_bonds(p, pts, radii)
            if self.style == "vdw":
                self._draw_cloud(p, pts, order)
            self._draw_atoms(p, pts, radii, order)
            if self.show_dipoles:
                self._draw_dipoles(p, pts)
        if self.show_geom:
            self._draw_callouts(p, pts)
        if self.show_chiral and self.stereo:
            p.setFont(QFont("Segoe UI", 9, QFont.Bold))
            for i in sorted(self.stereo):
                if i >= len(pts):
                    continue
                c = pts[i][0]; r = radii[i]
                badge = QPointF(c.x()+r+12, c.y()-r-12)
                p.setPen(QPen(QColor("#c678dd"), 1.4))
                p.setBrush(QBrush(QColor("#3b2a52")))
                p.drawEllipse(badge, 8.0, 8.0)
                p.setPen(QPen(QColor("#e6c8ff")))
                p.drawText(QRectF(badge.x()-8, badge.y()-8, 16, 16),
                           Qt.AlignCenter, "✦")
        if self.selected:
            p.setPen(QPen(QColor("#ffd166"), 2.2, Qt.DashLine))
            p.setBrush(Qt.NoBrush)
            for i in self.selected:
                if i < len(pts):
                    p.drawEllipse(pts[i][0], radii[i]+6, radii[i]+6)

    # ---- shared atom / single-bond drawing -----------------------------
    def _draw_atom(self, p, a, pos, r):
        col = QColor(ELEMENTS.get(a[0], ("#9aa3b2",))[0])
        g = QRadialGradient(pos + QPointF(-r*0.35, -r*0.35), max(1.0, r*1.3))
        g.setColorAt(0.0, lighten(col, 0.55))
        g.setColorAt(0.55, col)
        g.setColorAt(1.0, darken(col, 0.45))
        p.setBrush(QBrush(g))
        p.setPen(QPen(darken(col, 0.6), 1.0))
        p.drawEllipse(pos, r, r)
        sym = a[4] or a[0]
        tc = QColor("#15181f") if luminance(col) > 0.6 else QColor("#f2f5fb")
        p.setPen(QPen(tc))
        p.setFont(QFont("Segoe UI", max(9, int(r*0.42)), QFont.Bold))
        p.drawText(QRectF(pos.x()-r, pos.y()-r, 2*r, 2*r), Qt.AlignCenter, sym)

    def _draw_bond_k(self, p, k, pts, radii):
        """Draw one styled bond (reused by normal and build-up drawing)."""
        if k >= len(self.bonds):
            return
        i, j, _st0 = self.bonds[k]
        if i >= len(pts) or j >= len(pts):
            return
        st = self._bond_style(k)
        p1, z1 = pts[i]; p2, z2 = pts[j]
        d = p2-p1
        ln = math.hypot(d.x(), d.y()) or 1.0
        u = QPointF(d.x()/ln, d.y()/ln)
        n = QPointF(-u.y(), u.x())
        r1 = radii[i]*0.85; r2 = radii[j]*0.85
        a = QPointF(p1.x()+u.x()*r1, p1.y()+u.y()*r1)
        b = QPointF(p2.x()-u.x()*r2, p2.y()-u.y()*r2)
        def off(kk):
            return QPointF(n.x()*kk, n.y()*kk)
        col = QColor("#b9c2d8")
        if st == "ionic":
            p.setPen(QPen(QColor("#8fd3a7"), 2.2, Qt.DashLine)); p.drawLine(a, b)
        elif st == "1":
            if abs(z2-z1) > 7.0:
                if z2 > z1:
                    self._wedge(p, a, b, n, col, hashed=False)
                else:
                    self._wedge(p, b, a, n, col, hashed=True)
            else:
                p.setPen(QPen(col, 3.0)); p.drawLine(a, b)
        elif st == "2":
            p.setPen(QPen(col, 2.8))
            for kk in (-3.4, 3.4):
                p.drawLine(a+off(kk), b+off(kk))
        elif st == "3":
            p.setPen(QPen(col, 2.6))
            for kk in (-5.6, 0.0, 5.6):
                p.drawLine(a+off(kk), b+off(kk))
        elif st == "a":
            p.setPen(QPen(col, 2.8)); p.drawLine(a, b)
        else:   # partial
            p.setPen(QPen(col, 2.8)); p.drawLine(a, b)
            p.setPen(QPen(col, 2.2, Qt.DashLine))
            p.drawLine(a+off(6.0), b+off(6.0))

    def _paint_build(self, p, pts, order, radii):
        """Atom-by-atom construction: bonds grow outward, atoms pop in."""
        n = len(self.atoms)
        step = self.build_span / max(1, n - 1)

        def t_at(i):
            return self._build_rank.get(i, 0) * step

        col = QColor("#b9c2d8")
        tree = set(b for b in self._build_bond if b >= 0)
        # 1) growing tree bonds
        for i in range(n):
            bi = self._build_bond[i]
            if bi < 0:
                continue
            pa = clamp01((self.build_t - t_at(i)) / self.BUILD_POP)
            if pa <= 0:
                continue
            if pa >= 1.0:
                self._draw_bond_k(p, bi, pts, radii)
                continue
            j = self._build_parent[i]
            if j < 0:
                self._draw_bond_k(p, bi, pts, radii)
                continue
            p1 = pts[j][0]; p2 = pts[i][0]
            end = p1 + (p2 - p1) * ease_out_cubic(pa)
            p.setPen(QPen(col, 3.0, Qt.SolidLine, Qt.RoundCap))
            p.drawLine(p1, end)
        # 2) ring-closing / extra bonds once both ends exist
        for k in range(len(self.bonds)):
            if k in tree:
                continue
            i, j, _s = self.bonds[k]
            if i >= n or j >= n:
                continue
            pa = clamp01((self.build_t - max(t_at(i), t_at(j))) / self.BUILD_POP)
            if pa <= 0:
                continue
            if pa >= 1.0:
                self._draw_bond_k(p, k, pts, radii)
            else:
                p.setPen(QPen(col, 3.0, Qt.SolidLine, Qt.RoundCap))
                p.drawLine(pts[i][0], pts[j][0])
        # 3) dashed target reticles on the frontier
        pen_g = QPen(QColor(255, 209, 102, 150), 1.6, Qt.DashLine)
        for i in range(n):
            if t_at(i) > self.build_t:
                j = self._build_parent[i]
                if j >= 0 and t_at(j) <= self.build_t:
                    p.setPen(pen_g); p.setBrush(Qt.NoBrush)
                    r = radii[i]*0.72
                    p.drawEllipse(pts[i][0], r, r)
        # 4) atoms pop in (scale bounce)
        for i in order:
            pa = clamp01((self.build_t - t_at(i)) / self.BUILD_POP)
            if pa <= 0:
                continue
            self._draw_atom(p, self.atoms[i], pts[i][0],
                            radii[i]*ease_out_back(pa))

    def _draw_bonds(self, p, pts, radii):
        # resonance curly arrows first (under everything else)
        ra = self._res_alpha()
        if ra > 0.02 and self._res_arrows:
            for (a, b) in self._res_arrows:
                arr = CurlyArrow(QPointF(a[0], -a[1]), QPointF(b[0], -b[1]), 34)
                arr.set_prog(ra)
                arr.paint(p, None, None)
        for k in range(len(self.bonds)):
            self._draw_bond_k(p, k, pts, radii)

    def _aromatic_centroid(self, pts):
        xs = ys = cnt = 0
        for b in self.bonds:
            if b[2] == "a" and b[0] < len(pts) and b[1] < len(pts):
                xs += pts[b[0]][0].x()+pts[b[1]][0].x()
                ys += pts[b[0]][0].y()+pts[b[1]][0].y()
                cnt += 2
        if not cnt:
            return None
        return QPointF(xs/cnt, ys/cnt)

    def _wedge(self, p, narrow, wide, n, col, hashed):
        if not hashed:
            poly = QPolygonF([narrow,
                              QPointF(wide.x()+n.x()*3.8, wide.y()+n.y()*3.8),
                              QPointF(wide.x()-n.x()*3.8, wide.y()-n.y()*3.8)])
            p.setPen(Qt.NoPen); p.setBrush(QBrush(col))
            p.drawPolygon(poly)
        else:
            p.setPen(QPen(col, 2.2))
            for k in range(7):
                t = (k+0.5)/7.0
                w = 1.2+3.0*t
                c = QPointF(narrow.x()+(wide.x()-narrow.x())*t,
                            narrow.y()+(wide.y()-narrow.y())*t)
                p.drawLine(QPointF(c.x()-n.x()*w, c.y()-n.y()*w),
                           QPointF(c.x()+n.x()*w, c.y()+n.y()*w))

    def _draw_atoms(self, p, pts, radii, order):
        for i in order:
            self._draw_atom(p, self.atoms[i], pts[i][0], radii[i])

    def _draw_cloud(self, p, pts, order):
        for i in order:
            a = self.atoms[i]
            pos = pts[i][0]
            col = QColor(ELEMENTS.get(a[0], ("#9aa3b2",))[0])
            r = CPK_R.get(a[0], 40.0)
            for rr, al in ((1.55, 22), (1.28, 40), (1.0, 66)):
                g = QRadialGradient(pos, r*rr)
                g.setColorAt(0.0, QColor(col.red(), col.green(), col.blue(), al))
                g.setColorAt(1.0, QColor(col.red(), col.green(), col.blue(), 0))
                p.setBrush(QBrush(g)); p.setPen(Qt.NoPen)
                p.drawEllipse(pos, r*rr, r*rr)
            g = QRadialGradient(pos + QPointF(-r*0.3, -r*0.3), r*1.15)
            g.setColorAt(0.0, lighten(col, 0.45))
            g.setColorAt(1.0, darken(col, 0.25))
            p.setBrush(QBrush(g))
            p.setPen(QPen(QColor(col.red(), col.green(), col.blue(), 130), 1.0))
            p.drawEllipse(pos, r*0.82, r*0.82)

    def _draw_lewis(self, p, pts, order):
        col = QColor("#aab6cf")
        cen = self._aromatic_centroid(pts)
        for k, (i, j, st) in enumerate(self.bonds):
            if i >= len(pts) or j >= len(pts):
                continue
            stx = self._bond_style(k)
            p1 = pts[i][0]; p2 = pts[j][0]
            d = p2-p1
            ln = math.hypot(d.x(), d.y()) or 1.0
            u = QPointF(d.x()/ln, d.y()/ln)
            n = QPointF(-u.y(), u.x())
            a = QPointF(p1.x()+u.x()*11, p1.y()+u.y()*11)
            b = QPointF(p2.x()-u.x()*11, p2.y()-u.y()*11)
            def off(kk):
                return QPointF(n.x()*kk, n.y()*kk)
            if stx == "ionic":
                p.setPen(QPen(QColor("#8fd3a7"), 1.8, Qt.DashLine))
                p.drawLine(a, b)
            elif stx == "1":
                p.setPen(QPen(col, 2.2)); p.drawLine(a, b)
            elif stx == "2":
                p.setPen(QPen(col, 2.0))
                for kk in (-2.8, 2.8):
                    p.drawLine(a+off(kk), b+off(kk))
            elif stx == "3":
                p.setPen(QPen(col, 1.9))
                for kk in (-4.6, 0.0, 4.6):
                    p.drawLine(a+off(kk), b+off(kk))
            elif stx in ("a", "partial"):
                p.setPen(QPen(col, 2.0)); p.drawLine(a, b)
                if cen is not None:
                    mx = (a.x()+b.x())/2; my = (a.y()+b.y())/2
                    dx, dy = cen.x()-mx, cen.y()-my
                    l2 = math.hypot(dx, dy) or 1.0
                    s = 6.0/l2
                    ia = QPointF(a.x()+dx*s, a.y()+dy*s)
                    ib = QPointF(b.x()+dx*s, b.y()+dy*s)
                    p.setPen(QPen(col, 1.6, Qt.DashLine))
                    p.drawLine(ia, ib)
        # atoms as letter badges
        for i in order:
            a = self.atoms[i]
            pos = pts[i][0]
            col2 = QColor(ELEMENTS.get(a[0], ("#9aa3b2",))[0])
            p.setBrush(QBrush(lighten(col2, 0.2)))
            p.setPen(QPen(darken(col2, 0.55), 1.4))
            p.drawEllipse(pos, 11.0, 11.0)
            sym = a[4] or a[0]
            tc = QColor("#15181f") if luminance(col2) > 0.6 else QColor("#f2f5fb")
            p.setPen(QPen(tc))
            p.setFont(QFont("Segoe UI", 8, QFont.Bold))
            p.drawText(QRectF(pos.x()-11, pos.y()-11, 22, 22),
                       Qt.AlignCenter, sym)
        # lone pairs
        if self.show_lp:
            omap = {"1": 1, "2": 2, "3": 3, "a": 1.5, "partial": 1.5, "ionic": 0}
            p.setBrush(QBrush(QColor("#ffe9a8")))
            p.setPen(Qt.NoPen)
            for i, a in enumerate(self.atoms):
                el = a[0]
                if el == "H" or el not in VE or i >= len(pts):
                    continue
                ssum = sum(omap.get(b[2], 1) for b in self.bonds
                           if i in (b[0], b[1]))
                lp = int(max(0, VE[el] - ssum))
                lp = min(lp, 4)
                if lp <= 0:
                    continue
                pos = pts[i][0]
                angs = []
                for b in self.bonds:
                    if i in (b[0], b[1]):
                        j = b[1] if b[0] == i else b[0]
                        if j < len(pts):
                            q = pts[j][0]
                            angs.append(math.atan2(q.y()-pos.y(),
                                                   q.x()-pos.x()))
                slots = sorted((0.0, math.pi/2, math.pi, -math.pi/2),
                               key=lambda sa: min(
                                   abs((sa-g + math.pi) % (2*math.pi) - math.pi)
                                   for g in angs) if angs else 0,
                               reverse=True)
                for sa in slots[:lp]:
                    for s in (-5.5, 5.5):
                        a2 = sa + math.radians(s)
                        dpos = QPointF(pos.x()+19*math.cos(a2),
                                       pos.y()+19*math.sin(a2))
                        p.drawEllipse(dpos, 2.1, 2.1)

    def _draw_dipoles(self, p, pts):
        col = QColor("#ff6b6b")
        for pair in self.mol.get("dipoles", []):
            i, j = pair
            if i >= len(pts) or j >= len(pts):
                continue
            p1 = pts[i][0]; p2 = pts[j][0]
            d = p2-p1
            ln = math.hypot(d.x(), d.y())
            if ln < 30:
                continue
            u = QPointF(d.x()/ln, d.y()/ln)
            n = QPointF(-u.y(), u.x())
            side = 1.0 if n.y() < 0 else -1.0
            offv = QPointF(n.x()*22*side, n.y()*22*side)
            a = QPointF(p1.x()+u.x()*34+offv.x(), p1.y()+u.y()*34+offv.y())
            b = QPointF(p2.x()-u.x()*34+offv.x(), p2.y()-u.y()*34+offv.y())
            p.setPen(QPen(col, 2.4, Qt.SolidLine, Qt.RoundCap))
            p.drawLine(a, b)
            p.setBrush(QBrush(col)); p.setPen(Qt.NoPen)
            head = QPolygonF([b,
                              QPointF(b.x()-u.x()*10+n.x()*5, b.y()-u.y()*10+n.y()*5),
                              QPointF(b.x()-u.x()*10-n.x()*5, b.y()-u.y()*10-n.y()*5)])
            p.drawPolygon(head)
            p.setPen(QPen(col, 2.0))
            for s in (-4.0, 4.0):
                t = QPointF(a.x()-u.x()*s, a.y()-u.y()*s)
                p.drawLine(QPointF(t.x()-n.x()*5, t.y()-n.y()*5),
                           QPointF(t.x()+n.x()*5, t.y()+n.y()*5))

    def _chip(self, p, pos, txt):
        p.setFont(QFont("Segoe UI", 8))
        fm = QFontMetricsF(p.font())
        w = fm.horizontalAdvance(txt)+10
        h = fm.height()+6
        rect = QRectF(pos.x()-w/2, pos.y()-h/2, w, h)
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(13, 16, 23, 210))
        p.drawRoundedRect(rect, 4, 4)
        p.setPen(QPen(QColor("#c7d2e8")))
        p.drawText(rect, Qt.AlignCenter, txt)

    def _draw_callouts(self, p, pts):
        if len(self.atoms) > 30:
            return
        shown = 0
        for i, a in enumerate(self.atoms):
            if shown >= 6:
                break
            nbs = []
            for b in self.bonds:
                if i in (b[0], b[1]):
                    j = b[1] if b[0] == i else b[0]
                    if j < len(self.atoms) and self.atoms[j][0] != "H":
                        nbs.append(j)
            if len(nbs) not in (2, 3) or i >= len(pts):
                continue
            v = []
            for j in nbs[:2]:
                q = pts[j][0]
                v.append(math.atan2(q.y()-pts[i][0].y(), q.x()-pts[i][0].x()))
            dang = abs((v[0]-v[1]+math.pi) % (2*math.pi) - math.pi)
            deg = math.degrees(dang)
            r = self._atom_r(a[0])
            self._chip(p, QPointF(pts[i][0].x(), pts[i][0].y()-r-16),
                       f"{deg:.0f}°")
            shown += 1
        for (i, j, st) in self.bonds:
            if shown >= 12:
                break
            if st == "ionic" or self.atoms[i][0] == "H" or \
                    self.atoms[j][0] == "H" or i >= len(pts) or j >= len(pts):
                continue
            d3 = math.sqrt((self.atoms[i][1]-self.atoms[j][1])**2 +
                           (self.atoms[i][2]-self.atoms[j][2])**2)
            mid = QPointF((pts[i][0].x()+pts[j][0].x())/2,
                          (pts[i][0].y()+pts[j][0].y())/2)
            self._chip(p, QPointF(mid.x()+18, mid.y()-18),
                       f"{d3/56.0:.2f} Å")
            shown += 1

# ---------------------------------------------------------------------------
# Hydrogen-bond overlay (water cluster)
# ---------------------------------------------------------------------------
class HbondOverlay(QGraphicsItem):
    def __init__(self, pairs):
        super().__init__()
        self.pairs = pairs  # (itemA, h_idx, itemB, o_idx)

    def boundingRect(self):
        return QRectF(-600, -600, 1200, 1200)

    def paint(self, p, option, widget=None):
        p.setRenderHint(QPainter.Antialiasing, True)
        pen = QPen(QColor(127, 181, 255, 210), 2.4, Qt.DashLine, Qt.RoundCap)
        p.setPen(pen)
        for (itA, hi, itB, oi) in self.pairs:
            try:
                a = itA.atom_scene_pos(hi)
                b = itB.atom_scene_pos(oi)
            except Exception:
                continue
            p.drawLine(a, b)
            p.setBrush(QBrush(QColor(127, 181, 255, 220)))
            p.setPen(Qt.NoPen)
            p.drawEllipse(a, 3.0, 3.0)
            p.drawEllipse(b, 3.0, 3.0)
            p.setPen(pen)

# ---------------------------------------------------------------------------
# Reaction scenes
# ---------------------------------------------------------------------------
class ReactionScene:
    DUR = 7.0

    def __init__(self, win, kind):
        self.win = win
        self.kind = kind
        self.t = 0.0
        self.m = []
        self.arrows = []
        self.overlay = None
        self._last_cap = -1
        self._build()

    def _mini(self, smi, scale=0.95):
        m = MolItem(mol_from_smiles(smi, smi), self.win.sfx)
        m.spin = False
        m.show_chiral = False
        m.setScale(scale)
        self.win.scene.addItem(m)
        self.m.append(m)
        return m

    def _arrow(self):
        a = CurlyArrow()
        self.win.scene.addItem(a)
        self.arrows.append(a)
        return a

    def _build(self):
        k = self.kind
        if k == "SN2 substitution":
            central = self._mini("CCl", 1.0)
            nu = self._mini("[OH-]", 0.8)
            cl = self._mini("[Cl-]", 0.8)
            prod = self._mini("CO", 0.95)
            self.m = [central, nu, cl, prod]
            self.a1 = self._arrow(); self.a2 = self._arrow()
        elif k == "Electrophilic addition":
            eth = self._mini("C=C", 1.0)
            hbr = self._mini("[BrH]", 0.85)
            prod = self._mini("CCBr", 1.0)
            self.m = [eth, hbr, prod]
            self.a1 = self._arrow(); self.a2 = self._arrow()
        elif k == "Acid–base proton transfer":
            nh3 = self._mini("N", 1.0)
            h2o = self._mini("O", 1.0)
            nh4 = self._mini("[NH4+]", 0.95)
            oh = self._mini("[OH-]", 0.85)
            self.m = [nh3, h2o, nh4, oh]
            self.a1 = self._arrow(); self.a2 = self._arrow()
        elif k == "Hydrogen-bond water cluster":
            ws = [self._mini("O", 0.75) for _ in range(5)]
            self.m = ws
            pairs = []
            for i in range(5):
                pairs.append((ws[i], 1, ws[(i+1) % 5], 0))
            self.overlay = HbondOverlay(pairs)
            self.win.scene.addItem(self.overlay)
        caps = REACTIONS[k]
        t = QGraphicsTextItem(caps[0])
        f = QFont(); f.setBold(True); f.setPointSize(14)
        t.setFont(f); t.setDefaultTextColor(QColor("#e8edf5"))
        self.win.scene.addItem(t)
        self.cap_item = t

    def tick(self, dt):
        self.t = (self.t + dt) % self.DUR
        ph = self.t / self.DUR
        k = self.kind
        if k == "SN2 substitution":
            central, nu, cl, prod = self.m
            pA = ease_out_cubic(clamp01(ph/0.30))
            pB = ease_in_out(clamp01((ph-0.33)/0.30))
            pC = ease_out_cubic(clamp01((ph-0.68)/0.28))
            central.setPos(0, 0)
            central.yaw = 180.0*pB
            central.setOpacity(1.0-pC)
            nu.setPos(-300+150*pA-80*pB, 90-50*pB)
            nu.setOpacity(1.0-pC)
            cl.setPos(150+140*pB, -10)
            cl.setOpacity(0.25+0.75*clamp01(pB))
            prod.setPos(0, -6); prod.setOpacity(pC)
            self.a1.set_geom(nu.mapToScene(QPointF(8, -6)),
                             central.mapToScene(QPointF(-28, 4)))
            self.a1.set_prog(pB)
            self.a2.set_geom(central.mapToScene(QPointF(32, 0)),
                             cl.mapToScene(QPointF(-18, 0)))
            self.a2.set_prog(pB)
            cap = 0 if ph < 0.33 else (1 if ph < 0.68 else 2)
        elif k == "Electrophilic addition":
            eth, hbr, prod = self.m
            pA = ease_out_cubic(clamp01(ph/0.30))
            pB = ease_in_out(clamp01((ph-0.33)/0.30))
            pC = ease_out_cubic(clamp01((ph-0.66)/0.30))
            eth.setPos(-60-30*(1-pA), 40)
            eth.setOpacity(1.0-pC)
            hbr.setPos(120-70*pA, -170+90*pA)
            hbr.setOpacity(1.0-pC)
            prod.setPos(0, 20); prod.setOpacity(pC)
            self.a1.set_geom(eth.mapToScene(QPointF(0, -26)),
                             hbr.mapToScene(QPointF(0, 12)))
            self.a1.set_prog(pB)
            self.a2.set_geom(hbr.mapToScene(QPointF(0, 16)),
                             hbr.mapToScene(QPointF(6, 40)))
            self.a2.set_prog(pB)
            cap = 0 if ph < 0.33 else (1 if ph < 0.66 else 2)
        elif k == "Acid–base proton transfer":
            nh3, h2o, nh4, oh = self.m
            pB = ease_in_out(clamp01((ph-0.25)/0.35))
            pC = ease_out_cubic(clamp01((ph-0.65)/0.3))
            nh3.setPos(-190-30*pC, 20)
            nh3.setOpacity(1.0-pC)
            h2o.setPos(180+40*pC, 10)
            h2o.setOpacity(1.0-pC)
            nh4.setPos(-210, -30); nh4.setOpacity(pC)
            oh.setPos(230, 40); oh.setOpacity(pC)
            self.a1.set_geom(nh3.mapToScene(QPointF(14, -12)),
                             h2o.mapToScene(QPointF(-14, -8)))
            self.a1.set_prog(pB)
            self.a2.set_geom(h2o.mapToScene(QPointF(4, 14)),
                             h2o.mapToScene(QPointF(26, 40)))
            self.a2.set_prog(pB)
            cap = 0 if ph < 0.28 else (1 if ph < 0.65 else 2)
        elif k == "Hydrogen-bond water cluster":
            for wi, w in enumerate(self.m):
                a = -math.pi/2 + 2*math.pi*wi/5
                x = 175*math.cos(a)
                y = 175*math.sin(a) + 8*math.sin(2*math.pi*ph*2 + wi*1.3)
                w.setPos(x, y)
                w.yaw = (w.yaw + 12*dt) % 360
                w.update()
            if self.overlay:
                self.overlay.update()
            cap = 0
        caps = REACTIONS[k]
        if cap != self._last_cap:
            self._last_cap = cap
            self.cap_item.setPlainText(caps[cap])
        br = self.cap_item.boundingRect()
        self.cap_item.setPos(-br.width()/2, 300)

    def close(self):
        sc = self.win.scene
        for it in list(self.m) + list(self.arrows) + [self.cap_item]:
            try:
                sc.removeItem(it)
            except Exception:
                pass
        if self.overlay:
            try:
                sc.removeItem(self.overlay)
            except Exception:
                pass

# ---------------------------------------------------------------------------
# View
# ---------------------------------------------------------------------------
class MolView(QGraphicsView):
    def __init__(self, scene, win):
        super().__init__(scene)
        self.win = win
        self._zoom = 1.0
        self._center = QPointF(0, 0)
        self._panning = False
        self._last = QPointF()
        self.setBackgroundBrush(QBrush(QColor("#0b0f17")))
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setRenderHints(QPainter.Antialiasing |
                            QPainter.SmoothPixmapTransform)
        self.setSceneRect(-4000, -4000, 8000, 8000)

    def apply(self):
        self.setTransform(QTransform().scale(self._zoom, self._zoom))
        self.centerOn(self._center)

    def set_zoom(self, z):
        self._zoom = max(0.15, min(6.0, z))
        self.apply()

    def fit_molecule(self, item):
        e = max(40.0, item._extent)
        vw = self.viewport().width() or 900
        vh = self.viewport().height() or 600
        self._zoom = min(vw, vh)*0.82/(2*e)
        self._center = QPointF(0, 0)
        self.apply()

    def wheelEvent(self, ev):
        f = 1.0015 ** ev.angleDelta().y()
        self.set_zoom(self._zoom*f)

    def mousePressEvent(self, ev):
        pos = ev.position()
        if ev.button() == Qt.LeftButton and self.win.builder_mode != "none":
            self.win._builder_click(self.mapToScene(pos.toPoint()))
            return
        self._panning = True
        self._last = pos
        self.setCursor(Qt.ClosedHandCursor)

    def mouseMoveEvent(self, ev):
        if self._panning:
            d = self.mapToScene(ev.position().toPoint()) - \
                self.mapToScene(self._last.toPoint())
            self._center = self._center - d
            self._last = ev.position()
            self.apply()
        else:
            super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        self._panning = False
        self.setCursor(Qt.ArrowCursor)
        super().mouseReleaseEvent(ev)

    def paintEvent(self, ev):
        super().paintEvent(ev)
        if self.win is not None and getattr(self.win, "guide_shorts", False):
            qp = QPainter(self.viewport())
            w = self.viewport().width()
            h = self.viewport().height()
            cw = int(h*9/16)
            if cw < w:
                side = (w-cw)//2
                qp.fillRect(QRect(0, 0, side, h), QColor(5, 6, 10, 190))
                qp.fillRect(QRect(w-side, 0, side, h), QColor(5, 6, 10, 190))
                qp.setPen(QPen(QColor(255, 209, 102, 120), 1, Qt.DashLine))
                qp.drawLine(side, 0, side, h)
                qp.drawLine(w-side, 0, w-side, h)
            qp.end()

# ---------------------------------------------------------------------------
# Periodic-table shell explorer
# ---------------------------------------------------------------------------
class ShellWidget(QWidget):
    def __init__(self):
        super().__init__()
        self.el = None
        self.setMinimumSize(340, 340)

    def set_element(self, el):
        ensure_element(el)
        self.el = el
        self.update()

    def paintEvent(self, _ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.fillRect(self.rect(), QColor("#0d1119"))
        if not self.el:
            return
        w = self.width(); h = self.height()
        c = QPointF(w/2, h/2 - 8)
        col = QColor(ELEMENTS[self.el][0])
        shells = SHELLS.get(self.el, [2, 8, 18, 8])
        maxr = min(w, h)*0.42
        p.setFont(QFont("Segoe UI", 13, QFont.Bold))
        p.setBrush(QBrush(QColor("#141a26")))
        p.setPen(QPen(col, 2))
        for k in range(len(shells)):
            r = maxr*(k+1)/len(shells)
            p.drawEllipse(c, r, r)
        p.setBrush(QBrush(col))
        p.drawEllipse(c, 24, 24)
        p.setPen(QPen(QColor("#10131a") if luminance(col) > 0.6
                      else QColor("#f2f5fb")))
        p.drawText(QRectF(c.x()-24, c.y()-24, 48, 48), Qt.AlignCenter,
                   self.el)
        p.setPen(Qt.NoPen)
        for k, ne in enumerate(shells):
            r = maxr*(k+1)/len(shells)
            for e in range(ne):
                a = 2*math.pi*e/ne + k*0.5
                d = QPointF(c.x()+r*math.cos(a), c.y()+r*math.sin(a))
                p.setBrush(QBrush(QColor("#dfe6f5")))
                p.drawEllipse(d, 3.4, 3.4)
        info = ELEMENTS[self.el]
        p.setPen(QPen(QColor("#c7d2e8")))
        p.setFont(QFont("Segoe UI", 9))
        txt = (f"{info[3]}  ·  {info[2]:.3f} g/mol  ·  "
               f"EN {info[4]:.2f}  ·  shells {shells}")
        p.drawText(QRectF(0, h-30, w, 24), Qt.AlignCenter, txt)

class PeriodicDialog(QDialog):
    def __init__(self, parent):
        super().__init__(parent)
        self.setWindowTitle("🧭 Periodic table · shell explorer")
        self.setMinimumWidth(560)
        lay = QVBoxLayout(self)
        self.shell = ShellWidget()
        lay.addWidget(self.shell)
        grid = QGridLayout()
        els = sorted(set(ELEMENTS) | set(EXTRA_ELEMENTS),
                     key=lambda e: (ELEMENTS.get(e, (0, 0, 999))[2]))
        for i, el in enumerate(els):
            b = QPushButton(f"{el}\n{ELEMENTS.get(el, (0, 0, 0))[3]}")
            b.setFixedSize(72, 52)
            b.clicked.connect(lambda _=False, e=el: self.shell.set_element(e))
            grid.addWidget(b, i // 7, i % 7)
        lay.addLayout(grid)
        self.shell.set_element("C")

# ---------------------------------------------------------------------------
# Export dialog
# ---------------------------------------------------------------------------
class ExportDialog(QDialog):
    def __init__(self, parent, shorts=False):
        super().__init__(parent)
        self.setWindowTitle("🎞 Render video")
        form = QFormLayout(self)
        self.preset = QComboBox()
        self.preset.addItems(["1920×1080  (16:9)", "1080×1920  (9:16 Shorts)"])
        self.preset.setCurrentIndex(1 if shorts else 0)
        self.dur = QSlider(Qt.Horizontal)
        self.dur.setRange(4, 30); self.dur.setValue(10)
        lab = QLabel("10 s"); lab.setMinimumWidth(40)
        self.dur.valueChanged.connect(lambda v: lab.setText(f"{v} s"))
        drow = QHBoxLayout(); drow.addWidget(self.dur); drow.addWidget(lab)
        dw = QWidget(); dw.setLayout(drow)
        self.fps = QComboBox(); self.fps.addItems(["24", "30", "60"])
        self.fps.setCurrentIndex(1)
        self.hook = QComboBox(); self.hook.addItems(HOOKS)
        self.hook.setCurrentIndex(1 if shorts else 0)
        self.sound = QCheckBox("Synth music + SFX, muxed into MP4")
        self.sound.setChecked(True)
        form.addRow("Frame size", self.preset)
        form.addRow("Duration", dw)
        form.addRow("FPS", self.fps)
        form.addRow("Shorts hook", self.hook)
        form.addRow("", self.sound)
        bb = QHBoxLayout()
        ok = QPushButton("Render ✅"); ca = QPushButton("Cancel")
        ok.clicked.connect(self.accept); ca.clicked.connect(self.reject)
        bb.addStretch(1); bb.addWidget(ca); bb.addWidget(ok)
        form.addRow(bb)

    def values(self):
        if self.preset.currentIndex() == 1:
            w, h = 1080, 1920
        else:
            w, h = 1920, 1080
        return (w, h, int(self.fps.currentText()), self.dur.value(),
                self.hook.currentText(), self.sound.isChecked())

# ---------------------------------------------------------------------------
# Main window
# ---------------------------------------------------------------------------
class MoleculeWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Molecule Studio Pro")
        self.resize(1500, 960)
        self.setAcceptDrops(True)
        self.sfx = Sfx()
        self.builder_mode = "none"
        self.builder_element = "C"
        self._bond_a = None
        self.reaction = None
        self.guide_shorts = False
        self._render_state = None
        self.custom_mols = list(CUSTOM_MOLS)

        self.scene = QGraphicsScene(-4000, -4000, 8000, 8000)
        self.view = MolView(self.scene, self)
        self.mol_item = MolItem(dict(MOLECULES[3]), self.sfx)   # water
        self.scene.addItem(self.mol_item)
        self.setCentralWidget(self.view)

        self._build_docks()
        self._build_tabs()
        self._build_toolbar()
        self.load_molecule(dict(MOLECULES[3]))

        self._elapsed = QElapsedTimer(); self._elapsed.start()
        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick)
        self.timer.start(33)

        QShortcut(QKeySequence("Space"), self, self._toggle_play)
        QShortcut(QKeySequence("B"), self, self.act_build.toggle)

    # ---- docks ---------------------------------------------------------
    def _build_docks(self):
        lib = QDockWidget("📚 Library", self)
        w = QWidget(); v = QVBoxLayout(w)
        self.search = QLineEdit()
        self.search.setPlaceholderText("🔎 Filter molecules…")
        self.search.textChanged.connect(self._filter_library)
        self.mol_list = QListWidget()
        self.mol_list.itemClicked.connect(self._library_pick)
        v.addWidget(self.search); v.addWidget(self.mol_list)
        hb = QHBoxLayout()
        rnd = QPushButton("🎲 Random")
        rnd.clicked.connect(self._random_molecule)
        home = QPushButton("🏠 Reset view")
        home.clicked.connect(lambda: self.view.fit_molecule(self.mol_item))
        hb.addWidget(rnd); hb.addWidget(home)
        v.addLayout(hb)
        w.setLayout(v)
        lib.setWidget(w)
        self.addDockWidget(Qt.DockWidgetArea.LeftDockWidgetArea, lib)

        info = QDockWidget("ℹ Info", self)
        self.info_label = QLabel()
        self.info_label.setWordWrap(True)
        self.info_label.setAlignment(Qt.AlignTop)
        self.info_label.setMinimumHeight(120)
        info.setWidget(self.info_label)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea, info)
        self._refresh_library()

    def _refresh_library(self):
        self.mol_list.clear()
        idx = 0
        for title, count in GROUPS:
            head = QListWidgetItem(f"▸ {title}")
            f = head.font(); f.setBold(True); head.setFont(f)
            head.setFlags(Qt.ItemFlag.NoItemFlags)
            self.mol_list.addItem(head)
            for _ in range(count):
                if not (0 <= idx < len(MOLECULES)):
                    break
                m = MOLECULES[idx]
                it = QListWidgetItem(f"  {m.get('name','?')}  ·  "
                                     f"{m.get('formula','')}")
                it.setData(Qt.ItemDataRole.UserRole, idx)
                self.mol_list.addItem(it)
                idx += 1

    def _filter_library(self, text):
        t = text.strip().lower()
        for i in range(self.mol_list.count()):
            it = self.mol_list.item(i)
            idx = it.data(Qt.ItemDataRole.UserRole)
            if idx is None:
                it.setHidden(False)
            else:
                m = MOLECULES[idx]
                hay = (m.get("name", "") + " " + m.get("formula", "") +
                       " " + m.get("geometry", "")).lower()
                it.setHidden(bool(t) and t not in hay)

    def _library_pick(self, it):
        idx = it.data(Qt.ItemDataRole.UserRole)
        if idx is None:
            return
        self.load_molecule(dict(MOLECULES[idx]))

    def _random_molecule(self):
        i = random.randrange(len(MOLECULES))
        self.load_molecule(dict(MOLECULES[i]), f"Random pick #{i}")
        for r in range(self.mol_list.count()):
            if self.mol_list.item(r).data(Qt.ItemDataRole.UserRole) == i:
                self.mol_list.setCurrentRow(r)
                break

    # ---- tabs ----------------------------------------------------------
    def _build_tabs(self):
        self.tabs = QTabWidget()
        dock = QDockWidget("🧰 Tools", self)
        dock.setWidget(self.tabs)
        dock.setFeatures(QDockWidget.DockWidgetFeature.DockWidgetFloatable |
                         QDockWidget.DockWidgetFeature.DockWidgetMovable)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea, dock)

        # Formula tab
        fw = QWidget(); fv = QVBoxLayout(fw)
        fh = QHBoxLayout()
        self.formula_edit = QLineEdit()
        self.formula_edit.setPlaceholderText("Type a formula — H2O, CH3COOH, "
                                             "NH4+, SO4^2- …")
        self.formula_edit.returnPressed.connect(self._formula_go)
        fbtn = QPushButton("⚡ Show")
        fbtn.clicked.connect(self._formula_go)
        fh.addWidget(self.formula_edit); fh.addWidget(fbtn)
        fv.addLayout(fh)
        self.formula_out = QLabel("Type a formula and press Enter — known "
                                  "molecules load with library geometry, "
                                  "unknown ones get a generated structure.")
        self.formula_out.setWordWrap(True)
        fv.addWidget(self.formula_out)
        fv.addStretch(1)
        fw.setLayout(fv)
        self.tabs.addTab(fw, "⌨ Formula")

        # SMILES & files tab
        sw = QWidget(); sv = QVBoxLayout(sw)
        sh = QHBoxLayout()
        self.smiles_edit = QLineEdit()
        self.smiles_edit.setPlaceholderText("SMILES — CCO, CC(=O)Oc1ccccc1C(=O)O …")
        self.smiles_edit.returnPressed.connect(self._smiles_go)
        sbtn = QPushButton("🧬 Build")
        sbtn.clicked.connect(self._smiles_go)
        sh.addWidget(self.smiles_edit); sh.addWidget(sbtn)
        sv.addLayout(sh)
        h2 = QHBoxLayout()
        openb = QPushButton("📂 Open MOL/SDF…")
        openb.clicked.connect(self._open_molfile)
        pub = QPushButton("🌐 PubChem lookup…")
        pub.clicked.connect(self._pubchem_go)
        h2.addWidget(openb); h2.addWidget(pub)
        sv.addLayout(h2)
        self.smiles_out = QLabel("You can also drag & drop a .mol/.sdf file "
                                 "anywhere onto the window.")
        self.smiles_out.setWordWrap(True)
        sv.addWidget(self.smiles_out)
        sv.addStretch(1)
        sw.setLayout(sv)
        self.tabs.addTab(sw, "🧬 SMILES & files")

        # Builder tab
        bw = QWidget(); bv = QVBoxLayout(bw)
        eg = QGroupBox("Element palette")
        eh = QHBoxLayout(eg)
        self.el_combo = QComboBox()
        for el in sorted(set(ELEMENTS) | set(EXTRA_ELEMENTS)):
            self.el_combo.addItem(f"{el} — {ELEMENTS.get(el, ('','','','?'))[3]}")
        self.el_combo.setCurrentText("C — Carbon")
        self.el_combo.currentTextChanged.connect(self._builder_element)
        eh.addWidget(self.el_combo)
        bv.addWidget(eg)
        bg = QGroupBox("Tools")
        bh = QGridLayout(bg)
        self.b_add = QPushButton("➕ Add atom")
        self.b_bond = QPushButton("🔗 Bond / order")
        self.b_del = QPushButton("🗑 Delete")
        for b in (self.b_add, self.b_bond, self.b_del):
            b.setCheckable(True)
        grp = QButtonGroup(self); grp.setExclusive(True)
        grp.addButton(self.b_add); grp.addButton(self.b_bond)
        grp.addButton(self.b_del)
        self.b_add.clicked.connect(lambda: self._builder_mode("add"))
        self.b_bond.clicked.connect(lambda: self._builder_mode("bond"))
        self.b_del.clicked.connect(lambda: self._builder_mode("delete"))
        sat = QPushButton("🧴 Saturate with H")
        sat.clicked.connect(self._builder_saturate)
        clr = QPushButton("♻ Clear")
        clr.clicked.connect(self._builder_clear)
        save = QPushButton("💾 Save custom")
        save.clicked.connect(self._builder_save)
        bh.addWidget(self.b_add, 0, 0); bh.addWidget(self.b_bond, 0, 1)
        bh.addWidget(self.b_del, 1, 0); bh.addWidget(sat, 1, 1)
        bh.addWidget(clr, 2, 0); bh.addWidget(save, 2, 1)
        bv.addWidget(bg)
        self.builder_tip = QLabel("Pick a tool, then click on the canvas. "
                                  "Bond tool: click two atoms — repeats "
                                  "cycle single→double→triple.")
        self.builder_tip.setWordWrap(True)
        bv.addWidget(self.builder_tip)
        bv.addStretch(1)
        bw.setLayout(bv)
        self.tabs.addTab(bw, "🛠 Builder")

    def _builder_element(self, text):
        self.builder_element = text.split(" ")[0]

    def _builder_mode(self, mode):
        self.builder_mode = mode
        self._bond_a = None
        self.mol_item.cancel_build()
        self.mol_item.selected = set()
        if mode != "none":
            self.mol_item.spin = False
            self.act_play.setChecked(False)
            self.mol_item.yaw = 0.0
        tips = {"add": "Click empty canvas to drop atoms; click near an "
                       "existing atom to nudge-place beside it.",
                "bond": "Click atom A then atom B. Clicking an existing pair "
                        "cycles its order.",
                "delete": "Click an atom to remove it (and its bonds)."}
        self.builder_tip.setText(tips[mode])
        self.mol_item.update()

    def _builder_click(self, sp):
        item = self.mol_item
        if self.builder_mode == "add":
            item.add_atom_at(sp, self.builder_element)
            self.sfx.play("click", 0.4)
        elif self.builder_mode == "bond":
            i = item.atom_at(sp)
            if i is None:
                self.statusBar().showMessage("No atom there — click closer "
                                             "to an atom.", 2500)
                return
            if self._bond_a is None:
                self._bond_a = i
                item.selected = {i}
                self.statusBar().showMessage(f"Bond: atom {i} selected — "
                                             "click atom B.", 2500)
            else:
                item.cycle_bond(self._bond_a, i)
                self._bond_a = None
                item.selected = set()
                self.sfx.play("click", 0.5)
        elif self.builder_mode == "delete":
            if item.delete_nearest(sp):
                self.sfx.play("pop", 0.4)
        self._update_info("Edited in Builder")

    def _builder_saturate(self):
        self.mol_item.saturate_h()
        self.sfx.play("whoosh", 0.4)
        self._update_info("Hydrogens added")

    def _builder_clear(self):
        self.mol_item.set_mol({"name": "Empty", "formula": "—",
                               "geometry": "Custom builder", "polarity": "—",
                               "info": "Click ➕ Add atom to start building.",
                               "atoms": [], "bonds": []})
        self._update_info()

    def _builder_save(self):
        mol = self.mol_item.to_mol_dict()
        if not mol["atoms"]:
            QMessageBox.information(self, "Save custom",
                                    "The canvas is empty — build something "
                                    "first.")
            return
        mol["name"] = QInputDialog.getText(
            self, "Save custom", "Molecule name:",
            text=mol["formula"])[0] or mol["formula"]
        self.custom_mols.append(mol)
        MOLECULES.append(mol)
        try:
            CUSTOM_FILE.write_text(
                json.dumps(self.custom_mols, ensure_ascii=False, indent=1),
                encoding="utf-8")
        except Exception as e:
            print(f"[custom] save failed: {e}")
        if len(GROUPS) and GROUPS[-1][0] == "⭐ Custom":
            GROUPS[-1] = ("⭐ Custom", GROUPS[-1][1] + 1)
        else:
            GROUPS.append(("⭐ Custom", 1))
        self._refresh_library()
        self.load_molecule(dict(mol), "Saved to ⭐ Custom")

    # ---- toolbar --------------------------------------------------------
    def _build_toolbar(self):
        tb = QToolBar("main"); tb.setMovable(False)
        self.addToolBar(tb)
        self.act_play = QAction("⏸ Pause", self)
        self.act_play.setCheckable(True)
        self.act_play.toggled.connect(self._set_play)
        tb.addAction(self.act_play)

        self.style_combo = QComboBox()
        self.style_combo.addItems(["⚪ Ball & stick", "🫧 CPK space-fill",
                                   "••• Lewis dots", "☁ vdW cloud"])
        self.style_combo.currentIndexChanged.connect(self._set_style)
        tb.addWidget(self.style_combo)

        morph = QAction("🫧 Morph", self)
        morph.triggered.connect(self._morph_cpk)
        tb.addAction(morph)

        self.act_build = QAction("🧱 Build-up", self)
        self.act_build.setCheckable(True)
        self.act_build.setChecked(True)
        self.act_build.setToolTip("Step-by-step construction: atoms appear "
                                  "one by one, bonds grow between them. "
                                  "Replays on every molecule load. (B)")
        self.act_build.toggled.connect(self._toggle_build)
        tb.addAction(self.act_build)

        self.act_res = QAction("🔁 Resonance", self)
        self.act_res.setCheckable(True); self.act_res.setChecked(True)
        self.act_res.toggled.connect(self._toggle_res)
        tb.addAction(self.act_res)
        self.act_dip = QAction("🧭 Dipoles", self)
        self.act_dip.setCheckable(True); self.act_dip.setChecked(True)
        self.act_dip.toggled.connect(self._toggle_dip)
        tb.addAction(self.act_dip)
        self.act_geom = QAction("📐 Callouts", self)
        self.act_geom.setCheckable(True)
        self.act_geom.toggled.connect(self._toggle_geom)
        tb.addAction(self.act_geom)
        self.act_chi = QAction("✦ Chirality", self)
        self.act_chi.setCheckable(True); self.act_chi.setChecked(True)
        self.act_chi.toggled.connect(self._toggle_chi)
        tb.addAction(self.act_chi)
        mir = QAction("🪞 Mirror", self)
        mir.triggered.connect(self._mirror_anim)
        tb.addAction(mir)

        rbtn = QToolButton(); rbtn.setText("🎬 Reactions")
        rbtn.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup)
        rm = QMenu(rbtn)
        for kind in REACTIONS:
            rm.addAction(kind, lambda k=kind: self._open_reaction(k))
        rm.addSeparator()
        rm.addAction("↩ Back to molecule", self._close_reaction)
        rbtn.setMenu(rm)
        tb.addWidget(rbtn)

        per = QAction("🧭 Periodic", self)
        per.triggered.connect(self._open_periodic)
        tb.addAction(per)

        self.hero_combo = QComboBox()
        for h in HERO_SHOTS:
            self.hero_combo.addItem(h[0])
        self.hero_combo.currentIndexChanged.connect(self._hero_shot)
        tb.addWidget(self.hero_combo)

        self.act_guide = QAction("📱 9:16 guide", self)
        self.act_guide.setCheckable(True)
        self.act_guide.toggled.connect(self._toggle_guide)
        tb.addAction(self.act_guide)

        self.act_sfx = QAction("🔊 SFX", self)
        self.act_sfx.setCheckable(True); self.act_sfx.setChecked(True)
        self.act_sfx.toggled.connect(self._toggle_sfx)
        tb.addAction(self.act_sfx)

        ebtn = QToolButton(); ebtn.setText("🎞 Export")
        ebtn.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup)
        em = QMenu(ebtn)
        em.addAction("🖼 PNG snapshot", self._export_png)
        em.addAction("🎥 Render MP4 (16:9)…", lambda: self._export_video(False))
        em.addAction("📱 Render Short (9:16)…", lambda: self._export_video(True))
        ebtn.setMenu(em)
        tb.addWidget(ebtn)

    # ---- molecule loading ----------------------------------------------
    def load_molecule(self, mol, note=""):
        self._close_reaction()
        self.mol_item.set_mol(mol)
        self.mol_item.setVisible(True)
        self.view.fit_molecule(self.mol_item)
        self.act_res.setEnabled("resonance" in mol)
        if self.act_build.isChecked():
            self.mol_item.start_build()
        self._update_info(note)

    def _update_info(self, note=""):
        m = self.mol_item.mol
        mass = molar_mass(m)
        chi = len(self.mol_item.stereo)
        desc = shorts_description(m)
        html = (f"<h2 style='margin:2px'>{m.get('name','?')}</h2>"
                f"<p style='margin:2px'><b>Formula:</b> "
                f"{formula_html(m.get('formula',''))} &nbsp; "
                f"<b>M:</b> {mass:.2f} g/mol<br>"
                f"<b>Geometry:</b> {m.get('geometry','—')} &nbsp; "
                f"<b>Polarity:</b> {m.get('polarity','—')}"
                + (f" &nbsp; <b>Chiral centers:</b> {chi}" if chi else "")
                + f"<br><i>{m.get('info','')}</i>"
                + f"<br><span style='color:#7fb5ff'>🎬 {desc}</span>"
                + (f"<br><span style='color:#8fd3a7'>{note}</span>"
                   if note else ""))
        self.info_label.setText(html)

    # ---- tabs actions ----------------------------------------------------
    def _formula_go(self):
        text = self.formula_edit.text()
        counts, charge, err = parse_formula(text)
        if err:
            self.formula_out.setText(
                f"<span style='color:#ff8a8a'>⚠ {err}</span>")
            return
        mol, kind = build_molecule_from_formula(counts, charge,
                                                text.strip().title())
        self.load_molecule(mol)
        rich = formula_rich(mol["formula"])
        mass = molar_mass(mol)
        if kind == "known":
            self.formula_out.setText(
                f"<b style='color:#8fd3a7'>Recognized!</b> {rich} — "
                f"exact library geometry loaded. "
                f"<b>M = {mass:.2f} g/mol</b>, "
                f"{sum(counts.values())} atoms.")
        else:
            self.formula_out.setText(
                f"<b style='color:#ffd166'>Generated</b> {rich} with a "
                f"valence heuristic ({sum(counts.values())} atoms, "
                f"<b>M = {mass:.2f} g/mol</b>). Refine it in 🛠 Builder.")
        self.sfx.play("pop", 0.4)

    def _smiles_go(self):
        smi = self.smiles_edit.text().strip()
        try:
            mol = mol_from_smiles(smi, smi)
        except Exception as e:
            self.smiles_out.setText(
                f"<span style='color:#ff8a8a'>⚠ {e}</span>")
            return
        self.load_molecule(mol, f"Parsed SMILES: {smi}")
        self.smiles_out.setText(
            f"<b style='color:#8fd3a7'>Built</b> {formula_html(mol['formula'])}"
            f" — {len(mol['atoms'])} atoms, {len(mol['bonds'])} bonds.")
        self.sfx.play("pop", 0.4)

    def _open_molfile(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open MOL/SDF", "", "Structure files (*.mol *.sdf *.sd *.txt)")
        if path:
            self._load_molfile(Path(path))

    def _load_molfile(self, path):
        try:
            mol = parse_mol(path.read_text(encoding="utf-8", errors="replace"))
        except Exception as e:
            QMessageBox.warning(self, "Import failed", str(e))
            return
        self.load_molecule(mol, f"Imported {path.name}")
        self.sfx.play("pop", 0.4)

    def _pubchem_go(self):
        name = self.smiles_edit.text().strip()
        if not name:
            name, ok = QInputDialog.getText(
                self, "🌐 PubChem lookup", "Compound name (e.g. caffeine):")
            if not ok or not name.strip():
                return
        prog = QProgressDialog(f"Fetching “{name}” from PubChem…",
                               None, 0, 0, self)
        prog.setWindowModality(Qt.WindowModality.WindowModal)
        prog.show()
        QApplication.processEvents()
        try:
            sdf, rt = pubchem_fetch(name)
            mol = parse_mol(sdf)
            mol["name"] = name.strip().title()
            self.load_molecule(mol, f"Fetched from PubChem ({rt.upper()} record)")
            self.smiles_out.setText(
                f"<b style='color:#8fd3a7'>Fetched</b> "
                f"{formula_html(mol['formula'])} — {len(mol['atoms'])} atoms.")
            self.sfx.play("pop", 0.5)
        except Exception as e:
            QMessageBox.warning(self, "PubChem", str(e))
        finally:
            prog.close()

    def dragEnterEvent(self, ev):
        if ev.mimeData().hasUrls():
            ev.acceptProposedAction()

    def dropEvent(self, ev):
        for url in ev.mimeData().urls():
            p = Path(url.toLocalFile())
            if p.suffix.lower() in (".mol", ".sdf", ".sd", ".txt"):
                self._load_molfile(p)
                break

    # ---- toolbar slots ---------------------------------------------------
    def _tick(self):
        dt = min(0.1, self._elapsed.restart()/1000.0)
        if self.reaction:
            self.reaction.tick(dt)
        else:
            self.mol_item.tick(dt)
            self.mol_item.update()

    def _toggle_play(self):
        self.act_play.setChecked(not self.act_play.isChecked())

    def _set_play(self, on):
        self.mol_item.spin = not on
        self.act_play.setText("▶ Play" if on else "⏸ Pause")

    def _set_style(self, i):
        self.mol_item.style = ("ball", "cpk", "lewis", "vdw")[i]
        self.sfx.play("click", 0.35)
        self.mol_item.update()

    def _morph_cpk(self):
        self.sfx.play("whoosh", 0.5)
        target = 0.0 if self.mol_item.morph_t > 0.5 else 1.0
        anim = QVariantAnimation(self)
        anim.setDuration(900)
        anim.setStartValue(self.mol_item.morph_t)
        anim.setEndValue(target)
        anim.valueChanged.connect(
            lambda v: (setattr(self.mol_item, "morph_t", v),
                       self.mol_item.update()))
        anim.start()

    def _toggle_build(self, on):
        if on:
            self.mol_item.start_build()
            self.statusBar().showMessage(
                f"🧱 Build-up: {len(self.mol_item.atoms)} atoms pop in one "
                "by one — replays on every molecule you load. (B to toggle)")
        else:
            self.mol_item.cancel_build()

    def _toggle_res(self, on):
        self.mol_item.resonance_on = on
        self.mol_item._res_t = 0.0
        self.mol_item.update()

    def _toggle_dip(self, on):
        self.mol_item.show_dipoles = on
        self.mol_item.update()

    def _toggle_geom(self, on):
        self.mol_item.show_geom = on
        self.mol_item.update()

    def _toggle_chi(self, on):
        self.mol_item.show_chiral = on
        self.mol_item.update()

    def _toggle_sfx(self, on):
        self.sfx.enabled = on

    def _toggle_guide(self, on):
        self.guide_shorts = on
        self.view.viewport().update()

    def _mirror_anim(self):
        self.sfx.play("whoosh", 0.45)
        anim = QVariantAnimation(self)
        anim.setDuration(1800)
        anim.setStartValue(0.0)
        anim.setEndValue(2*math.pi)
        anim.valueChanged.connect(
            lambda v: (setattr(self.mol_item, "mirror", math.cos(v)),
                       self.mol_item.update()))
        anim.start()

    def _hero_shot(self, i):
        name, yaw, pitch, zoom = HERO_SHOTS[i]
        if yaw is None:
            return
        item = self.mol_item
        start_yaw = item.yaw
        dyaw = ((yaw - start_yaw + 180) % 360) - 180
        start_pitch = item.pitch
        anim = QVariantAnimation(self)
        anim.setDuration(650)
        anim.setStartValue(0.0); anim.setEndValue(1.0)
        def step(v):
            item.yaw = (start_yaw + dyaw*v) % 360
            item.pitch = start_pitch + (pitch-start_pitch)*v
            item.update()
            self.view.set_zoom(self.view._zoom *
                               (1.0 + (zoom-1.0)*0.02))
        anim.valueChanged.connect(step)
        anim.start()
        self.sfx.play("click", 0.4)

    def _open_reaction(self, kind):
        if self.reaction:
            self._close_reaction()
        self.reaction = ReactionScene(self, kind)
        self.mol_item.setVisible(False)
        vw = self.view.viewport().width() or 900
        vh = self.view.viewport().height() or 640
        self.view._center = QPointF(0, 0)
        self.view.set_zoom(min(vw, vh)*0.62/700.0)
        self.statusBar().showMessage(f"🎬 {kind} — press Reactions → Back to "
                                     "return to your molecule")

    def _close_reaction(self):
        if not self.reaction:
            return
        self.reaction.close()
        self.reaction = None
        self.mol_item.setVisible(True)
        self.statusBar().showMessage("Back to molecule")

    def _open_periodic(self):
        PeriodicDialog(self).exec()

    # ---- export ----------------------------------------------------------
    def _export_png(self):
        path, _ = QFileDialog.getSaveFileName(self, "Save PNG",
                                              "molecule.png", "PNG (*.png)")
        if not path:
            return
        self.view.grab().save(path, "PNG")
        self.sfx.play("pop", 0.5)
        self.statusBar().showMessage(f"🖼 Saved {path}", 4000)

    def _render_frame(self, t, w, h, hook, dur, events, want_sfx):
        item = self.mol_item
        item.yaw = (self._render_state["yaw"] + t*36.0) % 360.0
        # ---- build-up animation across the first seconds of the video ----
        build_active = False
        if self.act_build.isChecked():
            span = min(6.0, dur*0.55)
            n = len(item.atoms)
            item._plan_build()
            item.build_span = span if n > 1 else 0.0
            build_active = t < span + item.BUILD_POP + 0.05
            item.building = build_active
            item.build_t = min(t, span + item.BUILD_POP)
            popped = self._render_state.setdefault("build_popped", set())
            step_v = item.build_span / max(1, n - 1)
            for i, a in enumerate(item.atoms):
                if a[0] != "H" and i not in popped and \
                        item._build_rank.get(i, 0)*step_v <= t:
                    popped.add(i)
                    events.append((t, 0.0, 0, 1.0))
        if item._res_forms:
            per = item.RES_PERIOD
            k = int(t/per)
            if want_sfx and not build_active and \
                    k != self._render_state["res_k"] and t > 0.2:
                events.append((t, 0.0, 0, 1.0))
            self._render_state["res_k"] = k
            item._res_form = k % len(item._res_forms)
            item._res_t = t - k*per
        img = QImage(w, h, QImage.Format.Format_RGB888)
        img.fill(QColor("#0a0d13"))
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing, True)
        zb = (min(w, h)*0.78/(2*max(40.0, item._extent))) * \
            (1.0 + 0.07*ease_in_out(t/dur))
        p.translate(w/2, h/2)
        p.scale(zb, zb)
        item.paint(p, None, None)
        p.end()
        # cinematic overlays
        p2 = QPainter(img)
        p2.setRenderHint(QPainter.Antialiasing, True)
        fade = max(clamp01(t/0.5), clamp01((dur-t)/0.5))
        if fade < 1.0:
            p2.fillRect(img.rect(), QColor(5, 6, 10,
                                           int(200*(1.0-fade))))
        if hook and hook != HOOKS[0] and t < 2.6:
            a = ease_out_back(min(1.0, t/0.5)) * \
                (1.0 - clamp01((t-2.1)/0.5))
            col = QColor(255, 255, 255, int(255*clamp01(a)))
            f = QFont("Segoe UI", int(min(w, h)*0.045), QFont.Bold)
            p2.setFont(f)
            p2.setPen(QPen(col))
            p2.drawText(QRectF(w*0.06, h*0.06, w*0.88, h*0.14),
                        Qt.AlignHCenter | Qt.AlignVCenter, hook)
        p2.setFont(QFont("Segoe UI", max(9, int(h*0.014))))
        p2.setPen(QPen(QColor(200, 210, 235, 120)))
        p2.drawText(QRectF(w-260, h-34, 240, 24), Qt.AlignRight,
                    "Molecule Studio Pro")
        p2.end()
        img = img.convertToFormat(QImage.Format.Format_RGB888)
        bpl = img.bytesPerLine()
        arr = np.frombuffer(img.constBits(), dtype=np.uint8)
        arr = arr.reshape(img.height(), bpl // 3, 3)[:, :w, :].copy()
        return arr

    def _export_video(self, shorts):
        if not (IMAGEIO_OK and NUMPY_OK):
            QMessageBox.warning(self, "Export",
                                "Export needs  pip install imageio "
                                "imageio-ffmpeg numpy")
            return
        if self.reaction:
            QMessageBox.information(self, "Export",
                                    "Close the reaction scene first "
                                    "(Reactions → Back to molecule).")
            return
        dlg = ExportDialog(self, shorts=shorts)
        if not dlg.exec():
            return
        w, h, fps, dur, hook, want_sound = dlg.values()
        default = f"molecule_short_{hook[:10].strip()}.mp4" if shorts \
            else "molecule_video.mp4"
        path, _ = QFileDialog.getSaveFileName(self, "Render video", default,
                                              "MP4 (*.mp4)")
        if not path:
            return
        item = self.mol_item
        self._render_state = {"yaw": item.yaw, "res_k": -1,
                              "spin": item.spin, "style": item.style,
                              "morph": item.morph_t, "build_popped": set()}
        item.spin = False
        events = []
        nframes = int(dur*fps)
        prog = QProgressDialog("Rendering frames…", "Cancel", 0, nframes, self)
        prog.setWindowModality(Qt.WindowModality.WindowModal)
        writer = None
        try:
            writer = imageio.get_writer(path, fps=fps, codec="libx264",
                                        quality=8, pixelformat="yuv420p",
                                        macro_block_size=1)
            for f in range(nframes):
                t = f/fps
                arr = self._render_frame(t, w, h, hook, dur, events, want_sound)
                writer.append_data(arr)
                prog.setValue(f)
                QApplication.processEvents()
                if prog.wasCanceled():
                    break
            writer.close()
            writer = None
        except Exception as e:
            if writer:
                try:
                    writer.close()
                except Exception:
                    pass
            QMessageBox.warning(self, "Export failed", str(e))
            item.spin = self._render_state["spin"]
            item.building = False
            return
        msg = f"🎬 Rendered {nframes} frames → {path}"
        if want_sound:
            tmp = Path(tempfile.gettempdir())
            mus = tmp/"ms_music.wav"; sfxw = tmp/"ms_sfx.wav"
            mix = tmp/"ms_mix.wav"
            synth_music(mus, dur)
            render_sfx_track(events, dur, sfxw)
            if mix_wavs([mus, sfxw], mix):
                if mux_audio(path, mix, path):
                    msg += " · 🎵 audio muxed"
                else:
                    msg += " · (ffmpeg mux unavailable — silent video)"
        item.spin = self._render_state["spin"]
        item.yaw = self._render_state["yaw"]
        item.style = self._render_state["style"]
        item.morph_t = self._render_state["morph"]
        item.building = False
        item.build_t = 0.0
        item.build_span = item.BUILD_SPAN
        item.update()
        self.statusBar().showMessage(msg, 8000)
        QMessageBox.information(self, "Export complete", msg)
        self.sfx.play("pop", 0.6)

# ---------------------------------------------------------------------------
def main():
    app = QApplication(sys.argv)
    app.setApplicationName("Molecule Studio Pro")
    app.setStyle("Fusion")
    app.setStyleSheet("""
        QMainWindow, QDialog { background:#0d1017; }
        QWidget { color:#dbe2f0; font-size:10pt; }
        QLineEdit, QComboBox, QSpinBox, QListWidget, QSlider {
             background:#151a24; border:1px solid #2a3242;
             border-radius:6px; padding:4px; }
        QPushButton { background:#1c2432; border:1px solid #313c52;
             border-radius:6px; padding:5px 10px; }
        QPushButton:hover { background:#243049; }
        QPushButton:checked { background:#2c4a6e; }
        QToolBar { background:#10141d; border:none; spacing:4px; }
        QDockWidget::title { background:#10141d; padding:6px; }
        QTabWidget::pane { border:1px solid #2a3242; }
        QTabBar::tab { background:#131826; padding:6px 12px;
             border-top-left-radius:6px; border-top-right-radius:6px; }
        QTabBar::tab:selected { background:#1d2b45; }
        QLabel { background: transparent; }
    """)
    print(f"[Molecule Studio Pro] library loaded: {len(MOLECULES)} molecules")
    win = MoleculeWindow()
    win.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()