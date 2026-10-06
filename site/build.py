#!/usr/bin/env python3
"""Build the YieldSpace-in-Lean explainer page.

Inputs:  site/src/page.html (prose with $...$ / $$...$$ math, {{number}} placeholders,
         <!--FIG:name-->, <!--LEAN:decl--> and <!--LEANSIG:decl--> markers),
         YieldSpace/*.lean (Lean excerpts are copied from here by declaration name).
Outputs: site/index.html     (standalone page, all assets inlined)
         site/artifact.html  (same content without the document skeleton)

Run from the repository root:  python3 site/build.py
"""

import base64
import html
import json
import math
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "site"
LEAN_DIR = ROOT / "YieldSpace"

# ---------------------------------------------------------------------------
# The model, in floating point (mirrors YieldSpace/Defs.lean)
# ---------------------------------------------------------------------------


def inv(a, x, y):
    return x**a + y**a


def solve(a, k, z):
    return (k - z**a) ** (1 / a)


def out_given_in(a, x, y, d):
    return x - solve(a, inv(a, x, y), y + d)


def in_given_out(a, x, y, d):
    return solve(a, inv(a, x, y), y - d) - x


# Running example: x = 100 base, y = 110 fyToken, t = 0.5, fee g = 0.95.
X0, Y0, T, G = 100.0, 110.0, 0.5, 0.95
A = 1 - T
A_SELL, A_BUY = 1 - T / G, 1 - G * T


def numbers():
    n = {}
    k = inv(A, X0, Y0)
    n["k"] = f"{k:.3f}"
    n["ymax"] = f"{k ** (1 / A):.2f}"
    n["maxsell"] = f"{k ** (1 / A) - Y0:.2f}"
    n["price0"] = f"{(X0 / Y0) ** T:.4f}"
    n["rate_mat"] = f"{((Y0 / X0) ** T - 1) * 100:.2f}"
    o10 = out_given_in(A, X0, Y0, 10)
    n["x1_10"] = f"{X0 - o10:.3f}"
    n["out10"] = f"{o10:.3f}"
    n["avg10"] = f"{o10 / 10:.3f}"
    n["post10"] = f"{((X0 - o10) / (Y0 + 10)) ** T:.3f}"
    n["sqrt110"] = f"{Y0 ** 0.5:.3f}"
    n["sqrt120"] = f"{(Y0 + 10) ** 0.5:.3f}"
    n["d10"] = f"{(Y0 + 10) ** 0.5 - Y0 ** 0.5:.3f}"
    n["u1_10"] = f"{(X0 - o10) ** 0.5:.3f}"
    o120 = out_given_in(A, X0, Y0, 120)
    n["avg120"] = f"{o120 / 120:.3f}"
    n["post120"] = f"{((X0 - o120) / (Y0 + 120)) ** T:.3f}"
    o30 = out_given_in(A, X0, Y0, 30)
    n["out30"] = f"{o30:.2f}"
    n["avg30"] = f"{o30 / 30:.3f}"
    n["post30"] = f"{((X0 - o30) / (Y0 + 30)) ** T:.3f}"
    o4 = out_given_in(A, X0, Y0, 4)
    o6 = out_given_in(A, X0 - o4, Y0 + 4, 6)
    n["split4"], n["split6"], n["splitsum"] = f"{o4:.3f}", f"{o6:.3f}", f"{o4 + o6:.3f}"
    n["scale100"] = f"{out_given_in(A, 1000, 1100, 100):.2f}"
    i5 = in_given_out(A, X0, Y0, 5)
    n["buy5"] = f"{i5:.3f}"
    n["buy5avg"] = f"{i5 / 5:.3f}"
    n["buy5post"] = f"{((X0 + i5) / (Y0 - 5)) ** T:.3f}"
    s = out_given_in(A_SELL, X0, Y0, 10)
    b = in_given_out(A_BUY, X0 - s, Y0 + 10, 10)
    n["rt_sell"], n["rt_buy"], n["rt_loss"] = f"{s:.3f}", f"{b:.3f}", f"{b - s:.3f}"
    s2 = out_given_in(A_SELL, 200, 100, 10)
    b2 = in_given_out(A_BUY, 200 - s2, 110, 10)
    n["rt2_sell"], n["rt2_buy"], n["rt2_gain"] = f"{s2:.3f}", f"{b2:.3f}", f"{s2 - b2:.3f}"
    n["fee_buy_rate"] = f"{(1.1 ** 0.95 - 1) * 100:.2f}"
    n["fee_sell_rate"] = f"{(1.1 ** (1 / 0.95) - 1) * 100:.2f}"
    n["paper_nofee"] = f"{out_given_in(0.5, 100, 100, 100):.2f}"
    n["paper_fee"] = f"{out_given_in(1 - 0.5 / 0.95, 100, 100, 100):.2f}"
    n["paper_fee_x"] = f"{100 - out_given_in(1 - 0.5 / 0.95, 100, 100, 100):.2f}"
    n["a_sell"] = f"{A_SELL:.4f}"
    for t in (0.5, 0.25, 0.1, 0.01):
        key = str(t).replace(".", "")
        n[f"mat_nf_{key}"] = f"{out_given_in(1 - t, X0, Y0, 10):.3f}"
        n[f"mat_f_{key}"] = f"{out_given_in(1 - t / G, X0, Y0, 10):.3f}"
    return n


# ---------------------------------------------------------------------------
# SVG figures
# ---------------------------------------------------------------------------


def fmt_num(v):
    if abs(v - round(v)) < 1e-9:
        return f"{int(round(v))}"
    return f"{v:g}"


class Plot:
    """One panel of a chart. Data coordinates map linearly to the panel's box."""

    def __init__(self, fig, box, xr, yr):
        self.fig, (self.bx, self.by, self.bw, self.bh) = fig, box
        self.x0, self.x1 = xr
        self.y0, self.y1 = yr
        self.clip = f"{fig.name}-c{len(fig.panels)}"
        fig.panels.append(self)
        fig.defs.append(
            f'<clipPath id="{self.clip}"><rect x="{self.bx}" y="{self.by}" '
            f'width="{self.bw}" height="{self.bh}"/></clipPath>'
        )

    def X(self, v):
        return self.bx + (v - self.x0) / (self.x1 - self.x0) * self.bw

    def Y(self, v):
        return self.by + (1 - (v - self.y0) / (self.y1 - self.y0)) * self.bh

    def axes(self, xticks, yticks, xlabel, ylabel, xfmt=fmt_num, yfmt=fmt_num):
        f = self.fig
        bx, by, bw, bh = self.bx, self.by, self.bw, self.bh
        f.add(f'<path class="axis" d="M{bx},{by} V{by + bh} H{bx + bw}"/>')
        for v in xticks:
            px = self.X(v)
            f.add(f'<path class="axis" d="M{px:.1f},{by + bh} v5"/>')
            f.add(f'<text class="tick" x="{px:.1f}" y="{by + bh + 20}" text-anchor="middle">{xfmt(v)}</text>')
        for v in yticks:
            py = self.Y(v)
            f.add(f'<path class="axis" d="M{bx},{py:.1f} h-5"/>')
            f.add(f'<text class="tick" x="{bx - 9}" y="{py + 4.5:.1f}" text-anchor="end">{yfmt(v)}</text>')
        f.add(f'<text class="axlabel" x="{bx + bw / 2}" y="{by + bh + 44}" text-anchor="middle">{xlabel}</text>')
        f.add(
            f'<text class="axlabel" transform="translate({bx - 50},{by + bh / 2}) rotate(-90)" '
            f'text-anchor="middle">{ylabel}</text>'
        )

    def curve(self, pts, cls):
        pts = [(x, y) for x, y in pts if math.isfinite(y)]
        d = "M" + " L".join(f"{self.X(x):.2f},{self.Y(y):.2f}" for x, y in pts)
        self.fig.add(f'<path class="{cls}" clip-path="url(#{self.clip})" d="{d}"/>')

    def seg(self, xa, ya, xb, yb, cls):
        self.fig.add(
            f'<path class="{cls}" clip-path="url(#{self.clip})" '
            f'd="M{self.X(xa):.2f},{self.Y(ya):.2f} L{self.X(xb):.2f},{self.Y(yb):.2f}"/>'
        )

    def dot(self, x, y, cls="dot"):
        self.fig.add(f'<circle class="{cls}" cx="{self.X(x):.2f}" cy="{self.Y(y):.2f}" r="4"/>')

    def text(self, x, y, s, cls="lbl", anchor="start", dx=0, dy=0):
        self.fig.add(
            f'<text class="{cls}" x="{self.X(x) + dx:.1f}" y="{self.Y(y) + dy:.1f}" '
            f'text-anchor="{anchor}">{s}</text>'
        )

    def rect(self, xa, xb, ya, yb, cls):
        x, y = self.X(xa), self.Y(yb)
        w, h = self.X(xb) - x, self.Y(ya) - y
        self.fig.add(f'<rect class="{cls}" clip-path="url(#{self.clip})" x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}"/>')


class Figure:
    def __init__(self, name, w, h, label):
        self.name, self.w, self.h, self.label = name, w, h, label
        self.panels, self.defs, self.body = [], [], []

    def add(self, s):
        self.body.append(s)

    def svg(self):
        return (
            f'<svg class="plot" viewBox="0 0 {self.w} {self.h}" role="img" aria-label="{html.escape(self.label)}">'
            f'<defs>{"".join(self.defs)}</defs>{"".join(self.body)}</svg>'
        )


def I(s):
    return f'<tspan class="i">{s}</tspan>'


def linspace(a, b, n):
    return [a + (b - a) * i / (n - 1) for i in range(n)]


def fig_curves():
    f = Figure("curves", 640, 500, "Constant power sum curves through (100, 100)")
    p = Plot(f, (70, 16, 540, 410), (0, 420), (0, 420))
    p.axes(range(0, 401, 100), range(0, 401, 100),
           f"base reserve {I('x')}", f"fyToken reserve {I('y')}")
    xs = linspace(0.01, 420, 900)
    p.curve([(x, 10000 / x) for x in linspace(23.8, 420, 400)], "c4 dash")
    for t, cls in ((0.0, "c3"), (0.5, "c1"), (0.9, "c2")):
        a = 1 - t
        k = inv(a, 100, 100)
        pts = [(x, solve(a, k, x)) for x in xs if k - x**a > 0]
        p.curve(pts, cls)
    p.dot(100, 100)
    p.text(100, 100, "(100, 100)", dx=10, dy=-10)
    rows = ((f"{I('t')} = 0", "c3"), (f"{I('t')} = 0.5", "c1"), (f"{I('t')} = 0.9", "c2"),
            (f"{I('xy')} = 10 000", "c4 dash"))
    for i, (lab, cls) in enumerate(rows):
        yv = 395 - i * 26
        p.seg(270, yv, 300, yv, cls)
        p.text(300, yv, lab, "lbl", dx=10, dy=5)
    return f.svg()


def fig_coords():
    f = Figure("coords", 820, 420, "The trade in the variables u and w, and the map psi")
    k = inv(A, X0, Y0)
    u, w = X0**A, Y0**A
    w2 = (Y0 + 10) ** A
    u2 = k - w2
    # left: the line u + w = k
    p = Plot(f, (70, 16, 300, 330), (9.0, 11.2), (9.4, 11.6))
    p.axes([9.0, 9.5, 10.0, 10.5, 11.0], [9.5, 10.0, 10.5, 11.0, 11.5],
           f"{I('u')} = {I('x')}<tspan dy='-6' font-size='11'>1/2</tspan>",
           f"{I('w')} = {I('y')}<tspan dy='-6' font-size='11'>1/2</tspan>",
           xfmt=lambda v: f"{v:.1f}", yfmt=lambda v: f"{v:.1f}")
    p.curve([(9.0, k - 9.0), (11.2, k - 11.2)], "c4")
    p.seg(u, w, u2, w, "guide")
    p.seg(u2, w, u2, w2, "guide")
    p.curve([(u, w), (u2, w2)], "c1 thick")
    p.dot(u, w)
    p.dot(u2, w2)
    p.text(u, w, f"{I('P')}", dx=10, dy=4)
    p.text(u2, w2, f"{I('P')}′", dx=-10, dy=2, anchor="end")
    p.text((u + u2) / 2, w, f"−{I('d')}", dy=18, anchor="middle")
    p.text(u2, (w + w2) / 2, f"+{I('d')}", dx=-8, anchor="end", dy=5)
    p.text(10.65, k - 10.65, f"{I('u')} + {I('w')} = {I('k')}", "lbl t4", dx=8, dy=-6)
    # right: psi(s) = s^2
    q = Plot(f, (500, 16, 300, 330), (9.0, 11.2), (78, 125))
    q.axes([9.0, 9.5, 10.0, 10.5, 11.0], [80, 90, 100, 110, 120],
           f"{I('s')}", f"ψ({I('s')}) = {I('s')}<tspan dy='-6' font-size='11'>2</tspan>",
           xfmt=lambda v: f"{v:.1f}")
    q.curve([(s, s * s) for s in linspace(9.0, 11.2, 200)], "c4")
    for lo, hi, cls, lab in ((u2, u, "c2", "out"), (w, w2, "c1", f"{I('Δ')}")):
        q.rect(lo, hi, 78, 125, "band")
        q.seg(lo, 78, lo, lo * lo, "guide")
        q.seg(hi, 78, hi, hi * hi, "guide")
        q.seg(lo, lo * lo, hi, lo * lo, "guide")
        q.seg(hi, lo * lo, hi, hi * hi, f"{cls} thick")
        q.dot(lo, lo * lo, "dot small")
        q.dot(hi, hi * hi, "dot small")
        q.text(hi, (lo * lo + hi * hi) / 2,
               f"{lab} = {hi * hi - lo * lo:.2f}", f"lbl t{cls[1]}", dx=8, dy=5)
    q.text((u2 + u) / 2, 78, f"{I('u')}′ … {I('u')}", "tick", anchor="middle", dy=-8)
    q.text((w + w2) / 2, 78, f"{I('w')} … {I('w')}′", "tick", anchor="middle", dy=-8)
    return f.svg()


def fig_trade():
    f = Figure("trade", 640, 470, "Chord and tangent slopes for a sale of 120 fyToken")
    k = inv(A, X0, Y0)
    p = Plot(f, (70, 16, 470, 380), (90, 270), (0, 120))
    p.axes(range(100, 271, 40), range(0, 121, 20),
           f"fyToken reserve {I('y')}", f"base reserve {I('x')}")
    p.curve([(y, solve(A, k, y)) for y in linspace(90, 270, 400) if k - y**A > 0], "c4")
    ya, xa = Y0, X0
    yb = Y0 + 120
    xb = solve(A, k, yb)
    sa, sb = (xa / ya) ** T, (xb / yb) ** T
    p.seg(ya - 15, xa + 15 * sa, ya + 45, xa - 45 * sa, "c1")
    p.seg(yb - 45, xb + 45 * sb, yb + 40, xb - 40 * sb, "c2")
    p.seg(ya, xa, yb, xb, "c3 thick")
    p.dot(ya, xa)
    p.dot(yb, xb)
    p.text(ya, xa, "before", dx=10, dy=-8)
    p.text(yb, xb, "after", dx=-10, dy=22, anchor="end")
    p.text(ya + 45, xa - 45 * sa, f"tangent, slope −{sa:.3f}", "lbl t1", dx=-6, dy=20, anchor="middle")
    ym = (ya + yb) / 2
    p.text(ym, (xa + xb) / 2, f"chord, slope −{(xa - xb) / 120:.3f}", "lbl t3", dx=8, dy=-12)
    p.text(yb + 40, xb - 40 * sb, f"tangent, slope −{sb:.3f}", "lbl t2", dx=0, dy=-14, anchor="end")
    return f.svg()


def fig_impact():
    f = Figure("impact", 640, 440, "Average and marginal prices against trade size")
    p = Plot(f, (70, 16, 450, 350), (0, 150), (0.2, 1.0))
    p.axes(range(0, 151, 25), [0.2, 0.4, 0.6, 0.8, 1.0],
           f"fyToken sold, {I('Δ')}", "price (base per fyToken)", yfmt=lambda v: f"{v:.1f}")
    ds = linspace(0.01, 150, 300)
    pre = (X0 / Y0) ** T
    avg = [(d, out_given_in(A, X0, Y0, d) / d) for d in ds]
    post = [(d, ((X0 - out_given_in(A, X0, Y0, d)) / (Y0 + d)) ** T) for d in ds]
    p.curve([(0, pre), (150, pre)], "c1")
    p.curve(avg, "c3 thick")
    p.curve(post, "c2")
    p.text(150, pre, "before the trade", "lbl t1", dx=8, dy=5)
    p.text(150, avg[-1][1], "average", "lbl t3", dx=8, dy=5)
    p.text(150, post[-1][1], "after the trade", "lbl t2", dx=8, dy=5)
    p.seg(10, 0.2, 10, out_given_in(A, X0, Y0, 10) / 10, "guide")
    p.dot(10, out_given_in(A, X0, Y0, 10) / 10, "dot small")
    return f.svg()


def fig_roundtrip():
    f = Figure("roundtrip", 640, 440, "Round-trip result against the starting base reserve")

    def loss(x):
        s = out_given_in(A_SELL, x, 100, 10)
        return in_given_out(A_BUY, x - s, 110, 10) - s

    p = Plot(f, (70, 16, 520, 350), (50, 200), (-0.5, 0.3))
    p.axes(range(50, 201, 25), [-0.4, -0.2, 0.0, 0.2],
           f"starting base reserve {I('x')} (with {I('y')} = 100)",
           "buy-back cost − sale proceeds", yfmt=lambda v: f"{v:.1f}")
    p.rect(50, 100, -0.5, 0.3, "band")
    p.seg(50, 0, 200, 0, "axis")
    p.seg(100, -0.5, 100, 0.3, "guide")
    p.seg(110, -0.5, 110, 0.3, "guide")
    p.curve([(x, loss(x)) for x in linspace(50, 200, 300)], "c1 thick")
    p.dot(110, 0)
    p.text(100, 0.3, f"{I('x')} = {I('y')}", "tick", dx=-6, dy=16, anchor="end")
    p.text(110, 0.3, f"{I('x')}<tspan dy='4' font-size='11'>1</tspan><tspan dy='-4'> = {I('y')}</tspan>",
           "tick", dx=6, dy=16)
    p.text(58, 0.1, "trader loses", "lbl")
    p.text(194, -0.12, "trader gains", "lbl", anchor="end")
    return f.svg()


def fig_maturity():
    f = Figure("maturity", 640, 420, "Payout for selling 10 fyToken as t goes to 0")
    p = Plot(f, (70, 16, 470, 330), (0, 0.9), (8.0, 10.1))
    p.axes([0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9], [8.0, 8.5, 9.0, 9.5, 10.0],
           f"time to maturity {I('t')}", "base received for 10 fyToken",
           xfmt=lambda v: f"{v:.1f}", yfmt=lambda v: f"{v:.1f}")
    ts = linspace(0.0, 0.9, 200)
    p.seg(0, 10, 0.9, 10, "c4 dash")
    p.curve([(t, out_given_in(1 - t, X0, Y0, 10)) for t in ts], "c1 thick")
    p.curve([(t, out_given_in(1 - t / G, X0, Y0, 10)) for t in ts], "c2 thick")
    p.text(0.9, 10, "1 : 1", "lbl t4", dx=8, dy=5)
    p.text(0.9, out_given_in(1 - 0.9, X0, Y0, 10), "no fee", "lbl t1", dx=8, dy=-2)
    p.text(0.9, out_given_in(1 - 0.9 / G, X0, Y0, 10), f"{I('g')} = 0.95", "lbl t2", dx=8, dy=14)
    return f.svg()


FIGURES = {
    "curves": fig_curves,
    "coords": fig_coords,
    "trade": fig_trade,
    "impact": fig_impact,
    "roundtrip": fig_roundtrip,
    "maturity": fig_maturity,
}

# ---------------------------------------------------------------------------
# Lean excerpts
# ---------------------------------------------------------------------------

DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|structure)\s+(\S+)", re.M)


def load_lean():
    decls = {}
    for path in sorted(LEAN_DIR.glob("*.lean")):
        text = path.read_text()
        for m in DECL_RE.finditer(text):
            start = m.start()
            # include an immediately preceding doc comment
            before = text[:start]
            dm = re.search(r"/--(?:(?!-/).)*-/\s*$", before, re.S)
            if dm:
                start = dm.start()
            end = text.find("\n\n", m.end())
            end = len(text) if end == -1 else end
            name = m.group(2)
            decls[name] = (path.name, text[start:end].rstrip())
    return decls


LEAN_KW = (
    "theorem lemma def structure where namespace end open variable noncomputable section "
    "import fun by have show from at with let calc obtain refine exact rw simp unfold "
    "linarith nlinarith intro rcases subst set field_simp convert ring positivity "
    "constructor sorry simpa conv_lhs conv_rhs only using rfl first exact? apply"
).split()
TACTICS = set(
    "by have show obtain refine exact rw simp unfold linarith nlinarith intro rcases subst set "
    "field_simp convert ring positivity constructor simpa conv_lhs conv_rhs rfl first calc apply".split()
)
KEYWORDS = set(LEAN_KW) - TACTICS

TOKEN_RE = re.compile(
    r"(?P<cm>/-.*?-/|--[^\n]*)"
    r"|(?P<decl>(?<=theorem )\S+|(?<=lemma )\S+|(?<=def )\S+|(?<=structure )\S+)"
    r"|(?P<word>[A-Za-z_][A-Za-z0-9_'.?]*)"
    r"|(?P<other>.)",
    re.S,
)


def highlight(code):
    out = []
    for m in TOKEN_RE.finditer(code):
        kind, s = m.lastgroup, m.group()
        e = html.escape(s, quote=False)
        if kind == "cm":
            out.append(f'<span class="l-cm">{e}</span>')
        elif kind == "decl":
            out.append(f'<span class="l-decl">{e}</span>')
        elif kind == "word" and s in KEYWORDS:
            out.append(f'<span class="l-kw">{e}</span>')
        elif kind == "word" and s in TACTICS:
            out.append(f'<span class="l-tac">{e}</span>')
        else:
            out.append(e)
    return "".join(out)


def lean_block(decls, names, sig_only):
    parts, kinds, files = [], set(), []
    for name in names.split(","):
        fname, code = decls[name]
        if fname not in files:
            files.append(fname)
        is_def = bool(re.search(r"^(?:noncomputable\s+)?(?:def|structure)\s", code, re.M))
        kinds.add("definition" if is_def else "theorem")
        if sig_only:
            i = code.index(":=")
            code = code[:i].rstrip() + " := …"
        parts.append(code)
    code = "\n\n".join(parts)
    fname = ", ".join(files)
    if kinds == {"definition"}:
        tag = "definitions" if len(parts) > 1 else "definition"
    else:
        tag = "statement" if sig_only else "statement and proof"
    return (
        f'<div class="lean"><div class="lean-h"><span>{"YieldSpace/" + fname}</span>'
        f'<span>{tag}</span></div><pre><code>{highlight(code)}</code></pre></div>'
    )


# ---------------------------------------------------------------------------
# Math
# ---------------------------------------------------------------------------


def render_math(src):
    items, pieces = [], []

    def grab(display):
        def f(m):
            items.append({"tex": html.unescape(m.group(1)), "display": display})
            return f"\x00MATH{len(items) - 1}\x00"
        return f

    src = re.sub(r"\$\$(.+?)\$\$", grab(True), src, flags=re.S)
    src = re.sub(r"\$(.+?)\$", grab(False), src, flags=re.S)
    res = subprocess.run(
        ["node", str(SITE / "katex_render.js")],
        input=json.dumps(items), capture_output=True, text=True, check=True,
    )
    rendered = json.loads(res.stdout)
    return re.sub(r"\x00MATH(\d+)\x00", lambda m: rendered[int(m.group(1))], src)


def katex_css():
    dist = SITE / "node_modules" / "katex" / "dist"
    css = (dist / "katex.min.css").read_text()

    def font(m):
        fname = m.group(1)
        data = base64.b64encode((dist / "fonts" / fname).read_bytes()).decode()
        return f'url(data:font/woff2;base64,{data}) format("woff2")'

    css = re.sub(r'url\(fonts/([^)]+\.woff2)\) format\("woff2"\)', font, css)
    css = re.sub(r',url\(fonts/[^)]+\.(?:woff|ttf)\) format\("(?:woff|truetype)"\)', "", css)
    return css


# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------


def toc(body):
    items = []
    for m in re.finditer(r'<h([23]) id="([^"]+)">(.*?)</h\1>', body):
        level, ident, title = m.groups()
        nm = re.match(r'<span class="n">(.*?)</span>(.*)', title)
        num, rest = (nm.group(1), nm.group(2)) if nm else ("", title)
        label = f'<span class="toc-n">{num}</span>{re.sub(r"<[^>]+>", "", rest)}'
        items.append((int(level), ident, label))
    out, open_sub = ['<nav class="toc"><h2 class="toc-h">Contents</h2><ol>'], False
    for level, ident, title in items:
        if level == 2:
            if open_sub:
                out.append("</ol></li>")
                open_sub = False
            elif len(out) > 1:
                out.append("</li>")
            out.append(f'<li><a href="#{ident}">{title}</a>')
        else:
            if not open_sub:
                out.append("<ol>")
                open_sub = True
            out.append(f'<li><a href="#{ident}">{title}</a></li>')
    out.append("</ol></li>" if open_sub else "</li>")
    out.append("</ol></nav>")
    return "".join(out)


def main():
    src = (SITE / "src" / "page.html").read_text()
    css = (SITE / "src" / "style.css").read_text()
    nums = numbers()
    src = re.sub(r"\{\{(\w+)\}\}", lambda m: nums[m.group(1)], src)
    src = render_math(src)
    decls = load_lean()
    src = re.sub(r"<!--LEAN:(\S+?)-->", lambda m: lean_block(decls, m.group(1), False), src)
    src = re.sub(r"<!--LEANSIG:(\S+?)-->", lambda m: lean_block(decls, m.group(1), True), src)
    src = re.sub(r"<!--FIG:(\w+)-->", lambda m: FIGURES[m.group(1)](), src)
    src = src.replace("<!--TOC-->", toc(src))
    missing = re.findall(r"<!--(?:LEAN|LEANSIG|FIG):\S+?-->|\{\{\w+\}\}", src)
    assert not missing, missing

    head = (
        "<title>YieldSpace in Lean</title>\n"
        '<link rel="preconnect" href="https://fonts.googleapis.com">\n'
        '<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
        '<link rel="stylesheet" href="https://fonts.googleapis.com/css2?'
        'family=JetBrains+Mono:wght@400;600&family=Noto+Sans+Mono:wght@400;600&display=swap">\n'
        f"<style>\n{katex_css()}\n{css}\n</style>\n"
    )
    fragment = head + src
    (SITE / "artifact.html").write_text(fragment)
    (SITE / "index.html").write_text(
        '<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
        + head + "</head>\n<body>\n" + src + "\n</body>\n</html>\n"
    )
    print(f"wrote site/index.html ({len(fragment) // 1024} KB)")


if __name__ == "__main__":
    main()
