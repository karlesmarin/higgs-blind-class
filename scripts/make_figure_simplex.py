#!/usr/bin/env python3
"""make_figure_simplex.py - Proposition 1 drawn: a boundary condition sees a multiplet through
three characters, and each of the three layers the simplex in a different direction.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Haba-Hosotani-Kawamura label a boundary condition of SU(N) on S^1/Z_2 by four non-negative integers
[p;q,r;s] with p+q+r+s = N, so the set of boundary conditions IS a simplex.  For SU(4) it has 35
points.  Proposition 1 of Part V says a representation enters only through

    chi(P0),  chi(P1),  chi(P0 P1)

and the boundary-condition sign eta = eta_0 eta_1 multiplies the third and nothing else.  The three
characters depend on the block sizes only through r+s, q+s and q+r respectively, so the SAME simplex
is layered three different ways -- which is what this figure shows, one panel each.

The colour job is polarity (the characters take both signs), so it is a diverging ramp with a
neutral midpoint, never a rainbow.  Points where the character VANISHES are ringed: on the third
panel those are exactly the boundary conditions for which eta is invisible to this multiplet.

Exact integer arithmetic (characters via the Schur polynomial at a sign alphabet); the figure is
drawn from the numbers, not from a formula typed twice.
"""
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap, TwoSlopeNorm

from fibre import ONE, lmul, ladd, lscale, schur

HERE = os.path.dirname(os.path.abspath(__file__))
# --es: the Spanish edition of the paper gets its own figure, as in Parts III and IV
ES = "--es" in sys.argv


def T(en, es):
    return es if ES else en


OUTP = os.path.join(HERE, "paper", "fig_simplex_es.pdf" if ES else "fig_simplex.pdf")

HDRBLUE = (31 / 255, 78 / 255, 121 / 255)
WARMRED = (178 / 255, 34 / 255, 34 / 255)
# diverging: two hues, neutral grey midpoint
DIV = LinearSegmentedColormap.from_list(
    "div", [WARMRED, "#e6b3b3", "#eceff2", "#a8c0d6", HDRBLUE])

N = 4
LAM = (2, 1, 1, 0)            # the gauge adjoint 15 of SU(4): present in every model
LABEL = r"$\mathbf{15}=(2,1,1,0)$"


def chi(lam, signs):
    """character of the SU(4) irrep `lam` at diag(signs), exactly: s_lambda evaluated there"""
    alpha = [{0: int(x)} for x in signs]
    return sum(schur(list(lam), alpha).values())


def main():
    pts, vals = [], {0: [], 1: [], 2: []}
    for p in range(N + 1):
        for q in range(N + 1 - p):
            for r in range(N + 1 - p - q):
                s = N - p - q - r
                p0 = [+1] * p + [+1] * q + [-1] * r + [-1] * s
                p1 = [+1] * p + [-1] * q + [+1] * r + [-1] * s
                u = [a * b for a, b in zip(p0, p1)]
                pts.append((p, q, r))
                vals[0].append(chi(LAM, p0))
                vals[1].append(chi(LAM, p1))
                vals[2].append(chi(LAM, u))
    pts = np.array(pts)
    assert len(pts) == 35, len(pts)

    titles = [r"$\chi_\lambda(P_0)$" + "\n" + T(r"layers by $r+s$", r"estratifica por $r+s$"),
              r"$\chi_\lambda(P_1)$" + "\n" + T(r"layers by $q+s$", r"estratifica por $q+s$"),
              T(r"$\chi_\lambda(P_0P_1)$   $-$ the one $\eta$ multiplies",
                r"$\chi_\lambda(P_0P_1)$   $-$ el que multiplica $\eta$") + "\n"
              + T(r"layers by $q+r$", r"estratifica por $q+r$")]

    fig = plt.figure(figsize=(10.4, 3.7))
    for k in range(3):
        ax = fig.add_subplot(1, 3, k + 1, projection="3d")
        v = np.array(vals[k], dtype=float)
        norm = TwoSlopeNorm(vmin=min(v.min(), -1), vcenter=0, vmax=max(v.max(), 1))
        # on the third panel, ring the boundary conditions whose winding element has det = -1:
        # the reflection coset, the only place eta can act at all.
        coset = np.array([(q + r) % 2 == 1 for (p, q, r) in pts]) if k == 2 else np.zeros(
            len(pts), dtype=bool)
        sc = ax.scatter(pts[~coset, 0], pts[~coset, 1], pts[~coset, 2], c=v[~coset], cmap=DIV,
                        norm=norm, s=62, edgecolors="white", linewidths=0.7, depthshade=False)
        if coset.any():
            ax.scatter(pts[coset, 0], pts[coset, 1], pts[coset, 2], c=v[coset], cmap=DIV,
                       norm=norm, s=74, edgecolors=WARMRED, linewidths=1.5, depthshade=False,
                       label=T(r"$\det U=-1$: the coset  (%d of 35)" % coset.sum(),
                               r"$\det U=-1$: el coset  (%d de 35)" % coset.sum()))
            ax.legend(loc="upper left", fontsize=7.5, frameon=False, bbox_to_anchor=(-0.10, 1.03))
        ax.set_xlabel("$p$", fontsize=10, labelpad=-6)
        ax.set_ylabel("$q$", fontsize=10, labelpad=-6)
        ax.set_zlabel("$r$", fontsize=10, labelpad=-6)
        ax.set_xticks(range(N + 1))
        ax.set_yticks(range(N + 1))
        ax.set_zticks(range(N + 1))
        ax.tick_params(labelsize=7, pad=-3)
        ax.set_title(titles[k], fontsize=9.5, pad=-1)
        ax.view_init(elev=19, azim=-56)
        cb = fig.colorbar(sc, ax=ax, pad=0.10, shrink=0.52, aspect=13)
        cb.ax.tick_params(labelsize=7)

    fig.suptitle(T(r"the 35 boundary conditions $[p;q,r;s]$ of $SU(4)$, seen by the multiplet ",
                   r"las 35 condiciones de contorno $[p;q,r;s]$ de $SU(4)$, vistas por el "
                   r"multiplete ")
                 + LABEL, fontsize=11, y=1.02)
    fig.tight_layout(w_pad=1.6)
    fig.savefig(OUTP, bbox_inches="tight")
    fig.savefig(OUTP.replace(".pdf", ".png"), dpi=150, bbox_inches="tight")

    for k, nm in enumerate(("chi(P0)", "chi(P1)", "chi(P0P1)")):
        v = np.array(vals[k])
        print("%-10s range [%3d,%3d]   zeros %2d of 35" % (nm, v.min(), v.max(), (v == 0).sum()))
    # the layering claim, checked and not merely asserted
    for k, f in enumerate((lambda p, q, r, s: r + s, lambda p, q, r, s: q + s,
                           lambda p, q, r, s: q + r)):
        seen = {}
        ok = True
        for (p, q, r), val in zip(pts, vals[k]):
            key = f(p, q, r, N - p - q - r)
            if seen.setdefault(key, val) != val:
                ok = False
        print("  panel %d constant on its stated layers: %s" % (k + 1, ok))
    print("written:", OUTP)


if __name__ == "__main__":
    main()
