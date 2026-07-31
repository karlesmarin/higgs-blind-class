#!/usr/bin/env python3
"""make_figure_positivity.py - the asymmetry between the two halves, measured in the basis where it
is a theorem and not a metaphor.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Both halves of the potential are GL(4) characters restricted to O(4): the identity half to the
identity component, the coset half to the reflection coset.  Expanded in SU(2) characters
chi_m(t) = t^m + t^{m-2} + ... + t^{-m}, the difference is visible and exact:

  identity half  Sigma_lambda(t) = s_lambda(1, 1,t,1/t)  -- a genuine restriction, so its
                 multiplicities are branching multiplicities and CANNOT be negative;
  coset half     D_lambda(t)     = s_lambda(1,-1,t,1/t)  -- a virtual (twining) character, whose
                 coefficients are signed, so cancellation is possible and D can vanish entirely.

That is the physical statement of the paper -- even windings can never cancel, odd ones can -- shown
as the arithmetic fact it is.  Left panel: the two decompositions over the symmetric family
lambda = (n,0,0,0), which contains AHMN's 35 = (4,0,0,0).  Right panel: the census over all 455
multiplets in range.

Exact integer arithmetic; the figure is drawn from the numbers.
"""
import os
import sys
from itertools import combinations_with_replacement

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from fibre import schur, EVEN, ODD

HERE = os.path.dirname(os.path.abspath(__file__))
# --es: the Spanish edition of the paper gets its own figure, as in Parts III and IV
ES = "--es" in sys.argv


def T(en, es):
    return es if ES else en


OUTP = os.path.join(HERE, "paper", "fig_positivity_es.pdf" if ES else "fig_positivity.pdf")
HDRBLUE = (31 / 255, 78 / 255, 121 / 255)
WARMRED = (178 / 255, 34 / 255, 34 / 255)


def to_su2(poly):
    """expand a symmetric Laurent polynomial in the basis chi_m(t); exact integers"""
    p, out = dict(poly), {}
    while p:
        m = max(p)
        c = p[m]
        out[m] = c
        for j in range(-m, m + 1, 2):
            p[j] = p.get(j, 0) - c
            if p[j] == 0:
                del p[j]
    return {k: v for k, v in out.items() if v}


def main():
    NMAX = 12
    fig = plt.figure(figsize=(10.2, 4.1))

    # ------------------------------------------------ left: the two decompositions, in 3D
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    for n in range(NMAX + 1):
        lam = [n, 0, 0, 0]
        for poly, col, dx in ((schur(lam, EVEN), HDRBLUE, -0.16),
                              (schur(lam, ODD), WARMRED, +0.16)):
            for m, c in sorted(to_su2(poly).items()):
                ax.plot([n + dx, n + dx], [m, m], [0, c], color=col, lw=1.5, alpha=0.85)
                ax.scatter([n + dx], [m], [c], color=col, s=11, depthshade=False)
    # the plane c = 0, which only the coset half crosses
    # drawn as an OUTLINE and not a filled surface: a filled one hides exactly the stems that
    # cross it, which is what the caption asks the reader to look at.
    lo, hi = -0.6, NMAX + 0.6
    for a, b in (((lo, lo), (hi, lo)), ((hi, lo), (hi, hi)),
                 ((hi, hi), (lo, hi)), ((lo, hi), (lo, lo))):
        ax.plot([a[0], b[0]], [a[1], b[1]], [0, 0], color="#5b6b7a", lw=1.0, alpha=0.9)
    for g in range(0, NMAX + 1, 4):
        ax.plot([lo, hi], [g, g], [0, 0], color="#9aa7b3", lw=0.5, alpha=0.55)
        ax.plot([g, g], [lo, hi], [0, 0], color="#9aa7b3", lw=0.5, alpha=0.55)
    ax.set_xlabel(T(r"$n$   in   $\lambda=(n,0,0,0)$", r"$n$   en   $\lambda=(n,0,0,0)$"),
                  fontsize=9, labelpad=-3)
    ax.set_ylabel(T(r"$SU(2)$ label $m$", r"etiqueta $m$ de $SU(2)$"), fontsize=9, labelpad=-3)
    ax.set_zlabel(T("coefficient", "coeficiente"), fontsize=9, labelpad=-4)
    ax.tick_params(labelsize=7, pad=-2)
    ax.view_init(elev=17, azim=-61)
    ax.set_title(T(r"$\Sigma_\lambda$ never goes below zero; $D_\lambda$ does",
                   r"$\Sigma_\lambda$ nunca baja de cero; $D_\lambda$ sí"), fontsize=10, pad=-2)
    from matplotlib.lines import Line2D
    ax.legend(handles=[Line2D([], [], color=HDRBLUE, lw=2,
                              label=T(r"$\Sigma_\lambda$  identity half",
                                      r"$\Sigma_\lambda$  mitad identidad")),
                       Line2D([], [], color=WARMRED, lw=2,
                              label=T(r"$D_\lambda$  coset half",
                                      r"$D_\lambda$  mitad coset"))],
              loc="upper left", fontsize=8, frameon=False, bbox_to_anchor=(-0.07, 1.00))

    # ------------------------------------------------ right: the census over all 455
    ax2 = fig.add_subplot(1, 2, 2)
    irreps = [list(c)[::-1] + [0] for c in combinations_with_replacement(range(NMAX + 1), 3)]
    irreps = [l for l in irreps if l[0] >= l[1] >= l[2]]
    negE = negO = zeroO = 0
    per_l1 = {}
    for lam in irreps:
        E, O = to_su2(schur(lam, EVEN)), to_su2(schur(lam, ODD))
        e = any(v < 0 for v in E.values())
        o = any(v < 0 for v in O.values())
        negE += e
        negO += o
        zeroO += not schur(lam, ODD)
        d = per_l1.setdefault(lam[0], [0, 0, 0])
        d[0] += 1
        d[1] += o
        d[2] += not schur(lam, ODD)
    ks = sorted(per_l1)
    tot = np.array([per_l1[k][0] for k in ks], dtype=float)
    sgn = np.array([per_l1[k][1] for k in ks], dtype=float)
    zer = np.array([per_l1[k][2] for k in ks], dtype=float)
    # the three sets are DISJOINT, so they are stacked and not overlaid: D identically zero,
    # D with a sign change, and the rest (D of one sign and not zero).
    ax2.bar(ks, zer, color="#2b2b2b", width=0.72,
            label=T(r"$D_\lambda\equiv0$  ($\eta$ invisible)",
                    r"$D_\lambda\equiv0$  ($\eta$ invisible)"))
    ax2.bar(ks, sgn, bottom=zer, color=WARMRED, alpha=0.9, width=0.72,
            label=T(r"$D_\lambda$ has a negative coefficient",
                    r"$D_\lambda$ tiene un coeficiente negativo"))
    ax2.bar(ks, tot - zer - sgn, bottom=zer + sgn, color="#dfe6ee", width=0.72,
            label=T(r"$D_\lambda$ of one sign, not zero",
                    r"$D_\lambda$ de un solo signo, no nulo"))
    ax2.plot(ks, np.zeros_like(tot), color=HDRBLUE, lw=2.2,
             label=T(r"$\Sigma_\lambda$ with a negative coefficient: $0$ always",
                     r"$\Sigma_\lambda$ con coeficiente negativo: $0$ siempre"))
    ax2.set_xlabel(r"$\lambda_1$", fontsize=10)
    ax2.set_ylabel(T("multiplets", "multipletes"), fontsize=10)
    ax2.set_title(T("census over all %d multiplets" % len(irreps),
                    "censo sobre los %d multipletes" % len(irreps)), fontsize=10)
    ax2.legend(fontsize=7.6, frameon=False, loc="upper left")
    ax2.tick_params(labelsize=8)
    for sp in ("top", "right"):
        ax2.spines[sp].set_visible(False)
    for sp in ("left", "bottom"):
        ax2.spines[sp].set_color("#c8d1da")

    fig.tight_layout(w_pad=2.0)
    fig.savefig(OUTP, bbox_inches="tight")
    fig.savefig(OUTP.replace(".pdf", ".png"), dpi=150, bbox_inches="tight")
    print("multiplets                                    : %d" % len(irreps))
    print("Sigma with a negative SU(2) coefficient       : %d" % negE)
    print("D     with a negative SU(2) coefficient       : %d" % negO)
    print("D identically zero                            : %d" % zeroO)
    print("written:", OUTP)


if __name__ == "__main__":
    main()
