#!/usr/bin/env python3
"""make_figure_zeros.py - where the zeros are, which is the whole reason one half factors.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

`why_one_factors.py` established the dichotomy as a table of percentages. It deserves a picture,
because the statement is geometric: for a frozen block of roots of unity every zero of s_lambda lies
ON the unit circle, and for a frozen block of repeated letters they do not.

  left  (3D)  the complex plane stacked once per frozen block, with the unit circle drawn on each
              layer. The root-of-unity layers have every zero on their circle; the repeated-letter
              layers have zeros scattered off it, out to |z| ~ 4.
  right (2D)  the same data as the distribution of |z|: the root-of-unity blocks are a single spike
              at exactly 1, the repeated-letter blocks a broad spread.

Drawn from the same exact-integer characters as the table; the only floating point is np.roots.
"""
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from why_one_factors import e_mu, e_ones, e_pair, e_conv, schur_from_e, parts_of

HERE = os.path.dirname(os.path.abspath(__file__))
# --es: the Spanish edition of the paper gets its own figure, as in Parts III and IV
ES = "--es" in sys.argv


def T(en, es):
    return es if ES else en


OUTP = os.path.join(HERE, "paper", "fig_zeros_es.pdf" if ES else "fig_zeros.pdf")
HDRBLUE = (31 / 255, 78 / 255, 121 / 255)
WARMRED = (178 / 255, 34 / 255, 34 / 255)

BLOCKS = [("$\\mu_2$", e_mu(2), 4, 10, True),
          ("$\\{1,1\\}$", e_ones(2), 4, 10, False),
          ("$\\mu_3$", e_mu(3), 5, 9, True),
          ("$\\{1,1,1\\}$", e_ones(3), 5, 9, False),
          ("$\\mu_4$", e_mu(4), 6, 8, True),
          ("$\\{1,1,1,1\\}$", e_ones(4), 6, 8, False)]


def zeros_of(fe, rows, maxn):
    e = e_conv(fe, e_pair())
    out = []
    for lam in parts_of(maxn, rows):
        s = schur_from_e(lam, e, rows)
        if not s or len(s) < 2:
            continue
        lo, hi = min(s), max(s)
        c = [s.get(k, 0) for k in range(lo, hi + 1)]
        out.extend(np.roots(c[::-1]))
    return np.array(out)


def main():
    data = [(name, zeros_of(fe, rows, mx), unity) for name, fe, rows, mx, unity in BLOCKS]

    fig = plt.figure(figsize=(10.4, 4.2))

    # ---------------------------------------------------- left: stacked complex planes, in 3D
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    th = np.linspace(0, 2 * np.pi, 200)
    for k, (name, z, unity) in enumerate(data):
        col = HDRBLUE if unity else WARMRED
        ax.plot(np.cos(th), np.sin(th), zs=k, zdir="z", color="#9aa7b3", lw=0.8, alpha=0.7)
        ax.scatter(z.real, z.imag, zs=k, zdir="z", s=5, color=col, alpha=0.55,
                   edgecolors="none", depthshade=False)
    ax.set_xlabel(r"$\mathrm{Re}\,z$", fontsize=9.5, labelpad=-4)
    ax.set_ylabel(r"$\mathrm{Im}\,z$", fontsize=9.5, labelpad=-4)
    ax.set_zticks(range(len(data)))
    ax.set_zticklabels([n for n, _, _ in data], fontsize=8.5, ha="left")
    ax.set_xlim(-4, 4)
    ax.set_ylim(-4, 4)
    ax.tick_params(labelsize=7.5, pad=-2)
    ax.view_init(elev=16, azim=-64)
    ax.set_title(T("the zeros of $s_\\lambda$, one plane per frozen block",
                   "los ceros de $s_\\lambda$, un plano por bloque congelado"),
                 fontsize=10.5, pad=-2)
    from matplotlib.lines import Line2D
    ax.legend(handles=[Line2D([], [], marker="o", ls="", color=HDRBLUE, ms=5,
                              label=T("roots of unity", "raíces de la unidad")),
                       Line2D([], [], marker="o", ls="", color=WARMRED, ms=5,
                              label=T("repeated letters", "letras repetidas"))],
              loc="upper left", fontsize=8.5, frameon=False, bbox_to_anchor=(-0.08, 1.0))

    # ---------------------------------------------------- right: the distribution of |z|
    ax2 = fig.add_subplot(1, 2, 2)
    for k, (name, z, unity) in enumerate(data):
        r = np.abs(z)
        col = HDRBLUE if unity else WARMRED
        ax2.scatter(r, np.full_like(r, k) + np.random.default_rng(k).normal(0, 0.055, r.size),
                    s=4, color=col, alpha=0.4, edgecolors="none")
    ax2.axvline(1.0, color="#2b2b2b", lw=1.1, ls="--")
    ax2.text(1.12, 0.52, r"$|z|=1$", fontsize=9, color="#2b2b2b")
    ax2.set_yticks(range(len(data)))
    ax2.set_yticklabels([n for n, _, _ in data], fontsize=9.5)
    ax2.set_xlabel(r"$|z|$", fontsize=11)
    ax2.set_xlim(0, 4.2)
    ax2.set_title(T("every zero, by modulus", "todos los ceros, por módulo"),
                  fontsize=10.5, pad=12)
    ax2.tick_params(labelsize=8.5)
    for sp in ("top", "right"):
        ax2.spines[sp].set_visible(False)
    for sp in ("left", "bottom"):
        ax2.spines[sp].set_color("#c8d1da")

    fig.subplots_adjust(left=0.02, right=0.97, wspace=0.28, top=0.90, bottom=0.12)
    fig.savefig(OUTP, bbox_inches="tight")
    fig.savefig(OUTP.replace(".pdf", ".png"), dpi=150, bbox_inches="tight")
    print("block            zeros    max |z|   share with ||z|-1| < 1e-4")
    for name, z, unity in data:
        r = np.abs(z)
        print("  %-14s %6d %9.3f %14.1f%%"
              % (name.replace("$", "").replace("\\", ""), len(z), r.max(),
                 100.0 * np.mean(np.abs(r - 1) < 1e-4)))
    print("written:", OUTP)


if __name__ == "__main__":
    main()
