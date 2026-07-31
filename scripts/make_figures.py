#!/usr/bin/env python3
"""make_figures.py - the figures of Part V, drawn from the archived sweep and nothing else.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Reads outputs/fibre_eta.json (455 SU(4) irreps, exact integer Laurent characters; never recomputed)
and writes paper/fig_blindclass.pdf.

  left  (3D)  every irrep at its Dynkin-like coordinates (lambda_1, lambda_2, lambda_3), coloured by
              the MAGNITUDE |D_lambda(1)| on a log scale -- one hue, light to dark, because the job
              of the colour is magnitude.  The multiplets of Z, where D vanishes identically and the
              boundary-condition sign is invisible, are drawn as a separate class in the paper's
              accent colour: identity, not magnitude, so it does not sit on the ramp.
  right (2D)  the same set projected on (lambda_1, lambda_2): how many lambda_3 give a blind
              multiplet.  Same single hue for the counts.  This is what shows the blind class is a
              structured surface and not scattered dust.

Both panels use the paper's own colours: hdrblue (31,78,121) as the ramp endpoint and warmred
(178,34,34) as the accent.
"""
import json
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap, LogNorm
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "outputs", "fibre_eta.json")
# --es: the Spanish edition of the paper gets its own figure, as in Parts III and IV
ES = "--es" in sys.argv


def T(en, es):
    return es if ES else en


OUTP = os.path.join(HERE, "paper", "fig_blindclass_es.pdf" if ES else "fig_blindclass.pdf")

HDRBLUE = (31 / 255, 78 / 255, 121 / 255)
WARMRED = (178 / 255, 34 / 255, 34 / 255)
RAMP = LinearSegmentedColormap.from_list("hdr", ["#eef2f7", "#9db9d4", HDRBLUE])


def main():
    d = json.load(open(DATA, encoding="utf-8"))
    Z = {tuple(l) for l in d["vanishing_class_Z"]}

    lam, val = [], []
    for key, ch in d["characters"].items():
        l = tuple(json.loads(key))
        lam.append(l)
        val.append(abs(sum(c for _, c in ch["D"])))          # |D_lambda(1)|
    lam, val = np.array(lam), np.array(val, dtype=float)
    blind = np.array([tuple(l) in Z for l in map(tuple, lam)])
    assert blind.sum() == len(Z) == 47, (blind.sum(), len(Z))
    assert (val[blind] == 0).all(), "a multiplet of Z with D(1) != 0"
    assert (val[~blind] > 0).all(), "a multiplet outside Z with D(1) == 0"

    fig = plt.figure(figsize=(9.3, 4.0))

    # ---------------------------------------------------------------- left: the lattice in 3D
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    v = lam[~blind]
    s = ax.scatter(v[:, 0], v[:, 1], v[:, 2], c=val[~blind], cmap=RAMP,
                   norm=LogNorm(vmin=1, vmax=val.max()), s=13, linewidths=0.2,
                   edgecolors="white", depthshade=False)
    b = lam[blind]
    ax.scatter(b[:, 0], b[:, 1], b[:, 2], color=WARMRED, s=34, marker="o",
               edgecolors="white", linewidths=0.6, depthshade=False,
               label=T(r"$D_\lambda \equiv 0$:  $\eta$ invisible   (47 of 455)",
                       r"$D_\lambda \equiv 0$:  $\eta$ invisible   (47 de 455)"))
    ax.set_xlabel(r"$\lambda_1$", labelpad=-2, fontsize=10.5)
    ax.set_ylabel(r"$\lambda_2$", labelpad=-2, fontsize=10.5)
    ax.set_zlabel(r"$\lambda_3$", labelpad=-5, fontsize=10.5)
    ax.tick_params(labelsize=8.5, pad=-1)
    ax.set_title(T(r"the 455 multiplets, coloured by $|D_\lambda(1)|$",
                   r"los 455 multipletes, coloreados por $|D_\lambda(1)|$"), fontsize=11, pad=-2)
    ax.view_init(elev=20, azim=-58)
    ax.legend(loc="upper left", fontsize=9, frameon=False, bbox_to_anchor=(-0.02, 0.98))
    cb = fig.colorbar(s, ax=ax, pad=0.09, shrink=0.62, aspect=16)
    cb.set_label(r"$|D_\lambda(1)| = |n_+ - n_-|$", fontsize=9.5)
    cb.ax.tick_params(labelsize=8.5)

    # ---------------------------------------------------------------- right: the projection in 2D
    ax2 = fig.add_subplot(1, 2, 2)
    L = int(lam[:, 0].max())
    grid = np.full((L + 1, L + 1), np.nan)
    for l1 in range(L + 1):
        for l2 in range(l1 + 1):
            m = (lam[:, 0] == l1) & (lam[:, 1] == l2)
            if m.any():
                grid[l2, l1] = blind[m].sum()
    im = ax2.imshow(grid, origin="lower", cmap=RAMP, vmin=0, vmax=np.nanmax(grid),
                    interpolation="nearest")
    for l1 in range(L + 1):
        for l2 in range(l1 + 1):
            n = grid[l2, l1]
            if not np.isnan(n) and n > 0:
                ax2.text(l1, l2, "%d" % n, ha="center", va="center", fontsize=8,
                         color="white" if n > np.nanmax(grid) * 0.55 else "#26323d")
    ax2.set_xlabel(r"$\lambda_1$", fontsize=11, labelpad=20)
    ax2.set_ylabel(r"$\lambda_2$", fontsize=11)
    ax2.set_title(T(r"blind multiplets per $(\lambda_1,\lambda_2)$, over all $\lambda_3$",
                    r"multipletes ciegos por $(\lambda_1,\lambda_2)$, sobre todo $\lambda_3$"),
                  fontsize=11)
    ax2.set_xticks(range(0, L + 1, 2))
    ax2.set_yticks(range(0, L + 1, 2))
    ax2.tick_params(labelsize=8.5)
    for sp in ax2.spines.values():
        sp.set_color("#c8d1da")
    # The regularity this panel exists to show: every populated column has lambda_1 odd. Marked
    # UNDER the axis, where a reader cannot mistake the mark for the shading of a cell.
    for l1 in range(L + 1):
        col = grid[:, l1]
        if np.nansum(col) > 0:
            ax2.plot([l1], [-1.4], marker="v", color=WARMRED, markersize=4.5, clip_on=False)
    ax2.text(-0.5, -3.9, T(r"$\lambda_1$ odd: the only columns holding a blind multiplet",
                           r"$\lambda_1$ impar: las únicas columnas con multiplete ciego"),
             fontsize=8.5, color=WARMRED)
    ax2.set_ylim(-0.5, L + 0.5)
    cb2 = fig.colorbar(im, ax=ax2, pad=0.02, shrink=0.86, aspect=18)
    cb2.set_label(T("count", "recuento"), fontsize=9.5)
    cb2.ax.tick_params(labelsize=8.5)

    fig.tight_layout(w_pad=2.4)
    fig.savefig(OUTP, bbox_inches="tight")
    fig.savefig(OUTP.replace(".pdf", ".png"), dpi=150, bbox_inches="tight")
    print("irreps %d   blind %d   max |D(1)| %d" % (len(lam), blind.sum(), val.max()))
    print("blind per lambda_1 :", {int(k): int((blind & (lam[:, 0] == k)).sum())
                                   for k in range(L + 1)})
    print("written:", OUTP)


if __name__ == "__main__":
    main()
