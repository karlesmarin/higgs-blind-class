#!/usr/bin/env python3
"""ghu_potential.py - the one-loop potential built from the VERIFIED characters, and validated
against AHMN's published vacuum and published Higgs mass matrix before it is used for anything.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

`ghu_oracle.py` assembled the potential from `mults()` with hand-set weights `Ng, Nf`. The Socratic
descent of GATE_AHMN_MASS.md §3b localised the fault there: the characters are right (the anchor
checks 12 of AHMN's printed numbers), the fall-off is right, the argument convention is right, and
the assembled total is nevertheless not theirs. So this module throws the assembly away and builds
the potential from the pair the rest of Part V is about.

For a multiplet lambda, with Sigma_lambda(t) = sum_j a_j t^j and D_lambda(t) = sum_j d_j t^j exact
integer Laurent polynomials, the physical charge of the exponent j is q = j/2 and

    A_j = (a_j + d_j)/2      parity-even mode count at that charge
    B_j = (a_j - d_j)/2      parity-odd  mode count

(both non-negative integers -- checked, 0 failures on 455 multiplets), and

    V(alpha) = sum_{k != 0} |k|^{-6} sum_{j>0} [A_j + B_j (-1)^{k_2}] cos(2 pi q_j (k1 a1 + k2 a2))

with fermions entering with `+` and the gauge/ghost sector with `-`, which is AHMN's own assembly
V = 3*(their 3.25) - (their 3.11).  Conventions fixed by reproducing their published vacuum.

NOTHING here is used until validate() passes.
"""
import math

from fibre import schur, EVEN, ODD

KMAX = int(__import__('os').environ.get('GHU_KMAX', 20))   # cheaper settings must REVALIDATE
ADJOINT = (2, 1, 1, 0)          # the SU(4) gauge multiplet


def modes(lam):
    """(charge, A, B) for a multiplet: the parity-even and parity-odd mode counts per charge"""
    S, D = schur(list(lam), EVEN), schur(list(lam), ODD)
    out = []
    for j in sorted(set(S) | set(D)):
        if j <= 0:
            continue                       # the spectrum is symmetric; j>0 with a factor 2 below
        a, d = S.get(j, 0), D.get(j, 0)
        A, B = (a + d) // 2, (a - d) // 2
        assert (a + d) % 2 == 0 and A >= 0 and B >= 0, (lam, j, a, d)
        out.append((j / 2.0, A, B))
    return out


def gauge_modes(lam=None):
    """The gauge/ghost sector carries the ANTIPERIODIC twist AHMN state in their text below their
    eq. (3.11), and that twist is exactly A <-> B. Leaving it out was the assembly bug: it moved
    their (8,3) at charge 1 to (9,2), and nothing else.  [ahmn_anchor.py recorded the twist and the
    assembly never applied it.]"""
    return [(q, B, A) for q, A, B in modes(lam or ADJOINT)]


_LATT = [(k1, k2) for k1 in range(-KMAX, KMAX + 1) for k2 in range(-KMAX, KMAX + 1)
         if (k1, k2) != (0, 0)]
_W = {k: (k[0] ** 2 + k[1] ** 2) ** -3.0 for k in _LATT}


def V(content, a1, a2, halves=False):
    """content = [(lambda, weight)]; weight > 0 fermionic, < 0 for the gauge sector.
    Returns V, or (V_identity, V_coset) if halves=True."""
    # the gauge sector (weight < 0) carries the antiperiodic twist: A <-> B
    spec = [(w, modes(lam) if w > 0 else gauge_modes(lam)) for lam, w in content]
    vi = vc = 0.0
    for (k1, k2) in _LATT:
        w = _W[(k1, k2)]
        th = k1 * a1 + k2 * a2
        odd = k2 % 2
        for wt, ms in spec:
            for q, A, B in ms:
                c = math.cos(2 * math.pi * q * th) * w * wt
                vi += A * c                       # A rides on the identity component
                vc += (-B if odd else B) * c      # B rides on the coset, with the (-1)^{k2}
    return (vi, vc) if halves else vi + vc


def minimise(content, N=int(__import__('os').environ.get('GHU_GRID', 100)), refine=(0.004, 0.001)):
    best = None
    for i in range(N + 1):
        for j in range(N + 1):
            a1, a2 = i / N, j / N
            v = V(content, a1, a2)
            if best is None or v < best[0]:
                best = (v, a1, a2)
    v0, A1, A2 = best
    for st in refine:
        moved = True
        while moved:
            moved = False
            for d1 in (-st, 0, st):
                for d2 in (-st, 0, st):
                    x, y = min(max(A1 + d1, 0.0), 1.0), min(max(A2 + d2, 0.0), 1.0)
                    v = V(content, x, y)
                    if v < v0 - 1e-12:
                        v0, A1, A2, moved = v, x, y, True
    return A1, A2


def hessian(content, a1, a2, h=0.002, part=None):
    def f(x, y):
        if part is None:
            return V(content, x, y)
        return V(content, x, y, halves=True)[part]
    fxx = (f(a1 + h, a2) - 2 * f(a1, a2) + f(a1 - h, a2)) / h ** 2
    fyy = (f(a1, a2 + h) - 2 * f(a1, a2) + f(a1, a2 - h)) / h ** 2
    fxy = (f(a1 + h, a2 + h) - f(a1 + h, a2 - h) - f(a1 - h, a2 + h)
           + f(a1 - h, a2 - h)) / (4 * h ** 2)
    return fxx, fyy, fxy


AHMN = [((4, 0, 0, 0), +3), (ADJOINT, -1)]      # their eq. (4.1) = 3 x (3.25) - (3.11)


def validate():
    """the instrument is not used until this passes"""
    print("=" * 92)
    print("validation against AHMN arXiv:2312.08608 -- vacuum and Higgs mass matrix")
    print("=" * 92)
    a1, a2 = minimise(AHMN)
    print("   vacuum  ours (%.3f, %.3f)   theirs (0.438, 0.299)   |delta| = (%.3f, %.3f)"
          % (a1, a2, abs(a1 - 0.438), abs(a2 - 0.299)))
    fxx, fyy, fxy = hessian(AHMN, a1, a2)
    print("   mass matrix, normalised to m11")
    print("      ours   : %8.4f %8.4f %8.4f" % (1.0, fyy / fxx, fxy / fxx))
    a, b, x = 0.0645, 0.0796, -0.0109
    print("      AHMN   : %8.4f %8.4f %8.4f" % (1.0, b / a, x / a))
    tr, dt = fxx + fyy, fxx * fyy - fxy * fxy
    disc = math.sqrt(max(tr * tr - 4 * dt, 0.0))
    l1, l2 = (tr - disc) / 2, (tr + disc) / 2
    ours = math.sqrt(l2 / l1) if l1 > 0 else float("nan")
    trT, dtT = a + b, a * b - x * x
    dT = math.sqrt(trT * trT - 4 * dtT)
    theirs = math.sqrt(((trT + dT) / 2) / ((trT - dT) / 2))
    print("   mass ratio  ours %.4f   theirs %.4f   discrepancy %.1f%%"
          % (ours, theirs, 100 * (ours / theirs - 1)))
    # The sign of m12 is the orientation of alpha_2: the mirror point (a1, 1-a2) has the same V
    # and the same eigenvalues with m12 reversed, so compare |m12| and demand the rest agree.
    # (The first version of this line demanded the signs be OPPOSITE and therefore passed on the
    # discrepancy it was written to catch. A guard that cannot fail is not a guard.)
    ok = (abs(a1 - 0.438) < 0.01 and min(abs(a2 - 0.299), abs(a2 - 0.701)) < 0.01
          and abs(fyy / fxx - b / a) < 0.02
          and abs(abs(fxy / fxx) - abs(x / a)) < 0.01
          and abs(ours / theirs - 1) < 0.01)
    print("\n   VERDICT: %s" % ("PASS -- the instrument may be used" if ok else
                                "FAIL -- do not use it for anything"))
    return ok


if __name__ == "__main__":
    validate()
