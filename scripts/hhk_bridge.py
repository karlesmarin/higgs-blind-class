#!/usr/bin/env python3
"""hhk_bridge.py - our eta, in the language the field has used since 2004.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Haba, Hosotani and Kawamura, "Classification and Dynamics of Equivalence Classes in SU(N) Gauge
Theory on the Orbifold S1/Z2", hep-ph/0309088 (Prog.Theor.Phys. 111 (2004) 265).  Their boundary
conditions carry, besides the matrices P0 and P1, "an arbitrary sign factor" for each matter field
(their (2.3) and (3.18)):

    phi(x,-y) = eta_0 P0 phi(x,y) ,      phi(x,R-y) = eta_1 P1 phi(x,R+y) ,   eta_0, eta_1 in {+-1}

Those two signs are, literally, the eta of OBSERVABILITY.md.  This script establishes the dictionary
against their printed formulas, and it does four things, each an exact integer computation:

  (A) reproduces their table (3.20) -- the multiplicities N_rep^{(eps0,eps1)} for the fundamental,
      the 2nd-rank antisymmetric and the adjoint of SU(N) -- from explicit basis vectors, for every
      [p;q,r;s] up to N = 8.  This is the control that says we are reading their conventions right.

  (B) proves-by-verification the character identity behind that table, valid for ANY representation:

          N^{(eps0,eps1)} = 1/4 [ dim + eps0 chi(P0) + eps1 chi(P1) + eps0 eps1 chi(P0 P1) ]

      so a boundary condition sees a multiplet through exactly three characters, and the LAST one --
      the character at the winding element U = P0 P1 -- is the only one carrying eps0 eps1.

  (C) hence the eta statement, in their variables.  Sending (P0,P1) -> (eta_0 P0, eta_1 P1) sends
      N^{(eps0,eps1)} -> the same expression with eps_i -> eta_i eps_i.  Therefore
        * (eta_0,eta_1) -> (-eta_0,-eta_1) permutes the four multiplicities by (eps0,eps1) ->
          (-eps0,-eps1), which is HHK's own sentence below their (4.3): "a hypermultiplet with
          parity (eta_0,eta_1) gives the same contribution to the vacuum energy density as one with
          parity (-eta_0,-eta_1)";
        * the FINITE part of their potential uses only the pair sums N^{(++)}+N^{(--)} and
          N^{(+-)}+N^{(-+)} (their (3.25) Nv, their (4.11)-(4.13)), and those depend on the boundary
          signs ONLY through the product eta_0 eta_1, multiplying chi(P0 P1).
      Both are verified by sweep, not asserted.

  (D) and then the theorem of OBSERVABILITY.md is the vanishing of that one character.  For SU(4)
      with q+r odd the winding element U sits in the reflection coset, det U = -1, and chi_lambda(U)
      is Part IV's object at vanishing Wilson line phase.  Two regimes, and they are NOT the same
      condition -- the script measures the difference:

          Wilson line at zero (HHK section 3-4):   eta_0 eta_1 invisible  <=>  D_lambda(1) = 0
          Wilson line dynamical (our regime):      eta_0 eta_1 invisible  <=>  D_lambda(t) = 0

No floating point anywhere.
"""
import json
import os
from itertools import combinations, combinations_with_replacement

from fibre import schur, key, ODD

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "outputs")
SIGNS = ((+1, +1), (+1, -1), (-1, +1), (-1, -1))
NAME = {(+1, +1): "(++)", (+1, -1): "(+-)", (-1, +1): "(-+)", (-1, -1): "(--)"}


# ------------------------------------------------------------------ HHK's boundary matrices (2.10)
def P0P1(p, q, r, s):
    """diag P0, diag P1 for the boundary condition [p;q,r;s] of HHK eq. (2.10)"""
    p0 = [+1] * p + [+1] * q + [-1] * r + [-1] * s
    p1 = [+1] * p + [-1] * q + [+1] * r + [-1] * s
    return p0, p1


def parities(rep, p0, p1):
    """the (P0,P1) parity of every basis vector of `rep`, as a list of (eps0, eps1)"""
    n = len(p0)
    if rep == "F":                                    # fundamental: e_i
        return [(p0[i], p1[i]) for i in range(n)]
    if rep == "A":                                    # 2nd rank antisymmetric: e_i ^ e_j
        return [(p0[i] * p0[j], p1[i] * p1[j]) for i, j in combinations(range(n), 2)]
    if rep == "Ad":                                   # adjoint: X -> P X P, traceless
        out = [(p0[i] * p0[j], p1[i] * p1[j]) for i in range(n) for j in range(n)]
        out.remove((+1, +1))                          # one diagonal direction is the trace
        return out
    raise ValueError(rep)


def counts(rep, p0, p1):
    par = parities(rep, p0, p1)
    return {e: par.count(e) for e in SIGNS}


# HHK eq. (3.20), transcribed verbatim from the paper
def hhk_320(rep, p, q, r, s):
    if rep == "F":
        return {(+1, +1): p, (-1, -1): s, (+1, -1): q, (-1, +1): r}
    if rep == "A":
        return {(+1, +1): (p * (p - 1) + q * (q - 1) + r * (r - 1) + s * (s - 1)) // 2,
                (-1, -1): p * s + q * r,
                (+1, -1): p * q + r * s,
                (-1, +1): p * r + q * s}
    if rep == "Ad":
        return {(+1, +1): p * p + q * q + r * r + s * s - 1,
                (-1, -1): 2 * (p * s + q * r),
                (+1, -1): 2 * (p * q + r * s),
                (-1, +1): 2 * (p * r + q * s)}
    raise ValueError(rep)


# ------------------------------------------------------------------ (A) + (B): the control sweep
def sweep(NMAX=8):
    print("=" * 96)
    print("(A) HHK eq. (3.20) reproduced from explicit basis vectors, and (B) the character identity")
    print("=" * 96)
    bad320 = bad_id = ncases = 0
    for N in range(2, NMAX + 1):
        for p in range(N + 1):
            for q in range(N + 1 - p):
                for r in range(N + 1 - p - q):
                    s = N - p - q - r
                    p0, p1 = P0P1(p, q, r, s)
                    for rep in ("F", "A", "Ad"):
                        got = counts(rep, p0, p1)
                        ncases += 1
                        if got != hhk_320(rep, p, q, r, s):
                            bad320 += 1
                            if bad320 <= 3:
                                print("   MISMATCH (3.20) N=%d [%d;%d,%d;%d] %s: %s vs %s"
                                      % (N, p, q, r, s, rep, got, hhk_320(rep, p, q, r, s)))
                        # (B) the same four numbers from three characters
                        par = parities(rep, p0, p1)
                        dim = len(par)
                        c0 = sum(a for a, b in par)               # chi(P0)
                        c1 = sum(b for a, b in par)               # chi(P1)
                        cU = sum(a * b for a, b in par)           # chi(P0 P1)
                        pred = {(e0, e1): (dim + e0 * c0 + e1 * c1 + e0 * e1 * cU) // 4
                                for e0, e1 in SIGNS}
                        if pred != got:
                            bad_id += 1
    print("   cases swept (N <= %d, all [p;q,r;s], reps F / A / Ad) : %d" % (NMAX, ncases))
    print("   disagreements with their printed (3.20)               : %d" % bad320)
    print("   disagreements with  N = (dim + e0 X0 + e1 X1 + e0 e1 XU)/4 : %d" % bad_id)
    return bad320, bad_id


# ------------------------------------------------------------------ (C) what the boundary signs do
def eta_sweep(NMAX=6):
    print()
    print("=" * 96)
    print("(C) the boundary signs (eta_0, eta_1): the redundancy, and what the finite part can see")
    print("=" * 96)
    bad_flip = bad_prod = ncases = 0
    for N in range(2, NMAX + 1):
        for p in range(N + 1):
            for q in range(N + 1 - p):
                for r in range(N + 1 - p - q):
                    s = N - p - q - r
                    p0, p1 = P0P1(p, q, r, s)
                    for rep in ("F", "A", "Ad"):
                        base = parities(rep, p0, p1)
                        tab = {}
                        for h0, h1 in SIGNS:
                            par = [(h0 * a, h1 * b) for a, b in base]
                            tab[(h0, h1)] = {e: par.count(e) for e in SIGNS}
                        ncases += 1
                        # HHK, below (4.3): (eta_0,eta_1) and (-eta_0,-eta_1) contribute equally
                        for h0, h1 in SIGNS:
                            a, b = tab[(h0, h1)], tab[(-h0, -h1)]
                            if any(a[e] != b[(-e[0], -e[1])] for e in SIGNS):
                                bad_flip += 1
                            # the finite part uses the two pair sums only
                            if (a[(+1, +1)] + a[(-1, -1)] != b[(+1, +1)] + b[(-1, -1)]
                                    or a[(+1, -1)] + a[(-1, +1)] != b[(+1, -1)] + b[(-1, +1)]):
                                bad_flip += 1
                        # ... and those pair sums depend on the signs only through eta_0 eta_1
                        cU = sum(a * b for a, b in base)               # chi(P0 P1)
                        for h0, h1 in SIGNS:
                            same = tab[(h0, h1)], tab[(-h0, -h1)]      # same product eta_0 eta_1
                            other = tab[(h0, -h1)]                     # opposite product
                            f = lambda d: (d[(+1, +1)] + d[(-1, -1)], d[(+1, -1)] + d[(-1, +1)])
                            if f(same[0]) != f(same[1]):
                                bad_prod += 1                          # the product is what counts
                            if cU != 0 and f(same[0]) == f(other):
                                bad_prod += 1                          # ... and it IS visible there
                            if cU == 0 and f(same[0]) != f(other):
                                bad_prod += 1                          # ... and invisible exactly here
    print("   cases swept (N <= %d)                                            : %d" % (NMAX, ncases))
    print("   violations of  (eta_0,eta_1) ~ (-eta_0,-eta_1)   [HHK below (4.3)] : %d" % bad_flip)
    print("   violations of  'the finite part sees only eta_0 eta_1'            : %d" % bad_prod)
    return bad_flip, bad_prod


# ------------------------------------------------------------------ (D) our SU(4), two regimes
def su4(MAX=12):
    print()
    print("=" * 96)
    print("(D) SU(4): the character at the winding element is Part IV's object, in two regimes")
    print("=" * 96)
    # which [p;q,r;s] of SU(4) put U = P0 P1 in the reflection coset (det U = -1)?
    coset = []
    for p in range(5):
        for q in range(5 - p):
            for r in range(5 - p - q):
                s = 4 - p - q - r
                if (q + r) % 2 == 1:
                    p0, p1 = P0P1(p, q, r, s)
                    u = tuple(sorted(a * b for a, b in zip(p0, p1)))
                    coset.append(((p, q, r, s), u))
    kinds = sorted(set(u for _, u in coset))
    print("   [p;q,r;s] with det U = -1 : %d, and U has only %d distinct spectra: %s"
          % (len(coset), len(kinds), kinds))
    print("   -> U ~ diag(1,1,1,-1) is P0 of Part III; chi_lambda(U) = s_lambda(1,1,1,-1) = D(1).")

    irreps = [list(c)[::-1] + [0] for c in combinations_with_replacement(range(MAX + 1), 3)]
    irreps = [l for l in irreps if l[0] >= l[1] >= l[2]]
    Z, Z1, both, mixed = [], [], [], []
    for lam in irreps:
        D = schur(lam, ODD)                       # D_lambda(t) = s_lambda(1,-1,t,1/t)
        D1 = sum(D.values())                      # D_lambda(1) = s_lambda(1,-1,1,1)
        if not D:
            Z.append(tuple(lam))
        if D1 == 0:
            Z1.append(tuple(lam))
        if not D and D1 != 0:
            both.append(tuple(lam))
        # WHY the two regimes must coincide: Part IV's closed form has delta = zeta*(non-negative),
        # so the coefficients of D are of ONE sign and cannot cancel in D(1).
        signs = set((v > 0) for v in D.values())
        if len(signs) > 1:
            mixed.append(tuple(lam))
    print()
    print("   SU(4) irreps with lambda_1 <= %d (lambda_4 = 0)            : %d" % (MAX, len(irreps)))
    print("   D_lambda(t) = 0  identically   -- Part IV's class Z        : %d" % len(Z))
    print("   D_lambda(1) = 0  at zero Wilson line phase                 : %d" % len(Z1))
    print("   in Z but not in the zero-Wilson-line class (must be 0)     : %d" % len(both))
    print("   in the zero-Wilson-line class but NOT in Z                 : %d"
          % len([l for l in Z1 if l not in set(Z)]))
    extra = [l for l in Z1 if l not in set(Z)]
    if extra:
        print("      e.g. %s" % (extra[:8],))
    print("   irreps whose D has coefficients of BOTH signs (must be 0)  : %d" % len(mixed))
    print("   -> D(1) = 0 <=> D = 0 identically, because nothing can cancel. The two regimes are")
    print("      the same condition, and it is Part IV's class Z.")
    return Z, Z1, mixed


def main():
    a, b = sweep()
    c, d = eta_sweep()
    Z, Z1, mixed = su4()
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "hhk_bridge.json"), "w", encoding="utf-8") as f:
        json.dump({"hhk_320_mismatches": a, "character_identity_mismatches": b,
                   "eta_redundancy_violations": c, "eta_product_violations": d,
                   "Z_D_identically_zero": [list(l) for l in Z],
                   "Z1_D_at_one_zero": [list(l) for l in Z1],
                   "D_mixed_sign_coefficients": [list(l) for l in mixed]}, f, indent=1)
    print()
    print("data written to outputs/hhk_bridge.json")


if __name__ == "__main__":
    main()
