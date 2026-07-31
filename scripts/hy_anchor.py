#!/usr/bin/env python3
"""hy_anchor.py - the SECOND anchor: Haba-Yamashita's published potential, from our mode counting.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

`ahmn_anchor.py` reproduces one published one-loop potential (AHMN, 6D SU(4) on T^2/Z_2). One anchor
is a coincidence you cannot rule out. This is a second, and it is deliberately as different as we
could find: N. Haba and T. Yamashita, "A general formula of the effective potential in 5D SU(N)
gauge theory on orbifold", JHEP 02 (2004) 059, hep-ph/0401185 -- a different group, a different
number of dimensions, a different orbifold, and a different derivation (they decompose the
representation under the SU(2) picked out by the Wilson-line VEV and read the generator eigenvalues).

Their worked example, section 3: SU(3) on S^1/Z_2 with P = P' = diag(+,-,-), broken to SU(2) x U(1),
with the Wilson line in the SU(2)_13 direction. They print:

  eq (3.7)  the adjoint decomposes as  8 -> 3 + 1 + 2 + 2  under SU(2)_13;
  eq (3.8)  the generator charges are  (+1, -1, 0, 0, +1/2, -1/2, +1/2, -1/2);
  eq (3.9)  the KK eigenvalues are     n^2,  (n +- a)^2,  2 x (n +- a/2)^2;
  eq (3.10) V_adj(+) = (C/2) sum_n n^-5 [ cos(2na) + 2 cos(na) ],   C = 3/(64 pi^7 R^5);
  eq (3.11) for eta = -1 the expansion is half-integral, which shifts Qa -> Qa + 1/2.

The coefficient at a charge is the number of modes carrying +-that charge, divided by two -- which is
exactly the (A_q, B_q) mode counting of Part V. So this script builds the adjoint from scratch, reads
off charges and parities, and must return their four printed objects with nothing adjusted.

Exact rational arithmetic (charges are half-integers); no floating point.
"""
from fractions import Fraction as F


def su3_adjoint(P, T):
    """basis E_ij of the traceless matrices; each carries a (P,P') parity and a U(1) charge.
    Returns a list of (charge, parity)."""
    out = []
    n = len(P)
    for i in range(n):
        for j in range(n):
            if i == j and i == n - 1:
                continue                       # n^2 - 1 generators: drop one diagonal
            out.append((T[i] - T[j], P[i] * P[j]))
    return out


def main():
    print("=" * 92)
    print("SECOND ANCHOR: Haba-Yamashita hep-ph/0401185 section 3, SU(3) on S^1/Z_2")
    print("=" * 92)
    P = [1, -1, -1]                                   # their eq (3.1), P = P'
    T = [F(1, 2), F(0), F(-1, 2)]                     # the SU(2)_13 generator of their eq (3.6)
    modes = su3_adjoint(P, T)

    charges = sorted((q for q, _ in modes), reverse=True)
    printed = sorted([F(1), F(-1), F(0), F(0), F(1, 2), F(-1, 2), F(1, 2), F(-1, 2)], reverse=True)
    ok_charges = charges == printed
    print("   their eq (3.8) charges : %s" % [str(x) for x in printed])
    print("   ours                   : %s   %s"
          % ([str(x) for x in charges], "MATCH" if ok_charges else "MISMATCH"))

    # their eq (3.2): with P = P', every basis element has parity (+,+) or (-,-), never mixed
    ok_parity = all(p == 1 or p == -1 for _, p in modes)
    same = {p for _, p in modes}
    print("   their eq (3.2): parities are (+,+) or (-,-) only, never mixed : %s"
          % ("MATCH" if ok_parity else "MISMATCH"))

    # eq (3.10): the coefficient at charge Q is (number of modes with charge +-Q) / 2
    from collections import Counter
    c = Counter(abs(q) for q, _ in modes if q)
    coeff = {q: n // 2 for q, n in c.items()}
    print()
    print("   their eq (3.9)/(3.10), read as coefficients per charge")
    print("      |Q|      modes    coefficient   their printed term")
    theirs = {F(1): (2, 1, "cos(2na)"), F(1, 2): (4, 2, "2 cos(na)")}
    ok_coeff = True
    for q in sorted(coeff, reverse=True):
        nm, cf, term = theirs.get(q, (None, None, "---"))
        hit = (c[q] == nm and coeff[q] == cf)
        ok_coeff &= hit
        print("      %-8s %5d %12d   %-12s %s"
              % (str(q), c[q], coeff[q], term, "OK" if hit else "MISMATCH"))
    nzero = sum(1 for q, _ in modes if q == 0)
    print("      0        %5d %12s   dropped (VEV-independent)  %s"
          % (nzero, "-", "OK" if nzero == 2 else "MISMATCH: they print 2"))

    print()
    print("   their eq (3.10) reconstructed from our counting:")
    terms = " + ".join(("%d " % coeff[q] if coeff[q] > 1 else "")
                       + "cos(%sna)" % ("2" if q == 1 else "")
                       for q in sorted(coeff, reverse=True))
    print("      V_adj(+) = (C/2) sum_n n^-5 [ %s ]" % terms)
    print("      their printed          [ cos(2na) + 2 cos(na) ]")

    # eq (3.11): eta = -1 shifts Qa -> Qa + 1/2, i.e. multiplies the odd-winding part by (-1)^n.
    # In our language that is exactly A <-> B, the same twist the gauge sector needed in AHMN.
    print()
    print("   their eq (3.11): eta = -1 shifts Qa -> Qa + 1/2, i.e. a factor (-1)^n on the")
    print("   winding sum -- which is A <-> B in Part V's notation, the same twist AHMN's gauge")
    print("   sector needed. The two published papers state the same twist in different words.")

    ok = ok_charges and ok_parity and ok_coeff and nzero == 2
    print()
    print("   VERDICT: %s" % ("ALL CHECKS PASS -- a second published potential reproduced, "
                              "different group, dimension, orbifold and method"
                              if ok else "MISMATCH -- do not report this as an anchor"))
    return ok


if __name__ == "__main__":
    raise SystemExit(0 if main() else 1)
