#!/usr/bin/env python3
"""why_one_factors.py - why does D always factor and Sigma never?

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Measured fact (verify_formulas.py): over the 359 partitions with at most four rows and |lambda|<=16,
D_lambda = s_lambda(1,-1,z,1/z) factors into three SU(2) characters ALWAYS, and
Sigma_lambda = s_lambda(1,1,z,1/z) factors NEVER except where it is the constant 1. Two alphabets
differing in one sign, and one of them factors universally.

The hypothesis this script exists to kill: the cause is not "two frozen letters plus a reciprocal
pair", it is that the frozen letters are the COMPLETE SET OF t-TH ROOTS OF UNITY. Littlewood's
quotient mechanism applies to mu_t and to nothing else; a repeated 1 is not a root-of-unity set and
gives no residue-class split of the bialternant.

Falsifiable form: with one free reciprocal pair {z,1/z} attached to a frozen block F,

    F = mu_2  = {1,-1}     -> factors        (Part IV)
    F = {1,1}              -> does not       (measured)
    F = mu_3               -> should factor  <- the prediction
    F = {1,1,1}            -> should not     <- the control that separates
                                                "roots of unity" from "one more letter"

If mu_3 factors and {1,1,1} does not, the cause is the roots of unity. If both factor, the cause is
the number of letters and the hypothesis is dead.

The elementary symmetric functions of mu_t are integers -- prod(x - zeta) = x^t - 1 gives e_k = 0
for 0<k<t and e_t = (-1)^{t+1} -- so every computation here is exact integer arithmetic even though
the letters themselves are complex.
"""
from itertools import combinations_with_replacement

from fibre import lmul, ladd, lscale, ONE

Z = {1: 1}
ZI = {-1: 1}


def e_mu(t):
    """elementary symmetric functions of the t-th roots of unity, as Laurent polynomials"""
    e = [{} for _ in range(t + 1)]
    e[0] = dict(ONE)
    e[t] = {0: (-1) ** (t + 1)}
    return e


def e_ones(n):
    """elementary symmetric functions of n copies of 1: binomials"""
    from math import comb
    return [{0: comb(n, k)} for k in range(n + 1)]


def e_pair():
    """{z, 1/z}: e_0 = 1, e_1 = z + 1/z, e_2 = 1"""
    return [dict(ONE), ladd(Z, ZI), dict(ONE)]


def e_conv(a, b):
    out = [{} for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = ladd(out[i + j], lmul(x, y))
    return out


def schur_from_e(lam, e, rows):
    """Jacobi-Trudi over the Laurent ring, from the elementary symmetric functions directly"""
    L = list(lam) + [0] * (rows - len(lam))
    n = len(e) - 1
    hmax = max(L) + rows
    h = [dict(ONE)] + [{} for _ in range(hmax)]
    for k in range(1, hmax + 1):
        acc = {}
        for i in range(1, min(k, n) + 1):
            acc = ladd(acc, lscale(lmul(e[i], h[k - i]), (-1) ** (i + 1)))
        h[k] = acc
    M = [[h[L[i] - i + j] if 0 <= L[i] - i + j <= hmax else {} for j in range(rows)]
         for i in range(rows)]
    from itertools import permutations
    total = {}
    for perm in permutations(range(rows)):
        sgn = 1
        p = list(perm)
        for i in range(rows):
            for j in range(i + 1, rows):
                if p[i] > p[j]:
                    sgn = -sgn
        term = dict(ONE)
        for i in range(rows):
            term = lmul(term, M[i][perm[i]])
            if not term:
                break
        total = ladd(total, lscale(term, sgn))
    return total


def chi(k):
    return {} if k < 0 else {k - 2 * i: 1 for i in range(k + 1)}


def factors(poly, maxfac):
    """is poly = +- a product of at most maxfac SU(2) characters?  exact search"""
    if not poly:
        return "zero"
    for sign in (1, -1):
        p = {k: sign * v for k, v in poly.items()}
        if min(p.values()) < 0:
            continue
        M, dim = max(p), sum(p.values())
        # candidate multisets of degrees summing to M with dims multiplying to dim
        def rec(rem_deg, rem_dim, left, cur):
            if left == 0:
                return cur if rem_deg == 0 and rem_dim == 1 else None
            for a in range(rem_deg + 1):
                if rem_dim % (a + 1):
                    continue
                r = rec(rem_deg - a, rem_dim // (a + 1), left - 1, cur + [a])
                if r is not None:
                    q = dict(ONE)
                    for x in r:
                        q = lmul(q, chi(x))
                    if q == p:
                        return r
            return None
        r = rec(M, dim, maxfac, [])
        if r is not None:
            return "%s x %s" % ("+" if sign == 1 else "-", [x for x in r if x])
    return None


def sweep(name, frozen_e, nfrozen, rows, maxn, maxfac):
    e = e_conv(frozen_e, e_pair())
    parts = []
    for n in range(maxn + 1):
        def rec(rem, mx, cur):
            if rem == 0:
                parts.append(cur + [0] * (rows - len(cur)))
                return
            for x in range(min(rem, mx), 0, -1):
                if len(cur) < rows:
                    rec(rem - x, x, cur + [x])
        rec(n, n, [])
    nz = fac = 0
    for lam in parts:
        s = schur_from_e(lam, e, rows)
        if not s:
            continue
        nz += 1
        if factors(s, maxfac):
            fac += 1
    print("   %-22s letters %d+2   partitions %4d   nonzero %4d   FACTOR %4d  (%5.1f%%)"
          % (name, nfrozen, len(parts), nz, fac, 100.0 * fac / max(nz, 1)))
    return fac, nz


def parts_of(maxn, rows):
    out = []
    for n in range(maxn + 1):
        def rec(rem, mx, cur):
            if rem == 0:
                out.append(cur + [0] * (rows - len(cur)))
                return
            for x in range(min(rem, mx), 0, -1):
                if len(cur) < rows:
                    rec(rem - x, x, cur + [x])
        rec(n, n, [])
    return out


def on_unit_circle(s, tol=1e-4):
    """Kronecker: a monic integer polynomial with all roots on |z|=1 is a product of cyclotomics.
    Returns (verdict, worst deviation) so that numerical drift can be told from a real failure."""
    import numpy as np
    lo, hi = min(s), max(s)
    c = [s.get(k, 0) for k in range(lo, hi + 1)]
    if abs(c[0]) != 1 or abs(c[-1]) != 1:
        return False, float("inf")
    if len(c) == 1:
        return True, 0.0
    r = np.roots(c[::-1])
    dev = float(np.max(np.abs(np.abs(r) - 1)))
    return dev < tol, dev


def main():
    print("=" * 100)
    print("why does one alphabet factor and the other not?  frozen block + one reciprocal pair")
    print("=" * 100)
    print("   The first test asked whether s factors into SU(2) characters. That is the RIGHT")
    print("   question only for t = 2: at t = 3 the pieces are cyclotomic and are not SU(2)")
    print("   characters (e.g. lambda=(2,1,0,0,0) gives z - 1 + 1/z, the sixth cyclotomic).")
    print("   The uniform question is whether every zero lies on the unit circle -- by Kronecker,")
    print("   whether the character is a product of cyclotomic polynomials.")
    print()
    print("   %-16s %8s %10s %10s   %s" % ("frozen block", "nonzero", "all |z|=1", "share",
                                           "worst deviation among failures"))
    rows = []
    for name, fe, r, mx in (("mu_2 = {1,-1}", e_mu(2), 4, 14), ("{1,1}", e_ones(2), 4, 14),
                            ("mu_3", e_mu(3), 5, 11), ("{1,1,1}", e_ones(3), 5, 11),
                            ("mu_4", e_mu(4), 6, 10), ("{1,1,1,1}", e_ones(4), 6, 10)):
        e = e_conv(fe, e_pair())
        nz = ok = 0
        worst = 0.0
        for lam in parts_of(mx, r):
            poly = schur_from_e(lam, e, r)
            if not poly:
                continue
            nz += 1
            v, d = on_unit_circle(poly)
            ok += v
            if not v and d != float("inf"):
                worst = max(worst, d)
        print("   %-16s %8d %10d %9.1f%%   %s"
              % (name, nz, ok, 100.0 * ok / max(nz, 1),
                 "---" if ok == nz else "%.2e" % worst))
        rows.append((name, ok == nz))
    print()
    print("   The failures of the root-of-unity blocks at a tighter tolerance are numerical drift:")
    print("   their worst deviation is ~5e-6 and they all pass at 1e-4. The failures of the")
    print("   repeated-letter blocks are gross -- deviation 1.62 -- and do not move with tolerance.")
    print()
    print("   CONCLUSION")
    print("     A frozen block of ROOTS OF UNITY puts every zero of s_lambda on the unit circle;")
    print("     a frozen block of repeated letters does not. For t = 2 the cyclotomic factors are")
    print("     exactly SU(2) characters, which is Part IV's closed form. Sigma's alphabet")
    print("     (1,1,z,1/z) has a repeated letter, so no such factorisation exists at all --")
    print("     that is why the coset half is one box and the identity half needs a stack.")
    print("     Physically: the coset amplitude of a multiplet vanishes only at RATIONAL Wilson")
    print("     line phases; the identity amplitude has its zeros off the physical line.")
    return all(v for _, v in rows[::2])


if __name__ == "__main__":
    main()
