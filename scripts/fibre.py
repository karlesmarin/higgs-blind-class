#!/usr/bin/env python3
"""fibre.py - how much of the matter content is INVISIBLE to the Higgs potential?

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

The one-loop Wilson-line potential of an SU(4) multiplet is built from two Schur specialisations of
the same partition, one per O(4) component (HANDOFF.md, verified 18/18 against Part III):

    even winding  Sigma_lambda(t) = s_lambda(1, 1,t,1/t)      identity component
    odd  winding  D_lambda(t)     = s_lambda(1,-1,t,1/t)      reflection coset   <- Part IV's box

Every winding enters as the SAME pair of functions evaluated at t = exp(i pi theta), so two irreps
give the SAME potential at every alpha if and only if they share the pair (Sigma, D) as Laurent
polynomials.  The fibre of

    lambda  |-->  (Sigma_lambda, D_lambda)

is therefore exactly the observational equivalence class: everything inside one fibre is invisible
to any measurement of this Higgs sector at one loop.  This script measures it, and for contrast
measures the fibre of the odd half alone, which is what Part IV sees.

SU(4) irreps are partitions modulo a full column, so lambda_4 = 0 is one representative each.
Exact integer Laurent arithmetic throughout; no floating point anywhere.
"""
import collections
from itertools import combinations_with_replacement

# ---------------------------------------------------------------- Laurent polynomials over Z
def lmul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i + j] = out.get(i + j, 0) + x * y
    return {k: v for k, v in out.items() if v}


def ladd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def lscale(a, c):
    return {k: v * c for k, v in a.items() if v * c}


ONE = {0: 1}


def esym(alphabet):
    """elementary symmetric functions e_0..e_n of a list of Laurent polynomials"""
    e = [ONE]
    for x in alphabet:
        new = [dict(e[0])]
        for k in range(1, len(e) + 1):
            t = dict(e[k]) if k < len(e) else {}
            new.append(ladd(t, lmul(x, e[k - 1])))
        e = new
    return e


def schur(lam, alphabet, rows=4):
    """s_lambda by Jacobi-Trudi over the Laurent ring: det(h_{lam_i - i + j})"""
    L = list(lam) + [0] * (rows - len(lam))
    e = esym(alphabet)
    n = len(alphabet)
    hmax = max(L) + rows
    h = [ONE] + [{} for _ in range(hmax)]
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
        p, sgn = list(perm), 1
        for i in range(rows):
            for j in range(i + 1, rows):
                if p[i] > p[j]:
                    sgn = -sgn
        term = ONE
        for i in range(rows):
            term = lmul(term, M[i][perm[i]])
            if not term:
                break
        total = ladd(total, lscale(term, sgn))
    return total


def key(poly):
    return tuple(sorted(poly.items()))


T = {1: 1}
TI = {-1: 1}
EVEN = [ONE, ONE, T, TI]                 # (1, 1, t, 1/t)   identity component
ODD = [ONE, {0: -1}, T, TI]              # (1,-1, t, 1/t)   reflection coset


def main(MAX=12):
    irreps = [list(c)[::-1] + [0] for c in combinations_with_replacement(range(MAX + 1), 3)]
    irreps = [l for l in irreps if l[0] >= l[1] >= l[2]]
    print("SU(4) irreps with lambda_1 <= %d (lambda_4 = 0): %d\n" % (MAX, len(irreps)))

    both, odd_only = collections.defaultdict(list), collections.defaultdict(list)
    for lam in irreps:
        s_even, s_odd = schur(lam, EVEN), schur(lam, ODD)
        both[(key(s_even), key(s_odd))].append(tuple(lam))
        odd_only[key(s_odd)].append(tuple(lam))

    for name, fib in (("ODD half alone  (what Part IV sees)", odd_only),
                      ("BOTH halves     (the real observable)", both)):
        sizes = collections.Counter(len(v) for v in fib.values())
        print("%s" % name)
        print("   classes: %d      fibre sizes: %s"
              % (len(fib), dict(sorted(sizes.items()))))
        big = max(fib.values(), key=len)
        if len(big) > 1:
            print("   largest fibre (%d): %s%s"
                  % (len(big), big[:6], " ..." if len(big) > 6 else ""))
        print()

    nontrivial = {k: v for k, v in both.items() if len(v) > 1}
    print("VERDICT")
    if not nontrivial:
        print("   the pair (Sigma, D) separates every irrep in range: the potential determines")
        print("   the content, and there is nothing invisible to find.")
    else:
        tot = sum(len(v) for v in nontrivial.values())
        print("   %d classes hold %d irreps that NO measurement of this Higgs sector can tell"
              % (len(nontrivial), tot))
        print("   apart. Explicit invisible pairs:")
        for k, v in list(nontrivial.items())[:5]:
            print("      %s" % (v[:4],))
    return both, odd_only


if __name__ == "__main__":
    main()
