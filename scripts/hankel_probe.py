#!/usr/bin/env python3
"""hankel_probe.py - is our moment tower the same object Calisto-Cheung-Remmen-Sciotti-Tarquini invert?

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Their structure (arXiv:2604.15423, Eqs. 28-33): the EFT coefficients are a signed sum of geometric
sequences, c_k = sum_n sigma_n lambda_n^{1+k}; the Hankel matrix [c_r]_ij = c_{r+i+j} factorises as
Vandermonde * diagonal * Vandermonde^T, hence has rank d = number of terms; and the generalized
eigenvalue problem det(c^{(d)}_{r+1} - lambda c^{(d)}_r) = 0 returns the lambda_n.

Our tower is M_{2r} = sum_m m^{2r} delta(m) = sum_m delta(m) * (m^2)^r -- a signed sum of geometric
sequences with ratios m^2 and weights delta(m). So the claim to test, before saying it out loud:

  (1) rank of the Hankel matrix of (M_0, M_2, M_4, ...) = number of DISTINCT m^2 with delta(m) != 0;
  (2) the generalized eigenvalue problem returns exactly those m^2;
  (3) the recovered weights are the delta(m), summed over +-m.

Everything in exact rational arithmetic: our ratios are squares of integers, so unlike the EFT case
there is no conditioning question at all -- this either holds exactly or it fails.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement


def chi(k):
    return {k - 2 * i: 1 for i in range(k + 1)}


def conv(a, b):
    out = {}
    for m, x in a.items():
        for n, y in b.items():
            out[m + n] = out.get(m + n, 0) + x * y
    return out


def delta(p, q, r):
    return conv(conv(chi(p), chi(q)), chi(r))


def moments(d, upto):
    return [sum(m ** (2 * j) * v for m, v in d.items()) for j in range(upto + 1)]


def rank(M):
    M = [[F(x) for x in row] for row in M]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        f = M[r][c]
        M[r] = [x / f for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                g = M[i][c]
                M[i] = [x - g * y for x, y in zip(M[i], M[r])]
        r += 1
    return r


def charpoly_roots_int(H0, H1, candidates):
    """solve det(H1 - lambda H0) = 0 over the integer candidates, exactly"""
    n = len(H0)
    out = []
    for lam in candidates:
        M = [[F(H1[i][j]) - F(lam) * F(H0[i][j]) for j in range(n)] for i in range(n)]
        if rank(M) < n:
            out.append(lam)
    return out


def main():
    print("Is our moment tower a finite-rank Hankel object? -- exact test\n")
    print("  %-14s %6s %8s %8s   %s" % ("(p,q,r)", "d_true", "rankH", "match", "recovered m^2"))
    ok = True
    for (p, q, r) in [(1, 1, 1), (2, 1, 1), (3, 2, 1), (4, 3, 2), (2, 2, 2), (5, 3, 1), (0, 2, 3)]:
        dd = delta(p, q, r)
        supp = sorted({m * m for m, v in dd.items() if v != 0})
        d_true = len(supp)
        N = d_true + 3
        M = moments(dd, 2 * N)
        H = [[M[i + j] for j in range(N + 1)] for i in range(N + 1)]
        rk = rank(H)
        # the generalized eigenvalue problem on the d x d leading block
        H0 = [[M[i + j] for j in range(rk)] for i in range(rk)]
        H1 = [[M[i + j + 1] for j in range(rk)] for i in range(rk)]
        cand = sorted({m * m for m in range(0, p + q + r + 2)})
        roots = charpoly_roots_int(H0, H1, cand)
        good = (rk == d_true and roots == supp)
        ok &= good
        print("  %-14s %6d %8d %8s   %s" % ("(%d,%d,%d)" % (p, q, r), d_true, rk,
                                            "yes" if good else "NO", roots))
    print("\n  rank == number of distinct m^2, and the eigenvalues ARE those m^2:",
          "CONFIRMED" if ok else "*** FAILED ***")

    # what the physics question needs: does the box determine the content?
    print("\n  the kernel probe -- distinct (p,q,r) sharing a moment tower:")
    seen = {}
    coll = 0
    for t in combinations_with_replacement(range(0, 13), 3):
        key = tuple(moments(delta(*t), 6))
        if key in seen:
            print("      %s and %s share (M_0..M_6)" % (seen[key], t))
            coll += 1
        seen[key] = t
    print("      %d collisions among %d unordered triples" % (coll, len(seen) + coll))


if __name__ == "__main__":
    main()
