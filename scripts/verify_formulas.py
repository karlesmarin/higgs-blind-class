#!/usr/bin/env python3
"""verify_formulas.py - every displayed formula of Part V against an exact computation.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

The paper carries fifteen labelled equations. Several of them were checked once, in a Sage session
or inline, and their evidence never reached `outputs/`. This script re-derives what can be re-derived
in exact integer arithmetic and archives one output for all of it, so that no equation in the paper
rests on a memory of having checked it.

Each block prints its own counts and its own verdict. A block that cannot fail is not a check, so
where a claim is definitional it says so instead of pretending to test it.
"""
from itertools import combinations_with_replacement

from fibre import schur, EVEN, ODD, ONE, lmul, ladd, lscale

RANGE = 10                      # lambda_1 <= RANGE, lambda_4 = 0


def irreps(m=RANGE):
    out = [list(c)[::-1] + [0] for c in combinations_with_replacement(range(m + 1), 3)]
    return [l for l in out if l[0] >= l[1] >= l[2]]


def chi(k):
    """SU(2) character chi_k(t) = t^k + t^{k-2} + ... + t^{-k}; chi_{-1} = 0"""
    if k < 0:
        return {}
    return {k - 2 * i: 1 for i in range(k + 1)}


def to_su2(poly):
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


def dual(l):
    return [l[0] - l[3], l[0] - l[2], l[0] - l[1], 0]


def line(tag, eq, bad, n, note=""):
    print("   %-9s %-16s %6d / %-6d %s %s"
          % (tag, eq, n - bad, n, "PASS" if bad == 0 else "FAIL(%d)" % bad, note))
    return bad


def main():
    L = irreps()
    print("=" * 96)
    print("Part V: every displayed equation against an exact computation")
    print("   range: SU(4) irreps with lambda_1 <= %d, lambda_4 = 0  ->  %d multiplets"
          % (RANGE, len(L)))
    print("=" * 96)
    print("   %-9s %-16s %-15s %s" % ("eq", "what", "checks passed", "verdict"))
    fails = 0

    # ---- (1) the root: U_6 = P_2 P_0^{-1}, and the three determinants
    p0, p2 = [1, 1, 1, -1], [1, 1, -1, -1]
    u6 = [a * b for a, b in zip(p2, p0)]          # P_0^{-1} = P_0
    d = lambda v: v[0] * v[1] * v[2] * v[3]
    bad = int(u6 != [1, 1, -1, 1] or d(p0) != -1 or d(p2) != 1 or d(u6) != -1)
    fails += line("(1),(2)", "root, dets", bad, 1, "det P0=-1, det P2=+1, det U6=-1")

    # ---- (4) the two alphabets have det +1 and -1
    bad = int(1 * 1 * 1 * 1 != 1 or 1 * (-1) * 1 * 1 != -1)
    fails += line("(4)", "alphabets", bad, 1, "definitional: (1,1,t,1/t) and (1,-1,t,1/t)")

    # ---- (10) s_{lambda*}(A) = det(A)^{lambda_1} s_lambda(A), on both alphabets
    bad = 0
    for l in L:
        dl = dual(l)
        if dl[0] > RANGE:
            continue
        if schur(dl, EVEN) != schur(l, EVEN):
            bad += 1
        s, o = schur(dl, ODD), schur(l, ODD)
        if s != ({k: -v for k, v in o.items()} if l[0] % 2 else o):
            bad += 1
    fails += line("(10)", "conjugation", bad, 2 * len(L), "Sigma fixed, D by (-1)^{lambda_1}")

    # ---- (8) eta acts as (Sigma, D) -> (Sigma, eta D): the det twist lambda -> lambda+(1,1,1,1)
    bad = 0
    for l in L:
        tw = [x + 1 for x in l]
        if schur(tw, EVEN) != schur(l, EVEN):
            bad += 1
        if schur(tw, ODD) != {k: -v for k, v in schur(l, ODD).items()}:
            bad += 1
    fails += line("(8)", "the det twist", bad, 2 * len(L), "same irrep; D flips, Sigma does not")

    # ---- (9) A = (Sigma+D)/2 and B = (Sigma-D)/2 are non-negative integers (mode counts)
    bad = tot = 0
    for l in L:
        S, D = schur(l, EVEN), schur(l, ODD)
        for j in set(S) | set(D):
            a, b = S.get(j, 0), D.get(j, 0)
            tot += 2
            bad += ((a + b) % 2 != 0 or a + b < 0) + ((a - b) % 2 != 0 or a - b < 0)
    fails += line("(9)", "A,B mode counts", bad, tot, "non-negative integers at every charge")

    # ---- (6) Sigma_chi = n+ + n-, D_chi = n+ - n-: the halves of (6) must be multiplicities
    bad = tot = 0
    for l in L:
        S, D = to_su2(schur(l, EVEN)), to_su2(schur(l, ODD))
        for m in set(S) | set(D):
            a, b = S.get(m, 0), D.get(m, 0)
            tot += 2
            bad += ((a + b) % 2 != 0 or a + b < 0) + ((a - b) % 2 != 0 or a - b < 0)
    fails += line("(6)", "dimension/index", bad, tot, "(Sigma_chi +- D_chi)/2 in Z_{>=0}")

    # ---- (7) n+_m - n-_m = zeta c_m with c_m >= 0: D's SU(2) coefficients are of ONE sign
    bad = 0
    for l in L:
        v = to_su2(schur(l, ODD)).values()
        if len({x > 0 for x in v}) > 1:
            bad += 1
    fails += line("(7)", "one sign", bad, len(L), "no D has coefficients of both signs")

    # ---- Part IV's closed form, which (5) rests on: |D| = |chi_a chi_b chi_c|
    bad = tested = 0
    for l in L:
        beta = [l[0] + 3, l[1] + 2, l[2] + 1, l[3]]
        E = sorted([b for b in beta if b % 2 == 0], reverse=True)
        O = sorted([b for b in beta if b % 2 == 1], reverse=True)
        D = schur(l, ODD)
        if not E or not O:
            bad += int(bool(D))                       # must vanish
            tested += 1
            continue
        if len(E) == 2:
            A, B = E, O
        elif len(O) == 2:
            A, B = O, E
        else:                                          # 3+1: overlapping pairs from the big class
            big = E if len(E) == 3 else O
            A, B = [big[0], big[1]], [big[1], big[2]]
        d1, d2 = A[0] - A[1], B[0] - B[1]
        d3 = abs(A[0] + A[1] - B[0] - B[1])
        prod = lmul(lmul(chi(d1 // 2 - 1), chi(d2 // 2 - 1)), chi(d3 // 2 - 1))
        tested += 1
        if {k: abs(v) for k, v in D.items()} != {k: abs(v) for k, v in prod.items()}:
            bad += 1
    fails += line("(5)", "Part IV closed form", bad, tested, "|D| = |chi chi chi| off the beta-set")

    # ---- (11) the identity-half positive stack, WITH the range our notes never recorded.
    # Determined by testing candidates, not assumed: 0 <= q <= p <= lambda_1, skipping any term
    # with a negative block index. Two natural-looking alternatives fail on 56 of 84.
    bad = 0
    for l in L:
        tot = {}
        for p in range(l[0] + 1):
            for q in range(p + 1):
                m1, m2 = l[0] - max(p, l[1]), min(p, l[1]) - max(q, l[2])
                m3 = min(q, l[2]) - l[3]
                if m1 < 0 or m2 < 0 or m3 < 0:
                    continue
                b = lmul(lmul(chi(m1), chi(m2)), chi(m3))
                for k, v in b.items():
                    tot[k] = tot.get(k, 0) + (p - q + 1) * v
        if {k: v for k, v in tot.items() if v} != schur(l, EVEN):
            bad += 1
    fails += line("(11)", "identity stack", bad, len(L), "support fixed by m_i >= 0")

    # ---- (11b) the range is not a choice: the degree identity forces a finite support, so any
    # box containing it gives the same sum. Three very different boxes, and q <= p implied.
    bad = bad2 = viol = npairs = 0
    for l in L[:60]:
        ref = schur(l, EVEN)
        for lo, hi in ((0, l[0]), (-15, l[0] + 15), (-40, l[0] + 40)):
            tot = {}
            for p_ in range(lo, hi + 1):
                for q_ in range(lo, hi + 1):
                    m1, m2 = l[0] - max(p_, l[1]), min(p_, l[1]) - max(q_, l[2])
                    m3 = min(q_, l[2]) - l[3]
                    if m1 < 0 or m2 < 0 or m3 < 0:
                        continue
                    npairs += 1
                    viol += q_ > p_
                    if m1 + m2 + m3 != (l[0] - l[3]) - abs(p_ - l[1]) - abs(q_ - l[2]):
                        bad2 += 1
                    b = lmul(lmul(chi(m1), chi(m2)), chi(m3))
                    for k, v in b.items():
                        tot[k] = tot.get(k, 0) + (p_ - q_ + 1) * v
            if {k: v for k, v in tot.items() if v} != ref:
                bad += 1
    fails += line("(11b)", "range is no choice", bad + bad2 + viol, 3 * 60,
                  "3 boxes agree; degree identity holds; q>p never occurs")
    print("             pairs with all m_i >= 0 across the three boxes: %d, of which q>p: %d"
          % (npairs, viol))

    # ---- the second moment of a box is the sum of three SU(2) Casimirs. This is what turns the
    # curvature of the coset half into a group-theoretic invariant, and it had no archived run.
    bad = tested = 0
    for k1 in range(0, 13):
        for k2 in range(0, 13):
            for k3 in range(0, 13):
                box = lmul(lmul(chi(k1), chi(k2)), chi(k3))
                m2 = sum(m * m * c for m, c in box.items())
                dim = (k1 + 1) * (k2 + 1) * (k3 + 1)
                cas = sum((k / 2) * (k / 2 + 1) for k in (k1, k2, k3))
                tested += 1
                if abs(m2 - dim * (4.0 / 3.0) * cas) > 1e-9:
                    bad += 1
    fails += line("(5b)", "box 2nd moment", bad, tested, "sum m^2 = dim * (4/3) * sum C_2(j_i)")

    # ---- "Sigma factors into at most three SU(2) characters for only 5 of 359": ported from
    # identity_half.sage. The test is exact: a product chi_a chi_b chi_c has top exponent a+b+c,
    # value (a+1)(b+1)(c+1) at t=1 and leading coefficient 1, so the candidate triples are finite
    # and few; each is then compared coefficient by coefficient.
    def parts(maxn=16, maxlen=4):
        out = []
        for n in range(maxn + 1):
            def rec(rem, mx, cur):
                if rem == 0:
                    out.append(cur + [0] * (maxlen - len(cur)))
                    return
                for x in range(min(rem, mx), 0, -1):
                    if len(cur) < maxlen:
                        rec(rem - x, x, cur + [x])
            rec(n, n, [])
        return out

    def factors3(poly):
        if not poly:
            return None
        M = max(poly)
        dim = sum(poly.values())
        for a in range(M + 1):
            for b in range(min(a, M - a) + 1):
                c = M - a - b
                if c < 0 or c > b:
                    continue
                if (a + 1) * (b + 1) * (c + 1) != dim:
                    continue
                if lmul(lmul(chi(a), chi(b)), chi(c)) == poly:
                    return (a, b, c)
        return None

    P = parts()
    hits = [tuple(l) for l in P if factors3(schur(l, EVEN))]
    print("   %-9s %-16s %6d / %-6d %s %s"
          % ("(11c)", "Sigma factors", len(hits), len(P), "  ", "into <= 3 SU(2) characters"))
    print("             the %d that do: %s" % (len(hits), sorted(hits)))
    bad = 0 if len(P) == 359 else 1
    fails += bad

    # ---- the identity behind the whole paper, and it is an identity and not a reading:
    # sigma . diag(1,1,t,1/t) = diag(1,-1,t,1/t), so the two halves are the TRACE and the
    # SIGMA-TWISTED TRACE of the same group element on the same space.
    bad = 0
    for a, b in ((1, 1), (1, -1), (1, 0)):
        pass
    sigma = (1, -1, 1, 1)
    even_letters = (1, 1, "t", "1/t")
    odd_letters = tuple(s * l if isinstance(l, int) else ("-" + l if s < 0 else l)
                        for s, l in zip(sigma, even_letters))
    bad += int(odd_letters != (1, -1, "t", "1/t"))
    # and the consequence, on the characters themselves
    for l in L:
        S, D = schur(l, EVEN), schur(l, ODD)
        for j in set(S) | set(D):
            a, b = S.get(j, 0), D.get(j, 0)
            if (a + b) % 2 or (a - b) % 2 or a + b < 0 or a - b < 0:
                bad += 1
    fails += line("trace/str", "Sigma=Tr, D=Tr(sigma.)", bad, 1 + len(L),
                  "sigma . even alphabet = odd alphabet, and n+- are counts")

    # ---- the vanishing characterisation behind Proposition 2
    bad = 0
    for l in L:
        a = l[0] % 2 == 1 and l[1] % 2 == 0 and l[2] % 2 == 1
        b = l[0] % 2 == 1 and l[1] % 2 == 1 and l[2] % 2 == 0 and l[1] + l[2] == l[0]
        if (a or b) != (not schur(l, ODD)):
            bad += 1
    fails += line("Prop 2", "Z characterised", bad, len(L), "branches (a),(b), disjoint")

    print()
    print("   TOTAL FAILURES: %d" % fails)
    print()
    print("   Not re-derived here, and said so rather than implied:")
    print("     eq (3)  V(alpha) as a winding sum        -- definitional, and the assembly that")
    print("             realises it is validated in ghu_potential.py against AHMN's vacuum;")
    print("     eq (5)  the box expansion of V_odd       -- its FOUNDATION is checked above;")
    print("             the exponential rearrangement itself is box_potential.py (Sage);")
    print("     eq (11) is now checked ABOVE, with the range recovered by test, not assumed;")
    print("     eq (12) the three-character identity     -- hhk_bridge.py, 1470 cases, 0 failures;")
    print("     eq (13) the breaking criterion           -- rho archived in blkt_rho.txt.")
    return fails


if __name__ == "__main__":
    raise SystemExit(1 if main() else 0)
