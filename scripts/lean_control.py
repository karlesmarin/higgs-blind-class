#!/usr/bin/env python3
"""lean_control.py -- the control that must pass BEFORE any Lean is written.

  Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)

Part V's Proposition 2 is stated in partition coordinates lambda = (l1,l2,l3,0).
The machine-checked brick we already own, NotchCentreCharge.lean, states the same
vanishing criterion in DYNKIN coordinates (a,b,c):

    N a b c = 0  <->  Odd b and ((Odd a and Odd c) or a = c)

with the dictionary  lambda = (a+b+c, b+c, c, 0),  i.e.  a = l1-l2, b = l2-l3, c = l3.

Three things must hold before the Lean statement is worth writing, and each is a
separate way for the plan to die:

  C1  the two characterisations describe the SAME set (dictionary is right)
  C2  l1 is never even on that set
  C3  the count at l1 = 2k+1 is ceil((k+1)^2/2)

C3 is checked BOTH by brute force and by the fibre decomposition that the Lean
proof will actually follow -- if the decomposition disagrees with brute force, the
proof architecture is wrong and no amount of Lean will fix it.
"""
from math import ceil


def notch(a, b, c):
    """The criterion certified in NotchCentreCharge.lean, verbatim."""
    return (b % 2 == 1) and ((a % 2 == 1 and c % 2 == 1) or a == c)


def partV(l1, l2, l3):
    """Part V, Proposition 2: branch (a) or branch (b)."""
    return ((l1 % 2 == 1 and l2 % 2 == 0 and l3 % 2 == 1) or
            (l1 % 2 == 1 and l2 % 2 == 1 and l3 % 2 == 0 and l2 + l3 == l1))


def main():
    LMAX = 60
    lams = [(l1, l2, l3)
            for l1 in range(LMAX + 1)
            for l2 in range(l1 + 1)
            for l3 in range(l2 + 1)]

    # C1 -- same set under the dictionary
    bad = [(l1, l2, l3) for (l1, l2, l3) in lams
           if notch(l1 - l2, l2 - l3, l3) != partV(l1, l2, l3)]
    print("C1  dictionary: %d partitions swept, %d disagreements" % (len(lams), len(bad)))
    for t in bad[:5]:
        print("      MISMATCH %s" % (t,))

    # C2 -- l1 never even
    Z = [t for t in lams if partV(*t)]
    even_l1 = [t for t in Z if t[0] % 2 == 0]
    print("C2  parity  : |Z| = %d up to l1 = %d, with l1 even: %d" % (len(Z), LMAX, len(even_l1)))

    # C3a -- brute force count per shell
    print("C3  count   : k  brute  ceil((k+1)^2/2)  fibre-sum   Gauss+parity")
    fails = 0
    for k in range((LMAX - 1) // 2 + 1):
        l1 = 2 * k + 1
        brute = sum(1 for t in Z if t[0] == l1)
        closed = ceil((k + 1) ** 2 / 2)

        # C3b -- the decomposition the Lean proof will follow.
        # Fibre over b (odd), b = 2j+1.  With a+c = 2k+1-b = 2s even, the pairs
        # (a,c) admitted are: a odd (s of them), plus a = c = s when s is even.
        fibre = 0
        for j in range(k + 1):
            s = k - j
            fibre += s + (1 if s % 2 == 0 else 0)

        # C3c -- and its closed form: Gauss sum + the count of even s in [0,k]
        gauss = k * (k + 1) // 2 + (k // 2 + 1)

        ok = brute == closed == fibre == gauss
        fails += 0 if ok else 1
        if k <= 8 or not ok:
            print("            %-3d %-6d %-16d %-11d %-6d %s"
                  % (k, brute, closed, fibre, gauss, "" if ok else "  <-- FAIL"))
    print("            ... swept k = 0..%d, %d failures" % ((LMAX - 1) // 2, fails))

    # the control that can fail: a deliberately wrong dictionary must break C1
    wrong = [(l1, l2, l3) for (l1, l2, l3) in lams
             if notch(l1 - l2, l2 - l3, l2 - l3) != partV(l1, l2, l3)]
    print("C0  falsification: wrong dictionary (c := b) disagrees on %d partitions"
          " (must be > 0)" % len(wrong))

    return len(bad) == 0 and len(even_l1) == 0 and fails == 0 and len(wrong) > 0


if __name__ == "__main__":
    print("PASS" if main() else "FAIL")
