# box_potential.py -- Part V, brick 4.  The potential as a box.
#
#   The odd-winding half of the one-loop Wilson-line potential is
#       V_odd(alpha) = sum_{k2 odd} W_k sum_m delta(m) cos(pi m (k1 a1 + k2 a2)),   W_k = 1/(k1^2+k2^2)^3
#   and Part IV's closed form says  sum_m delta(m) t^m = eps * chi_{k1} chi_{k2} chi_{k3}(t).
#   Expanding each SU(2) character as a sum of exponentials turns that into a BOX:
#       delta(m) = eps * #{ (a1,a2,a3) : 0 <= a_i <= k_i,  m = sum k_i - 2 sum a_i }
#   hence
#       V_odd(alpha) = eps * sum_{a in Box} G(m(a) a1, m(a) a2),
#       G(x1,x2) := sum_{k2 odd} cos(pi(k1 x1 + k2 x2)) / (k1^2+k2^2)^3
#   ONE universal function, independent of the representation; the representation enters only as a
#   multiset of integers m(a) read off the Young diagram by the spin map.  No Kaluza-Klein spectrum.
#
#   HONESTY: given delta(m) = eps * box counts (already verified), the identity above is ALGEBRAIC,
#   so the numerical agreement below is a control on the code, not new evidence.  What is new is
#   (i) the argument list is produced by the spin map instead of assembled by hand per representation
#   (compare AHMN 2312.08608 eq. (3.25), Kawamura et al. 2502.08250 eqs. (5.22)-(5.28)), and
#   (ii) the curvature -- hence the Higgs mass -- becomes a SECOND MOMENT of the box:
#       d^2 V_odd / d alpha_2^2 = eps * sum_{a in Box} m(a)^2 G_22(m(a) a1, m(a) a2).
#   Carles Marin <karlesmarin@gmail.com> (with Claude, Anthropic, as AI assistant).

import json, itertools, numpy as np

H = json.load(open("release_iii/scripts/hists.json"))
LAB = {"35":(4,0,0), "60":(0,2,1), "84":(0,1,3), "140a":(1,1,2), "140b":(0,3,1),
       "224":(0,2,3), "280":(0,4,1), "360":(1,2,2), "756":(1,3,2)}
ORDER = ["35","60","84","140a","140b","224","280","360","756"]
KMAX = 16

def lam_of(abc):
    a,b,c = abc
    return [a+b+c, b+c, c, 0]

def spins(lam):
    b = [lam[j]+(3-j) for j in range(4)]
    E = sorted([x for x in b if x % 2 == 0], reverse=True)
    O = sorted([x for x in b if x % 2 == 1], reverse=True)
    e,o = len(E), len(O)
    if e == 4 or o == 4: return None
    if e == 2 and o == 2:
        p,q = E; r,s = O
        A = (r-s)//2; B = (p+q-r-s)//2; C = (p-q)//2
        if B == 0: return None
        return tuple(sorted([abs(A)-1, abs(B)-1, abs(C)-1]))
    if e == 3 and o == 1:
        p1,p2,p3 = E
        return tuple(sorted([(p1-p2)//2-1, (p2-p3)//2-1, (p1-p3)//2-1]))
    r1,r2,r3 = O
    return tuple(sorted([(r1-r2)//2-1, (r2-r3)//2-1, (r1-r3)//2-1]))

def hist(rep):
    d = {}
    for k,v in H[rep].items():
        m,q = map(int, k.split(',')); d[(m,q)] = d.get((m,q),0) + int(v)
    return d

def delta(rep):
    d = hist(rep); ms = sorted(set(m for (m,q) in d))
    return {m: d.get((m,0),0) - d.get((m,1),0) for m in ms if d.get((m,0),0) - d.get((m,1),0) != 0}

def box(sp):
    """the multiset of exponents m(a) = sum k_i - 2 sum a_i"""
    S = sum(sp)
    return [S - 2*sum(a) for a in itertools.product(*[range(k+1) for k in sp])]

KS_ODD = [(k1,k2) for k1 in range(-KMAX,KMAX+1) for k2 in range(-KMAX,KMAX+1)
          if k2 % 2 != 0]

def G(x1, x2):
    """the universal function, restricted to odd k2"""
    tot = 0.0
    for (k1,k2) in KS_ODD:
        tot += np.cos(np.pi*(k1*x1 + k2*x2)) / (k1*k1 + k2*k2)**3
    return tot

def G22(x1, x2):
    """d^2/dx2^2 of G, at fixed scaling -- the kernel of the curvature"""
    tot = 0.0
    for (k1,k2) in KS_ODD:
        tot += -(np.pi*k2)**2 * np.cos(np.pi*(k1*x1 + k2*x2)) / (k1*k1 + k2*k2)**3
    return tot

def V_odd_direct(rep, a1, a2):
    dl = delta(rep); tot = 0.0
    for (k1,k2) in KS_ODD:
        th = k1*a1 + k2*a2
        s = sum(mu*np.cos(np.pi*m*th) for m,mu in dl.items())
        tot += s / (k1*k1 + k2*k2)**3
    return tot

print("="*100)
print("A. control -- is delta(m) exactly eps times the box counts?")
print("="*100)
print("  %-6s %-9s %-11s %-5s %-6s %s" % ("rep","(a,b,c)","spins","eps","|box|","delta == eps * box counts"))
EPS = {}
for r in ORDER:
    lam = lam_of(LAB[r]); sp = spins(lam); dl = delta(r)
    bx = box(sp)
    cnt = {}
    for m in bx: cnt[m] = cnt.get(m,0) + 1
    eps = 1 if all(dl.get(m,0) == cnt.get(m,0) for m in set(list(dl)+list(cnt))) else -1
    EPS[r] = eps
    ok = all(dl.get(m,0) == eps*cnt.get(m,0) for m in set(list(dl)+list(cnt)))
    print("  %-6s %-9s %-11s %+5d %-6d %s" % (r, str(LAB[r]), str(sp), eps, len(bx),
                                              "YES" if ok else "*** NO ***"))

print()
print("="*100)
print("B. the argument list the spin map produces -- what AHMN / Kawamura assemble by hand")
print("="*100)
for r in ORDER:
    sp = spins(lam_of(LAB[r])); bx = sorted(box(sp), reverse=True)
    cnt = {}
    for m in bx: cnt[m] = cnt.get(m,0) + 1
    terms = " + ".join(("%d*" % c if c > 1 else "") + "G(%d a)" % m
                       for m,c in sorted(cnt.items(), reverse=True) if m >= 0)
    sgn = "+" if EPS[r] > 0 else "-"
    print("  V_odd[%-5s] = %s [ %s ]%s" % (r, sgn, terms, "  (m<0 mirrors m>0)"))

print()
print("="*100)
print("C. the identity, evaluated -- box formula vs direct mode sum (code control)")
print("="*100)
pts = [(0.0,0.0),(0.3,0.2),(0.4360,0.2986),(0.1,0.5),(0.7,0.45)]
print("  %-6s %s" % ("rep", "  ".join("(%.2f,%.2f)" % p for p in pts)))
worst = 0.0
for r in ORDER:
    sp = spins(lam_of(LAB[r])); bx = box(sp); eps = EPS[r]
    row = []
    for (a1,a2) in pts:
        direct = V_odd_direct(r, a1, a2)
        viabox = eps * sum(G(m*a1, m*a2) for m in bx)
        row.append(abs(direct - viabox)); worst = max(worst, abs(direct-viabox))
    print("  %-6s %s" % (r, "  ".join("%9.2e" % x for x in row)))
print("\n  worst absolute discrepancy over all reps and points: %.3e" % worst)

print()
print("="*100)
print("D. the payoff -- the alpha_2 curvature of the odd sector as a SECOND MOMENT of the box")
print("="*100)
print("  d2V_odd/da2^2 = eps * sum_{a in Box} m(a)^2 G22(m a1, m a2)")
print()
print("  tested at a GENERIC point (0.3, 0.27).  The earlier version of this check used")
print("  alpha_2 = 1/2, where every admissible representation vanishes -- a control with no content.")
print()
print("  %-6s %-11s %-9s %-14s %-14s %-7s %s"
      % ("rep","spins","sum m^2","box curvature","direct","agree","at a2=1/2"))
for r in ORDER:
    sp = spins(lam_of(LAB[r])); bx = box(sp); eps = EPS[r]
    a1, a2 = 0.3, 0.27
    cur_box = eps * sum(m*m * G22(m*a1, m*a2) for m in bx)
    h = 1e-4
    cur_dir = (V_odd_direct(r,a1,a2+h) - 2*V_odd_direct(r,a1,a2) + V_odd_direct(r,a1,a2-h))/h**2
    rel = abs(cur_box-cur_dir)/max(abs(cur_dir),1e-9)
    half = eps * sum(m*m * G22(m*0.3, m*0.5) for m in bx)
    print("  %-6s %-11s %-9d %-14.4f %-14.4f %-7s %.4f"
          % (r, str(sp), sum(m*m for m in bx), cur_box, cur_dir,
             "ok" if rel < 1e-3 else "MISMATCH", half))
print()
print("  Last column: the same second moment at alpha_2 = 1/2.  The kernel G22 then grades m mod 4,")
print("  which is exactly Part III's script-D; every admissible representation has all m(a) ODD")
print("  (that IS the notch), so every term dies and only the non-admissible 35 survives.")
print("  Part III's decoupling corollary is one line from the box.")
