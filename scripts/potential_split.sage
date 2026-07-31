# potential_split.sage -- Part V, brick 1.
#   Claim under test: the ENTIRE one-loop Wilson-line potential of an SU(4) fermion
#   multiplet is carried by exactly TWO Schur specialisations of the same partition,
#   selected by the parity of the winding number k2 (Part III, S6.1):
#       k2 even  ->  amplitude = sigma(m) = mult(m,0)+mult(m,1)  =  [t^m] s_lambda(1, 1,t,1/t)
#       k2 odd   ->  amplitude = delta(m) = mult(m,0)-mult(m,1)  =  [t^m] s_lambda(1,-1,t,1/t)
#   The second is the O(4)^- coset object of Parts III/IV (closed form known);
#   the first is its identity-component partner (Ciucu-Krattenthaler regime).
#   Verified here against the multiplicity histograms that generated Part III's figures.
#   Carles Marin <karlesmarin@gmail.com> (with Claude, Anthropic, as AI assistant).

import json

R = LaurentPolynomialRing(QQ, 't'); t = R.gen()
Sym = SymmetricFunctions(QQ); sch = Sym.schur()

LAB = {"35":(4,0,0), "60":(0,2,1), "84":(0,1,3), "140a":(1,1,2), "140b":(0,3,1),
       "224":(0,2,3), "280":(0,4,1), "360":(1,2,2), "756":(1,3,2)}
ORDER = ["35","60","84","140a","140b","224","280","360","756"]
H = json.load(open("release_iii/scripts/hists.json"))

def lam_of(abc):
    a,b,c = abc
    return [a+b+c, b+c, c, 0]

def gl4dim(lam):
    d = QQ(1)
    for i in range(4):
        for j in range(i+1,4):
            d *= QQ(lam[i]-lam[j]+j-i)/QQ(j-i)
    return ZZ(d)

def spec(lam, vals):
    P = sch[[x for x in lam if x>0]].expand(4)
    return R(P(vals[0], vals[1], vals[2], vals[3]))

def hist(rep):
    d = {}
    for k,v in H[rep].items():
        m,q = map(int, k.split(',')); d[(m,q)] = d.get((m,q),0)+int(v)
    return d

def gen(d, sign):
    ms = sorted(set(m for (m,q) in d))
    return sum((d.get((m,0),0) + sign*d.get((m,1),0)) * t**m for m in ms)

# --- the closed form of Part IV (spin map), for the k2-odd half ---
def betas(lam): return [lam[j]+(3-j) for j in range(4)]
def su2(k): return sum(t**(k-2*j) for j in range(k+1))
def spins_formula(lam):
    b = betas(lam)
    E = sorted([x for x in b if x%2==0], reverse=True)
    O = sorted([x for x in b if x%2==1], reverse=True)
    e,o = len(E), len(O)
    if e==4 or o==4: return "VANISH-a"
    if e==2 and o==2:
        p,q = E; r,s = O
        A=(r-s)//2; B=(p+q-r-s)//2; C=(p-q)//2
        if B==0: return "VANISH-b"
        return tuple(sorted([abs(A)-1, abs(B)-1, abs(C)-1]))
    if e==3 and o==1:
        p1,p2,p3 = E
        return tuple(sorted([(p1-p2)//2-1,(p2-p3)//2-1,(p1-p3)//2-1]))
    r1,r2,r3 = O
    return tuple(sorted([(r1-r2)//2-1,(r2-r3)//2-1,(r1-r3)//2-1]))

print("="*100)
print("A. the two generating functions ARE the two Schur specialisations (exact, per rep)")
print("="*100)
print("%-6s %-9s %5s  %-22s %-22s" % ("rep","(a,b,c)","dim","k2-even: s(1,1,t,1/t)","k2-odd: s(1,-1,t,1/t)"))
allok = True
for r in ORDER:
    abc = LAB[r]; lam = lam_of(abc); d = hist(r)
    dim = gl4dim(lam)
    assert dim == ZZ(r.rstrip('ab')), (r, dim)
    S = spec(lam, [R(1), R(1),  t, t**-1])
    D = spec(lam, [R(1), R(-1), t, t**-1])
    okS = (S == gen(d, +1)); okD = (D == gen(d, -1))
    allok = allok and okS and okD
    print("%-6s %-9s %5d  %-22s %-22s" % (r, str(abc), dim,
          "MATCH" if okS else "MISMATCH", "MATCH" if okD else "MISMATCH"))
print("\nall nine representations, both halves:", "VERIFIED" if allok else "FAILED")

print()
print("="*100)
print("B. what each half looks like -- factored (this is the Part V content)")
print("="*100)
for r in ORDER:
    abc = LAB[r]; lam = lam_of(abc)
    S = spec(lam, [R(1), R(1),  t, t**-1])
    D = spec(lam, [R(1), R(-1), t, t**-1])
    L = abc[0]+2*abc[1]+3*abc[2]
    adm = (L % 2 == 1) and abc[1] >= 1 and sum(abc) >= 3
    sp = spins_formula(lam)
    # closed-form check of the odd half
    if isinstance(sp, tuple):
        pr = su2(sp[0])*su2(sp[1])*su2(sp[2])
        cf = "eps*chi_%d chi_%d chi_%d" % sp
        okcf = (D == pr or D == -pr)
    else:
        cf = sp; okcf = (D == 0)
    par = "odd" if D(-t) == -D else ("even" if D(-t) == D else "MIXED")
    print("%-6s %-9s L=%2d %-12s  D parity in t: %-5s   closed form: %-22s %s"
          % (r, str(abc), L, "ADMISSIBLE" if adm else "not admissible", par, cf,
             "ok" if okcf else "FAIL"))

print()
print("="*100)
print("C. the notch, restated as a statement about D(t) alone")
print("="*100)
print("   admissible <=> centre charge L=a+2b+3c odd <=> D(t) is an ODD function of t")
print("   <=> delta(m)=0 for every even m  <=> every (m even, k2 odd) Fourier seat is empty.")
print()
for r in ORDER:
    lam = lam_of(LAB[r])
    D = spec(lam, [R(1), R(-1), t, t**-1])
    de = {m: D[m] for m in range(-30,31) if D[m] != 0 and m % 2 == 0}
    L = sum(c*(i+1) for i,c in enumerate(LAB[r]))
    print("  %-6s L=%2d (%s)   nonzero delta(m) at even m: %s"
          % (r, L, "odd" if L%2 else "even", de if de else "NONE  <-- notch"))
