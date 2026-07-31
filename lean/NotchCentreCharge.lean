/-
  NotchCentreCharge.lean
  Author: Carles Marín <karlesmarin@gmail.com>  (Claude, Anthropic, as AI assistant).

  Machine-checked brick for the SU(4) 6D gauge-Higgs unification study: the
  "even-m notch" of an SU(4) irrep (a,b,c) and its identification with the
  Z4 centre charge |lambda| = a + 2b + 3c.

  Setting.  For Dynkin labels (a,b,c) put lambda = (a+b+c, b+c, c, 0) and let
  D(t) = s_lambda(1,-1,t,t^-1) be the signed generating function of the
  orbifold histogram; the notch holds iff D is an odd Laurent polynomial.
  Writing D = N/V as a bialternant with the ordered alphabet
  y = (1, -1, T, T^-1) and exponents mu = (a+b+c+3, b+c+2, c+1, 0), the whole
  question is controlled by the 4x4 determinant N = det (y i ^ mu j) over
  ℤ[T;T⁻¹].

  What is certified here.

  * `notch_degenerate_iff` (T1, the core):
        N a b c = 0  <->  Odd b ∧ ((Odd a ∧ Odd c) ∨ a = c).
    Proved by an honest Laplace expansion along the two constant rows
    (`det_four_first_row_one`), reduction of every complementary 2x2 minor to
    the bracket [x] = T^x - T^(-x) (`brmul`), an eight-way parity split, and —
    for the non-vanishing half — extraction of the single Laurent coefficient
    at the strictly largest bracket argument (`co`).  That coefficient
    extraction is the finite, effective replacement for the abstract
    "linear independence of {[x]}_{x>0}" step of the paper proof.

  * `N_neg_alphabet`, `Ntilde_eq`, `notch_parity` (T2, the parity lemma):
    the homogeneity/symmetry statement s_lambda(-x) = (-1)^|lambda| s_lambda(x)
    in its finite bialternant form, including the cross-multiplied
    D(-t) = (-1)^|lambda| D(t) with no division.

  * `degenerate_centre_charge_even`, `degenerate_disjoint_admissible` (T3):
    every degenerate (a,b,c) has a+2b+3c even, so the degenerate set is
    disjoint from the SM-admissible set (Gate 1 = "a+2b+3c odd").

  Sorry-free.  `#print axioms` at the bottom.
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

open LaurentPolynomial

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

noncomputable section

namespace Notch

/-- Laurent polynomials with integer coefficients, `ℤ[T;T⁻¹]`. -/
abbrev L := LaurentPolynomial ℤ

/-! ### Coefficient extraction -/

/-- The coefficient of `T ^ k` in a Laurent polynomial. -/
def co (f : L) (k : ℤ) : ℤ := f k

@[simp] lemma co_zero (k : ℤ) : co 0 k = 0 := rfl

@[simp] lemma co_add (f g : L) (k : ℤ) : co (f + g) k = co f k + co g k :=
  Finsupp.add_apply f g k

@[simp] lemma co_sub (f g : L) (k : ℤ) : co (f - g) k = co f k - co g k :=
  Finsupp.sub_apply f g k

@[simp] lemma co_neg (f : L) (k : ℤ) : co (-f) k = - co f k :=
  Finsupp.neg_apply f k

@[simp] lemma co_T (n k : ℤ) : co (T n) k = if n = k then 1 else 0 :=
  T_apply k n

lemma ne_zero_of_co {f : L} {k : ℤ} (h : co f k ≠ 0) : f ≠ 0 := by
  intro hf; exact h (by rw [hf]; simp)

/-! ### The bracket `[x] = T^x - T^(-x)` -/

/-- `br x = T^x - T^(-x)`, the complementary 2x2 minor on the rows `(T, T⁻¹)`. -/
def br (x : ℤ) : L := T x - T (-x)

@[simp] lemma co_br (x k : ℤ) :
    co (br x) k = (if x = k then 1 else 0) - (if -x = k then 1 else 0) := by
  simp [br]

/-- Every complementary 2x2 minor of the bottom two rows is a bracket. -/
lemma brmul (m n : ℤ) : (T m : L) * T (-n) - T n * T (-m) = br (m - n) := by
  rw [br, ← T_add, ← T_add]
  congr 2
  ring

/-! ### Laplace expansion along the first two rows -/

/-- Laplace expansion of a 4x4 determinant along rows 0 and 1, when row 0 is
constant equal to `1`.  Pure ring identity. -/
lemma det_four_first_row_one {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (h : ∀ j, A 0 j = 1) :
    A.det =
        (A 1 1 - A 1 0) * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
      - (A 1 2 - A 1 0) * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
      + (A 1 3 - A 1 0) * (A 2 1 * A 3 2 - A 2 2 * A 3 1)
      + (A 1 2 - A 1 1) * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
      - (A 1 3 - A 1 1) * (A 2 0 * A 3 2 - A 2 2 * A 3 0)
      + (A 1 3 - A 1 2) * (A 2 0 * A 3 1 - A 2 1 * A 3 0) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, h]
  ring

/-! ### The bialternant -/

/-- The ordered alphabet `y = (1, -1, T, T⁻¹)`. -/
def y : Fin 4 → L := ![1, -1, T 1, T (-1)]

/-- The exponents `mu = (a+b+c+3, b+c+2, c+1, 0)` (strictly decreasing). -/
def mu (a b c : ℕ) : Fin 4 → ℕ := ![a + b + c + 3, b + c + 2, c + 1, 0]

/-- The bialternant matrix `M i j = y i ^ mu j`. -/
def M (a b c : ℕ) : Matrix (Fin 4) (Fin 4) L := fun i j => y i ^ mu a b c j

/-- `N a b c = det (y i ^ mu j)`; `D = N / V` and `D = 0 ↔ N = 0`. -/
def N (a b c : ℕ) : L := (M a b c).det

lemma neg_one_pow_even {n : ℕ} (h : n % 2 = 0) : ((-1 : L)) ^ n = 1 :=
  (Nat.even_iff.2 h).neg_one_pow

lemma neg_one_pow_odd {n : ℕ} (h : n % 2 = 1) : ((-1 : L)) ^ n = -1 :=
  (Nat.odd_iff.2 h).neg_one_pow

/-- Laplace expansion of `N`, with every minor written as a bracket. -/
lemma N_expand (a b c : ℕ) :
    N a b c =
        ((-1 : L) ^ (b + c + 2) - (-1 : L) ^ (a + b + c + 3)) * br ((c : ℤ) + 1)
      - ((-1 : L) ^ (c + 1) - (-1 : L) ^ (a + b + c + 3)) * br ((b : ℤ) + c + 2)
      + (1 - (-1 : L) ^ (a + b + c + 3)) * br ((b : ℤ) + 1)
      + ((-1 : L) ^ (c + 1) - (-1 : L) ^ (b + c + 2)) * br ((a : ℤ) + b + c + 3)
      - (1 - (-1 : L) ^ (b + c + 2)) * br ((a : ℤ) + b + 2)
      + (1 - (-1 : L) ^ (c + 1)) * br ((a : ℤ) + 1) := by
  have hy0 : y 0 = (1 : L) := rfl
  have hy1 : y 1 = (-1 : L) := rfl
  have hy2 : y 2 = (T 1 : L) := rfl
  have hy3 : y 3 = (T (-1) : L) := rfl
  have hrow0 : ∀ j, M a b c 0 j = 1 := by intro j; simp [M, hy0]
  have hrow2 : ∀ j, M a b c 2 j = T ((mu a b c j : ℤ)) := by
    intro j; simp [M, hy2, T_pow]
  have hrow3 : ∀ j, M a b c 3 j = T (-(mu a b c j : ℤ)) := by
    intro j; simp [M, hy3, T_pow]
  have hrow1 : ∀ j, M a b c 1 j = (-1 : L) ^ (mu a b c j) := by
    intro j; simp [M, hy1]
  have hm0 : mu a b c 0 = a + b + c + 3 := rfl
  have hm1 : mu a b c 1 = b + c + 2 := rfl
  have hm2 : mu a b c 2 = c + 1 := rfl
  have hm3 : mu a b c 3 = 0 := rfl
  rw [N, det_four_first_row_one _ hrow0]
  rw [hrow1 0, hrow1 1, hrow1 2, hrow1 3,
      hrow2 0, hrow2 1, hrow2 2, hrow2 3,
      hrow3 0, hrow3 1, hrow3 2, hrow3 3,
      hm0, hm1, hm2, hm3]
  rw [brmul, brmul, brmul, brmul, brmul, brmul]
  have e1 : ((c + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (c : ℤ) + 1 := by push_cast; ring
  have e2 : ((b + c + 2 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (b : ℤ) + c + 2 := by push_cast; ring
  have e3 : ((b + c + 2 : ℕ) : ℤ) - ((c + 1 : ℕ) : ℤ) = (b : ℤ) + 1 := by push_cast; ring
  have e4 : ((a + b + c + 3 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (a : ℤ) + b + c + 3 := by push_cast; ring
  have e5 : ((a + b + c + 3 : ℕ) : ℤ) - ((c + 1 : ℕ) : ℤ) = (a : ℤ) + b + 2 := by push_cast; ring
  have e6 : ((a + b + c + 3 : ℕ) : ℤ) - ((b + c + 2 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  simp only [pow_zero]

/-! ### T1: the exact degeneracy condition -/

theorem notch_degenerate_iff (a b c : ℕ) :
    N a b c = 0 ↔ (Odd b ∧ ((Odd a ∧ Odd c) ∨ a = c)) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      rcases Nat.mod_two_eq_zero_or_one c with hc | hc
  -- (0,0,0):  S = br(c+1) + br(b+1) - br(a+b+c+3) + br(a+1),  peak a+b+c+3
  · refine iff_of_false ?_ (by simp only [Nat.odd_iff]; omega)
    have hS : N a b c =
        ((br ((c : ℤ) + 1) + br ((b : ℤ) + 1) - br ((a : ℤ) + b + c + 3) + br ((a : ℤ) + 1))
       + (br ((c : ℤ) + 1) + br ((b : ℤ) + 1) - br ((a : ℤ) + b + c + 3) + br ((a : ℤ) + 1))) := by
      rw [N_expand, neg_one_pow_even (n := b + c + 2) (by omega),
        neg_one_pow_odd (n := a + b + c + 3) (by omega),
        neg_one_pow_odd (n := c + 1) (by omega)]
      ring
    refine ne_zero_of_co (k := (a : ℤ) + b + c + 3) ?_
    rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
  -- (0,0,1):  S = -br(c+1) + br(a+b+c+3) - br(a+b+2),  peak a+b+c+3
  · refine iff_of_false ?_ (by simp only [Nat.odd_iff]; omega)
    have hS : N a b c =
        ((br ((a : ℤ) + b + c + 3) - br ((c : ℤ) + 1) - br ((a : ℤ) + b + 2))
       + (br ((a : ℤ) + b + c + 3) - br ((c : ℤ) + 1) - br ((a : ℤ) + b + 2))) := by
      rw [N_expand, neg_one_pow_odd (n := b + c + 2) (by omega),
        neg_one_pow_even (n := a + b + c + 3) (by omega),
        neg_one_pow_even (n := c + 1) (by omega)]
      ring
    refine ne_zero_of_co (k := (a : ℤ) + b + c + 3) ?_
    rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
  -- (0,1,0):  S = br(b+c+2) - br(c+1) + br(a+1) - br(a+b+2);  zero iff a = c
  · have hRHS : (Odd b ∧ ((Odd a ∧ Odd c) ∨ a = c)) ↔ a = c := by
      simp only [Nat.odd_iff]; omega
    rw [hRHS]
    have hS : N a b c =
        ((br ((b : ℤ) + c + 2) - br ((c : ℤ) + 1) + br ((a : ℤ) + 1) - br ((a : ℤ) + b + 2))
       + (br ((b : ℤ) + c + 2) - br ((c : ℤ) + 1) + br ((a : ℤ) + 1) - br ((a : ℤ) + b + 2))) := by
      rw [N_expand, neg_one_pow_odd (n := b + c + 2) (by omega),
        neg_one_pow_even (n := a + b + c + 3) (by omega),
        neg_one_pow_odd (n := c + 1) (by omega)]
      ring
    constructor
    · intro hz
      by_contra hac
      rcases Nat.lt_or_ge a c with hlt | hge
      · -- a < c: the peak is b + c + 2
        refine ne_zero_of_co (k := (b : ℤ) + c + 2) ?_ hz
        rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
      · -- a > c: the peak is a + b + 2
        have hgt : c < a := by omega
        refine ne_zero_of_co (k := (a : ℤ) + b + 2) ?_ hz
        rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
    · rintro rfl
      rw [hS]
      have h1 : ((a : ℤ) + b + 2) = ((b : ℤ) + a + 2) := by ring
      rw [h1]
      ring
  -- (0,1,1):  S = br(c+1) - br(b+c+2) + br(b+1),  peak b+c+2
  · refine iff_of_false ?_ (by simp only [Nat.odd_iff]; omega)
    have hS : N a b c =
        ((br ((c : ℤ) + 1) - br ((b : ℤ) + c + 2) + br ((b : ℤ) + 1))
       + (br ((c : ℤ) + 1) - br ((b : ℤ) + c + 2) + br ((b : ℤ) + 1))) := by
      rw [N_expand, neg_one_pow_even (n := b + c + 2) (by omega),
        neg_one_pow_odd (n := a + b + c + 3) (by omega),
        neg_one_pow_even (n := c + 1) (by omega)]
      ring
    refine ne_zero_of_co (k := (b : ℤ) + c + 2) ?_
    rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
  -- (1,0,0):  S = br(b+c+2) - br(a+b+c+3) + br(a+1),  peak a+b+c+3
  · refine iff_of_false ?_ (by simp only [Nat.odd_iff]; omega)
    have hS : N a b c =
        ((br ((b : ℤ) + c + 2) - br ((a : ℤ) + b + c + 3) + br ((a : ℤ) + 1))
       + (br ((b : ℤ) + c + 2) - br ((a : ℤ) + b + c + 3) + br ((a : ℤ) + 1))) := by
      rw [N_expand, neg_one_pow_even (n := b + c + 2) (by omega),
        neg_one_pow_even (n := a + b + c + 3) (by omega),
        neg_one_pow_odd (n := c + 1) (by omega)]
      ring
    refine ne_zero_of_co (k := (a : ℤ) + b + c + 3) ?_
    rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
  -- (1,0,1):  S = -br(b+c+2) + br(b+1) + br(a+b+c+3) - br(a+b+2),  peak a+b+c+3
  · refine iff_of_false ?_ (by simp only [Nat.odd_iff]; omega)
    have hS : N a b c =
        ((br ((a : ℤ) + b + c + 3) - br ((b : ℤ) + c + 2) + br ((b : ℤ) + 1)
            - br ((a : ℤ) + b + 2))
       + (br ((a : ℤ) + b + c + 3) - br ((b : ℤ) + c + 2) + br ((b : ℤ) + 1)
            - br ((a : ℤ) + b + 2))) := by
      rw [N_expand, neg_one_pow_odd (n := b + c + 2) (by omega),
        neg_one_pow_odd (n := a + b + c + 3) (by omega),
        neg_one_pow_even (n := c + 1) (by omega)]
      ring
    refine ne_zero_of_co (k := (a : ℤ) + b + c + 3) ?_
    rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
  -- (1,1,0):  S = br(b+1) - br(a+b+2) + br(a+1),  peak a+b+2
  · refine iff_of_false ?_ (by simp only [Nat.odd_iff]; omega)
    have hS : N a b c =
        ((br ((b : ℤ) + 1) - br ((a : ℤ) + b + 2) + br ((a : ℤ) + 1))
       + (br ((b : ℤ) + 1) - br ((a : ℤ) + b + 2) + br ((a : ℤ) + 1))) := by
      rw [N_expand, neg_one_pow_odd (n := b + c + 2) (by omega),
        neg_one_pow_odd (n := a + b + c + 3) (by omega),
        neg_one_pow_odd (n := c + 1) (by omega)]
      ring
    refine ne_zero_of_co (k := (a : ℤ) + b + 2) ?_
    rw [hS]; simp only [co_add, co_sub, co_br]; split_ifs <;> omega
  -- (1,1,1): all mu even, every 2x2 minor on the constant rows vanishes
  · refine iff_of_true ?_ (by simp only [Nat.odd_iff]; omega)
    rw [N_expand, neg_one_pow_even (n := b + c + 2) (by omega),
      neg_one_pow_even (n := a + b + c + 3) (by omega),
      neg_one_pow_even (n := c + 1) (by omega)]
    ring

/-- The Vandermonde denominator `V = N 0 0 0` is non-zero, so `D = N/V` is legitimate. -/
theorem V_ne_zero : N 0 0 0 ≠ 0 := by
  simp only [ne_eq, notch_degenerate_iff, Nat.odd_iff]
  omega

/-! ### T2: the parity (homogeneity) lemma -/

/-- Negating the whole alphabet scales the bialternant by `(-1)^(a+2b+3c)`. -/
theorem N_neg_alphabet (a b c : ℕ) :
    (Matrix.of fun i j => (-(y i)) ^ (mu a b c j)).det = (-1 : L) ^ (a + 2 * b + 3 * c) * N a b c := by
  have h : (Matrix.of fun i j => (-(y i)) ^ (mu a b c j))
      = Matrix.of fun i j => ((-1 : L) ^ (mu a b c j)) * (M a b c i j) := by
    funext i j
    show (-(y i)) ^ (mu a b c j) = ((-1 : L) ^ (mu a b c j)) * (y i) ^ (mu a b c j)
    exact neg_pow _ _
  rw [h, Matrix.det_mul_row]
  congr 1
  have : ∏ j : Fin 4, ((-1 : L) ^ (mu a b c j)) = (-1 : L) ^ (a + 2 * b + 3 * c + 6) := by
    rw [Fin.prod_univ_four]
    rw [show mu a b c 0 = a + b + c + 3 from rfl, show mu a b c 1 = b + c + 2 from rfl,
      show mu a b c 2 = c + 1 from rfl, show mu a b c 3 = 0 from rfl]
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [this]
  rw [show a + 2 * b + 3 * c + 6 = (a + 2 * b + 3 * c) + 6 from rfl, pow_add]
  norm_num

/-- The alphabet with `t` replaced by `-t`. -/
def ytilde : Fin 4 → L := ![1, -1, -(T 1), -(T (-1))]

/-- `Ntilde a b c` is `N a b c` with `t` replaced by `-t`. -/
def Ntilde (a b c : ℕ) : L := (Matrix.of fun i j => (ytilde i) ^ (mu a b c j)).det

/-- The finite bialternant form of `D(-t) = (-1)^|lambda| D(t)`:
`t -> -t` scales `N` by `(-1)^(a+2b+3c+1)` (the extra sign is the transposition
of the two constant letters, and it cancels in the quotient `N/V`). -/
theorem Ntilde_eq (a b c : ℕ) :
    Ntilde a b c = (-1 : L) ^ (a + 2 * b + 3 * c + 1) * N a b c := by
  have hsub : (Matrix.of fun i j => (ytilde i) ^ (mu a b c j))
      = (Matrix.of fun i j => (-(y i)) ^ (mu a b c j)).submatrix (Equiv.swap 0 1) id := by
    funext i j
    fin_cases i <;> simp [ytilde, y, Equiv.swap_apply_of_ne_of_ne]
  rw [Ntilde, hsub, Matrix.det_permute, N_neg_alphabet]
  rw [Equiv.Perm.sign_swap (by decide)]
  rw [show a + 2 * b + 3 * c + 1 = (a + 2 * b + 3 * c) + 1 from rfl, pow_add]
  push_cast
  ring

/-- The parity lemma at the level of `D = N/V`, cross-multiplied (no division):
`D(-t) = (-1)^(a+2b+3c) D(t)`. -/
theorem notch_parity (a b c : ℕ) :
    Ntilde a b c * N 0 0 0 = (-1 : L) ^ (a + 2 * b + 3 * c) * (N a b c * Ntilde 0 0 0) := by
  rw [Ntilde_eq, Ntilde_eq]
  norm_num
  ring

/-! ### T3: the bridge to Gate 1 (the Z4 centre charge) -/

/-- Every degenerate `(a,b,c)` has even centre charge `a + 2b + 3c`. -/
theorem degenerate_centre_charge_even (a b c : ℕ)
    (h : Odd b ∧ ((Odd a ∧ Odd c) ∨ a = c)) : Even (a + 2 * b + 3 * c) := by
  simp only [Nat.odd_iff] at h
  rw [Nat.even_iff]
  omega

/-- Hence the degenerate set is disjoint from the SM-admissible set, whose
Gate 1 is exactly "`a + 2b + 3c` odd". -/
theorem degenerate_disjoint_admissible (a b c : ℕ)
    (hadm : Odd (a + 2 * b + 3 * c)) : N a b c ≠ 0 := by
  simp only [ne_eq, notch_degenerate_iff]
  intro h
  exact (Nat.not_even_iff_odd.2 hadm) (degenerate_centre_charge_even a b c h)

/-! ### Sanity checks against the Sage verification -/

-- `(1,1,1)`: all Dynkin labels odd, branch 1 of the degenerate set.
example : N 1 1 1 = 0 := by rw [notch_degenerate_iff]; decide

-- `(2,1,2)`: `a = c` even and `b` odd, branch 2.
example : N 2 1 2 = 0 := by rw [notch_degenerate_iff]; decide

-- `(2,1,0)`: `b` odd but `a ≠ c` and `a`, `c` even — not degenerate.
example : N 2 1 0 ≠ 0 := by simp only [ne_eq, notch_degenerate_iff]; decide

-- The AHMN rep `35 = (4,0,0)`: `|lambda| = 4` is even, yet `(4,0,0)` is not
-- degenerate, so it *must* break the notch — the single catalog exception.
example : N 4 0 0 ≠ 0 := by simp only [ne_eq, notch_degenerate_iff]; decide

-- Gate 1 example: `(1,0,0)` has `|lambda| = 1` odd, hence is not degenerate.
example : N 1 0 0 ≠ 0 := degenerate_disjoint_admissible 1 0 0 (by decide)

#print axioms notch_degenerate_iff
#print axioms V_ne_zero
#print axioms N_neg_alphabet
#print axioms Ntilde_eq
#print axioms notch_parity
#print axioms degenerate_centre_charge_even
#print axioms degenerate_disjoint_admissible

end Notch

end
