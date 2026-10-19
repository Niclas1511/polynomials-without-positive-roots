import Mathlib

/-!
# No positive roots

Definitions and theorems from the note `noposroots.tex`.
The main theorem is proved using Lemma 2 (`quadratic_case`).
All lemmas and the main theorem are proved without `sorry`.
-/

namespace NoPosRoots

/-- All coefficients of `p` are nonnegative. -/
def NonnegCoeffs (p : Polynomial ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ p.coeff n

/-- The polynomial `p` has no positive real root. -/
def NoPositiveRoots (p : Polynomial ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → p.eval x ≠ 0

/-- There exists a nonzero polynomial `q` such that `p * q`
has nonnegative coefficients. -/
def HasNonnegMultiple (p : Polynomial ℝ) : Prop :=
  ∃ q : Polynomial ℝ, q ≠ 0 ∧ NonnegCoeffs (p * q)

/-- The sequence defined by `y₀ = 0`, `y₁ = 1`, and
`yₖ₊₂ = -(b / a) * yₖ₊₁ - (1 / a) * yₖ`.
The intended application has `a > 0`. -/
noncomputable def y (a b : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k + 2 => -(b / a) * y a b (k + 1) - (1 / a) * y a b k

/-- The polynomial `qₙ = ∑ k ∈ {0, …, n - 1}, yₖ₊₁ Xᵏ`.
This is the sum in the note with its index shifted by one. -/
noncomputable def q (a b : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range n, Polynomial.C (y a b (k + 1)) * Polynomial.X ^ k

/-- Lemma 3: multiplying the truncated sequence polynomial by the
quadratic leaves only the constant term and two boundary terms. -/
theorem pq_product
    (a b : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.X ^ 2) *
        q a b n =
      Polynomial.C a -
        Polynomial.C (a * y a b (n + 1)) * Polynomial.X ^ n +
        Polynomial.C (y a b n) * Polynomial.X ^ (n + 1) := by
  have hrec (k : ℕ) :
      a * y a b (k + 2) = -(y a b k + b * y a b (k + 1)) := by
    rw [y]
    field_simp [ha]
    ring
  induction n, hn using Nat.le_induction with
  | base =>
    have htwo : a * y a b 2 = -b := by
      simpa [y] using hrec 0
    have hqone : q a b 1 = 1 := by
      simp [q, y]
    rw [hqone, mul_one, htwo]
    simp [y]
  | succ n hn ih =>
    have hq : q a b (n + 1) =
        q a b n + Polynomial.C (y a b (n + 1)) * Polynomial.X ^ n := by
      simp only [q, Finset.sum_range_succ]
    rw [hq, mul_add, ih]
    rw [hrec n]
    simp only [map_neg, map_add, map_mul, pow_succ]
    ring

/-- Lemma 5: every real angle has a positive integer multiple
whose sine is nonpositive. -/
theorem sin_nonpositive_multiple (φ : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ Real.sin ((k : ℝ) * φ) ≤ 0 := by
  have hsin (x : ℝ) (hx : Real.pi ≤ x) (hx' : x ≤ 2 * Real.pi) :
      Real.sin x ≤ 0 := by
    simpa only [Real.sin_sub_two_pi] using
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (x := x - 2 * Real.pi) (by linarith) (by linarith))
  by_cases hφ : Real.sin φ ≤ 0
  · exact ⟨1, by norm_num, by simpa using hφ⟩
  -- Reduce modulo 2π; periodicity also holds for every integer multiple.
  obtain ⟨m, hm, _⟩ := existsUnique_sub_zsmul_mem_Ico Real.two_pi_pos φ 0
  let θ := φ - (m : ℝ) * (2 * Real.pi)
  have hθmem : θ ∈ Set.Ico 0 (2 * Real.pi) := by simpa [θ, zsmul_eq_mul] using hm
  have hperiod (k : ℕ) : Real.sin ((k : ℝ) * θ) = Real.sin ((k : ℝ) * φ) := by
    simpa [θ, mul_sub, mul_assoc, Int.cast_mul] using
      Real.sin_sub_int_mul_two_pi ((k : ℝ) * φ) ((k : ℤ) * m)
  have hθsin : 0 < Real.sin θ := by
    have heq : Real.sin θ = Real.sin φ := by simpa using hperiod 1
    rw [heq]
    exact lt_of_not_ge hφ
  have hθpos : 0 < θ := lt_of_le_of_ne hθmem.1 (by
    intro hzero
    simp [← hzero] at hθsin)
  have hθlt : θ < Real.pi := lt_of_not_ge fun h =>
    (not_le_of_gt hθsin) (hsin θ h hθmem.2.le)
  -- Choose k = ceil (π / θ), giving π ≤ kθ < π + θ < 2π.
  let k : ℕ := ⌈Real.pi / θ⌉₊
  have hlow : Real.pi ≤ (k : ℝ) * θ :=
    (div_le_iff₀ hθpos).mp (Nat.le_ceil _)
  have hupp : (k : ℝ) * θ < Real.pi + θ := by
    have := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (div_pos Real.pi_pos hθpos).le) hθpos
    nlinarith [div_mul_cancel₀ Real.pi (ne_of_gt hθpos)]
  exact ⟨k, Nat.one_le_ceil_iff.mpr (div_pos Real.pi_pos hθpos),
    (hperiod k) ▸ hsin _ hlow (by linarith)⟩

/-- The trigonometric closed form of the recurrence, verified from its initial values. -/
theorem y_eq_sin (a b r φ : ℝ) (hr : r ≠ 0) (hsin : Real.sin φ ≠ 0)
    (hcos : 2 * r * Real.cos φ = -(b / a)) (hrsq : r ^ 2 = 1 / a)
    (k : ℕ) :
    y a b k = r ^ k * Real.sin ((k : ℝ) * φ) / (r * Real.sin φ) := by
  have hsinrec (n : ℕ) :
      Real.sin (((n + 2 : ℕ) : ℝ) * φ) =
        2 * Real.cos φ * Real.sin (((n + 1 : ℕ) : ℝ) * φ) -
          Real.sin ((n : ℝ) * φ) := by
    have hplus : (((n + 2 : ℕ) : ℝ) * φ) =
        (((n + 1 : ℕ) : ℝ) * φ) + φ := by push_cast; ring
    have hminus : (n : ℝ) * φ = (((n + 1 : ℕ) : ℝ) * φ) - φ := by
      push_cast
      ring
    rw [hplus, hminus, Real.sin_add, Real.sin_sub]
    ring
  induction k using Nat.twoStepInduction with
  | zero => simp [y]
  | one => simp [y, mul_ne_zero hr hsin]
  | more n ih₀ ih₁ =>
    rw [y, ih₁, ih₀, ← hcos, ← hrsq, hsinrec]
    simp only [pow_add, pow_one]
    ring

/-- Lemma 4: under the assumptions of the quadratic case, the sequence
has a nonpositive term with positive index. -/
theorem nonpositive_member
    (a b : ℝ) (ha : 0 < a) (hb : b < 0)
    (hdiscr : b ^ 2 - 4 * a < 0) :
    ∃ k : ℕ, 1 ≤ k ∧ y a b k ≤ 0 := by
  let s := Real.sqrt a
  let r := s⁻¹
  let φ := Real.arccos (-b / (2 * s))
  have hs : 0 < s := Real.sqrt_pos.mpr ha
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hsq : s ^ 2 = a := Real.sq_sqrt ha.le
  have hcpos : 0 < -b / (2 * s) := div_pos (neg_pos.mpr hb) (by positivity)
  have hclt : -b / (2 * s) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * s)).mpr
    nlinarith [sq_nonneg (b + 2 * s)]
  have hφpos : 0 < φ := Real.arccos_pos.mpr hclt
  have hφlt : φ < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hsin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφpos hφlt
  have hr : 0 < r := inv_pos.mpr hs
  have hcos : 2 * r * Real.cos φ = -(b / a) := by
    rw [show Real.cos φ = -b / (2 * s) from
      Real.cos_arccos (by linarith) hclt.le]
    dsimp [r]
    rw [← hsq]
    field_simp
  have hrsq : r ^ 2 = 1 / a := by
    dsimp [r]
    rw [inv_pow, hsq, one_div]
  obtain ⟨k, hk, hksin⟩ := sin_nonpositive_multiple φ
  refine ⟨k, hk, ?_⟩
  rw [y_eq_sin a b r φ (ne_of_gt hr) (ne_of_gt hsin) hcos hrsq k]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (pow_pos hr k).le hksin)
    (mul_pos hr hsin).le

/-- A constant nonnegative polynomial has nonnegative coefficients. -/
theorem NonnegCoeffs.C {a : ℝ} (ha : 0 ≤ a) : NonnegCoeffs (Polynomial.C a) := by
  intro n
  simp only [Polynomial.coeff_C]
  split_ifs <;> positivity

/-- Every power of the variable has nonnegative coefficients. -/
theorem NonnegCoeffs.X_pow (n : ℕ) : NonnegCoeffs (Polynomial.X ^ n : Polynomial ℝ) := by
  intro k
  simp only [Polynomial.coeff_X_pow]
  split_ifs <;> positivity

/-- Nonnegative coefficients are preserved under addition. -/
theorem NonnegCoeffs.add {p r : Polynomial ℝ}
    (hp : NonnegCoeffs p) (hr : NonnegCoeffs r) : NonnegCoeffs (p + r) := by
  intro n
  rw [Polynomial.coeff_add]
  exact add_nonneg (hp n) (hr n)

/-- Nonnegative coefficients are preserved under multiplication. -/
theorem NonnegCoeffs.mul {p r : Polynomial ℝ}
    (hp : NonnegCoeffs p) (hr : NonnegCoeffs r) : NonnegCoeffs (p * r) := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i.1) (hr i.2)

/-- Lemma 2: a monic quadratic with positive constant coefficient,
negative linear coefficient, and negative discriminant has a nonzero
multiple with nonnegative coefficients. -/
theorem quadratic_case
    (a b : ℝ) (ha : 0 < a) (hb : b < 0)
    (hdiscr : b ^ 2 - 4 * a < 0) :
    HasNonnegMultiple
      (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C a) := by
  classical
  -- Choose the first nonpositive term after y₀.
  have hex := nonpositive_member a b ha hb hdiscr
  let k := Nat.find hex
  have hk : 1 ≤ k ∧ y a b k ≤ 0 := Nat.find_spec hex
  have hk2 : 2 ≤ k := by
    have hkne : k ≠ 1 := by
      intro heq
      norm_num [heq, y] at hk
    omega
  let n := k - 1
  have hn : 1 ≤ n := by omega
  have hnk : n + 1 = k := by omega
  have hyn : 0 < y a b n := by
    by_contra! hnonpos
    exact Nat.find_min hex (show n < k by omega) ⟨hn, hnonpos⟩
  have hynext : y a b (n + 1) ≤ 0 := by simpa [hnk] using hk.2
  refine ⟨q a b n, ?_, ?_⟩
  · -- Its constant coefficient is y₁ = 1.
    have hconst : (q a b n).coeff 0 = 1 := by
      simp [q, Polynomial.finsetSum_coeff,
        y, show 0 < n by omega]
    intro hzero
    simp [hzero] at hconst
  · -- Lemma 3 leaves three terms with nonnegative coefficients.
    have heq : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C a :
        Polynomial ℝ) = Polynomial.C a + Polynomial.C b * Polynomial.X +
          Polynomial.X ^ 2 := by ring
    rw [heq, pq_product a b (ne_of_gt ha) n hn]
    have hmiddle : 0 ≤ -(a * y a b (n + 1)) :=
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le hynext)
    have hc := ((NonnegCoeffs.C ha.le).add
      ((NonnegCoeffs.C hmiddle).mul (NonnegCoeffs.X_pow n))).add
      ((NonnegCoeffs.C hyn.le).mul (NonnegCoeffs.X_pow (n + 1)))
    simpa only [map_neg, neg_mul, sub_eq_add_neg] using hc

/-- A nonzero polynomial with nonnegative coefficients is positive at positive arguments. -/
theorem NonnegCoeffs.eval_pos {p : Polynomial ℝ}
    (hc : NonnegCoeffs p) (hp : p ≠ 0) {x : ℝ} (hx : 0 < x) : 0 < p.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hc i) (pow_nonneg hx.le i)
  · refine ⟨p.natDegree, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    exact mul_pos (lt_of_le_of_ne (hc _) (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hp)))
      (pow_pos hx _)

/-- A nonnegative multiple rules out positive roots of the original polynomial. -/
theorem HasNonnegMultiple.noPositiveRoots {p : Polynomial ℝ}
    (h : HasNonnegMultiple p) (hp : p ≠ 0) : NoPositiveRoots p := by
  obtain ⟨q, hq, hc⟩ := h
  intro x hx hroot
  have hpos := hc.eval_pos (mul_ne_zero hp hq) hx
  have hzero : (p * q).eval x = 0 := by simp [hroot]
  linarith

/-- The property of having a nonnegative multiple is preserved under multiplication. -/
theorem HasNonnegMultiple.mul {p r : Polynomial ℝ}
    (hp : HasNonnegMultiple p) (hr : HasNonnegMultiple r) :
    HasNonnegMultiple (p * r) := by
  obtain ⟨q, hq, hcq⟩ := hp
  obtain ⟨s, hs, hcs⟩ := hr
  refine ⟨q * s, mul_ne_zero hq hs, ?_⟩
  have heq : (p * r) * (q * s) = (p * q) * (r * s) := by ring
  rw [heq]
  exact hcq.mul hcs

/-- Every nonzero constant polynomial has a nonnegative multiple. -/
theorem hasNonnegMultiple_C (a : ℝ) (ha : a ≠ 0) :
    HasNonnegMultiple (Polynomial.C a) := by
  refine ⟨Polynomial.C a⁻¹, by simpa using inv_ne_zero ha, ?_⟩
  rw [← Polynomial.C_mul, mul_inv_cancel₀ ha]
  exact NonnegCoeffs.C (by norm_num)

/-- A monic linear polynomial without positive roots already has nonnegative coefficients. -/
theorem linear_case (a : ℝ)
    (h : NoPositiveRoots (Polynomial.X + Polynomial.C a)) :
    HasNonnegMultiple (Polynomial.X + Polynomial.C a) := by
  have ha : 0 ≤ a := by
    by_contra! ha
    exact h (-a) (neg_pos.mpr ha) (by simp)
  refine ⟨1, one_ne_zero, ?_⟩
  rw [mul_one]
  have hx : NonnegCoeffs (Polynomial.X : Polynomial ℝ) := by
    simpa using NonnegCoeffs.X_pow 1
  exact hx.add (NonnegCoeffs.C ha)

/-- For a monic irreducible quadratic, the discriminant is negative. -/
theorem quadratic_discriminant_neg (a b : ℝ)
    (hi : Irreducible (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C a : Polynomial ℝ)) : b ^ 2 - 4 * a < 0 := by
  by_contra! hd
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (a := (1 : ℝ)) (b := b) (c := a)
    one_ne_zero (by
      refine ⟨Real.sqrt (b ^ 2 - 4 * a), ?_⟩
      dsimp [discrim]
      nlinarith [Real.sq_sqrt hd])
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C a : Polynomial ℝ).natDegree = 2 :=
    (Polynomial.isMonicOfDegree_add_add_two b a).natDegree_eq
  apply hi.not_isRoot_of_natDegree_ne_one (by omega) (x := x)
  simpa [Polynomial.IsRoot, pow_two] using hx

/-- The reduction to monic irreducible factors uses the linear case and Lemma 2. -/
theorem monic_irreducible_case (p : Polynomial ℝ) (hm : p.Monic)
    (hi : Irreducible p) (h : NoPositiveRoots p) : HasNonnegMultiple p := by
  have hpos := hi.natDegree_pos
  have hle := hi.natDegree_le_two
  have hdegree : p.natDegree = 1 ∨ p.natDegree = 2 := by omega
  rcases hdegree with hdegree | hdegree
  · rw [hm.eq_X_add_C hdegree] at h ⊢
    exact linear_case _ h
  · obtain ⟨b, a, rfl⟩ := Polynomial.isMonicOfDegree_two_iff.mp ⟨hdegree, hm⟩
    have hd := quadratic_discriminant_neg a b hi
    have ha : 0 < a := by nlinarith [sq_nonneg b]
    by_cases hb : b < 0
    · exact quadratic_case a b ha hb hd
    · have hb : 0 ≤ b := le_of_not_gt hb
      refine ⟨1, one_ne_zero, ?_⟩
      rw [mul_one]
      exact ((NonnegCoeffs.X_pow 2).add
        ((NonnegCoeffs.C hb).mul (by simpa using NonnegCoeffs.X_pow 1))).add
        (NonnegCoeffs.C ha.le)

/-- Factorization reduces the reverse implication to monic irreducible polynomials. -/
theorem hasNonnegMultiple_of_noPositiveRoots
    (p : Polynomial ℝ) (hp : p ≠ 0) (h : NoPositiveRoots p) : HasNonnegMultiple p := by
  classical
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n = 0
    · have heq := Polynomial.eq_C_of_natDegree_eq_zero (hd.trans hn)
      rw [heq] at hp ⊢
      exact hasNonnegMultiple_C _ (by simpa using hp)
    · obtain ⟨f, hfm, hfi, g, hfg⟩ := Polynomial.exists_monic_irreducible_factor p
        (Polynomial.not_isUnit_of_natDegree_pos p (by omega))
      have hg : g ≠ 0 := by
        intro hg
        apply hp
        rw [hfg, hg, mul_zero]
      have hfroots : NoPositiveRoots f := by
        intro x hx hroot
        apply h x hx
        simp [hfg, hroot]
      have hgroots : NoPositiveRoots g := by
        intro x hx hroot
        apply h x hx
        simp [hfg, hroot]
      have hdegrees : n = f.natDegree + g.natDegree := by
        rw [← hd, hfg, Polynomial.natDegree_mul hfi.ne_zero hg]
      have hlt : g.natDegree < n := by
        have := hfi.natDegree_pos
        omega
      rw [hfg]
      exact (monic_irreducible_case f hfm hfi hfroots).mul
        (ih g.natDegree hlt g hg hgroots rfl)

/-- Main theorem of the note (Stanley, Chapter 3, Exercise 3(a)).
The reverse implication depends on `quadratic_case` (Lemma 2). -/
theorem no_positive_roots_iff
    (p : Polynomial ℝ) (hp : p ≠ 0) :
    HasNonnegMultiple p ↔ NoPositiveRoots p := by
  constructor
  · intro h
    exact h.noPositiveRoots hp
  · exact hasNonnegMultiple_of_noPositiveRoots p hp

end NoPosRoots
