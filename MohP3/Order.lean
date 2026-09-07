import Mathlib

/-!
# Weighted orders on `k[[x,y,z]]` and `k[[y]]`

For the formal-local generation theorem we need a filtration of
`k[[x,y,z]]` which is compatible with the sixteen closure identities of
`MohP3.Closure`.  The total-degree filtration is *not* (the identities
involve cancellations in top degree); the correct one is the weighted
filtration attached to the parametrization itself,

    wt x = 6,  wt y = 8,  wt z = 10.

`WOrd F n` says that every monomial occurring in `F` has weight at least
`n`; `YOrd p n` is the corresponding statement in `k[[y]]`, where the
variable stands for `y` and hence carries weight `8`.

This file develops the elementary calculus of these two predicates:
they are additive submonoids, they add under multiplication, a series
with `WOrd F n` for every `n` vanishes, and a family of series whose
orders tend to infinity can be summed coefficientwise.
-/

noncomputable section

open MvPowerSeries

namespace MohP3.Wt

variable {k : Type*} [CommRing k]

/-- The weight of a monomial `x^a y^b z^c` is `6a + 8b + 10c`. -/
def wt (d : Fin 3 →₀ ℕ) : ℕ := 6 * d 0 + 8 * d 1 + 10 * d 2

lemma wt_add (d e : Fin 3 →₀ ℕ) : wt (d + e) = wt d + wt e := by
  simp only [wt, Finsupp.add_apply]; ring

/-! ### The weighted order on `k[[x,y,z]]` -/

/-- `WOrd F n`: all monomials of `F` have weight `≥ n`. -/
def WOrd (F : MvPowerSeries (Fin 3) k) (n : ℕ) : Prop :=
  ∀ d, wt d < n → coeff d F = 0

lemma wOrd_zero (F : MvPowerSeries (Fin 3) k) : WOrd F 0 := by
  intro d hd; exact absurd hd (Nat.not_lt_zero _)

lemma wOrd_mono {F : MvPowerSeries (Fin 3) k} {m n : ℕ} (h : n ≤ m) (hF : WOrd F m) :
    WOrd F n := fun d hd => hF d (lt_of_lt_of_le hd h)

lemma wOrd_of_zero {n : ℕ} : WOrd (0 : MvPowerSeries (Fin 3) k) n := by
  intro d _; simp

lemma wOrd_add {F G : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) (hG : WOrd G n) :
    WOrd (F + G) n := by
  intro d hd; simp [hF d hd, hG d hd]

lemma wOrd_neg {F : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) : WOrd (-F) n := by
  intro d hd; simp [hF d hd]

lemma wOrd_sub {F G : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) (hG : WOrd G n) :
    WOrd (F - G) n := by
  rw [sub_eq_add_neg]; exact wOrd_add hF (wOrd_neg hG)

lemma wOrd_sum {ι : Type*} {s : Finset ι} {F : ι → MvPowerSeries (Fin 3) k} {n : ℕ}
    (h : ∀ i ∈ s, WOrd (F i) n) : WOrd (∑ i ∈ s, F i) n := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (wOrd_of_zero (k := k) (n := n))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact wOrd_add (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma wOrd_mul {F G : MvPowerSeries (Fin 3) k} {m n : ℕ} (hF : WOrd F m) (hG : WOrd G n) :
    WOrd (F * G) (m + n) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨d1, d2⟩ hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hw : wt d1 + wt d2 = wt d := by rw [← wt_add, hp]
  rcases lt_or_ge (wt d1) m with h1 | h1
  · rw [hF d1 h1, zero_mul]
  · have h2 : wt d2 < n := by omega
    rw [hG d2 h2, mul_zero]

lemma wOrd_mul' {F G : MvPowerSeries (Fin 3) k} {m n p : ℕ} (hp : p ≤ m + n)
    (hF : WOrd F m) (hG : WOrd G n) : WOrd (F * G) p :=
  wOrd_mono hp (wOrd_mul hF hG)

lemma wOrd_pow {F : MvPowerSeries (Fin 3) k} {m : ℕ} (hF : WOrd F m) (e : ℕ) :
    WOrd (F ^ e) (e * m) := by
  induction e with
  | zero => simpa using wOrd_zero (1 : MvPowerSeries (Fin 3) k)
  | succ e ih =>
      have := wOrd_mul ih hF
      rw [pow_succ]
      exact wOrd_mono (by ring_nf; omega) this

lemma wOrd_X (i : Fin 3) : WOrd (X i : MvPowerSeries (Fin 3) k) (wt (Finsupp.single i 1)) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_X]
  split
  · next h => exact absurd (h ▸ hd) (lt_irrefl _)
  · rfl

lemma wOrd_eq_zero {F : MvPowerSeries (Fin 3) k} (h : ∀ n, WOrd F n) : F = 0 := by
  ext d
  simpa using h (wt d + 1) d (by omega)

/-! ### The weighted order on `k[[y]]` -/

/-- `YOrd p n`: all monomials `y^m` of `p` have weight `8m ≥ n`. -/
def YOrd (p : PowerSeries k) (n : ℕ) : Prop :=
  ∀ m, 8 * m < n → PowerSeries.coeff m p = 0

lemma yOrd_zero (p : PowerSeries k) : YOrd p 0 := by
  intro m hm; exact absurd hm (Nat.not_lt_zero _)

lemma yOrd_mono {p : PowerSeries k} {m n : ℕ} (h : n ≤ m) (hp : YOrd p m) : YOrd p n :=
  fun d hd => hp d (lt_of_lt_of_le hd h)

lemma yOrd_of_zero {n : ℕ} : YOrd (0 : PowerSeries k) n := by intro m _; simp

lemma yOrd_add {p q : PowerSeries k} {n : ℕ} (hp : YOrd p n) (hq : YOrd q n) :
    YOrd (p + q) n := by intro m hm; simp [hp m hm, hq m hm]

lemma yOrd_neg {p : PowerSeries k} {n : ℕ} (hp : YOrd p n) : YOrd (-p) n := by
  intro m hm; simp [hp m hm]

lemma yOrd_sub {p q : PowerSeries k} {n : ℕ} (hp : YOrd p n) (hq : YOrd q n) :
    YOrd (p - q) n := by rw [sub_eq_add_neg]; exact yOrd_add hp (yOrd_neg hq)

lemma yOrd_sum {ι : Type*} {s : Finset ι} {p : ι → PowerSeries k} {n : ℕ}
    (h : ∀ i ∈ s, YOrd (p i) n) : YOrd (∑ i ∈ s, p i) n := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (yOrd_of_zero (k := k) (n := n))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact yOrd_add (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma yOrd_mul {p q : PowerSeries k} {m n : ℕ} (hp : YOrd p m) (hq : YOrd q n) :
    YOrd (p * q) (m + n) := by
  intro d hd
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨d1, d2⟩ hpair
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpair
  rcases lt_or_ge (8 * d1) m with h1 | h1
  · rw [hp d1 h1, zero_mul]
  · have h2 : 8 * d2 < n := by omega
    rw [hq d2 h2, mul_zero]

lemma yOrd_mul' {p q : PowerSeries k} {m n r : ℕ} (hr : r ≤ m + n)
    (hp : YOrd p m) (hq : YOrd q n) : YOrd (p * q) r :=
  yOrd_mono hr (yOrd_mul hp hq)

lemma yOrd_X_pow (e : ℕ) : YOrd ((PowerSeries.X : PowerSeries k) ^ e) (8 * e) := by
  intro m hm
  rw [PowerSeries.coeff_X_pow]
  have : m ≠ e := by omega
  simp [this]

/-- A monomial `c * y^e` has weighted order at least `n` as soon as `n ≤ 8e`. -/
lemma yOrd_monomial (c : k) (e n : ℕ) (h : n ≤ 8 * e) :
    YOrd (PowerSeries.C c * (PowerSeries.X : PowerSeries k) ^ e) n :=
  yOrd_mul' (by omega) (yOrd_zero _) (yOrd_X_pow e)

/-! ### Coefficientwise limits

A family of series whose weighted orders tend to infinity has a
coefficientwise limit, which is approximated by its partial sums. -/

lemma exists_yOrd_limit (g : ℕ → PowerSeries k) (s₀ : ℕ)
    (hg : ∀ s, YOrd (g s) (s - s₀)) :
    ∃ G : PowerSeries k, ∀ M, YOrd (G - ∑ s ∈ Finset.range M, g s) (M - s₀) := by
  refine ⟨PowerSeries.mk fun m => ∑ s ∈ Finset.range (8 * m + s₀ + 1), PowerSeries.coeff m (g s),
    ?_⟩
  intro M m hm
  have hMle : 8 * m + s₀ + 1 ≤ M := by omega
  have hzero : ∀ s ∈ Finset.range M, s ∉ Finset.range (8 * m + s₀ + 1) →
      PowerSeries.coeff m (g s) = 0 := by
    intro s _ hs
    rw [Finset.mem_range] at hs
    exact hg s m (by omega)
  have hsub : Finset.range (8 * m + s₀ + 1) ⊆ Finset.range M := by
    intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
  simp only [map_sub, PowerSeries.coeff_mk, map_sum]
  rw [Finset.sum_subset hsub hzero, sub_self]

lemma exists_wOrd_limit (g : ℕ → MvPowerSeries (Fin 3) k) (s₀ : ℕ)
    (hg : ∀ s, WOrd (g s) (s - s₀)) :
    ∃ G : MvPowerSeries (Fin 3) k, ∀ M, WOrd (G - ∑ s ∈ Finset.range M, g s) (M - s₀) := by
  let G : MvPowerSeries (Fin 3) k :=
    fun d => ∑ s ∈ Finset.range (wt d + s₀ + 1), coeff d (g s)
  refine ⟨G, ?_⟩
  intro M d hd
  have hMle : wt d + s₀ + 1 ≤ M := by omega
  have hzero : ∀ s ∈ Finset.range M, s ∉ Finset.range (wt d + s₀ + 1) → coeff d (g s) = 0 := by
    intro s _ hs
    rw [Finset.mem_range] at hs
    exact hg s d (by omega)
  have hco : coeff d G = ∑ s ∈ Finset.range (wt d + s₀ + 1), coeff d (g s) := rfl
  have hsub : Finset.range (wt d + s₀ + 1) ⊆ Finset.range M := by
    intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
  rw [map_sub, hco, map_sum, Finset.sum_subset hsub hzero, sub_self]

/-! ### The weight-homogeneous decomposition -/

/-- The monomial exponent `x^a y^b z^c`. -/
def dd (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] lemma dd_apply_zero (a b c : ℕ) : dd a b c 0 = a := by
  simp [dd]

@[simp] lemma dd_apply_one (a b c : ℕ) : dd a b c 1 = b := by
  simp [dd]

@[simp] lemma dd_apply_two (a b c : ℕ) : dd a b c 2 = c := by
  simp [dd]

@[simp] lemma wt_dd (a b c : ℕ) : wt (dd a b c) = 6 * a + 8 * b + 10 * c := by
  simp [wt]

lemma dd_self (d : Fin 3 →₀ ℕ) : dd (d 0) (d 1) (d 2) = d := by
  ext i
  fin_cases i <;> simp

lemma dd_injective {a b c a' b' c' : ℕ} (h : dd a b c = dd a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (fun d => d 0) h
  · simpa using congrArg (fun d => d 1) h
  · simpa using congrArg (fun d => d 2) h

lemma monomial_dd (a b c : ℕ) :
    (MvPowerSeries.monomial (dd a b c) (1 : k)) =
      (X 0) ^ a * (X 1) ^ b * (X 2) ^ c := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial, one_mul, one_mul]
  rfl

/-- The finite index set of monomials of weight exactly `n`. -/
def En (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p => 6 * p.1 + 8 * p.2.1 + 10 * p.2.2 = n)

lemma mem_En {n : ℕ} {p : ℕ × ℕ × ℕ} (hp : p ∈ En n) :
    6 * p.1 + 8 * p.2.1 + 10 * p.2.2 = n := by
  simpa [En] using (Finset.mem_filter.mp hp).2

lemma mem_En_of {n a b c : ℕ} (h : 6 * a + 8 * b + 10 * c = n) : (a, b, c) ∈ En n := by
  simp only [En, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨by omega, by omega, by omega⟩, h⟩

/-- Splitting off the weight-`n` homogeneous part of a series of weighted order `≥ n`. -/
lemma wOrd_sub_top_part (F : MvPowerSeries (Fin 3) k) (n : ℕ) (hF : WOrd F n) :
    WOrd (F - ∑ p ∈ En n, MvPowerSeries.monomial (dd p.1 p.2.1 p.2.2)
      (coeff (dd p.1 p.2.1 p.2.2) F)) (n + 1) := by
  classical
  intro d hd
  rw [map_sub, map_sum]
  have hcoe : ∀ p : ℕ × ℕ × ℕ,
      coeff d (MvPowerSeries.monomial (dd p.1 p.2.1 p.2.2) (coeff (dd p.1 p.2.1 p.2.2) F)) =
        if d = dd p.1 p.2.1 p.2.2 then coeff d F else 0 := by
    intro p
    rw [MvPowerSeries.coeff_monomial]
    split
    · next h => rw [h]
    · rfl
  simp only [hcoe]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
  · rw [hF d hlt]
    refine sub_eq_zero_of_eq ?_
    refine (Finset.sum_eq_zero ?_).symm
    intro p hp
    have hwp : wt (dd p.1 p.2.1 p.2.2) = n := by rw [wt_dd]; exact mem_En hp
    have : d ≠ dd p.1 p.2.1 p.2.2 := by
      intro hdp; rw [hdp, hwp] at hlt; omega
    simp [this]
  · have hp₀ : (d 0, d 1, d 2) ∈ En n := mem_En_of (by simpa [wt] using heq)
    rw [Finset.sum_eq_single (d 0, d 1, d 2)]
    · rw [dd_self]
      simp
    · intro b _ hb
      have : d ≠ dd b.1 b.2.1 b.2.2 := by
        intro hdb
        have hdb' : dd (d 0) (d 1) (d 2) = dd b.1 b.2.1 b.2.2 := by rw [dd_self, hdb]
        obtain ⟨h1, h2, h3⟩ := dd_injective hdb'
        exact hb (by rw [Prod.ext_iff, Prod.ext_iff]; exact ⟨h1.symm, h2.symm, h3.symm⟩)
      simp [this]
    · intro h; exact absurd hp₀ h

end MohP3.Wt
