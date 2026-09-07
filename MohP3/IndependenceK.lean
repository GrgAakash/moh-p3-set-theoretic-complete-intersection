import Mathlib

/-!
# Linear independence of the eight basis polynomials over `k[t^8]`

This is the analogue of `MohP3.Independence` for an arbitrary field `k` of
characteristic zero.  The eight polynomials `vvK k 0, …, vvK k 7` are the
images under the parametrization `rho_k` of the eight module generators
`hh 0, …, hh 7`.  Their trailing degrees are pairwise distinct modulo `8`,
and the trailing degree of `p.comp (X^8)` is always a multiple of `8`, so
`∑ i, (p i).comp (X ^ 8) * vvK k i = 0` forces `p = 0`.
-/

noncomputable section

open Polynomial

namespace MohP3.K

variable (k : Type*) [Field k]

/-- `vvK k i = rho_k (hh i)`, written so that the trailing monomial is visible. -/
def vvK : Fin 8 → Polynomial k :=
  ![1, X ^ 6 * (1 + X ^ 25), X ^ 10, X ^ 12 * (1 + 2 * X ^ 25 + X ^ 50), X ^ 41,
    X ^ 43 * (3 + 3 * X ^ 25 + X ^ 50), X ^ 45 * (-2 - X ^ 25), X ^ 47]

/-- The trailing degrees of the `vvK k i`. -/
def ooK : Fin 8 → ℕ := ![0, 6, 10, 12, 41, 43, 45, 47]

variable {k}

/-- The coefficients of `p.comp (X^8)` are supported on multiples of `8`. -/
lemma comp_X8_coeff (p : Polynomial k) (n : ℕ) (hn : ¬ (8 ∣ n)) : (p.comp (X ^ 8)).coeff n = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq]
  | monomial m a =>
      rw [Polynomial.monomial_comp, ← pow_mul, coeff_C_mul, coeff_X_pow]
      have : n ≠ 8 * m := by rintro rfl; exact hn ⟨m, rfl⟩
      simp [this]

lemma comp_X8_ne_zero {p : Polynomial k} (hp : p ≠ 0) : p.comp (X ^ 8) ≠ 0 := by
  rw [Ne, Polynomial.comp_eq_zero_iff]
  push_neg
  refine ⟨hp, fun _ hq => ?_⟩
  have := congrArg (fun r => r.natDegree) hq
  simp at this

lemma dvd8_ntd {p : Polynomial k} (hp : p ≠ 0) : 8 ∣ (p.comp (X ^ 8)).natTrailingDegree := by
  by_contra h
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (comp_X8_ne_zero hp))
    (comp_X8_coeff p _ h)

lemma ntd_X_pow_mul (n : ℕ) (w : Polynomial k) (hw : w.coeff 0 ≠ 0) :
    ((X : Polynomial k) ^ n * w).natTrailingDegree = n := by
  have hw0 : w ≠ 0 := fun h => hw (by simp [h])
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) hw0,
    natTrailingDegree_X_pow, Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hw), add_zero]

variable (k) [CharZero k]

lemma vvK_ne_zero (i : Fin 8) : vvK k i ≠ 0 := by
  fin_cases i <;> simp [vvK] <;> intro h <;>
    · have := congrArg (fun r : Polynomial k => r.coeff 0) h
      simp [coeff_X_pow] at this

lemma ntd_vvK (i : Fin 8) : (vvK k i).natTrailingDegree = ooK i := by
  fin_cases i
  · simp [vvK, ooK]
  · simpa [vvK, ooK] using ntd_X_pow_mul 6 (1 + X ^ 25 : Polynomial k) (by simp [coeff_X_pow])
  · simp [vvK, ooK, natTrailingDegree_X_pow]
  · simpa [vvK, ooK] using
      ntd_X_pow_mul 12 (1 + 2 * X ^ 25 + X ^ 50 : Polynomial k) (by simp [coeff_X_pow])
  · simp [vvK, ooK, natTrailingDegree_X_pow]
  · simpa [vvK, ooK] using
      ntd_X_pow_mul 43 (3 + 3 * X ^ 25 + X ^ 50 : Polynomial k) (by simp [coeff_X_pow])
  · simpa [vvK, ooK] using
      ntd_X_pow_mul 45 (-2 - X ^ 25 : Polynomial k) (by simp [coeff_X_pow])
  · simp [vvK, ooK, natTrailingDegree_X_pow]

lemma ooK_mod_inj {i j : Fin 8} (h : ooK i % 8 = ooK j % 8) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [ooK]

/-- The eight polynomials `vvK k i` are linearly independent over `k[t^8]`. -/
theorem indepK (p : Fin 8 → Polynomial k) (hs : ∑ i, (p i).comp (X ^ 8) * vvK k i = 0) :
    ∀ i, p i = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hcon
  set w : Fin 8 → Polynomial k := fun i => (p i).comp (X ^ 8) * vvK k i with hw
  set S : Finset (Fin 8) := Finset.univ.filter (fun i => p i ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨i0, by simp [hSdef, hi0]⟩
  have hwne : ∀ i ∈ S, w i ≠ 0 := by
    intro i hi
    simp [hSdef] at hi
    exact mul_ne_zero (comp_X8_ne_zero hi) (vvK_ne_zero k i)
  have hntd : ∀ i ∈ S, (w i).natTrailingDegree % 8 = ooK i % 8 := by
    intro i hi
    simp [hSdef] at hi
    rw [hw]
    simp only
    rw [Polynomial.natTrailingDegree_mul (comp_X8_ne_zero hi) (vvK_ne_zero k i), ntd_vvK]
    obtain ⟨m, hm⟩ := dvd8_ntd hi
    omega
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun i => (w i).natTrailingDegree) hS
  set d := (w m).natTrailingDegree with hd
  have key : (∑ i, w i).coeff d = (w m).coeff d := by
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
    · intro b _ hbm
      by_cases hb : b ∈ S
      · have h1 : d ≤ (w b).natTrailingDegree := hmin b hb
        have h2 : (w b).natTrailingDegree ≠ d := fun he =>
          hbm (ooK_mod_inj (by rw [← hntd b hb, ← hntd m hmS, he]))
        exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_le_of_ne h1 (Ne.symm h2))
      · have : p b = 0 := by simpa [hSdef] using hb
        simp [hw, this]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  rw [hs] at key
  simp at key
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (hwne m hmS)) key.symm

end MohP3.K
