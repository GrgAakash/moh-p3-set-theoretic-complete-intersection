import Mathlib

/-!
# Linear independence of the eight basis polynomials over `ℚ[t^8]`

The eight polynomials `vv 0, …, vv 7` are the images under the parametrization
`rho` of the eight module generators `hh 0, …, hh 7` used in `MohP3.Kernel`.
Their trailing degrees `oo i` are pairwise distinct modulo `8`; since the
trailing degree of `p.comp (X^8)` is always a multiple of `8`, this forces
`∑ i, (p i).comp (X ^ 8) * vv i = 0 → p = 0`.
-/

noncomputable section

open Polynomial

namespace MohP3

/-- `vv i = rho (hh i)`, written so that the trailing monomial is visible. -/
def vv : Fin 8 → ℚ[X] :=
  ![1, X^6*(1+X^25), X^10, X^12*(1+2*X^25+X^50), X^41, X^43*(3+3*X^25+X^50),
    X^45*(-2-X^25), X^47]

/-- The trailing degrees of the `vv i`. -/
def oo : Fin 8 → ℕ := ![0, 6, 10, 12, 41, 43, 45, 47]

/-- The coefficients of `p.comp (X^8)` are supported on multiples of `8`. -/
lemma comp_X8_coeff (p : ℚ[X]) (n : ℕ) (hn : ¬ (8 ∣ n)) : (p.comp (X^8)).coeff n = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq]
  | monomial k a =>
      rw [Polynomial.monomial_comp, ← pow_mul, coeff_C_mul, coeff_X_pow]
      have : n ≠ 8*k := by rintro rfl; exact hn ⟨k, rfl⟩
      simp [this]

lemma comp_X8_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : p.comp (X^8) ≠ 0 := by
  rw [Ne, Polynomial.comp_eq_zero_iff]
  push_neg
  refine ⟨hp, fun _ hq => ?_⟩
  have := congrArg (fun r => r.natDegree) hq
  simp at this

lemma dvd8_ntd {p : ℚ[X]} (hp : p ≠ 0) : 8 ∣ (p.comp (X^8)).natTrailingDegree := by
  by_contra h
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (comp_X8_ne_zero hp))
    (comp_X8_coeff p _ h)

lemma ntd_X_pow_mul (n : ℕ) (w : ℚ[X]) (hw : w.coeff 0 ≠ 0) :
    ((X:ℚ[X])^n * w).natTrailingDegree = n := by
  have hw0 : w ≠ 0 := fun h => hw (by simp [h])
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) hw0,
    natTrailingDegree_X_pow, Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hw), add_zero]

lemma vv_ne_zero (i : Fin 8) : vv i ≠ 0 := by
  fin_cases i <;> simp [vv] <;> intro h <;>
    · have := congrArg (fun r : ℚ[X] => r.coeff 0) h
      simp [coeff_X_pow] at this

lemma ntd_vv (i : Fin 8) : (vv i).natTrailingDegree = oo i := by
  fin_cases i
  · simp [vv, oo]
  · simpa [vv, oo] using ntd_X_pow_mul 6 (1+X^25) (by simp [coeff_X_pow])
  · simp [vv, oo, natTrailingDegree_X_pow]
  · simpa [vv, oo] using ntd_X_pow_mul 12 (1+2*X^25+X^50) (by simp [coeff_X_pow])
  · simp [vv, oo, natTrailingDegree_X_pow]
  · simpa [vv, oo] using ntd_X_pow_mul 43 (3+3*X^25+X^50) (by simp [coeff_X_pow])
  · simpa [vv, oo] using ntd_X_pow_mul 45 (-2-X^25) (by simp [coeff_X_pow])
  · simp [vv, oo, natTrailingDegree_X_pow]

lemma oo_mod_inj {i j : Fin 8} (h : oo i % 8 = oo j % 8) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [oo]

/-- The eight polynomials `vv i` are linearly independent over `ℚ[t^8]`. -/
theorem indep (p : Fin 8 → ℚ[X]) (hs : ∑ i, (p i).comp (X^8) * vv i = 0) :
    ∀ i, p i = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hcon
  set w : Fin 8 → ℚ[X] := fun i => (p i).comp (X^8) * vv i with hw
  set S : Finset (Fin 8) := Finset.univ.filter (fun i => p i ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨i0, by simp [hSdef, hi0]⟩
  have hwne : ∀ i ∈ S, w i ≠ 0 := by
    intro i hi
    simp [hSdef] at hi
    exact mul_ne_zero (comp_X8_ne_zero hi) (vv_ne_zero i)
  have hntd : ∀ i ∈ S, (w i).natTrailingDegree % 8 = oo i % 8 := by
    intro i hi
    simp [hSdef] at hi
    rw [hw]
    simp only
    rw [Polynomial.natTrailingDegree_mul (comp_X8_ne_zero hi) (vv_ne_zero i), ntd_vv]
    obtain ⟨k, hk⟩ := dvd8_ntd hi
    omega
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun i => (w i).natTrailingDegree) hS
  set d := (w m).natTrailingDegree with hd
  have key : (∑ i, w i).coeff d = (w m).coeff d := by
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
    · intro b _ hbm
      by_cases hb : b ∈ S
      · have h1 : d ≤ (w b).natTrailingDegree := hmin b hb
        have h2 : (w b).natTrailingDegree ≠ d := fun he =>
          hbm (oo_mod_inj (by rw [← hntd b hb, ← hntd m hmS, he]))
        exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_le_of_ne h1 (Ne.symm h2))
      · have : p b = 0 := by simpa [hSdef] using hb
        simp [hw, this]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  rw [hs] at key
  simp at key
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (hwne m hmS)) key.symm

end MohP3
