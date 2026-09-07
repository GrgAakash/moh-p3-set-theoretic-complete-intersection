import MohP3.Global
import MohP3.Ara

/-!
# Moh P3: the height of `P` and the arithmetic rank of `P`

The global theorem of `MohP3.Global` says that the two explicit polynomials
`H1, H2` cut out the Moh curve set-theoretically, `Ideal.radical Q = P`.  That
gives the upper bound `arithRank P ≤ 2`.  Here we prove the matching lower
bound, i.e. that `P` really has height `2`:

* `MohP3.height_P_le_two` — Krull's height theorem applied to `P`, a minimal
  prime of the two-generated ideal `Q`;
* `MohP3.two_le_height_P` — the chain of primes `⊥ < Psurf < P`, where `Psurf`
  is the (prime) ideal of the surface `y^5 = z^4`, which contains the Moh
  curve;
* `MohP3.height_P` — `P.height = 2`;
* `MohP3.arithRank_P` — `arithRank P = 2`, i.e. `P` is a set-theoretic complete
  intersection in the literal sense.

The surface `y^5 = z^4` is parametrized by `x ↦ s`, `y ↦ w^4`, `z ↦ w^5`, and
the Moh parametrization factors through it via `s ↦ t^6 + t^31`, `w ↦ t^2`;
that is the content of `MohP3.rho_eq_tau_comp_sigma`.  Consequently the prime
`Psurf = ker sigma` is contained in `P = ker rho`, and it is a *strictly*
intermediate prime because `y^5 - z^4 ≠ 0` lies in it while `f4` does not.
-/

noncomputable section

open MvPolynomial

namespace MohP3

/-! ### `P` is a minimal prime of `Q`, hence has height at most two -/

/-- `P` is a minimal prime of `Q`: indeed `Q.radical = P`. -/
theorem P_mem_minimalPrimes_Q : P ∈ Q.minimalPrimes :=
  mem_minimalPrimes_of_radical_eq P_isPrime radical_Q

open scoped Classical in
/-- Krull's height theorem: `P` is minimal over the two-generated ideal `Q`. -/
theorem height_P_le_two : P.height ≤ 2 := by
  have hQ : Q = Ideal.span ((({H1, H2} : Finset R) : Finset R) : Set R) := by
    simp [Q]
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (p := P) (s := ({H1, H2} : Finset R)) (by rw [← hQ]; exact P_mem_minimalPrimes_Q)
  refine h.trans ?_
  have : ({H1, H2} : Finset R).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  exact_mod_cast this

/-! ### The intermediate prime: the surface `y^5 = z^4` -/

/-- The coordinate ring `ℚ[s,w]` of the parametrizing plane of the surface
`y^5 = z^4`. -/
abbrev Rsurf := MvPolynomial (Fin 2) ℚ

/-- The parametrization `x ↦ s`, `y ↦ w^4`, `z ↦ w^5` of the surface
`y^5 = z^4` (times the `x`-line). -/
def sigma : R →+* Rsurf :=
  eval₂Hom C ![X 0, (X 1)^4, (X 1)^5]

/-- The map `s ↦ t^6 + t^31`, `w ↦ t^2` through which the Moh parametrization
factors. -/
def tau : Rsurf →+* T :=
  eval₂Hom Polynomial.C ![Polynomial.X^6 + Polynomial.X^31, Polynomial.X^2]

/-- The Moh curve lies on the surface `y^5 = z^4`. -/
theorem rho_eq_tau_comp_sigma : rho = tau.comp sigma := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [sigma, tau]
  · fin_cases i <;> simp [sigma, tau, rho] <;> ring

@[simp] lemma sigma_x : sigma x = X 0 := by simp [sigma, x]

@[simp] lemma sigma_y : sigma y = (X 1 : Rsurf)^4 := by
  simp [sigma, y, Matrix.cons_val_one]

@[simp] lemma sigma_z : sigma z = (X 1 : Rsurf)^5 := by
  simp [sigma, z]

/-- The ideal of the surface `y^5 = z^4`. -/
def Psurf : Ideal R := RingHom.ker sigma

lemma mem_Psurf_iff {g : R} : g ∈ Psurf ↔ sigma g = 0 := Iff.rfl

theorem Psurf_isPrime : Psurf.IsPrime := RingHom.ker_isPrime sigma

/-- Every polynomial vanishing on the surface vanishes on the Moh curve. -/
theorem Psurf_le_P : Psurf ≤ P := by
  rw [← kernel_rho]
  intro g hg
  rw [mem_Psurf_iff] at hg
  rw [RingHom.mem_ker, rho_eq_tau_comp_sigma, RingHom.comp_apply, hg, map_zero]

/-- `y^5 - z^4` is a nonzero element of `Psurf`. -/
theorem Psurf_ne_bot : Psurf ≠ ⊥ := by
  have hmem : y^5 - z^4 ∈ Psurf := by
    rw [mem_Psurf_iff]
    simp only [map_sub, map_pow, sigma_y, sigma_z]
    ring
  have hne : (y^5 - z^4 : R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![0, 1, 0]) h
    simp [y, z] at this
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hne hmem

/-- `f4` vanishes on the curve but not on the surface. -/
theorem f4_notMem_Psurf : f4 ∉ Psurf := by
  intro h
  rw [mem_Psurf_iff] at h
  have h2 : (MvPolynomial.eval ![(1 : ℚ), 1]) (sigma f4) = 0 := by rw [h, map_zero]
  rw [f4] at h2
  simp only [map_sub, map_add, map_mul, map_pow, sigma_x, sigma_y, sigma_z, map_ofNat,
    eval_X] at h2
  norm_num at h2

theorem Psurf_lt_P : Psurf < P :=
  lt_of_le_of_ne Psurf_le_P (fun h => f4_notMem_Psurf (h ▸ f4_mem))

theorem bot_lt_Psurf : (⊥ : Ideal R) < Psurf :=
  lt_of_le_of_ne bot_le (Ne.symm Psurf_ne_bot)

/-! ### The height of `P` -/

theorem two_le_height_P : 2 ≤ P.height := by
  haveI := P_isPrime
  haveI := Psurf_isPrime
  haveI : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal R).height + 1 ≤ Psurf.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime bot_lt_Psurf
  have h2 : Psurf.height + 1 ≤ P.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime Psurf_lt_P
  have hbot : (⊥ : Ideal R).height = 0 := Ideal.height_bot
  calc (2 : ℕ∞) = (⊥ : Ideal R).height + 1 + 1 := by rw [hbot]; rfl
    _ ≤ Psurf.height + 1 := by gcongr
    _ ≤ P.height := h2

/-- **The height of the Moh curve ideal is two.** -/
theorem height_P : P.height = 2 := le_antisymm height_P_le_two two_le_height_P

/-! ### The arithmetic rank -/

open scoped Classical in
/-- **The arithmetic rank of `P` is two**: two equations suffice (the explicit
witnesses `H1, H2`), and by Krull's height theorem one equation cannot suffice.
Thus `P` is a set-theoretic complete intersection in the literal sense,
`arithRank P = height P = 2`. -/
theorem arithRank_P : arithRank P = 2 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (arithRank_le ({H1, H2} : Finset R) ?_) ?_
    · have hQ : Ideal.span ((({H1, H2} : Finset R) : Finset R) : Set R) = Q := by
        simp [Q]
      rw [hQ, radical_Q, P_radical]
    · have : ({H1, H2} : Finset R).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact_mod_cast this
  · calc (2 : ℕ∞) = P.height := height_P.symm
      _ ≤ arithRank P := height_le_arithRank P P_isPrime

end MohP3
