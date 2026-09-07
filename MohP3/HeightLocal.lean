import MohP3.Generation
import MohP3.Ara
import MohP3.MvPowerSeriesAux

/-!
# Moh P3: the height of `Pk` and the arithmetic rank of `Pk` after completion

This is the formal-local analogue of `MohP3.Height`.  Over `k[[x,y,z]]` for a
characteristic-zero field `k` we prove

* `MohP3.FormalLocal.height_Pk` — `(Pk k).height = 2`;
* `MohP3.FormalLocal.arithRank_Pk` — `arithRank (Pk k) = 2`.

The upper bound is Krull's height theorem, applied to `Pk`, which by the
formal-local theorem of `MohP3.Generation` is a minimal prime of the
two-generated ideal `Qk`; this needs `k[[x,y,z]]` to be Noetherian, which is
supplied by `MohP3.MvPowerSeriesAux`.

The lower bound is the chain of primes `⊥ < Psurfk < Pk`, where `Psurfk` is the
kernel of the substitution `x ↦ s`, `y ↦ w^4`, `z ↦ w^5` into `k[[s,w]]`, i.e.
the ideal of the surface `y^5 = z^4`.  The Moh parametrization factors through
that surface via `s ↦ t^6 + t^31`, `w ↦ t^2`, whence `Psurfk ≤ ker psi = Pk`;
the inclusion is strict because `f4` does not vanish on the surface.
-/

noncomputable section

open MvPowerSeries

namespace MohP3.FormalLocal

variable (k : Type*) [Field k] [CharZero k]

/-! ### `Pk` is prime, and is a minimal prime of `Qk` -/

theorem Pk_isPrime : (Pk k).IsPrime := ker_psi k ▸ ker_psi_isPrime k

/-- The formal-local theorem, in the form `(Qk).radical = Pk`. -/
theorem radical_Qk_eq_Pk : (Qk k).radical = Pk k := by
  rw [formalLocal_radical_Qk, ker_psi]

theorem Pk_mem_minimalPrimes_Qk : Pk k ∈ (Qk k).minimalPrimes :=
  mem_minimalPrimes_of_radical_eq (Pk_isPrime k) (radical_Qk_eq_Pk k)

open scoped Classical in
theorem height_Pk_le_two : (Pk k).height ≤ 2 := by
  have hQ : Qk k = Ideal.span
      ((({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)) :
        Set (Sk k))) := by
    simp [Qk, Gen.Q]
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (p := Pk k)
    (s := ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)))
    (by rw [← hQ]; exact Pk_mem_minimalPrimes_Qk k)
  refine h.trans ?_
  have : ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} :
      Finset (Sk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  exact_mod_cast this

/-! ### The intermediate prime: the surface `y^5 = z^4` -/

/-- The substitution `x ↦ s`, `y ↦ w^4`, `z ↦ w^5` parametrizing the surface
`y^5 = z^4`. -/
def bb : Fin 3 → MvPowerSeries (Fin 2) k :=
  ![X 0, (X 1)^4, (X 1)^5]

omit [CharZero k] in
lemma hasSubst_bb : MvPowerSeries.HasSubst (bb k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> simp [bb]

/-- The parametrization of the surface, as an algebra map
`k[[x,y,z]] → k[[s,w]]`. -/
def sigmaS : Sk k →ₐ[k] MvPowerSeries (Fin 2) k :=
  MvPowerSeries.substAlgHom (hasSubst_bb k)

omit [CharZero k] in
@[simp] lemma sigmaS_xs : sigmaS k (xs k) = X 0 := by
  rw [sigmaS, xs, MvPowerSeries.substAlgHom_X]; simp [bb]

omit [CharZero k] in
@[simp] lemma sigmaS_ys : sigmaS k (ys k) = (X 1 : MvPowerSeries (Fin 2) k)^4 := by
  rw [sigmaS, ys, MvPowerSeries.substAlgHom_X]; simp [bb]

omit [CharZero k] in
@[simp] lemma sigmaS_zs : sigmaS k (zs k) = (X 1 : MvPowerSeries (Fin 2) k)^5 := by
  rw [sigmaS, zs, MvPowerSeries.substAlgHom_X]; simp [bb]

/-- The substitution `s ↦ t^6 + t^31`, `w ↦ t^2` through which the Moh
parametrization factors. -/
def cc : Fin 2 → PowerSeries k :=
  ![PowerSeries.X^6 + PowerSeries.X^31, PowerSeries.X^2]

omit [CharZero k] in
lemma hasSubst_cc : MvPowerSeries.HasSubst (cc k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
    PowerSeries.constantCoeff_X
  fin_cases s <;> simp [cc, hX]

/-- The map `k[[s,w]] → k[[t]]` restricting the Moh parametrization to the
surface. -/
def tauS : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k :=
  MvPowerSeries.substAlgHom (hasSubst_cc k)

omit [CharZero k] in
lemma subst_cc_bb (s : Fin 3) : MvPowerSeries.subst (cc k) (bb k s) = aa k s := by
  fin_cases s
  · rw [show ((bb k) ⟨0, by norm_num⟩) = (X 0 : MvPowerSeries (Fin 2) k) from by simp [bb],
      MvPowerSeries.subst_X (hasSubst_cc k)]
    simp [cc, aa]
  · rw [show ((bb k) ⟨1, by norm_num⟩) = (X 1 : MvPowerSeries (Fin 2) k)^4 from by simp [bb],
      ← MvPowerSeries.coe_substAlgHom (hasSubst_cc k), map_pow,
      MvPowerSeries.substAlgHom_X]
    simp [cc, aa, ← pow_mul]
  · rw [show ((bb k) ⟨2, by norm_num⟩) = (X 1 : MvPowerSeries (Fin 2) k)^5 from by simp [bb],
      ← MvPowerSeries.coe_substAlgHom (hasSubst_cc k), map_pow,
      MvPowerSeries.substAlgHom_X]
    simp [cc, aa, ← pow_mul]

omit [CharZero k] in
/-- The Moh curve lies on the surface `y^5 = z^4`. -/
theorem psi_eq_tauS_sigmaS (f : Sk k) : psi k f = tauS k (sigmaS k f) := by
  rw [psi, tauS, sigmaS, MvPowerSeries.coe_substAlgHom, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_comp_subst_apply
      (hasSubst_bb k) (hasSubst_cc k)]
  congr 1
  funext s
  exact (subst_cc_bb k s).symm

/-- The ideal of the surface `y^5 = z^4` in `k[[x,y,z]]`. -/
def Psurfk : Ideal (Sk k) := RingHom.ker (sigmaS k)

omit [CharZero k] in
lemma mem_Psurfk_iff {g : Sk k} : g ∈ Psurfk k ↔ sigmaS k g = 0 := Iff.rfl

instance : IsDomain (MvPowerSeries (Fin 2) k) := NoZeroDivisors.to_isDomain _

omit [CharZero k] in
theorem Psurfk_isPrime : (Psurfk k).IsPrime := RingHom.ker_isPrime (sigmaS k)

theorem Psurfk_le_Pk : Psurfk k ≤ Pk k := by
  rw [← ker_psi]
  intro g hg
  rw [mem_Psurfk_iff] at hg
  rw [RingHom.mem_ker, psi_eq_tauS_sigmaS, hg, map_zero]

/-- `y^5 - z^4` is a nonzero element of `Psurfk`. -/
theorem Psurfk_ne_bot : Psurfk k ≠ ⊥ := by
  have hmem : (ys k)^5 - (zs k)^4 ∈ Psurfk k := by
    rw [mem_Psurfk_iff]
    simp only [map_sub, map_pow, sigmaS_ys, sigmaS_zs]
    ring
  have hne : ((ys k)^5 - (zs k)^4 : Sk k) ≠ 0 := by
    intro h
    have h2 := congrArg (MvPowerSeries.coeff (Finsupp.single 1 5)) h
    rw [map_sub, ys, zs] at h2
    have h3 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 5)
        ((X 1 : Sk k)^5) = 1 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_same]
    have h4 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 5)
        ((X 2 : Sk k)^4) = 0 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial]
      rw [if_neg]
      intro hc
      have := congrArg (fun (u : Fin 3 →₀ ℕ) => u 1) hc
      simp at this
    rw [h3, h4] at h2
    simp at h2
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hne hmem

/-- The auxiliary substitution `s ↦ t`, `w ↦ t`, used to detect that `f4` does
not vanish on the surface. -/
def chiS : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k :=
  MvPowerSeries.substAlgHom (a := ![PowerSeries.X, PowerSeries.X])
    (by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s
      have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
        PowerSeries.constantCoeff_X
      fin_cases s <;> simpa using hX)

omit [CharZero k] in
@[simp] lemma chiS_X0 : chiS k (X 0) = PowerSeries.X := by
  rw [chiS, MvPowerSeries.substAlgHom_X]; simp

omit [CharZero k] in
@[simp] lemma chiS_X1 : chiS k (X 1) = PowerSeries.X := by
  rw [chiS, MvPowerSeries.substAlgHom_X]; simp

omit [CharZero k] in
/-- `f4` does not vanish on the surface `y^5 = z^4`. -/
theorem f4S_notMem_Psurfk : Gen.f4 (xs k) (ys k) (zs k) ∉ Psurfk k := by
  intro h
  rw [mem_Psurfk_iff] at h
  have h2 : chiS k (sigmaS k (Gen.f4 (xs k) (ys k) (zs k))) = 0 := by rw [h, map_zero]
  rw [Gen.f4] at h2
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, sigmaS_xs, sigmaS_ys, sigmaS_zs,
    chiS_X0, chiS_X1] at h2
  have h3 : ((PowerSeries.X : PowerSeries k)^11 - PowerSeries.X^13 - PowerSeries.X^13
      - PowerSeries.X^40 + PowerSeries.X^15) = 0 := by
    rw [← h2]; ring
  have h4 := congrArg (PowerSeries.coeff 11) h3
  simp [PowerSeries.coeff_X_pow] at h4

theorem Psurfk_lt_Pk : Psurfk k < Pk k :=
  lt_of_le_of_ne (Psurfk_le_Pk k)
    (fun h => f4S_notMem_Psurfk k (h ▸ Gen.f4_mem (xs k) (ys k) (zs k)))

theorem bot_lt_Psurfk : (⊥ : Ideal (Sk k)) < Psurfk k :=
  lt_of_le_of_ne bot_le (Ne.symm (Psurfk_ne_bot k))

/-! ### The height and the arithmetic rank after completion -/

theorem two_le_height_Pk : 2 ≤ (Pk k).height := by
  haveI := Pk_isPrime k
  haveI := Psurfk_isPrime k
  haveI : (⊥ : Ideal (Sk k)).IsPrime := Ideal.isPrime_bot
  have h2 : (Psurfk k).primeHeight + 1 ≤ (Pk k).primeHeight :=
    Ideal.primeHeight_add_one_le_of_lt (Psurfk_lt_Pk k)
  have h1 : (⊥ : Ideal (Sk k)).primeHeight + 1 ≤ (Psurfk k).primeHeight :=
    Ideal.primeHeight_add_one_le_of_lt (bot_lt_Psurfk k)
  rw [Ideal.height_eq_primeHeight]
  have hbot : (⊥ : Ideal (Sk k)).primeHeight = 0 := by
    rw [← Ideal.height_eq_primeHeight, Ideal.height_bot]
  calc (2 : ℕ∞) = (⊥ : Ideal (Sk k)).primeHeight + 1 + 1 := by rw [hbot]; rfl
    _ ≤ (Psurfk k).primeHeight + 1 := by gcongr
    _ ≤ (Pk k).primeHeight := h2

/-- **After completion the Moh curve ideal still has height two.** -/
theorem height_Pk : (Pk k).height = 2 :=
  le_antisymm (height_Pk_le_two k) (two_le_height_Pk k)

open scoped Classical in
/-- **The arithmetic rank of `Pk` is two** as well: the two explicit witnesses
`H1, H2` cut out the curve set-theoretically in `k[[x,y,z]]`, and by Krull's
height theorem one equation cannot suffice. -/
theorem arithRank_Pk : arithRank (Pk k) = 2 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (arithRank_le
      ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)) ?_) ?_
    · have hQ : Ideal.span
          ((({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)) :
            Set (Sk k))) = Qk k := by
        simp [Qk, Gen.Q]
      rw [hQ, radical_Qk_eq_Pk, (Pk_isPrime k).radical]
    · have : ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} :
          Finset (Sk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact_mod_cast this
  · calc (2 : ℕ∞) = (Pk k).height := (height_Pk k).symm
      _ ≤ arithRank (Pk k) := height_le_arithRank (Pk k) (Pk_isPrime k)

end MohP3.FormalLocal
