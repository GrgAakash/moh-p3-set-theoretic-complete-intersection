import MohP3.GlobalK
import MohP3.Ara

/-!
# Moh P3: height and arithmetic rank over an arbitrary characteristic-zero field

This is the version of `MohP3.Height` for the polynomial ring `k[x,y,z]` over
an arbitrary field `k` of characteristic zero:

* `MohP3.height_Ppoly` — `(Ppoly k).height = 2`;
* `MohP3.arithRank_Ppoly` — `arithRank (Ppoly k) = 2`.

The argument is the same as over `ℚ`: Krull's height theorem for the upper
bound, and the chain of primes `⊥ < Psurf k < Ppoly k` given by the surface
`y^5 = z^4` for the lower bound.
-/

noncomputable section

open MvPolynomial

namespace MohP3

variable (k : Type*) [Field k] [CharZero k]

/-- `Ppoly k` is a minimal prime of `Qpoly k`. -/
theorem Ppoly_mem_minimalPrimes_Qpoly : Ppoly k ∈ (Qpoly k).minimalPrimes :=
  mem_minimalPrimes_of_radical_eq (Ppoly_isPrime k) (global_radical_k k)

open scoped Classical in
theorem height_Ppoly_le_two : (Ppoly k).height ≤ 2 := by
  have hQ : Qpoly k = Ideal.span
      ((({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)) :
        Set (Rk k))) := by
    simp [Qpoly, Gen.Q]
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (p := Ppoly k)
    (s := ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)))
    (by rw [← hQ]; exact Ppoly_mem_minimalPrimes_Qpoly k)
  refine h.trans ?_
  have : ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} :
      Finset (Rk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  exact_mod_cast this

/-- The parametrization `x ↦ s`, `y ↦ w^4`, `z ↦ w^5` of the surface
`y^5 = z^4`. -/
def sigmaK : Rk k →+* MvPolynomial (Fin 2) k :=
  eval₂Hom C ![X 0, (X 1)^4, (X 1)^5]

/-- The map `s ↦ t^6 + t^31`, `w ↦ t^2`. -/
def tauK : MvPolynomial (Fin 2) k →+* Polynomial k :=
  eval₂Hom Polynomial.C ![Polynomial.X^6 + Polynomial.X^31, Polynomial.X^2]

omit [CharZero k] in
theorem rho_k_eq_tauK_comp_sigmaK : rho_k k = (tauK k).comp (sigmaK k) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [sigmaK, tauK]
  · fin_cases i <;> simp [sigmaK, tauK, rho_k] <;> ring

omit [CharZero k] in
@[simp] lemma sigmaK_xk : sigmaK k (xk k) = X 0 := by simp [sigmaK, xk]

omit [CharZero k] in
@[simp] lemma sigmaK_yk : sigmaK k (yk k) = (X 1 : MvPolynomial (Fin 2) k)^4 := by
  simp [sigmaK, yk, Matrix.cons_val_one]

omit [CharZero k] in
@[simp] lemma sigmaK_zk : sigmaK k (zk k) = (X 1 : MvPolynomial (Fin 2) k)^5 := by
  simp [sigmaK, zk]

/-- The ideal of the surface `y^5 = z^4` in `k[x,y,z]`. -/
def PsurfK : Ideal (Rk k) := RingHom.ker (sigmaK k)

omit [CharZero k] in
lemma mem_PsurfK_iff {g : Rk k} : g ∈ PsurfK k ↔ sigmaK k g = 0 := Iff.rfl

omit [CharZero k] in
theorem PsurfK_isPrime : (PsurfK k).IsPrime := RingHom.ker_isPrime (sigmaK k)

theorem PsurfK_le_Ppoly : PsurfK k ≤ Ppoly k := by
  rw [← global_kernel_k]
  intro g hg
  rw [mem_PsurfK_iff] at hg
  rw [RingHom.mem_ker, rho_k_eq_tauK_comp_sigmaK, RingHom.comp_apply, hg, map_zero]

omit [CharZero k] in
/-- `y^5 - z^4` is a nonzero element of `PsurfK`. -/
theorem PsurfK_ne_bot : PsurfK k ≠ ⊥ := by
  have hmem : (yk k)^5 - (zk k)^4 ∈ PsurfK k := by
    rw [mem_PsurfK_iff]
    simp only [map_sub, map_pow, sigmaK_yk, sigmaK_zk]
    ring
  have hne : ((yk k)^5 - (zk k)^4 : Rk k) ≠ 0 := by
    intro h
    have h2 := congrArg (MvPolynomial.eval ![0, 1, 0]) h
    simp [yk, zk] at h2
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hne hmem

omit [CharZero k] in
/-- `f4` vanishes on the curve but not on the surface. -/
theorem f4K_notMem_PsurfK : Gen.f4 (xk k) (yk k) (zk k) ∉ PsurfK k := by
  intro h
  rw [mem_PsurfK_iff] at h
  have h2 : (MvPolynomial.eval ![(1 : k), 1]) (sigmaK k (Gen.f4 (xk k) (yk k) (zk k))) = 0 := by
    rw [h, map_zero]
  rw [Gen.f4] at h2
  simp only [map_sub, map_add, map_mul, map_pow, sigmaK_xk, sigmaK_yk, sigmaK_zk, map_ofNat,
    eval_X] at h2
  norm_num at h2

theorem PsurfK_lt_Ppoly : PsurfK k < Ppoly k :=
  lt_of_le_of_ne (PsurfK_le_Ppoly k)
    (fun h => f4K_notMem_PsurfK k (h ▸ Gen.f4_mem (xk k) (yk k) (zk k)))

omit [CharZero k] in
theorem bot_lt_PsurfK : (⊥ : Ideal (Rk k)) < PsurfK k :=
  lt_of_le_of_ne bot_le (Ne.symm (PsurfK_ne_bot k))

theorem two_le_height_Ppoly : 2 ≤ (Ppoly k).height := by
  haveI := Ppoly_isPrime k
  haveI := PsurfK_isPrime k
  haveI : (⊥ : Ideal (Rk k)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (Rk k)).primeHeight + 1 ≤ (PsurfK k).primeHeight :=
    Ideal.primeHeight_add_one_le_of_lt (bot_lt_PsurfK k)
  have h2 : (PsurfK k).primeHeight + 1 ≤ (Ppoly k).primeHeight :=
    Ideal.primeHeight_add_one_le_of_lt (PsurfK_lt_Ppoly k)
  rw [Ideal.height_eq_primeHeight]
  have hbot : (⊥ : Ideal (Rk k)).primeHeight = 0 := by
    rw [← Ideal.height_eq_primeHeight, Ideal.height_bot]
  calc (2 : ℕ∞) = (⊥ : Ideal (Rk k)).primeHeight + 1 + 1 := by rw [hbot]; rfl
    _ ≤ (PsurfK k).primeHeight + 1 := by gcongr
    _ ≤ (Ppoly k).primeHeight := h2

/-- **The height of the curve ideal is two over any characteristic-zero
field.** -/
theorem height_Ppoly : (Ppoly k).height = 2 :=
  le_antisymm (height_Ppoly_le_two k) (two_le_height_Ppoly k)

open scoped Classical in
/-- **The arithmetic rank of the curve ideal is two over any
characteristic-zero field.** -/
theorem arithRank_Ppoly : arithRank (Ppoly k) = 2 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (arithRank_le
      ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)) ?_) ?_
    · have hQ : Ideal.span
          ((({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)) :
            Set (Rk k))) = Qpoly k := by
        simp [Qpoly, Gen.Q]
      rw [hQ, global_radical_k, (Ppoly_isPrime k).radical]
    · have : ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} :
          Finset (Rk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact_mod_cast this
  · calc (2 : ℕ∞) = (Ppoly k).height := (height_Ppoly k).symm
      _ ≤ arithRank (Ppoly k) := height_le_arithRank (Ppoly k) (Ppoly_isPrime k)

end MohP3
