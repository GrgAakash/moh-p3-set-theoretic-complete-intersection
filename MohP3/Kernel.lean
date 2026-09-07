import MohP3.Closure
import MohP3.Independence

/-!
# Moh P3: `RingHom.ker rho = P`

The inclusion `P ≤ ker rho` is the evaluation `rho (f i) = 0`.

For the converse we use the sixteen closure identities of `MohP3.Closure`:
they show that the `ℚ[y]`-submodule of `R/P` spanned by the eight elements
`hh 0, …, hh 7` is stable under multiplication by `x`, `y` and `z` and contains
`1`; hence it is all of `R/P` (`good_all`).  On the other side the eight
polynomials `rho (hh i) = vv i` have pairwise distinct trailing degrees modulo
`8`, hence are linearly independent over `rho (ℚ[y]) = ℚ[t^8]`
(`MohP3.indep`).  Combining the two gives `ker rho ≤ P`.
-/

noncomputable section

open MvPolynomial

namespace MohP3

/-! ### The images of the eight generators under `rho` -/

lemma rho_hh (i : Fin 8) : rho (hh i) = vv i := by
  fin_cases i <;> simp [hh, vv] <;> ring

lemma rho_iota (p : Polynomial ℚ) : rho (iota p) = p.comp (Polynomial.X^8) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
      rw [Polynomial.monomial_comp, ← pow_mul,
        show iota ((Polynomial.monomial k) a) = MvPolynomial.C a * y ^ k by
          simp [iota, Polynomial.eval₂_monomial],
        map_mul, map_pow, rho_y, rho_C, ← pow_mul]

/-! ### `R/P` is generated over `ℚ[y]` by the eight elements `hh i` -/

/-- `Good g` means: some nonzero integer multiple of `g` is, modulo `P`, a
`ℚ[y]`-linear combination of `hh 0, …, hh 7`. -/
def Good (g : R) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ ∃ p : Fin 8 → Polynomial ℚ, (n : R) * g - ∑ i, iota (p i) * hh i ∈ P

lemma good_C (a : ℚ) : Good (MvPolynomial.C a) := by
  refine ⟨1, one_ne_zero, ![Polynomial.C a, 0, 0, 0, 0, 0, 0, 0], ?_⟩
  have h : ((1:ℕ) : R) * MvPolynomial.C a
      - ∑ i, iota ((![Polynomial.C a, 0, 0, 0, 0, 0, 0, 0] : Fin 8 → Polynomial ℚ) i) * hh i
      = 0 := by
    simp [Fin.sum_univ_eight, hh]
  rw [h]
  exact Ideal.zero_mem P

lemma good_add {g₁ g₂ : R} (h₁ : Good g₁) (h₂ : Good g₂) : Good (g₁ + g₂) := by
  obtain ⟨n₁, hn₁, p, hp⟩ := h₁
  obtain ⟨n₂, hn₂, q, hq⟩ := h₂
  refine ⟨n₁*n₂, mul_ne_zero hn₁ hn₂,
    fun i => (n₂ : Polynomial ℚ) * p i + (n₁ : Polynomial ℚ) * q i, ?_⟩
  have key : ((n₁*n₂ : ℕ) : R) * (g₁ + g₂)
      - ∑ i, iota ((n₂ : Polynomial ℚ) * p i + (n₁ : Polynomial ℚ) * q i) * hh i
      = (n₂ : R) * ((n₁ : R) * g₁ - ∑ i, iota (p i) * hh i)
        + (n₁ : R) * ((n₂ : R) * g₂ - ∑ i, iota (q i) * hh i) := by
    push_cast
    simp only [map_add, map_mul, map_natCast, Fin.sum_univ_eight]
    ring
  rw [key]
  exact P.add_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hq)

lemma good_mul_y {g : R} (h : Good g) : Good (y * g) := by
  obtain ⟨n, hn, p, hp⟩ := h
  refine ⟨n, hn, fun i => Polynomial.X * p i, ?_⟩
  have key : (n : R) * (y * g) - ∑ i, iota (Polynomial.X * p i) * hh i
      = y * ((n : R) * g - ∑ i, iota (p i) * hh i) := by
    simp only [map_mul, iota_X, Fin.sum_univ_eight]
    ring
  rw [key]
  exact Ideal.mul_mem_left _ _ hp

lemma good_mul_x {g : R} (h : Good g) : Good (x * g) := by
  obtain ⟨n, hn, p, hp⟩ := h
  refine ⟨18*n, by simpa using hn, fun j => ∑ i, p i * QX i j, ?_⟩
  have key : ((18*n : ℕ) : R) * (x * g) - ∑ j, iota (∑ i, p i * QX i j) * hh j
      = (18 : R) * x * ((n : R) * g - ∑ i, iota (p i) * hh i)
        + ∑ i, iota (p i) * ((18 : R) * (x * hh i) - ∑ j, iota (QX i j) * hh j) := by
    push_cast
    simp only [Fin.sum_univ_eight, map_add, map_mul]
    ring
  rw [key]
  exact P.add_mem (Ideal.mul_mem_left _ _ hp)
    (Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (key_x i)))

lemma good_mul_z {g : R} (h : Good g) : Good (z * g) := by
  obtain ⟨n, hn, p, hp⟩ := h
  refine ⟨18*n, by simpa using hn, fun j => ∑ i, p i * QZ i j, ?_⟩
  have key : ((18*n : ℕ) : R) * (z * g) - ∑ j, iota (∑ i, p i * QZ i j) * hh j
      = (18 : R) * z * ((n : R) * g - ∑ i, iota (p i) * hh i)
        + ∑ i, iota (p i) * ((18 : R) * (z * hh i) - ∑ j, iota (QZ i j) * hh j) := by
    push_cast
    simp only [Fin.sum_univ_eight, map_add, map_mul]
    ring
  rw [key]
  exact P.add_mem (Ideal.mul_mem_left _ _ hp)
    (Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (key_z i)))

/-- Every polynomial is, up to a nonzero integer factor and modulo `P`, a
`ℚ[y]`-combination of the eight generators. -/
lemma good_all (g : R) : Good g := by
  induction g using MvPolynomial.induction_on with
  | C a => exact good_C a
  | add p q hp hq => exact good_add hp hq
  | mul_X p i hp =>
      fin_cases i
      · rw [mul_comm]; exact good_mul_x hp
      · rw [mul_comm]; exact good_mul_y hp
      · rw [mul_comm]; exact good_mul_z hp

/-! ### The kernel -/

lemma rho_f1 : rho f1 = 0 := by
  simp only [f1, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_x, rho_y, rho_z]
  ring

lemma rho_f2 : rho f2 = 0 := by
  simp only [f2, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_x, rho_y, rho_z]
  ring

lemma rho_f3 : rho f3 = 0 := by
  simp only [f3, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_x, rho_y, rho_z]
  ring

lemma rho_f4 : rho f4 = 0 := by
  simp only [f4, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_x, rho_y, rho_z]
  ring

theorem P_le_ker : P ≤ RingHom.ker rho := by
  rw [P, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact RingHom.mem_ker.mpr rho_f1
  · exact RingHom.mem_ker.mpr rho_f2
  · exact RingHom.mem_ker.mpr rho_f3
  · exact RingHom.mem_ker.mpr rho_f4

/-- The kernel of the parametrization is exactly `P`. -/
theorem kernel_rho : RingHom.ker rho = P := by
  refine le_antisymm ?_ P_le_ker
  intro g hg
  obtain ⟨n, hn, p, hp⟩ := good_all g
  have hng : (n : R) * g ∈ RingHom.ker rho := Ideal.mul_mem_left _ _ hg
  have hsum_ker : (∑ i, iota (p i) * hh i) ∈ RingHom.ker rho := by
    simpa using sub_mem hng (P_le_ker hp)
  have h2 : ∑ i, (p i).comp (Polynomial.X^8) * vv i = 0 := by
    have h := RingHom.mem_ker.mp hsum_ker
    rw [map_sum] at h
    simpa [map_mul, rho_iota, rho_hh] using h
  have h3 := indep p h2
  have hzero : ∑ i, iota (p i) * hh i = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [h3 i]
  rw [hzero, sub_zero] at hp
  exact mem_of_nsmul_mem hn hp

end MohP3
