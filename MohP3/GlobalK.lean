import MohP3.GenClosure
import MohP3.IndependenceK

/-!
# The global theorem over an arbitrary field of characteristic zero

`MohP3.Global` proves, over `ℚ`, that the kernel of the parametrization is
the curve ideal `P` and that `√(H1,H2) = P`.  Both statements hold over any
field `k` of characteristic zero, by exactly the same argument: the sixteen
closure identities of `MohP3.GenClosure` have integer coefficients and the
only division performed is by `18`, which is invertible in `k`; the
independence statement is `MohP3.K.indepK`.

This file carries out that argument and records the two conclusions

* `MohP3.global_kernel_k : RingHom.ker (rho_k k) = Ppoly k`;
* `MohP3.global_radical_k : Ideal.radical (Qpoly k) = Ppoly k`.
-/

noncomputable section

open MvPolynomial

namespace MohP3

variable (k : Type*) [Field k] [CharZero k]

/-- The polynomial ring `k[x,y,z]`. -/
abbrev Rk := MvPolynomial (Fin 3) k

def xk : Rk k := X 0
def yk : Rk k := X 1
def zk : Rk k := X 2

/-- The curve ideal `(f1,f2,f3,f4)` of `k[x,y,z]`. -/
def Ppoly : Ideal (Rk k) := Gen.P (xk k) (yk k) (zk k)

/-- The ideal `(H1,H2)` of `k[x,y,z]`. -/
def Qpoly : Ideal (Rk k) := Gen.Q (xk k) (yk k) (zk k)

/-- The parametrization `x ↦ t^6+t^31`, `y ↦ t^8`, `z ↦ t^10` over `k`. -/
def rho_k : Rk k →+* Polynomial k :=
  eval₂Hom Polynomial.C ![Polynomial.X ^ 6 + Polynomial.X ^ 31, Polynomial.X ^ 8,
    Polynomial.X ^ 10]

/-- The eight module generators, over `k`. -/
def hhK (i : Fin 8) : Rk k := Gen.hh (xk k) (yk k) (zk k) i

/-- The four generators of the curve ideal, over `k`. -/
def ffK (j : Fin 4) : Rk k := Gen.ff (xk k) (yk k) (zk k) j

/-- The inclusion `k[y] ⊆ k[x,y,z]`. -/
def iotaK : Polynomial k →+* Rk k := Polynomial.eval₂RingHom MvPolynomial.C (yk k)

/-- The `(i,j)` entry of the `x`-closure matrix, read in `k[y]`. -/
def qxPoly (i j : Fin 8) : Polynomial k :=
  Polynomial.C (((Gen.qxD i j).1 : k)) * Polynomial.X ^ (Gen.qxD i j).2

/-- The `(i,j)` entry of the `z`-closure matrix, read in `k[y]`. -/
def qzPoly (i j : Fin 8) : Polynomial k :=
  Polynomial.C (((Gen.qzD i j).1 : k)) * Polynomial.X ^ (Gen.qzD i j).2

omit [CharZero k] in
@[simp] lemma rho_k_C (a : k) : rho_k k (MvPolynomial.C a) = Polynomial.C a := by simp [rho_k]

omit [CharZero k] in
@[simp] lemma rho_k_xk : rho_k k (xk k) = Polynomial.X ^ 6 + Polynomial.X ^ 31 := by
  simp [rho_k, xk]

omit [CharZero k] in
@[simp] lemma rho_k_yk : rho_k k (yk k) = Polynomial.X ^ 8 := by simp [rho_k, yk]

omit [CharZero k] in
@[simp] lemma rho_k_zk : rho_k k (zk k) = Polynomial.X ^ 10 := by simp [rho_k, zk]

omit [CharZero k] in
@[simp] lemma iotaK_X : iotaK k Polynomial.X = yk k := by simp [iotaK]

omit [CharZero k] in
@[simp] lemma iotaK_C (a : k) : iotaK k (Polynomial.C a) = MvPolynomial.C a := by simp [iotaK]

omit [CharZero k] in
lemma ffK_mem (j : Fin 4) : ffK k j ∈ Ppoly k := by
  fin_cases j
  exacts [Gen.f1_mem _ _ _, Gen.f2_mem _ _ _, Gen.f3_mem _ _ _, Gen.f4_mem _ _ _]

omit [CharZero k] in
lemma rho_k_ffK (j : Fin 4) : rho_k k (ffK k j) = 0 := by
  fin_cases j
  · show rho_k k (Gen.f1 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f1, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring
  · show rho_k k (Gen.f2 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f2, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring
  · show rho_k k (Gen.f3 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f3, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring
  · show rho_k k (Gen.f4 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f4, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring

omit [CharZero k] in
lemma rho_k_hhK (i : Fin 8) : rho_k k (hhK k i) = K.vvK k i := by
  fin_cases i <;> simp [hhK, Gen.hh, K.vvK, xk, yk, zk, rho_k] <;> ring

omit [CharZero k] in
lemma rho_k_iotaK (p : Polynomial k) : rho_k k (iotaK k p) = p.comp (Polynomial.X ^ 8) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m a =>
      rw [Polynomial.monomial_comp, ← pow_mul,
        show iotaK k ((Polynomial.monomial m) a) = MvPolynomial.C a * yk k ^ m by
          simp [iotaK, Polynomial.eval₂_monomial],
        map_mul, map_pow, rho_k_yk, rho_k_C, ← pow_mul]

/-! ### The closure identities in divided form -/

lemma C18_mul_18K : (MvPolynomial.C ((18 : k)⁻¹) : Rk k) * (18 : Rk k) = 1 := by
  have h18 : (18 : k) ≠ 0 := by norm_num
  rw [show (18 : Rk k) = MvPolynomial.C (18 : k) from (map_ofNat MvPolynomial.C 18).symm,
    ← map_mul, inv_mul_cancel₀ h18, map_one]

lemma key_x_divK (i : Fin 8) :
    xk k * hhK k i = MvPolynomial.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qxA (yk k) i j * hhK k j) +
        ∑ j, Gen.wxA (xk k) (yk k) (zk k) i j * ffK k j) := by
  have h : (18 : Rk k) * (xk k * hhK k i) =
      (∑ j, Gen.qxA (yk k) i j * hhK k j) +
        ∑ j, Gen.wxA (xk k) (yk k) (zk k) i j * ffK k j :=
    Gen.key_xA (xk k) (yk k) (zk k) i
  rw [← h, ← mul_assoc, C18_mul_18K, one_mul]

lemma key_z_divK (i : Fin 8) :
    zk k * hhK k i = MvPolynomial.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qzA (yk k) i j * hhK k j) +
        ∑ j, Gen.wzA (xk k) (yk k) (zk k) i j * ffK k j) := by
  have h : (18 : Rk k) * (zk k * hhK k i) =
      (∑ j, Gen.qzA (yk k) i j * hhK k j) +
        ∑ j, Gen.wzA (xk k) (yk k) (zk k) i j * ffK k j :=
    Gen.key_zA (xk k) (yk k) (zk k) i
  rw [← h, ← mul_assoc, C18_mul_18K, one_mul]

omit [CharZero k] in
lemma iotaK_qxPoly (i j : Fin 8) : iotaK k (qxPoly k i j) = Gen.qxA (yk k) i j := by
  rw [qxPoly, Gen.qxA, map_mul, map_pow, iotaK_C, iotaK_X]
  congr 1

omit [CharZero k] in
lemma iotaK_qzPoly (i j : Fin 8) : iotaK k (qzPoly k i j) = Gen.qzA (yk k) i j := by
  rw [qzPoly, Gen.qzA, map_mul, map_pow, iotaK_C, iotaK_X]
  congr 1

/-! ### Every polynomial is a combination of the eight generators modulo `Ppoly` -/

/-- `RepP g` : `g` is a `k[y]`-combination of the eight generators plus an
element of the curve ideal. -/
def RepP (g : Rk k) : Prop :=
  ∃ (p : Fin 8 → Polynomial k) (c : Fin 4 → Rk k),
    g = (∑ i, iotaK k (p i) * hhK k i) + ∑ j, c j * ffK k j

omit [CharZero k] in
lemma RepP_C (a : k) : RepP k (MvPolynomial.C a) := by
  refine ⟨![Polynomial.C a, 0, 0, 0, 0, 0, 0, 0], 0, ?_⟩
  simp [Fin.sum_univ_eight, hhK, Gen.hh]

omit [CharZero k] in
lemma RepP_add {g₁ g₂ : Rk k} (h₁ : RepP k g₁) (h₂ : RepP k g₂) : RepP k (g₁ + g₂) := by
  obtain ⟨p, c, hp⟩ := h₁
  obtain ⟨p', c', hp'⟩ := h₂
  refine ⟨p + p', c + c', ?_⟩
  rw [hp, hp']
  simp only [Pi.add_apply, map_add, Fin.sum_univ_eight, Fin.sum_univ_four, add_mul]
  ring

omit [CharZero k] in
lemma RepP_mul_yk {g : Rk k} (h : RepP k g) : RepP k (yk k * g) := by
  obtain ⟨p, c, hp⟩ := h
  refine ⟨fun i => Polynomial.X * p i, fun j => yk k * c j, ?_⟩
  rw [hp]
  simp only [map_mul, iotaK_X, Fin.sum_univ_eight, Fin.sum_univ_four]
  ring

lemma RepP_mul_xk {g : Rk k} (h : RepP k g) : RepP k (xk k * g) := by
  obtain ⟨p, c, hp⟩ := h
  refine ⟨fun j => Polynomial.C ((18 : k)⁻¹) * ∑ i, p i * qxPoly k i j,
    fun j => xk k * c j + MvPolynomial.C ((18 : k)⁻¹) *
      ∑ i, iotaK k (p i) * Gen.wxA (xk k) (yk k) (zk k) i j, ?_⟩
  have hp' : ∀ j : Fin 8, iotaK k (Polynomial.C ((18 : k)⁻¹) * ∑ i, p i * qxPoly k i j) =
      MvPolynomial.C ((18 : k)⁻¹) * ∑ i, iotaK k (p i) * Gen.qxA (yk k) i j := by
    intro j
    rw [map_mul, iotaK_C, map_sum]
    simp only [map_mul, iotaK_qxPoly]
  simp only [hp']
  have e0 := key_x_divK k 0
  have e1 := key_x_divK k 1
  have e2 := key_x_divK k 2
  have e3 := key_x_divK k 3
  have e4 := key_x_divK k 4
  have e5 := key_x_divK k 5
  have e6 := key_x_divK k 6
  have e7 := key_x_divK k 7
  simp only [Fin.sum_univ_eight, Fin.sum_univ_four] at hp e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  linear_combination (xk k) * hp + iotaK k (p 0) * e0 + iotaK k (p 1) * e1 +
    iotaK k (p 2) * e2 + iotaK k (p 3) * e3 + iotaK k (p 4) * e4 + iotaK k (p 5) * e5 +
    iotaK k (p 6) * e6 + iotaK k (p 7) * e7

lemma RepP_mul_zk {g : Rk k} (h : RepP k g) : RepP k (zk k * g) := by
  obtain ⟨p, c, hp⟩ := h
  refine ⟨fun j => Polynomial.C ((18 : k)⁻¹) * ∑ i, p i * qzPoly k i j,
    fun j => zk k * c j + MvPolynomial.C ((18 : k)⁻¹) *
      ∑ i, iotaK k (p i) * Gen.wzA (xk k) (yk k) (zk k) i j, ?_⟩
  have hp' : ∀ j : Fin 8, iotaK k (Polynomial.C ((18 : k)⁻¹) * ∑ i, p i * qzPoly k i j) =
      MvPolynomial.C ((18 : k)⁻¹) * ∑ i, iotaK k (p i) * Gen.qzA (yk k) i j := by
    intro j
    rw [map_mul, iotaK_C, map_sum]
    simp only [map_mul, iotaK_qzPoly]
  simp only [hp']
  have e0 := key_z_divK k 0
  have e1 := key_z_divK k 1
  have e2 := key_z_divK k 2
  have e3 := key_z_divK k 3
  have e4 := key_z_divK k 4
  have e5 := key_z_divK k 5
  have e6 := key_z_divK k 6
  have e7 := key_z_divK k 7
  simp only [Fin.sum_univ_eight, Fin.sum_univ_four] at hp e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  linear_combination (zk k) * hp + iotaK k (p 0) * e0 + iotaK k (p 1) * e1 +
    iotaK k (p 2) * e2 + iotaK k (p 3) * e3 + iotaK k (p 4) * e4 + iotaK k (p 5) * e5 +
    iotaK k (p 6) * e6 + iotaK k (p 7) * e7

/-- Every polynomial has a representation. -/
lemma RepP_all (g : Rk k) : RepP k g := by
  induction g using MvPolynomial.induction_on with
  | C a => exact RepP_C k a
  | add p q hp hq => exact RepP_add k hp hq
  | mul_X p i hp =>
      fin_cases i
      · rw [mul_comm]; exact RepP_mul_xk k hp
      · rw [mul_comm]; exact RepP_mul_yk k hp
      · rw [mul_comm]; exact RepP_mul_zk k hp

/-! ### The kernel of the parametrization -/

omit [CharZero k] in
theorem Ppoly_le_ker : Ppoly k ≤ RingHom.ker (rho_k k) := by
  rw [Ppoly, Gen.P, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 0)
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 1)
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 2)
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 3)

/-- **The global kernel computation over an arbitrary characteristic-zero
field**: the kernel of the parametrization is exactly the curve ideal. -/
theorem global_kernel_k : RingHom.ker (rho_k k) = Ppoly k := by
  refine le_antisymm ?_ (Ppoly_le_ker k)
  intro g hg
  obtain ⟨p, c, hp⟩ := RepP_all k g
  have hsum : ∑ i, (p i).comp (Polynomial.X ^ 8) * K.vvK k i = 0 := by
    have h0 : rho_k k g = 0 := RingHom.mem_ker.mp hg
    rw [hp, map_add, map_sum, map_sum] at h0
    have hz : ∑ j, rho_k k (c j * ffK k j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul, rho_k_ffK, mul_zero]
    rw [hz, add_zero] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, rho_k_iotaK, rho_k_hhK]
  have hp0 := K.indepK k p hsum
  have hzero : (∑ i, iotaK k (p i) * hhK k i) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [hp0 i]
  rw [hp, hzero, zero_add]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (ffK_mem k j)

/-- The curve ideal is prime over any characteristic-zero field. -/
theorem Ppoly_isPrime : (Ppoly k).IsPrime := global_kernel_k k ▸ RingHom.ker_isPrime (rho_k k)

/-- **The set-theoretic complete intersection statement over an arbitrary
characteristic-zero field.** -/
theorem global_radical_k : Ideal.radical (Qpoly k) = Ppoly k := by
  refine le_antisymm ?_ ?_
  · calc (Qpoly k).radical ≤ (Ppoly k).radical :=
          Ideal.radical_mono (Gen.Q_le_P (xk k) (yk k) (zk k))
      _ = Ppoly k := (Ppoly_isPrime k).radical
  · intro a ha
    exact ⟨2, Gen.P_sq_le_Q (xk k) (yk k) (zk k) (Ideal.pow_mem_pow ha 2)⟩

end MohP3
