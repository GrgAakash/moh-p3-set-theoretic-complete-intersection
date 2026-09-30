module

public import MohP3.Generic
public import Mathlib

@[expose] public section

/-!
# Hilbert–Burch exactness for the Moh matrix `Φ`

For every field `k` of characteristic zero, `S = k[x,y,z] = MvPolynomial (Fin 3) k`,
the existing exact generators `f1,…,f4` (`MohP3.Gen.f1` … `MohP3.Gen.f4`) and the
manuscript's exact `4 × 3` matrix `Φ` (display (3.2) / `eq:Phi`), we prove that

  `0 → S^3 --Φ--> S^4 --(f1,f2,f3,f4)--> S --> S/J → 0`

is exact, where `J = (f1,f2,f3,f4)`.

This module depends only on `MohP3.Generic` (the definitions of `f1,…,f4`) and
Mathlib.  It does not use the kernel theorem `J = ker ρ` or any consequence of it.

Proof: a direct proof of the relevant half of the Hilbert–Burch /
Buchsbaum–Eisenbud criterion in the `4 × 3` case (`exact_of_signedMinors`),
where `grade J ≥ 2` is witnessed by the explicit pair `s = 3g = y²f1 - xy f2 - 3z f4`,
`g = y⁵ - z⁴`, and `t = f1`, which is monic in `x` over `k[y,z]` and hence a
nonzerodivisor modulo `s ∈ k[y,z]`.
-/

set_option autoImplicit false

noncomputable section

namespace MohP3.HilbertBurch

open Matrix

/-- The maximal minor of a `4 × 3` matrix obtained by deleting row `i`. -/
def maximalMinor {A : Type*} [CommRing A] (B : Matrix (Fin 4) (Fin 3) A) (i : Fin 4) : A :=
  (B.submatrix i.succAbove id).det

/-- The manuscript's exact `4 × 3` matrix `Φ`, over any commutative ring. -/
def phi {A : Type*} [CommRing A] (x y z : A) : Matrix (Fin 4) (Fin 3) A :=
  !![0,2*x*y,-2*z*(2*x*y^3*z^2+y^5*z-1);
     z,-2*x^2,y*(4*x^2*y*z^3+2*x*y^3*z^2-3);
     -2*y,-3*z,-x+6*y^2*z^4;
     3*x,3*y,0]

/-- Direct expansion: `det Φ_{\hat i} = 6 (-1)^{i-1} f_i` (0-indexed here). -/
theorem phi_minors {A : Type*} [CommRing A] (x y z : A) :
    maximalMinor (phi x y z) =
      ![6*Gen.f1 x y z,-6*Gen.f2 x y z,6*Gen.f3 x y z,-6*Gen.f4 x y z] := by
  funext i
  fin_cases i <;>
    simp [maximalMinor, phi, Matrix.det_fin_three, Matrix.submatrix,
      Fin.succAbove, Fin.lt_def, Gen.f1,Gen.f2,Gen.f3,Gen.f4] <;> ring

/-- The three columns of `Φ` are relations among `f1,…,f4`. -/
theorem phi_relations {A : Type*} [CommRing A] (x y z : A) :
    ![Gen.f1 x y z,Gen.f2 x y z,Gen.f3 x y z,Gen.f4 x y z] ᵥ* phi x y z = 0 := by
  funext j
  fin_cases j <;>
    simp [phi,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,Gen.f1,Gen.f2,Gen.f3,Gen.f4] <;> ring

/-! ## The general criterion -/

section General

variable {S : Type*} [CommRing S]

/-- The map `S^4 → S`, `a ↦ ∑ a_i f_i`, given by a row of generators. -/
def rowMap (f : Fin 4 → S) : (Fin 4 → S) →ₗ[S] S where
  toFun a := a ⬝ᵥ f
  map_add' a b := add_dotProduct a b f
  map_smul' c a := by simp [smul_dotProduct]

@[simp] lemma rowMap_apply (f : Fin 4 → S) (a : Fin 4 → S) : rowMap f a = a ⬝ᵥ f := rfl

/-- The `4 × 4` matrix `[a | Φ]`. -/
def augment (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) : Matrix (Fin 4) (Fin 4) S :=
  Matrix.of fun r => (Fin.cons (a r) (Φ r) : Fin 4 → S)

omit [CommRing S] in
lemma augment_submatrix_succ (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) (i : Fin 4) :
    (augment a Φ).submatrix i.succAbove Fin.succ = Φ.submatrix i.succAbove id := by
  ext r c
  simp [augment]

/-- Laplace expansion of `det [a | Φ]` along its first column. -/
lemma det_augment (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) :
    (augment a Φ).det = ∑ i : Fin 4, (-1) ^ (i : ℕ) * a i * maximalMinor Φ i := by
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [augment_submatrix_succ]
  simp [augment, maximalMinor]

/-- The cofactor identity `[a | Φ] · adj [a | Φ] = det • 1`, read in the `j`-th
column: `((-1)^j m_j) • a + Φ w = det • e_j` for an explicit `w`. -/
lemma cofactor_column (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) (j : Fin 4) :
    ∃ w : Fin 3 → S, ∀ r : Fin 4,
      a r * ((-1) ^ (j : ℕ) * maximalMinor Φ j) + (Φ *ᵥ w) r =
        if r = j then (augment a Φ).det else 0 := by
  refine ⟨fun c => (augment a Φ).adjugate c.succ j, fun r => ?_⟩
  have h := congrFun (congrFun (Matrix.mul_adjugate (augment a Φ)) r) j
  rw [Matrix.mul_apply, Fin.sum_univ_succ] at h
  have h0 : (augment a Φ).adjugate 0 j = (-1) ^ (j : ℕ) * maximalMinor Φ j := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.val_zero, add_zero, Fin.succAbove_zero]
    rw [augment_submatrix_succ]
    rfl
  rw [h0] at h
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at h
  rw [← h]
  simp [augment, Matrix.mulVec, dotProduct]

end General

section Domain

variable {S : Type*} [CommRing S] [IsDomain S]

/-- If some maximal minor of `Φ` is nonzero, the map `Φ : S^3 → S^4` is injective. -/
lemma mulVec_injective_of_minor_ne_zero (Φ : Matrix (Fin 4) (Fin 3) S) (i : Fin 4)
    (hi : maximalMinor Φ i ≠ 0) : Function.Injective (Matrix.mulVecLin Φ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  change Φ *ᵥ v = 0 at hv
  set B := Φ.submatrix i.succAbove id
  have hB : B *ᵥ v = 0 := by
    ext r
    have := congrFun hv (i.succAbove r)
    simpa [B, Matrix.mulVec, dotProduct] using this
  have h2 : (B.adjugate * B) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  ext r
  have := congrFun h2 r
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hi

/-- **Hilbert–Burch exactness criterion** (`4 × 3` case, over a domain).

Hypotheses: the signed maximal minors of `Φ` are `c • f` with `c` a unit; the
columns of `Φ` are relations on `f`; and the ideal `(f)` contains a nonzero
`s` and an element `t` that is a nonzerodivisor modulo `s` (so `(f)` has grade
at least two).  Conclusion: `Φ : S^3 → S^4` is injective and its image is the
kernel of `f : S^4 → S`. -/
theorem exact_of_signedMinors (Φ : Matrix (Fin 4) (Fin 3) S) (f : Fin 4 → S) (c : S)
    (hc : IsUnit c)
    (hm : ∀ i : Fin 4, (-1) ^ (i : ℕ) * maximalMinor Φ i = c * f i)
    (hrel : f ᵥ* Φ = 0)
    (s t : S) (hs : s ∈ Ideal.span (Set.range f)) (ht : t ∈ Ideal.span (Set.range f))
    (hs0 : s ≠ 0)
    (hreg : ∀ u : S, t * u ∈ Ideal.span {s} → u ∈ Ideal.span {s}) :
    Function.Injective (Matrix.mulVecLin Φ) ∧
      LinearMap.range (Matrix.mulVecLin Φ) = LinearMap.ker (rowMap f) := by
  -- some generator is nonzero, hence some maximal minor is nonzero
  have hf : ∃ i, f i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hs0
    have : Set.range f ⊆ {0} := by
      rintro _ ⟨i, rfl⟩
      simp [hcon i]
    have := Ideal.span_mono this hs
    simpa using this
  obtain ⟨i₀, hi₀⟩ := hf
  have hminor : maximalMinor Φ i₀ ≠ 0 := by
    intro h0
    have := hm i₀
    rw [h0, mul_zero] at this
    exact hi₀ ((mul_eq_zero.mp this.symm).resolve_left hc.ne_zero)
  have hinj := mulVec_injective_of_minor_ne_zero Φ i₀ hminor
  refine ⟨hinj, ?_⟩
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    change (Φ *ᵥ v) ⬝ᵥ f = 0
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, hrel, zero_dotProduct]
  · intro a ha
    rw [LinearMap.mem_ker, rowMap_apply] at ha
    -- `c f_j a ∈ im Φ` for every `j`
    have hcol : ∀ j : Fin 4, ∃ w : Fin 3 → S, (c * f j) • a = Φ *ᵥ w := by
      intro j
      obtain ⟨w, hw⟩ := cofactor_column a Φ j
      have hdet : (augment a Φ).det = 0 := by
        rw [det_augment]
        have : ∀ i : Fin 4, (-1) ^ (i : ℕ) * a i * maximalMinor Φ i = c * (a i * f i) := by
          intro i
          have := hm i
          linear_combination a i * this
        simp only [this, ← Finset.mul_sum]
        rw [show (∑ i : Fin 4, a i * f i) = a ⬝ᵥ f from rfl, ha, mul_zero]
      refine ⟨-w, ?_⟩
      ext r
      have := hw r
      rw [hdet, ite_self, hm j] at this
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_neg, Pi.neg_apply]
      linear_combination this
    -- hence `c e a ∈ im Φ` for every `e ∈ (f)`
    have hideal : ∀ e ∈ Ideal.span (Set.range f), ∃ W : Fin 3 → S, (c * e) • a = Φ *ᵥ W := by
      intro e he
      obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp he
      choose w hw using hcol
      refine ⟨∑ j, β j • w j, ?_⟩
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, ← hw, Finset.mul_sum, Finset.sum_smul, smul_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp only [smul_eq_mul]
      ring
    obtain ⟨Ws, hWs⟩ := hideal s hs
    obtain ⟨Wt, hWt⟩ := hideal t ht
    -- `s Wt = t Ws` by injectivity
    have hst : s • Wt = t • Ws := by
      apply hinj
      change Φ *ᵥ (s • Wt) = Φ *ᵥ (t • Ws)
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← hWs, ← hWt, smul_smul, smul_smul]
      congr 1
      ring
    -- so every coordinate of `Ws` is divisible by `s`
    have hdiv : ∀ r, ∃ V, Ws r = s * V := by
      intro r
      have h1 : t * Ws r ∈ Ideal.span {s} := by
        have := congrFun hst r
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [← this]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self s)
      obtain ⟨V, hV⟩ := Ideal.mem_span_singleton'.mp (hreg _ h1)
      exact ⟨V, by rw [← hV, mul_comm]⟩
    choose V hV using hdiv
    have hWsV : Ws = s • V := by
      ext r
      simp [hV r]
    rw [hWsV, Matrix.mulVec_smul] at hWs
    -- cancel `s`, then `c`
    have hca : c • a = Φ *ᵥ V := by
      ext r
      have := congrFun hWs r
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      apply mul_left_cancel₀ hs0
      linear_combination this
    refine ⟨hc.unit⁻¹.val • V, ?_⟩
    change Φ *ᵥ (hc.unit⁻¹.val • V) = a
    rw [Matrix.mulVec_smul, ← hca, smul_smul]
    simp

end Domain

/-! ## A monic polynomial is a nonzerodivisor modulo an extended ideal -/

section Monic

open MvPolynomial

variable {K : Type*} [CommRing K]

/-- The identification `K[x,y,z] ≃ K[y,z][x]`. -/
noncomputable abbrev xEquiv : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  finSuccEquiv K 2

lemma xEquiv_X0 : xEquiv (X 0 : MvPolynomial (Fin 3) K) = Polynomial.X := finSuccEquiv_X_zero
lemma xEquiv_X1 : xEquiv (X 1 : MvPolynomial (Fin 3) K) = Polynomial.C (X 0) :=
  finSuccEquiv_X_succ (j := 0)
lemma xEquiv_X2 : xEquiv (X 2 : MvPolynomial (Fin 3) K) = Polynomial.C (X 1) :=
  finSuccEquiv_X_succ (j := 1)

/-- If `t` is monic in `x` over `K[y,z]` and `h ∈ K[y,z]`, then `t` is a
nonzerodivisor on `K[x,y,z]/(h)`. -/
theorem mem_span_of_monic_mul (h : MvPolynomial (Fin 2) K) (t u : MvPolynomial (Fin 3) K)
    (ht : (xEquiv t).Monic)
    (hu : t * u ∈ Ideal.span {xEquiv.symm (Polynomial.C h)}) :
    u ∈ Ideal.span {xEquiv.symm (Polynomial.C h)} := by
  set e := (xEquiv : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K))
  have hmap : ∀ v, v ∈ Ideal.span {e.symm (Polynomial.C h)} ↔ e v ∈ Ideal.span {Polynomial.C h} := by
    intro v
    constructor
    · intro hv
      simpa [Ideal.map_span] using Ideal.mem_map_of_mem e hv
    · intro hv
      simpa [Ideal.map_span] using Ideal.mem_map_of_mem e.symm hv
  rw [hmap] at hu ⊢
  set φ := Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span {h}))
  have hker : RingHom.ker φ = Ideal.span {Polynomial.C h} := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
  rw [← hker, RingHom.mem_ker] at hu ⊢
  rw [map_mul, map_mul] at hu
  have hmon : (φ (e t)).Monic := ht.map _
  exact hmon.mul_right_eq_zero_iff.mp hu

end Monic

/-! ## The Moh presentation -/

section Moh

open MvPolynomial

variable {A : Type*} [CommRing A]

/-- The generator row `(f1,f2,f3,f4)`. -/
def fvec (x y z : A) : Fin 4 → A := ![Gen.f1 x y z, Gen.f2 x y z, Gen.f3 x y z, Gen.f4 x y z]

lemma range_fvec (x y z : A) :
    Set.range (fvec x y z) = {Gen.f1 x y z, Gen.f2 x y z, Gen.f3 x y z, Gen.f4 x y z} := by
  ext w
  simp only [Set.mem_range, Fin.exists_fin_succ, Fin.exists_fin_zero, fvec, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  simp [eq_comm]

/-- `J = (f1,f2,f3,f4)` is the span of the generator row. -/
lemma span_fvec (x y z : A) : Ideal.span (Set.range (fvec x y z)) = Gen.P x y z := by
  rw [range_fvec]; rfl

lemma phi_signedMinors (x y z : A) (i : Fin 4) :
    (-1) ^ (i : ℕ) * maximalMinor (phi x y z) i = 6 * fvec x y z i := by
  rw [phi_minors]
  fin_cases i <;> simp [fvec]
  ring

lemma fvec_vecMul_phi (x y z : A) : fvec x y z ᵥ* phi x y z = 0 := phi_relations x y z

/-- The manuscript's identity (3.3): `3 g = y² f1 - x y f2 - 3 z f4`, `g = y⁵ - z⁴`. -/
theorem g_certificate (x y z : A) :
    3 * (y ^ 5 - z ^ 4) = y ^ 2 * Gen.f1 x y z - x * y * Gen.f2 x y z - 3 * z * Gen.f4 x y z := by
  simp only [Gen.f1, Gen.f2, Gen.f4]; ring

lemma f1_mem_span (x y z : A) : Gen.f1 x y z ∈ Ideal.span (Set.range (fvec x y z)) :=
  Ideal.subset_span ⟨0, rfl⟩

lemma f2_mem_span (x y z : A) : Gen.f2 x y z ∈ Ideal.span (Set.range (fvec x y z)) :=
  Ideal.subset_span ⟨1, rfl⟩

lemma f4_mem_span (x y z : A) : Gen.f4 x y z ∈ Ideal.span (Set.range (fvec x y z)) :=
  Ideal.subset_span ⟨3, rfl⟩

lemma g_mem (x y z : A) : 3 * (y ^ 5 - z ^ 4) ∈ Ideal.span (Set.range (fvec x y z)) := by
  rw [g_certificate]
  exact sub_mem (sub_mem (Ideal.mul_mem_left _ _ (f1_mem_span x y z))
    (Ideal.mul_mem_left _ _ (f2_mem_span x y z))) (Ideal.mul_mem_left _ _ (f4_mem_span x y z))

variable (k : Type*) [Field k] [CharZero k]

omit [CharZero k] in
lemma xEquiv_f1 :
    (xEquiv (Gen.f1 (X 0) (X 1) (X 2) : MvPolynomial (Fin 3) k)).Monic := by
  simp only [Gen.f1, map_sub, map_add, map_mul, map_pow, map_ofNat, xEquiv_X0, xEquiv_X1,
    xEquiv_X2]
  monicity!

omit [CharZero k] in
lemma g_eq_symm :
    (3 * ((X 1) ^ 5 - (X 2) ^ 4) : MvPolynomial (Fin 3) k) =
      xEquiv.symm (Polynomial.C (3 * ((X 0) ^ 5 - (X 1) ^ 4))) := by
  apply xEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  simp [xEquiv_X1, xEquiv_X2, map_ofNat]

lemma three_g_ne_zero : (3 * ((X 1) ^ 5 - (X 2) ^ 4) : MvPolynomial (Fin 3) k) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → k)) h
  simp at this

lemma six_isUnit : IsUnit (6 : MvPolynomial (Fin 3) k) := by
  rw [← map_ofNat (C : k →+* MvPolynomial (Fin 3) k) 6]
  exact (isUnit_iff_ne_zero.mpr (by norm_num)).map C

/-- **Hilbert–Burch presentation, first half.** Over `S = k[x,y,z]` the manuscript's
matrix `Φ : S^3 → S^4` is injective, and its image is exactly the module of
relations among `f1, f2, f3, f4`. -/
theorem phi_exact_aux :
    Function.Injective (Matrix.mulVecLin (phi (X 0) (X 1) (X 2) : Matrix (Fin 4) (Fin 3)
        (MvPolynomial (Fin 3) k))) ∧
      LinearMap.range (Matrix.mulVecLin (phi (X 0) (X 1) (X 2) : Matrix (Fin 4) (Fin 3)
        (MvPolynomial (Fin 3) k))) = LinearMap.ker (rowMap (fvec (X 0) (X 1) (X 2))) := by
  refine exact_of_signedMinors _ _ 6 (six_isUnit k) (phi_signedMinors _ _ _)
    (fvec_vecMul_phi _ _ _) _ _ (g_mem _ _ _) (f1_mem_span _ _ _) (three_g_ne_zero k) ?_
  intro u hu
  rw [g_eq_symm] at hu ⊢
  exact mem_span_of_monic_mul _ _ _ (xEquiv_f1 k) hu

/-- The image of the generator map is the span of the generators. -/
theorem range_rowMap (x y z : A) :
    LinearMap.range (rowMap (fvec x y z)) = (Gen.P x y z : Submodule A A) := by
  rw [← span_fvec]
  ext w
  change _ ↔ w ∈ Submodule.span A (Set.range (fvec x y z))
  rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
  simp only [rowMap_apply, dotProduct, smul_eq_mul]

/-! ## The requested maps and the exact complex -/

/-- `S = k[x,y,z]`. -/
abbrev S : Type _ := MvPolynomial (Fin 3) k

/-- `J = (f1, f2, f3, f4) ⊆ S`, with the existing exact generators. -/
def J : Ideal (S k) :=
  Ideal.span {Gen.f1 (X 0) (X 1) (X 2), Gen.f2 (X 0) (X 1) (X 2),
    Gen.f3 (X 0) (X 1) (X 2), Gen.f4 (X 0) (X 1) (X 2)}

/-- The `S`-linear map `S^3 → S^4` given by the manuscript's matrix `Φ`. -/
def phiMap : (Fin 3 → S k) →ₗ[S k] (Fin 4 → S k) :=
  Matrix.mulVecLin (phi (X 0) (X 1) (X 2))

/-- The `S`-linear map `S^4 → S`, `(a_i) ↦ ∑ a_i f_i`. -/
def genMap : (Fin 4 → S k) →ₗ[S k] S k :=
  rowMap (fvec (X 0) (X 1) (X 2))

omit [CharZero k] in
lemma phiMap_apply (v : Fin 3 → S k) : phiMap k v = phi (X 0) (X 1) (X 2) *ᵥ v := rfl

omit [CharZero k] in
lemma genMap_apply (a : Fin 4 → S k) :
    genMap k a = a 0 * Gen.f1 (X 0) (X 1) (X 2) + a 1 * Gen.f2 (X 0) (X 1) (X 2) +
      a 2 * Gen.f3 (X 0) (X 1) (X 2) + a 3 * Gen.f4 (X 0) (X 1) (X 2) := by
  simp [genMap, fvec, dotProduct, Fin.sum_univ_succ, add_assoc]

/-- **1.** `Φ : S^3 → S^4` is injective. -/
theorem phiMap_injective : Function.Injective (phiMap k) := (phi_exact_aux k).1

/-- **2.** The image of `Φ` is exactly the module of relations among `f1,…,f4`. -/
theorem range_phiMap_eq_ker_genMap : LinearMap.range (phiMap k) = LinearMap.ker (genMap k) :=
  (phi_exact_aux k).2

omit [CharZero k] in
/-- **3.** The image of the generator map is `J`. -/
theorem range_genMap_eq_J : LinearMap.range (genMap k) = J k := by
  have := range_rowMap (A := S k) (X 0) (X 1) (X 2)
  exact this

/-- **The exact complex** `0 → S^3 --Φ--> S^4 --(f_i)--> S --> S/J → 0`:
`Φ` is injective, exactness at `S^4`, exactness at `S`, and `S → S/J` is surjective. -/
theorem hilbertBurch_exact :
    Function.Injective (phiMap k) ∧
      Function.Exact (phiMap k) (genMap k) ∧
      Function.Exact (genMap k) (Ideal.Quotient.mkₐ k (J k)) ∧
      Function.Surjective (Ideal.Quotient.mkₐ k (J k)) := by
  refine ⟨phiMap_injective k, ?_, ?_, Ideal.Quotient.mkₐ_surjective k (J k)⟩
  · rw [LinearMap.exact_iff]
    exact (range_phiMap_eq_ker_genMap k).symm
  · intro w
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Set.mem_range,
      ← LinearMap.mem_range, range_genMap_eq_J]

/-- The same complex, stated with `S`-linear maps: `Ideal.Quotient.mkₐ` viewed as the
`S`-linear quotient map `S → S ⧸ J` (`Submodule.mkQ`). -/
theorem hilbertBurch_exact_linear :
    Function.Injective (phiMap k) ∧
      Function.Exact (phiMap k) (genMap k) ∧
      Function.Exact (genMap k) (J k).mkQ ∧
      Function.Surjective (J k).mkQ := by
  refine ⟨phiMap_injective k, ?_, ?_, Submodule.mkQ_surjective _⟩
  · rw [LinearMap.exact_iff]
    exact (range_phiMap_eq_ker_genMap k).symm
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, range_genMap_eq_J]

end Moh

end MohP3.HilbertBurch

end
