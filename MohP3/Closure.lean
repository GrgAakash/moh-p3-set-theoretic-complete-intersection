import MohP3.Certificate

/-!
# Moh P3: the kernel of the parametrization

This file proves `RingHom.ker rho = P` by a completely elementary, finite
argument, independent of any Gröbner-basis black box:

* eight explicit elements `hh 0, …, hh 7` of `R` are exhibited together with
  sixteen explicit identities showing that, modulo `P`, the `ℚ[y]`-module they
  span is stable under multiplication by `x` and by `z`.  Hence that module is
  all of `R/P` (Lemma `good_all`);
* the eight images `rho (hh i)` have pairwise distinct trailing degrees modulo
  `8 = deg rho y`, whence they are linearly independent over `ρ(ℚ[y]) = ℚ[t^8]`
  (Lemma `indep`).

Together these give `ker rho ⊆ P`; the reverse inclusion is the evaluation
`rho (f i) = 0`.
-/

noncomputable section

open MvPolynomial

namespace MohP3

/-! ### The coefficient ring `ℚ[y] ⊆ R` -/

/-- The embedding of the univariate polynomial ring as `ℚ[y] ⊆ R`. -/
def iota : Polynomial ℚ →+* R := Polynomial.eval₂RingHom MvPolynomial.C y

@[simp] lemma iota_X : iota Polynomial.X = y := by simp [iota]

@[simp] lemma iota_C (a : ℚ) : iota (Polynomial.C a) = MvPolynomial.C a := by simp [iota]

@[simp] lemma iota_ofNat (n : ℕ) [n.AtLeastTwo] :
    iota (no_index (OfNat.ofNat n)) = OfNat.ofNat n := map_ofNat iota n

/-! ### The eight module generators -/

/-- Eight elements of `R` whose classes generate `R/P` as a `ℚ[y]`-module, and
whose images under `rho` are a `ℚ[t^8]`-basis of the image of `rho`. -/
def hh : Fin 8 → R :=
  ![1, x, z, x^2, x*z - y^2, x^3 - y*z, z^2 - y*x^2, x^2*z - y^2*x - y^9]

/-- Coefficients of `18 * x * hh i` in the generators `hh j`. -/
def QX : Fin 8 → Fin 8 → Polynomial ℚ :=
![
  ![0, (18 : Polynomial ℚ), 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, (18 : Polynomial ℚ), 0, 0, 0, 0],
  ![18*Polynomial.X^2, 0, 0, 0, (18 : Polynomial ℚ), 0, 0, 0],
  ![0, 0, 18*Polynomial.X^1, 0, 0, (18 : Polynomial ℚ), 0, 0],
  ![18*Polynomial.X^9, 0, 0, 0, 0, 0, 0, (18 : Polynomial ℚ)],
  ![0, 12*Polynomial.X^21, 108*Polynomial.X^8, -54*Polynomial.X^14, 54*Polynomial.X^1, 24*Polynomial.X^7, -42*Polynomial.X^13, -12*Polynomial.X^19],
  ![0, 3*Polynomial.X^15, 0, -18*Polynomial.X^8, 0, -12*Polynomial.X^1, -15*Polynomial.X^7, -3*Polynomial.X^13],
  ![0, 9*Polynomial.X^9, 0, 0, 0, 0, -9*Polynomial.X^1, -9*Polynomial.X^7]]

/-- Coefficients of `18 * z * hh i` in the generators `hh j`. -/
def QZ : Fin 8 → Fin 8 → Polynomial ℚ :=
![
  ![0, 0, (18 : Polynomial ℚ), 0, 0, 0, 0, 0],
  ![18*Polynomial.X^2, 0, 0, 0, (18 : Polynomial ℚ), 0, 0, 0],
  ![0, 0, 0, 18*Polynomial.X^1, 0, 0, (18 : Polynomial ℚ), 0],
  ![18*Polynomial.X^9, 18*Polynomial.X^2, 0, 0, 0, 0, 0, (18 : Polynomial ℚ)],
  ![0, 3*Polynomial.X^15, 0, -18*Polynomial.X^8, 0, 6*Polynomial.X^1, -15*Polynomial.X^7, -3*Polynomial.X^13],
  ![0, 27*Polynomial.X^9, 0, 0, 0, 0, -27*Polynomial.X^1, -9*Polynomial.X^7],
  ![-18*Polynomial.X^10, 0, 0, 0, 0, 0, 0, -36*Polynomial.X^1],
  ![0, 0, 0, 0, 18*Polynomial.X^2, 0, 0, 0]]

lemma key_x_0 : (18 : R) * (x * hh 0) - ∑ j, iota (QX 0 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_ofNat, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_x_1 : (18 : R) * (x * hh 1) - ∑ j, iota (QX 1 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_ofNat, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_x_2 : (18 : R) * (x * hh 2) - ∑ j, iota (QX 2 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_x_3 : (18 : R) * (x * hh 3) - ∑ j, iota (QX 3 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_x_4 : (18 : R) * (x * hh 4) - ∑ j, iota (QX 4 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_x_5 : (18 : R) * (x * hh 5) - ∑ j, iota (QX 5 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -4*y^25 - 18*y^5*z + 18) (c2 := 4*x*y^24 + 12*x*y^4*z + 8*y^11*z - 15*y^6) (c3 := 3*x*y^5 - 4*y^12) (c4 := 12*y^23*z + 12*y^18 + 54*y^3*z^2) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero, map_neg,
      f1, f2, f3, f4]
    ring)

lemma key_x_6 : (18 : R) * (x * hh 6) - ∑ j, iota (QX 6 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -y^19) (c2 := x*y^18 + 2*y^5*z - 6) (c3 := -y^6) (c4 := 3*y^17*z + 3*y^12) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero, map_neg,
      f1, f2, f3, f4]
    ring)

lemma key_x_7 : (18 : R) * (x * hh 7) - ∑ j, iota (QX 7 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -3*y^13) (c2 := 3*x*y^12 - 6*y^4*z^2) (c3 := 3*y^5*z + 9) (c4 := 9*y^11*z + 18*y^6) (by
    simp only [hh, QX, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero, map_neg,
      f1, f2, f3, f4]
    ring)

lemma key_z_0 : (18 : R) * (z * hh 0) - ∑ j, iota (QZ 0 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_ofNat, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_z_1 : (18 : R) * (z * hh 1) - ∑ j, iota (QZ 1 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_z_2 : (18 : R) * (z * hh 2) - ∑ j, iota (QZ 2 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_z_3 : (18 : R) * (z * hh 3) - ∑ j, iota (QZ 3 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_z_4 : (18 : R) * (z * hh 4) - ∑ j, iota (QZ 4 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -y^19) (c2 := x*y^18 + 2*y^5*z - 6) (c3 := -y^6) (c4 := 3*y^17*z + 3*y^12) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero, map_neg,
      f1, f2, f3, f4]
    ring)

lemma key_z_5 : (18 : R) * (z * hh 5) - ∑ j, iota (QZ 5 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -3*y^13) (c2 := 3*x*y^12 - 6*y^4*z^2) (c3 := 3*y^5*z + 9) (c4 := 9*y^11*z + 18*y^6) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero, map_neg,
      f1, f2, f3, f4]
    ring)

lemma key_z_6 : (18 : R) * (z * hh 6) - ∑ j, iota (QZ 6 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -6*y^7) (c2 := 6*x*y^6) (c3 := 0) (c4 := 18*y^5*z + 18) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero, map_neg,
      f1, f2, f3, f4]
    ring)

lemma key_z_7 : (18 : R) * (z * hh 7) - ∑ j, iota (QZ 7 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -6*y^6*z + 6*y) (c2 := 6*x*y^5*z - 6*x) (c3 := 0) (c4 := 18*y^4*z^2) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)

lemma key_x (i : Fin 8) : (18 : R) * (x * hh i) - ∑ j, iota (QX i j) * hh j ∈ P := by
  fin_cases i
  exacts [key_x_0, key_x_1, key_x_2, key_x_3, key_x_4, key_x_5, key_x_6, key_x_7]

lemma key_z (i : Fin 8) : (18 : R) * (z * hh i) - ∑ j, iota (QZ i j) * hh j ∈ P := by
  fin_cases i
  exacts [key_z_0, key_z_1, key_z_2, key_z_3, key_z_4, key_z_5, key_z_6, key_z_7]

end MohP3
