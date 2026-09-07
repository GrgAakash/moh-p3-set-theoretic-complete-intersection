import MohP3

/-!
# Proved Palomar solution

The declarations below repeat the Mathlib-only challenge statements verbatim
and discharge them using the fully proved Moh P3 library.
-/

namespace MohP3.Palomar

theorem global_setTheoretic_completeIntersection
    (k : Type*) [Field k] [CharZero k] :
    let R := MvPolynomial (Fin 3) k
    let x : R := MvPolynomial.X 0
    let y : R := MvPolynomial.X 1
    let z : R := MvPolynomial.X 2
    let f1 := x^4 - x^2*y^4*z^3 - 2*x*y^6*z^2 - 4*x*y*z - 3*y^3*z^5 + 3*y^3
    let f2 := x^3*y - x*y^5*z^3 - 3*x*z^2 - 2*y^7*z^2 + 2*y^2*z
    let f3 := 2*x^3*z - 3*x^2*y^2 - 2*x*y^4*z^4 - y^6*z^3 + y*z^2
    let f4 := x^2*y*z - 2*x*y^3 - y^5*z^4 + z^3
    let ell := 64*x^4*y*z^2 - 40*x^3*y^3*z + 72*x*y^2*z^3 - 81*y^4*z^2
    let kappa := -40*x^3*y^2*z^2 + 25*x^2*y^4*z + 36*y^3*z^3
    let H1 := 81*f4 - 24*x*f1 + ell*f3
    let H2 := -12*y*f1 + 27*x*f2 + kappa*f3
    let P : Ideal R := Ideal.span ({f1, f2, f3, f4} : Set R)
    let Q : Ideal R := Ideal.span ({H1, H2} : Set R)
    let rho : R →+* Polynomial k :=
      MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X^6 + Polynomial.X^31,
        Polynomial.X^8, Polynomial.X^10]
    RingHom.ker rho = P ∧
    Q.radical = P ∧
    P.height = 2 ∧
    (⨅ s ∈ {s : Finset R | (Ideal.span (s : Set R)).radical = P.radical},
      (s.card : ℕ∞)) = 2 := by
  change RingHom.ker (rho_k k) = Ppoly k ∧
    (Qpoly k).radical = Ppoly k ∧
    (Ppoly k).height = 2 ∧
    arithRank (Ppoly k) = 2
  exact ⟨global_kernel_k k, global_radical_k k, height_Ppoly k, arithRank_Ppoly k⟩

theorem formalLocal_setTheoretic_completeIntersection
    (k : Type*) [Field k] [CharZero k] :
    let R := MvPowerSeries (Fin 3) k
    let x : R := MvPowerSeries.X 0
    let y : R := MvPowerSeries.X 1
    let z : R := MvPowerSeries.X 2
    let f1 := x^4 - x^2*y^4*z^3 - 2*x*y^6*z^2 - 4*x*y*z - 3*y^3*z^5 + 3*y^3
    let f2 := x^3*y - x*y^5*z^3 - 3*x*z^2 - 2*y^7*z^2 + 2*y^2*z
    let f3 := 2*x^3*z - 3*x^2*y^2 - 2*x*y^4*z^4 - y^6*z^3 + y*z^2
    let f4 := x^2*y*z - 2*x*y^3 - y^5*z^4 + z^3
    let ell := 64*x^4*y*z^2 - 40*x^3*y^3*z + 72*x*y^2*z^3 - 81*y^4*z^2
    let kappa := -40*x^3*y^2*z^2 + 25*x^2*y^4*z + 36*y^3*z^3
    let H1 := 81*f4 - 24*x*f1 + ell*f3
    let H2 := -12*y*f1 + 27*x*f2 + kappa*f3
    let P : Ideal R := Ideal.span ({f1, f2, f3, f4} : Set R)
    let Q : Ideal R := Ideal.span ({H1, H2} : Set R)
    let aa : Fin 3 → PowerSeries k :=
      ![PowerSeries.X^6 + PowerSeries.X^31, PowerSeries.X^8, PowerSeries.X^10]
    let haa : MvPowerSeries.HasSubst aa := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro i
      have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
        PowerSeries.constantCoeff_X
      fin_cases i <;> simp [aa, hX]
    let psi : R →ₐ[k] PowerSeries k := MvPowerSeries.substAlgHom haa
    RingHom.ker psi = P ∧
    Q.radical = P ∧
    P.height = 2 ∧
    (⨅ s ∈ {s : Finset R | (Ideal.span (s : Set R)).radical = P.radical},
      (s.card : ℕ∞)) = 2 := by
  change RingHom.ker (FormalLocal.psi k) = FormalLocal.Pk k ∧
    (FormalLocal.Qk k).radical = FormalLocal.Pk k ∧
    (FormalLocal.Pk k).height = 2 ∧
    arithRank (FormalLocal.Pk k) = 2
  exact ⟨FormalLocal.ker_psi k, FormalLocal.radical_Qk_eq_Pk k,
    FormalLocal.height_Pk k, FormalLocal.arithRank_Pk k⟩

end MohP3.Palomar

#print axioms MohP3.Palomar.global_setTheoretic_completeIntersection
#print axioms MohP3.Palomar.formalLocal_setTheoretic_completeIntersection
