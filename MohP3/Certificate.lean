import MohP3.Defs
import MohP3.Generic

/-!
# Moh P3: the exact containment certificate over `ℚ[x,y,z]`

`Q ≤ P` comes from the two reverse identities, and `P^2 ≤ Q` from the ten
scaled identities `d_ij * f_i * f_j = A_ij * H1 + B_ij * H2` of
`identities.txt`.  Both, and the ten identities themselves, are proved over an
arbitrary commutative ring in `MohP3.Generic`; here they are specialised to
`R = ℚ[x,y,z]`, where the definitions of `f1, …, f4, H1, H2` are literally the
generic ones evaluated at `x, y, z`.
-/

noncomputable section

open MvPolynomial

namespace MohP3

/-- Expanded form of `H1`, as recorded in `witnesses.txt`. -/
theorem H1_expanded : H1 =
    128*x^7*y*z^3 - 272*x^6*y^3*z^2 - 128*x^5*y^5*z^6
    + 120*x^5*y^5*z - 24*x^5 + 16*x^4*y^7*z^5
    + 208*x^4*y^2*z^4 + 40*x^3*y^9*z^4 - 394*x^3*y^4*z^3
    - 144*x^2*y^6*z^7 + 291*x^2*y^6*z^2 + 177*x^2*y*z
    + 90*x*y^8*z^6 + 144*x*y^3*z^5 - 234*x*y^3
    + 81*y^10*z^5 - 162*y^5*z^4 + 81*z^3 :=
  Gen.H1_expanded x y z

/-- Expanded form of `H2`, as recorded in `witnesses.txt`. -/
theorem H2_expanded : H2 =
    -80*x^6*y^2*z^3 + 170*x^5*y^4*z^2 + 80*x^4*y^6*z^6
    - 75*x^4*y^6*z + 15*x^4*y - 10*x^3*y^8*z^5
    + 32*x^3*y^3*z^4 - 25*x^2*y^10*z^4 - 98*x^2*y^5*z^3
    - 81*x^2*z^2 - 72*x*y^7*z^7 - 30*x*y^7*z^2
    + 102*x*y^2*z - 36*y^9*z^6 + 72*y^4*z^5 - 36*y^4 :=
  Gen.H2_expanded x y z

/-- The first reverse identity: `H1` is an explicit combination of `f1, f3, f4`. -/
theorem H1_eq : H1 = (-24*x)*f1 + ell*f3 + 81*f4 := Gen.H1_eq x y z

/-- The second reverse identity: `H2` is an explicit combination of `f1, f2, f3`. -/
theorem H2_eq : H2 = (-12*y)*f1 + (27*x)*f2 + kappa*f3 := Gen.H2_eq x y z

theorem H1_mem_P : H1 ∈ P := Gen.H1_mem_P x y z
theorem H2_mem_P : H2 ∈ P := Gen.H2_mem_P x y z

/-- `Q ≤ P`. -/
theorem Q_le_P : Q ≤ P := Gen.Q_le_P x y z

/-- `P ^ 2 ≤ Q`, by the ten scaled certificate identities
`Gen.cert_11, …, Gen.cert_44`. -/
theorem P_sq_le_Q : P ^ 2 ≤ Q := Gen.P_sq_le_Q x y z

/-- `Q` and `P` have the same radical. -/
theorem radical_Q_eq_radical_P : Q.radical = P.radical := Gen.radical_Q_eq_radical_P x y z

end MohP3
