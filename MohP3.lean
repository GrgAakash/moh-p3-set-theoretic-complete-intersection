import MohP3.Defs
import MohP3.Certificate
import MohP3.Independence
import MohP3.Closure
import MohP3.Kernel
import MohP3.Global
import MohP3.FormalLocal
import MohP3.Order
import MohP3.GenClosure
import MohP3.Generation
import MohP3.IndependenceK
import MohP3.GlobalK
import MohP3.Ara
import MohP3.Height
import MohP3.MvPowerSeriesAux
import MohP3.HeightLocal
import MohP3.HeightK

/-!
# Moh P3: exact global certificate

This is the top-level module.  The development is split as follows.

* `MohP3.Defs` – the ring `R = ℚ[x,y,z]`, the four curve generators
  `f1, …, f4`, the two witnesses `H1, H2`, the ideals `P = (f1,f2,f3,f4)` and
  `Q = (H1,H2)`, and the parametrization `rho : R →+* ℚ[t]`.
* `MohP3.Certificate` – the expanded forms of `H1, H2`, the two reverse
  identities giving `Q ≤ P`, and the ten scaled identities
  `d_ij * f_i * f_j = A_ij * H1 + B_ij * H2` giving `P ^ 2 ≤ Q`.
* `MohP3.Independence` – the eight polynomials `vv i = rho (hh i)` and their
  linear independence over `ℚ[t^8]`.
* `MohP3.Closure` – the eight module generators `hh i` and the sixteen
  identities expressing `18 * x * hh i` and `18 * z * hh i` as `ℚ[y]`-linear
  combinations of the `hh j` modulo `P`.
* `MohP3.Kernel` – the exact computation `RingHom.ker rho = P`, proved from
  the previous two files without any Gröbner-basis black box.
* `MohP3.Generic` – all the certificate identities over an arbitrary
  commutative ring, so that they can be reused verbatim over `k[[x,y,z]]`.
* `MohP3.Global` – `P` is prime and `Ideal.radical Q = P`.
* `MohP3.FormalLocal` – the formal-local situation over `k[[x,y,z]]` for a
  characteristic-zero field `k`: the certificate, `radical (H1,H2) = radical
  (f1,…,f4)`, `radical (H1,H2) ≤ ker psi`, and the linear independence of the
  eight generators over `k[[t^8]]`, together with the statement `Generation k`
  of the completed module-generation lemma and the deductions from it.
* `MohP3.GenClosure` – the sixteen closure identities over an arbitrary
  commutative ring, with the integer data and the weight estimates.
* `MohP3.Order` – the weighted orders `wt x = 6, wt y = 8, wt z = 10` on
  `k[[x,y,z]]` and on `k[[y]]`, their calculus, coefficientwise limits, and the
  weight-homogeneous decomposition.
* `MohP3.Generation` – the *unconditional* proof of `Generation k` by a formal
  division algorithm for the weighted filtration, and hence
  `RingHom.ker (psi k) = Pk k` and the formal-local theorem
  `(Qk k).radical = RingHom.ker (psi k)`.
* `MohP3.IndependenceK`, `MohP3.GlobalK` – the global theorem
  (`RingHom.ker (rho_k k) = Ppoly k` and `radical (Qpoly k) = Ppoly k`) over an
  arbitrary field `k` of characteristic zero.

The statements requested in the original specification are restated verbatim
below, in the namespace `MohP3.Summary`.
-/

noncomputable section

open MvPolynomial

namespace MohP3.Summary

/-- The full expanded form of `H1`, as recorded in `witnesses.txt`. -/
theorem H1_expanded : H1 =
    128*x^7*y*z^3 - 272*x^6*y^3*z^2 - 128*x^5*y^5*z^6
    + 120*x^5*y^5*z - 24*x^5 + 16*x^4*y^7*z^5
    + 208*x^4*y^2*z^4 + 40*x^3*y^9*z^4 - 394*x^3*y^4*z^3
    - 144*x^2*y^6*z^7 + 291*x^2*y^6*z^2 + 177*x^2*y*z
    + 90*x*y^8*z^6 + 144*x*y^3*z^5 - 234*x*y^3
    + 81*y^10*z^5 - 162*y^5*z^4 + 81*z^3 :=
  MohP3.H1_expanded

/-- The full expanded form of `H2`, as recorded in `witnesses.txt`. -/
theorem H2_expanded : H2 =
    -80*x^6*y^2*z^3 + 170*x^5*y^4*z^2 + 80*x^4*y^6*z^6
    - 75*x^4*y^6*z + 15*x^4*y - 10*x^3*y^8*z^5
    + 32*x^3*y^3*z^4 - 25*x^2*y^10*z^4 - 98*x^2*y^5*z^3
    - 81*x^2*z^2 - 72*x*y^7*z^7 - 30*x*y^7*z^2
    + 102*x*y^2*z - 36*y^9*z^6 + 72*y^4*z^5 - 36*y^4 :=
  MohP3.H2_expanded

/-- The two reverse identities imply this inclusion. -/
theorem Q_le_P : Q ≤ P := MohP3.Q_le_P

/-- The ten scaled identities of `identities.txt`; the scales are units in `ℚ`. -/
theorem P_sq_le_Q : P ^ 2 ≤ Q := MohP3.P_sq_le_Q

/-- The kernel computation, proved independently of the containments. -/
theorem kernel_rho : RingHom.ker rho = P := MohP3.kernel_rho

theorem P_isPrime : P.IsPrime := MohP3.P_isPrime

theorem radical_Q : Ideal.radical Q = P := MohP3.radical_Q

/-! ### Height and arithmetic rank -/

/-- The height of the Moh curve ideal is two. -/
theorem height_P : P.height = 2 := MohP3.height_P

/-- The arithmetic rank of the Moh curve ideal is two: it is a set-theoretic
complete intersection in the literal sense. -/
theorem arithRank_P : arithRank P = 2 := MohP3.arithRank_P

/-! ### Formal-local statements over `k[[x,y,z]]`

These are the completed second-milestone results.  The conditional bridge is
retained for documentation, and `MohP3.Generation` proves its hypothesis
unconditionally. -/

open MohP3.FormalLocal in
/-- Over `k[[x,y,z]]`, one inclusion of the formal-local statement holds
unconditionally. -/
theorem radical_Qk_le_ker (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical ≤ RingHom.ker (psi k) :=
  MohP3.FormalLocal.radical_Qk_le_ker k

open MohP3.FormalLocal in
/-- Over `k[[x,y,z]]`, the two ideals have the same radical, unconditionally. -/
theorem radical_Qk_eq_radical_Pk (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical = (Pk k).radical :=
  MohP3.FormalLocal.radical_Qk_eq_radical_Pk k

open MohP3.FormalLocal in
/-- The formal-local bridge, conditional on the completed generation statement
`Generation k`; the next theorem supplies this hypothesis unconditionally. -/
theorem radical_Qk_eq_ker_of_generation (k : Type*) [Field k] [CharZero k]
    (hgen : Generation k) : (Qk k).radical = RingHom.ker (psi k) :=
  MohP3.FormalLocal.radical_Qk_eq_ker_of_generation k hgen

open MohP3.FormalLocal in
/-- The completed generation statement itself, proved unconditionally. -/
theorem generation (k : Type*) [Field k] [CharZero k] : Generation k :=
  MohP3.FormalLocal.generation k

open MohP3.FormalLocal in
/-- The kernel of the formal parametrization, unconditionally. -/
theorem ker_psi (k : Type*) [Field k] [CharZero k] : RingHom.ker (psi k) = Pk k :=
  MohP3.FormalLocal.ker_psi k

open MohP3.FormalLocal in
/-- **The formal-local theorem**, unconditionally. -/
theorem formalLocal_radical_Qk (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical = RingHom.ker (psi k) :=
  MohP3.FormalLocal.formalLocal_radical_Qk k

open MohP3.FormalLocal in
/-- After completion the curve ideal still has height two. -/
theorem height_Pk (k : Type*) [Field k] [CharZero k] : (Pk k).height = 2 :=
  MohP3.FormalLocal.height_Pk k

open MohP3.FormalLocal in
/-- After completion the arithmetic rank is still two. -/
theorem arithRank_Pk (k : Type*) [Field k] [CharZero k] : arithRank (Pk k) = 2 :=
  MohP3.FormalLocal.arithRank_Pk k

/-! ### The global statements over an arbitrary characteristic-zero field -/

/-- The kernel of the parametrization over any field of characteristic zero. -/
theorem global_kernel_k (k : Type*) [Field k] [CharZero k] :
    RingHom.ker (rho_k k) = Ppoly k :=
  MohP3.global_kernel_k k

/-- The set-theoretic complete intersection statement over any field of
characteristic zero. -/
theorem global_radical_k (k : Type*) [Field k] [CharZero k] :
    Ideal.radical (Qpoly k) = Ppoly k :=
  MohP3.global_radical_k k

/-- The height of the curve ideal over any field of characteristic zero. -/
theorem height_Ppoly (k : Type*) [Field k] [CharZero k] : (Ppoly k).height = 2 :=
  MohP3.height_Ppoly k

/-- The arithmetic rank of the curve ideal over any field of characteristic
zero. -/
theorem arithRank_Ppoly (k : Type*) [Field k] [CharZero k] : arithRank (Ppoly k) = 2 :=
  MohP3.arithRank_Ppoly k

end MohP3.Summary

/-! ### Axiom audit

The five theorems requested for the audit; each depends only on the standard
Lean foundations `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms MohP3.FormalLocal.generation
#print axioms MohP3.FormalLocal.ker_psi
#print axioms MohP3.FormalLocal.formalLocal_radical_Qk
#print axioms MohP3.global_kernel_k
#print axioms MohP3.global_radical_k
#print axioms MohP3.height_P
#print axioms MohP3.arithRank_P
#print axioms MohP3.FormalLocal.height_Pk
#print axioms MohP3.FormalLocal.arithRank_Pk
#print axioms MohP3.height_Ppoly
#print axioms MohP3.arithRank_Ppoly
