import MohP3

/-!
# Proved Palomar solution

Comparator checks that these declarations have exactly the same types as the
Mathlib-only declarations in `Challenge.lean` and use only the permitted
axioms.
-/

namespace MohP3.Palomar

theorem global_setTheoretic_completeIntersection
    (k : Type*) [Field k] [CharZero k] :
    RingHom.ker (rho_k k) = Ppoly k ∧
    (Qpoly k).radical = Ppoly k ∧
    (Ppoly k).height = 2 ∧
    arithRank (Ppoly k) = 2 := by
  exact ⟨global_kernel_k k, global_radical_k k, height_Ppoly k, arithRank_Ppoly k⟩

theorem formalLocal_setTheoretic_completeIntersection
    (k : Type*) [Field k] [CharZero k] :
    RingHom.ker (FormalLocal.psi k) = FormalLocal.Pk k ∧
    (FormalLocal.Qk k).radical = FormalLocal.Pk k ∧
    (FormalLocal.Pk k).height = 2 ∧
    arithRank (FormalLocal.Pk k) = 2 := by
  exact ⟨FormalLocal.ker_psi k, FormalLocal.radical_Qk_eq_Pk k,
    FormalLocal.height_Pk k, FormalLocal.arithRank_Pk k⟩

end MohP3.Palomar

#print axioms MohP3.Palomar.global_setTheoretic_completeIntersection
#print axioms MohP3.Palomar.formalLocal_setTheoretic_completeIntersection
