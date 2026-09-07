import Mathlib

/-!
# Arithmetic rank

This file introduces the *arithmetic rank* `arithRank I` of an ideal `I` of a
commutative ring: the least number of elements of the ring whose span has the
same radical as `I` (so `arithRank I ≤ n` says exactly that `I` is, up to
radical, cut out by `n` equations).  An ideal `I` of a Noetherian ring is a
*set-theoretic complete intersection* when `arithRank I = height I`.

Two general facts are proved:

* `MohP3.mem_minimalPrimes_of_radical_eq` — if the radical of `I` is a prime
  `p`, then `p` is a minimal prime of `I`;
* `MohP3.height_le_arithRank` — Krull's height theorem gives
  `height p ≤ arithRank p` for a prime `p` of a Noetherian ring.

Together these give the standard lower bound for the arithmetic rank used in
`MohP3.Height`.
-/

noncomputable section

namespace MohP3

variable {A : Type*} [CommRing A]

/-- The **arithmetic rank** of an ideal `I`: the least cardinality of a finite
set of elements whose span has the same radical as `I`.  It is `⊤` if no finite
set works. -/
noncomputable def arithRank (I : Ideal A) : ℕ∞ :=
  ⨅ s ∈ {s : Finset A | (Ideal.span (s : Set A)).radical = I.radical}, (s.card : ℕ∞)

lemma arithRank_le {I : Ideal A} (s : Finset A)
    (hs : (Ideal.span (s : Set A)).radical = I.radical) :
    arithRank I ≤ s.card :=
  iInf₂_le (f := fun (s : Finset A) _ => (s.card : ℕ∞)) s hs

/-- If the radical of `I` is a prime ideal `p`, then `p` is a minimal prime
of `I`. -/
lemma mem_minimalPrimes_of_radical_eq {I p : Ideal A} (hp : p.IsPrime)
    (h : I.radical = p) : p ∈ I.minimalPrimes := by
  refine ⟨⟨hp, h ▸ Ideal.le_radical⟩, ?_⟩
  rintro q ⟨hq, hIq⟩ _
  exact h ▸ hq.radical_le_iff.mpr hIq

/-- **Krull's height theorem** gives the standard lower bound for the arithmetic
rank of a prime ideal of a Noetherian ring. -/
lemma height_le_arithRank [IsNoetherianRing A] (p : Ideal A) (hp : p.IsPrime) :
    p.height ≤ arithRank p := by
  refine le_iInf₂ fun s hs => ?_
  refine Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (mem_minimalPrimes_of_radical_eq hp ?_)
  rw [hs, hp.radical]

end MohP3
