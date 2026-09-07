# Moh P3 formalization — report

> Historical environment note: this report records the original Aristotle
> build under Lean 4.28.0.  The public submission package has since been
> migrated to Lean 4.33.0 and Mathlib revision
> `db584cd6d46c92f209a44c0f1c829460d327499d`, with theorem statements and
> assumptions unchanged; see `VERIFICATION.md` for the migration verification.

## 1. Environment

| item | value |
|---|---|
| Lean | `leanprover/lean4:v4.28.0` (file `lean-toolchain`) |
| Mathlib | `leanprover-community/mathlib4`, revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (input rev `v4.28.0`), as pinned in `lake-manifest.json` |
| build tool | `lake` |
| build command | `lake build MohP3` |

## 2. Project files

Lean sources (all inside the single library `MohP3`, declared in `lakefile.toml`
with `globs = ["MohP3", "MohP3.*"]`):

| file | contents |
|---|---|
| `MohP3.lean` | top-level module; imports everything, restates the requested theorems verbatim in namespace `MohP3.Summary`, and runs the axiom audit |
| `MohP3/Defs.lean` | `R = ℚ[x,y,z]`, `f1,…,f4`, `ell`, `kappa`, `H1`, `H2`, `P`, `Q`, `rho` |
| `MohP3/Generic.lean` | the whole certificate over an arbitrary commutative ring `A` and elements `x y z : A`: expansions of `H1,H2`, the two reverse identities, the ten scaled identities, `Q ≤ P`, `P^2 ≤ Q`, `radical Q = radical P` |
| `MohP3/Certificate.lean` | the `ℚ[x,y,z]` instantiation of `MohP3/Generic.lean` |
| `MohP3/Independence.lean` | the eight polynomials `vv i` and their linear independence over `ℚ[t^8]` |
| `MohP3/Closure.lean` | the eight module generators `hh i`, the coefficient tables `QX`, `QZ`, and the sixteen identities `18·x·hh i ≡ ∑ q_ij(y)·hh j`, `18·z·hh i ≡ ∑ q_ij(y)·hh j` (mod `P`), over `ℚ` |
| `MohP3/Kernel.lean` | `RingHom.ker rho = P` over `ℚ` |
| `MohP3/Global.lean` | `P.IsPrime`, `P.radical = P`, `Ideal.radical Q = P` |
| `MohP3/GenClosure.lean` | **new** — the same sixteen closure identities over an *arbitrary commutative ring*, with all data stored in integer arrays (`qxD`, `qzD`, `wxD`, `wzD`), together with the weight vectors `sig`, `tau` and the four weight estimates `qxD_wt`, `qzD_wt`, `wxD_wt`, `wzD_wt` |
| `MohP3/Order.lean` | **new** — the weighted orders `WOrd` on `k[[x,y,z]]` and `YOrd` on `k[[y]]` for the weighting `wt x = 6, wt y = 8, wt z = 10`; their calculus, the vanishing criterion, coefficientwise limits of families whose orders tend to infinity, and the weight-homogeneous decomposition of a series |
| `MohP3/Generation.lean` | **new** — the unconditional proof of `Generation k`, hence `RingHom.ker (psi k) = Pk k` and the formal-local theorem `(Qk k).radical = RingHom.ker (psi k)` |
| `MohP3/IndependenceK.lean` | **new** — linear independence of the eight polynomials `vvK k i` over `k[t^8]`, for an arbitrary characteristic-zero field `k` |
| `MohP3/GlobalK.lean` | **new** — the global theorem over an arbitrary characteristic-zero field: `RingHom.ker (rho_k k) = Ppoly k` and `Ideal.radical (Qpoly k) = Ppoly k` |
| `MohP3/FormalLocal.lean` | the formal-local setting over `k[[x,y,z]]`: `psi`, `Pk`, `Qk`, `hhS`, the certificate, `indepS`, the definition of `Generation`, and the deductions from it |
| `MohP3/Ara.lean` | **new** — the arithmetic rank `arithRank I` of an ideal, and the two general facts used about it: a prime equal to `I.radical` is a minimal prime of `I`, and (Krull's height theorem) `height p ≤ arithRank p` for a prime `p` of a Noetherian ring |
| `MohP3/Height.lean` | **new** — over `ℚ`: `P` is a minimal prime of `Q`, the surface prime `Psurf = ker (x ↦ s, y ↦ w^4, z ↦ w^5)`, the chain `⊥ < Psurf < P`, `P.height = 2` and `arithRank P = 2` |
| `MohP3/HeightK.lean` | **new** — the same over an arbitrary characteristic-zero field: `(Ppoly k).height = 2`, `arithRank (Ppoly k) = 2` |
| `MohP3/MvPowerSeriesAux.lean` | **new** — reindexing of variables `MvPowerSeries.reindexEquiv`, the splitting `MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R)` (`MvPowerSeries.optionEquiv`), and the consequence `IsNoetherianRing (MvPowerSeries (Fin n) R)` |
| `MohP3/HeightLocal.lean` | **new** — the formal-local versions: `(Pk k).height = 2` and `arithRank (Pk k) = 2` in `k[[x,y,z]]` |

Auxiliary, **not** part of any proof:

* `tools/*.py` — a small self-contained exact CAS (sparse polynomial arithmetic
  over `ℚ`, Buchberger with cofactor tracking, Hermite normal form) used to
  *derive* the data that appears in the Lean files (the eight module
  generators, the coefficient tables, all cofactors over `f1,…,f4`, and the
  weight estimates), and to re-check the transcription of `witnesses.txt` /
  `identities.txt`.  `tools/gen_genclosure.py` additionally re-verifies the
  sixteen closure identities and all weight inequalities with exact integer
  arithmetic and emits the data arrays of `MohP3/GenClosure.lean`.  Every
  statement these scripts produced is re-proved inside Lean by exact
  polynomial normalization (`ring`); the scripts are evidence only and are not
  trusted by the formalization.
* the user-supplied `witnesses.txt`, `identities.txt`, `PROOF.md`,
  `certificate.json`, `*.m2`, and the manuscript PDF.

## 3. Result 1 — the global theorem over `ℚ` (already complete)

All in namespace `MohP3.Summary` (`MohP3.lean`), with the underlying results in
namespace `MohP3`:

1. `H1_expanded`, `H2_expanded` — the two witnesses equal the expanded degree-16
   polynomials of `witnesses.txt`.
2. `Q_le_P` — from the two reverse identities
   `H1 = -24x·f1 + ell·f3 + 81·f4`, `H2 = -12y·f1 + 27x·f2 + kappa·f3`.
3. `P_sq_le_Q` — from the ten identities `d_ij·f_i·f_j = A_ij·H1 + B_ij·H2`
   (`MohP3.Gen.cert_11 … MohP3.Gen.cert_44`), each verified by `ring`, using
   that every `d_ij` is a unit of `ℚ`.
4. `kernel_rho : RingHom.ker rho = P` — proved independently, by an elementary
   finite argument (no Gröbner black box, no appeal to the Macaulay2 run):
   * `MohP3.good_all`: the sixteen identities of `MohP3/Closure.lean` show that
     modulo `P` the `ℚ[y]`-module spanned by
     `hh = (1, x, z, x², xz−y², x³−yz, z²−yx², x²z−y²x−y⁹)`
     is stable under multiplication by `x`, `y`, `z` and contains `1`, hence is
     all of `R/P`;
   * `MohP3.indep`: the images `rho (hh i)` have trailing degrees
     `0, 6, 10, 12, 41, 43, 45, 47`, pairwise distinct modulo `8 = ord (rho y)`,
     hence are linearly independent over `rho (ℚ[y]) = ℚ[t^8]`.
5. `P_isPrime` — `P` is the kernel of a ring map into the domain `ℚ[t]`.
6. `radical_Q : Ideal.radical Q = P`.

This part is unchanged from the previous submission; every theorem of that
submission is preserved verbatim, including the conditional statements
`MohP3.FormalLocal.radical_Qk_eq_ker_of_generation` and
`MohP3.FormalLocal.radical_Qk_eq_ker_of_ker_le`.

## 4. Result 2 — the global theorem over an arbitrary characteristic-zero field

`MohP3/GlobalK.lean`, namespace `MohP3`, for `k` any field with `CharZero k`:

```lean
abbrev Rk := MvPolynomial (Fin 3) k
def Ppoly : Ideal (Rk k) := Gen.P (xk k) (yk k) (zk k)   -- (f1,f2,f3,f4)
def Qpoly : Ideal (Rk k) := Gen.Q (xk k) (yk k) (zk k)   -- (H1,H2)
def rho_k : Rk k →+* Polynomial k                        -- x ↦ t^6+t^31, y ↦ t^8, z ↦ t^10

theorem global_kernel_k : RingHom.ker (rho_k k) = Ppoly k
theorem Ppoly_isPrime   : (Ppoly k).IsPrime
theorem global_radical_k : Ideal.radical (Qpoly k) = Ppoly k
```

The proof is the `ℚ`-argument carried out over `k`; no flatness or
scalar-extension argument is cited.  Concretely:

* the sixteen closure identities are proved once and for all over an arbitrary
  commutative ring in `MohP3/GenClosure.lean` (`Gen.key_xA`, `Gen.key_zA`);
  they have integer coefficients, and the only division performed afterwards is
  by `18`, a unit of `k` because `char k = 0`;
* `MohP3.RepP_all` : every `g ∈ k[x,y,z]` is *exactly* `∑ᵢ ι(pᵢ)·hh i + ∑ⱼ cⱼ·fⱼ`
  with `pᵢ ∈ k[y]`, by induction over `MvPolynomial.induction_on` using the
  closure identities;
* `MohP3.K.indepK` (`MohP3/IndependenceK.lean`) : the images `vvK k i` have
  pairwise distinct trailing degrees mod `8`, hence are independent over
  `k[t^8]`; the nonvanishing of the leading integer coefficients `1, 3, -2` is
  where characteristic zero is used;
* combining the two gives `ker rho_k ≤ Ppoly`; the reverse inclusion is
  `rho_k (f_j) = 0`, and `radical Qpoly = Ppoly` then follows from
  `Ppoly² ≤ Qpoly ≤ Ppoly` (the generic certificate) and primality.

## 5. Result 3 — the unconditional formal-local theorem

`MohP3/Generation.lean`, namespace `MohP3.FormalLocal`, for `k` any field with
`CharZero k`:

```lean
theorem generation             (k : Type*) [Field k] [CharZero k] : Generation k
theorem ker_psi                (k : Type*) [Field k] [CharZero k] : RingHom.ker (psi k) = Pk k
theorem formalLocal_radical_Qk (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical = RingHom.ker (psi k)
```

with `Generation`, `Pk`, `Qk`, `psi`, `hhS`, `iotaS` exactly as in the previous
submission (`MohP3/FormalLocal.lean`, unchanged):

```lean
def Generation : Prop :=
  ∀ F : Sk k, ∃ p : Fin 8 → PowerSeries k, F - ∑ i, iotaS k (p i) * hhS k i ∈ Pk k
```

There is no `Generation`, no `ker (psi k) ≤ Pk k`, no Noetherianity, no adic
completeness and no closedness hypothesis: the three theorems above take only
`[Field k] [CharZero k]`.

### 5.1 The idea: a weighted filtration compatible with the closure identities

The obstruction described in the previous report was that the closure
identities give the generation statement only modulo every power of the maximal
ideal.  The way around it is to make the reduction *converge*, by finding a
filtration for which each reduction step strictly increases the order.

The **total-degree** filtration does not work: the identity
`18·x·x² = 18y·z + 18(x³ − yz)` has a cancellation in lowest degree, so the
remainder does not gain order.  The correct filtration is the one attached to
the parametrization itself,

```
wt x = 6,  wt y = 8,  wt z = 10   (the t-degrees of the parametrization),
```

`WOrd F n` meaning that every monomial of `F` has weight `≥ n`
(`MohP3/Order.lean`).  With

```
sig = (0, 6, 10, 12, 16, 18, 20, 22)   -- weighted orders of hh 0 … hh 7
tau = (24, 26, 28, 30)                 -- weighted orders of f1 … f4
```

every entry of the two closure matrices and every cofactor satisfies the
required estimate:

```
Gen.qxD_wt :  6 + sig i ≤ 8·e_ij + sig j          (x-closure matrix entry c·y^e)
Gen.qzD_wt : 10 + sig i ≤ 8·e_ij + sig j          (z-closure matrix)
Gen.wxD_wt :  6 + sig i ≤ wt(term) + tau j        (cofactors of f j)
Gen.wzD_wt : 10 + sig i ≤ wt(term) + tau j
```

These are finite arithmetic statements about the integer arrays and are proved
in Lean by case analysis (`MohP3/GenClosure.lean`).

### 5.2 The division algorithm

`MohP3/Generation.lean` defines

```lean
def Rep (F : Sk k) (N : ℕ) : Prop :=
  ∃ (q : Fin 8 → PowerSeries k) (c : Fin 4 → Sk k),
    F = (∑ i, iotaS k (q i) * hhS k i) + ∑ j, c j * ffS k j ∧
      (∀ i, YOrd (q i) (N - Gen.sig i)) ∧ (∀ j, WOrd (c j) (N - Gen.tau j))
```

— an *exact* representation together with the weighted-order bounds — and
proves, in order:

1. `Rep_one`, `Rep_add`, `Rep_smul`, `Rep_sum` (closure properties);
2. `Rep_mul_xs`, `Rep_mul_ys`, `Rep_mul_zs` : multiplying a representation by
   `x`, `y`, `z` raises the level by `6`, `8`, `10`.  This is where the closure
   identities (in divided form `key_x_div`, `key_z_div`, using `18⁻¹ ∈ k`) and
   the weight estimates of §5.1 are used;
3. `Rep_monomial (a b c) : Rep k (x^a y^b z^c) (6a+8b+10c)`, by induction;
4. `Rep_step` : for `F` with `WOrd F n`, splitting off the (finite) weight-`n`
   homogeneous part of `F` gives a remainder `G` with `WOrd G (n+1)` and a
   representation of `F - G` at level `n`;
5. `iter` : the resulting sequence of remainders and of coefficient tuples,
   with `iter_wOrd : WOrd (iter k F s).1 s` and
   `iter_telescope`, the exact partial-sum identity for every `M`;
6. `generation` : the twelve coefficient series are then defined
   **coefficientwise** as the limits of their partial sums
   (`exists_yOrd_limit`, `exists_wOrd_limit` in `MohP3/Order.lean`; the
   defining formula for each coefficient is a *finite* sum, because the orders
   of the summands tend to infinity), and the difference between `F` and the
   limiting combination is shown to have weighted order `≥ n` for every `n`,
   hence to be `0` (`wOrd_eq_zero`).

So the four multipliers of `f1,…,f4` are constructed explicitly and the final
statement is an exact identity of power series — ideal membership is never
inferred from membership modulo all powers of the maximal ideal, and no general
theorem on adically closed ideals is used.  Nothing about Noetherianity,
completeness or Weierstrass division is needed, so the gap described in the
previous report is closed rather than circumvented.

### 5.3 From `generation` to the theorem

`ker_psi` follows from `generation` together with the (already proved)
power-series independence `indepS`, and `formalLocal_radical_Qk` then follows
from `Pk² ≤ Qk ≤ Pk` and the primality of `ker psi`, exactly as in the
conditional statements of the previous submission.

## 6. Result 4 — height two and arithmetic rank two

The theorem `radical Q = P` says that the two explicit polynomials `H1, H2` cut
out the Moh curve set-theoretically, i.e. that `ara(P) ≤ 2`.  For the literal
statement *`P` is a set-theoretic complete intersection*, i.e. `ara(P) = 2`,
one also needs the lower bound, and that is what this part adds.

**The definition** (`MohP3/Ara.lean`).  For an ideal `I` of a commutative ring,

```lean
noncomputable def arithRank (I : Ideal A) : ℕ∞ :=
  ⨅ s ∈ {s : Finset A | (Ideal.span (s : Set A)).radical = I.radical}, (s.card : ℕ∞)
```

the least number of elements whose span has the same radical as `I`.  Two
general lemmas are proved: `mem_minimalPrimes_of_radical_eq` (a prime equal to
`I.radical` is a minimal prime of `I`) and `height_le_arithRank`
(`p.height ≤ arithRank p` for a prime `p` of a Noetherian ring, by Krull's
height theorem).

**Upper bound.**  Since `Q.radical = P` and `P` is prime, `P` is a minimal
prime of `Q = (H1, H2)`; Krull's height theorem
(`Ideal.height_le_card_of_mem_minimalPrimes_span_finset`) gives
`P.height ≤ 2`, and `arithRank P ≤ 2` follows from the same two-element set.

**Lower bound.**  The Moh curve lies on the surface `y^5 = z^4`, which is
parametrized by `x ↦ s`, `y ↦ w^4`, `z ↦ w^5`; the Moh parametrization factors
through it via `s ↦ t^6 + t^31`, `w ↦ t^2` (`rho_eq_tau_comp_sigma`).  Hence
the prime `Psurf = ker (sigma)` — prime because the target `ℚ[s,w]` is a domain
— satisfies `Psurf ≤ ker rho = P`.  It is nonzero (`y^5 - z^4 ∈ Psurf`) and
different from `P` (`f4 ∉ Psurf`: its image at `(s,w) = (1,1)` is `-1`).  The
chain of primes `⊥ < Psurf < P` gives `2 ≤ P.height`, so

```lean
theorem MohP3.height_P     : P.height = 2
theorem MohP3.arithRank_P  : arithRank P = 2
```

the second one because `2 = P.height ≤ arithRank P ≤ 2`.  The identical
argument over an arbitrary characteristic-zero field is `MohP3/HeightK.lean`:
`MohP3.height_Ppoly` and `MohP3.arithRank_Ppoly`.

**After completion.**  The same two statements are proved in `k[[x,y,z]]`
(`MohP3/HeightLocal.lean`):

```lean
theorem MohP3.FormalLocal.height_Pk    : (Pk k).height = 2
theorem MohP3.FormalLocal.arithRank_Pk : arithRank (Pk k) = 2
```

The upper bound is again Krull's height theorem, applied to `Pk`, which is a
minimal prime of `Qk = (H1,H2)` by the formal-local theorem of §5.  This needs
`k[[x,y,z]]` to be Noetherian.  Mathlib knows `IsNoetherianRing R⟦X⟧` for
Noetherian `R`, but has no statement relating `MvPowerSeries (Option σ) R` to
`PowerSeries (MvPowerSeries σ R)`; `MohP3/MvPowerSeriesAux.lean` supplies the
missing infrastructure:

* `MvPowerSeries.reindexEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃+* MvPowerSeries τ R`;
* `MvPowerSeries.optionEquiv : MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R)`,
  the coefficientwise splitting, whose multiplicativity is the bijection
  between the antidiagonal of `Finsupp.optionElim n d` and the product of the
  antidiagonals of `n` and `d`;
* hence, by induction on `n` along `Fin (n+1) ≃ Option (Fin n)`,
  `IsNoetherianRing (MvPowerSeries (Fin n) R)`.

The lower bound is the power-series version of the surface argument: the
substitution `x ↦ s`, `y ↦ w^4`, `z ↦ w^5` into `k[[s,w]]` has prime kernel
`Psurfk` (the target has no zero divisors), and the Moh substitution factors
through it via `s ↦ t^6 + t^31`, `w ↦ t^2` (composition of substitutions), so
`Psurfk ≤ ker psi = Pk`; the chain `⊥ < Psurfk < Pk` is strict because
`y^5 - z^4 ≠ 0` lies in `Psurfk` while `f4` does not (its image under the
further substitution `s, w ↦ t` is `t^11 - 2t^13 - t^40 + t^15 ≠ 0`).

## 7. Soundness checks

* No `sorry`, no `admit`, no `axiom` declaration, no `constant`, no
  `@[implemented_by]`, no `native_decide` anywhere in the Lean sources:
  `rg -n "sorry|admit|axiom |native_decide" MohP3.lean MohP3/*.lean` returns
  nothing.
* The build produces no errors and no warnings.
* Axiom audit.  The five `#print axioms` commands requested are executed by the
  build itself (they are the last lines of `MohP3.lean`); their output appears
  verbatim in the build log of §7:

```
'MohP3.FormalLocal.generation'             : [propext, Classical.choice, Quot.sound]
'MohP3.FormalLocal.ker_psi'                : [propext, Classical.choice, Quot.sound]
'MohP3.FormalLocal.formalLocal_radical_Qk' : [propext, Classical.choice, Quot.sound]
'MohP3.global_kernel_k'                    : [propext, Classical.choice, Quot.sound]
'MohP3.global_radical_k'                   : [propext, Classical.choice, Quot.sound]
'MohP3.height_P'                           : [propext, Classical.choice, Quot.sound]
'MohP3.arithRank_P'                        : [propext, Classical.choice, Quot.sound]
'MohP3.FormalLocal.height_Pk'              : [propext, Classical.choice, Quot.sound]
'MohP3.FormalLocal.arithRank_Pk'           : [propext, Classical.choice, Quot.sound]
'MohP3.height_Ppoly'                       : [propext, Classical.choice, Quot.sound]
'MohP3.arithRank_Ppoly'                    : [propext, Classical.choice, Quot.sound]
```

  The results of the earlier submission are unchanged and still depend only on
  the same three axioms.

## 8. Complete build output

Command (from the project root, after `lake exe cache get` for Mathlib):

```
$ lake build MohP3
```

Output of a full rebuild of the library (Mathlib itself already built):

```
✔ [8027/8045] Built MohP3.IndependenceK (59s)
✔ [8028/8045] Built MohP3.Order (61s)
✔ [8029/8045] Built MohP3.MvPowerSeriesAux (63s)
✔ [8030/8045] Built MohP3.Independence (64s)
✔ [8031/8045] Built MohP3.Defs (64s)
✔ [8032/8045] Built MohP3.Generic (90s)
✔ [8033/8045] Built MohP3.FormalLocal (58s)
✔ [8034/8045] Built MohP3.Certificate (59s)
✔ [8035/8045] Built MohP3.GenClosure (67s)
✔ [8036/8045] Built MohP3.Closure (44s)
✔ [8037/8045] Built MohP3.GlobalK (54s)
✔ [8038/8045] Built MohP3.Generation (55s)
✔ [8039/8045] Built MohP3.Kernel (46s)
✔ [8040/8045] Built MohP3.HeightK (49s)
✔ [8041/8045] Built MohP3.HeightLocal (49s)
✔ [8042/8045] Built MohP3.Global (32s)
✔ [8043/8045] Built MohP3.Height (21s)
ℹ [8044/8045] Built MohP3 (41s)
info: MohP3.lean:189:0: 'MohP3.FormalLocal.generation' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:190:0: 'MohP3.FormalLocal.ker_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:191:0: 'MohP3.FormalLocal.formalLocal_radical_Qk' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:192:0: 'MohP3.global_kernel_k' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:193:0: 'MohP3.global_radical_k' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:194:0: 'MohP3.height_P' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:195:0: 'MohP3.arithRank_P' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:196:0: 'MohP3.FormalLocal.height_Pk' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:197:0: 'MohP3.FormalLocal.arithRank_Pk' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:198:0: 'MohP3.height_Ppoly' depends on axioms: [propext, Classical.choice, Quot.sound]
info: MohP3.lean:199:0: 'MohP3.arithRank_Ppoly' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8045 jobs).
```

There are no errors and no warnings.

## 9. Status summary

| statement | status |
|---|---|
| global theorem over `ℚ` (`kernel_rho`, `P_isPrime`, `radical_Q`) | proved (unchanged) |
| global theorem over any characteristic-zero field (`global_kernel_k`, `global_radical_k`) | proved |
| `Generation k` | proved unconditionally |
| `RingHom.ker (psi k) = Pk k` | proved unconditionally |
| `(Qk k).radical = RingHom.ker (psi k)` for every `[Field k] [CharZero k]` | proved unconditionally |
| `P.height = 2` and `arithRank P = 2` over `ℚ` | proved |
| `(Ppoly k).height = 2` and `arithRank (Ppoly k) = 2` over any characteristic-zero field | proved |
| `(Pk k).height = 2` and `arithRank (Pk k) = 2` in `k[[x,y,z]]` | proved |
| `IsNoetherianRing (MvPowerSeries (Fin n) R)` for Noetherian `R` | proved (new infrastructure) |

Nothing in the development is left unproved.
