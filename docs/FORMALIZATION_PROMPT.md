# Aristotle task: formalize the Moh P3 certificate in Lean 4 + Mathlib

Create a compiling Lean 4/Mathlib formalization of the explicit Moh P3
set-theoretic complete-intersection certificate supplied in this packet.

## Required first milestone: the global theorem over `ℚ`

Let

```text
R = MvPolynomial (Fin 3) ℚ
x = X 0, y = X 1, z = X 2,
```

and define `f1`, `f2`, `f3`, `f4`, `H1`, and `H2` exactly as in
`MohP3.lean` and `witnesses.txt`. Define

```text
P = Ideal.span {f1, f2, f3, f4}
Q = Ideal.span {H1, H2}.
```

Define the ring homomorphism

```text
rho : R ->+* Polynomial ℚ
x |-> t^6 + t^31, y |-> t^8, z |-> t^10.
```

Prove, with no axioms and no remaining `sorry`:

1. The two displayed reverse identities in `identities.txt`, hence `Q ≤ P`.
2. All ten displayed identities
   `d_ij * f_i * f_j = A_ij * H1 + B_ij * H2`.
3. Since every listed positive integer `d_ij` is a unit over `ℚ`, deduce
   `P ^ 2 ≤ Q`.
4. Prove `RingHom.ker rho = P`. Do not assume this as an axiom. A valid route
   is a fully formal elimination/Groebner certificate; another exact Lean proof
   is acceptable. The Macaulay2 log is evidence only, not a Lean proof.
5. Deduce that `P` is prime (or at least radical) from the kernel description
   and that `Polynomial ℚ` is a domain.
6. Prove

```text
Ideal.radical Q = P
```

from `P ^ 2 ≤ Q ≤ P` and radicality of `P`.

Keep the proof modular. Polynomial identities should be discharged by exact
normalization (`ring`/`ring_nf` or verified coefficient normalization), not by
reflection through untrusted external output.

## Required theorem boundary

The global `ℚ` theorem is the first deliverable. Do not claim that the full
manuscript has been formalized unless the following later milestones are also
completed:

- scalar extension from `ℚ` to an arbitrary characteristic-zero field;
- the formal power-series map `k[[x,y,z]] -> k[[t]]`;
- identification of its kernel with the extension/completion of the polynomial
  kernel;
- preservation of the two containments under extension;
- the formal-local radical equality and arithmetic-rank conclusion.

If Mathlib lacks convenient multivariable formal-power-series infrastructure,
state precisely which formal-local lemma remains and return the completed
global theorem without inserting an axiom.

## Trust and provenance rules

- Treat `PROOF.md`, `identities.txt`, and `witnesses.txt` as mathematical input.
- Use `certificate.json`, `certificate_data.m2`, and `verify_global_moh.m2` only
  to cross-check transcription.
- Do not execute or translate the Python checker as a substitute for a Lean
  proof.
- Do not use `axiom`, `admit`, `sorryAx`, or hidden classical assumptions to
  bypass kernel equality, primality, or completion.
- A result with any remaining `sorry` is partial and must be labeled partial.
- Report the exact Lean and Mathlib revisions used and include the build command.

Start from `MohP3.lean`. You may split it into modules if that improves compile
time or proof organization.
