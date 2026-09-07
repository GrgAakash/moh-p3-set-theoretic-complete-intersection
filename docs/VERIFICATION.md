# Verification record

## Supplied artifact

The final substantive development was supplied as
`f15c5a19-a3dc-493b-bcbc-398b0a941807-aristotle (1).tar.gz`, with SHA-256

```text
ba8a6c43d07070543968a2ce938536a9116c40de0c0897c72d895252ecd1330e
```

Its nested `MohP3-project.tar.gz` has SHA-256

```text
878259fcd825206a80c216154c5b4d94c301669019bdbb42506e06b677704ad6
```

The archive contained Lean source, the pinned toolchain and Lake manifest,
reports, exact-arithmetic certificate data, and the accompanying manuscript.
It contained no Git metadata, so repository or commit claims in supplied prose
were not independently verifiable from the archive.

## Independent clean build

The archive was extracted into a fresh temporary directory.  With the pinned
Mathlib cache available, the command

```text
lake build MohP3
```

completed successfully with 8,045 jobs under

```text
Lean:    leanprover/lean4:v4.28.0
Mathlib: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
```

The measured build time was

```text
real 1902.54 seconds
user  227.12 seconds
sys   806.80 seconds
```

No errors or warnings were emitted.

## Proof-placeholder and axiom audit

The substantive Lean source was searched for `sorry`, `admit`, custom `axiom`
declarations, `native_decide`, and `implemented_by`; none occurred.  Eleven
user-facing `#print axioms` commands reported only

```text
[propext, Classical.choice, Quot.sound]
```

The Palomar package deliberately adds two `sorry`s in `Challenge.lean`, one for
each statement-only declaration.  They are excluded from the proof-status
counts.  `Solution.lean` contains the corresponding proofs, and Comparator is
configured to reject dependence on `sorryAx` or any nonpermitted axiom.

## Mathematical scope checked

The development proves, globally and in formal power series over every
characteristic-zero field:

- identification of the parametrization kernel with the four-generated ideal;
- containment of the square of that ideal in `(H1,H2)` and the reverse
  containment;
- primality and radical equality;
- height two;
- arithmetic rank two.

The formal-local kernel equality is not obtained by silently extending the
polynomial theorem.  It is proved by an explicit convergent weighted division
algorithm.  The Hilbert–Burch symmetrization motivating `H1,H2` is described in
the manuscript but not formalized as matrix algebra.  The Macaulay2 scripts are
cross-checks only and are not used by Lean.

## Palomar packaging checks

The reorganized repository completed

```text
lake build
```

successfully with 8,049 jobs.  The only warnings were the two deliberate
statement holes in `Challenge.lean`.  Both selected declarations in
`Solution.lean` reported exactly

```text
[propext, Classical.choice, Quot.sound]
```

The template metadata validator reported no retained sentinels; its 83 tests
passed; the Landrun-wrapper policy test passed; and Palomar's current intake
metadata loader accepted the classifications, authorship, source provenance,
automation, and review fields.

The hardened Comparator/Landrun/NanoDa replay requires Linux, Go, and Rust,
which are not available in the local macOS audit environment.  The repository
pins all three verifier components, and the GitHub Actions `comparator` job is
the authoritative replay.  Until that job succeeds, the status should be read
as "Lean build and Palomar preflight passed; hardened Comparator replay
pending."
