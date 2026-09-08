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

## Current Lean 4.33 migration verification

The public submission package now pins

```text
Lean:    leanprover/lean4:v4.33.0
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d
```

A complete `lake build` succeeded with 8,729 jobs.  The substantive theorem
statements and assumptions are unchanged.  Compatibility edits use the public
`Ideal.height` API in place of the now-private `primeHeight` API, qualify the
moved antidiagonal and `finSuccEquiv` names, and add one type annotation needed
by Lean 4.33 elaboration.  The build emits only style/deprecation warnings and
the two deliberate `sorry` warnings in `Challenge.lean`; `Solution.lean` and
the substantive `MohP3` library remain fully proved.

The complete Comparator replay also succeeded using `lean4export` revision
`15f6055e299ad5b89345e533cc2192f4cc00f659`, which declares the same Lean
4.33.0 toolchain.  NanoDa accepted the exported solution, Lean's default
kernel accepted it, and Comparator reported `Your solution is okay!`.

## Original independent clean build

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

## Palomar registration

The formalization is registered as
[PALOMAR-2026-09-07-000012 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-07-000012&version=1),
which pins source commit
`e1dd554d07425ae9822389427795bd83485a5b2c`.  Palomar's public mechanical
[verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34147992901)
completed successfully.  The Challenge rendered successfully, and the
automated editorial review identified no blocking problem or nonblocking
warning.  This is machine verification and automated editorial review, not
independent expert mathematical peer review.

## Original Palomar packaging checks

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

At the time of the original packaging audit, the hardened
Comparator/Landrun/NanoDa replay was deferred to GitHub Actions because its Go
and Rust prerequisites were not installed in the local macOS environment.
During the Lean 4.33 migration, those prerequisites were installed in private
temporary directories and the complete local replay succeeded: NanoDa and
Lean's default kernel both accepted the exported solution, and Comparator
reported `Your solution is okay!`.  The repository's GitHub Actions replay and
Palomar's independent mechanical run subsequently succeeded on the registered
commit.
