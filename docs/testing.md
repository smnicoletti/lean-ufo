# Testing Guide

[Docs home](README.md) · [Project README](../README.md)

The test driver is:

```text
LeanUfoTest.lean
```

The test tree is:

```text
LeanUfo/Test/
  Syntax/
  Certification/
    Positive/
    Negative/
  Diagnostics/
  Coverage/
```

## Default Tests

```bash
lake test
```

The default profile checks syntax smoke fixtures, diagnostic rendering checks,
and registry/manifest consistency.

## CI

GitHub Actions runs the default `lake test` profile on pull requests and pushes
to `dev` or `main`.

The full semantic witness profile runs when the workflow is started manually.
The nightly scheduled workflow checks `dev` and runs the full profile only when
`dev` has received a commit in the previous 24 hours.

## Full Semantic Witness Tests

```bash
LEANUFO_FULL_TESTS=1 lake test
```

This runs the slower positive and negative certification fixtures.

## Selected Axiom Tests

```bash
LEANUFO_AXIOMS=ax13 lake test
LEANUFO_AXIOMS=ax10,ax18,ax61 lake test
LEANUFO_AXIOMS=ax66 lake test
LEANUFO_AXIOMS=ax1,ax2,ax3,ax4,ax5,ax6,ax7,ax8,ax9,ax10,ax11,ax12,ax13,ax14,ax15,ax16,ax17,ax61,ax71,ax77 lake test
LEANUFO_AXIOMS=ax18,ax19,ax20,ax21,ax22,ax23,ax24,ax25,ax26,ax27,ax28,ax29,ax30,ax31,ax32,ax33,ax_instEndurant,ax_sub_kind_sortal,ax_nonSortal_up,ax_kindStable lake test
LEANUFO_AXIOMS=ax34,ax35,ax36,ax37,ax38,ax39,ax40,ax41,ax42,ax43 lake test
LEANUFO_AXIOMS=ax44,ax45,ax46 lake test
LEANUFO_AXIOMS=ax47,ax48,ax49,ax50,ax51,ax52 lake test
LEANUFO_AXIOMS=ax53,ax54,ax55 lake test
LEANUFO_AXIOMS=ax56,ax57,ax58,ax59,ax60,ax61 lake test
LEANUFO_AXIOMS=ax62,ax63,ax64 lake test
LEANUFO_AXIOMS=ax65,ax66,ax67,ax68 lake test
LEANUFO_AXIOMS=ax69,ax70,ax71,ax72,ax73,ax74,ax75,ax76,ax77,ax78,ax79,ax80,axQuaIndividualOfEndurant lake test
LEANUFO_AXIOMS=ax81,ax82 lake test
LEANUFO_AXIOMS=ax83,ax84,ax85,ax86,ax87,ax88,ax89,ax91,ax92,ax93,ax94,ax100,ax101,axDistanceIdentity,axDistanceSymmetry,axDistanceTriangle lake test
LEANUFO_AXIOMS=ax102,ax103,ax104,ax105,ax106,ax107,ax108 lake test
```

Selecting axioms runs the relevant semantic witness profile for those fields.
Use this when changing one axiom extractor, one fixture, or one diagnostic path.
The long selections above exercise grouped regions of the reflective checker.

`ax68` is included in the §3.9 checker-backed selection. It uses the bounded
finite closure checker for `MomentOf` and `UltimateBearerOf`.

The `ax68` positive test is especially important after checker changes because
it exercises the Warshall-style finite closure bridge from executable
reachability to the core inductive `MomentOf` relation. The direct negative
fixture uses the same checker-aware counterexample pattern as the other
direct-complete checker fields: prove `¬ axN` from `checkAxN_complete` and a
computed `checkAxN = false`.

## Direct Negative Witness Audit

```bash
LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test
```

This is a strict backfill audit: it fails if any registered axiom lacks a direct
negative witness, including axioms that are currently classified as
compiler-enforced or blocked in the manifest. The ordinary `lake test` profile
checks that every registered axiom is classified exactly once.

## Coverage Manifest

The manifest lives in:

```text
LeanUfo/Test/Coverage/AxiomManifest.lean
```

Each registered axiom is classified for negative coverage as one of:

- `directNegativeWitnessAxioms`: a small fixture exists and Lean confirms the
  first semantic failure is this axiom;
- `compilerEnforcedNegativeAxioms`: direct falsification is not expected because
  compiler semantics enforces the condition;
- `blockedNegativeWitnessAxioms`: the axiom needs missing surface syntax,
  extractor support, or a better negation-proof path.

## Negative Fixture Rule

A negative fixture only counts as direct coverage if:

- the first stopped certificate field is the intended axiom;
- Lean confirms a finite semantic counterexample;
- the fixture is small and section-local where feasible.

Timeout-style counterexample-probe limits and unclassified probe failures do
not count as direct negative coverage.

[Docs home](README.md) · [Project README](../README.md)
