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
```

Selecting axioms runs the relevant semantic witness profile for those fields.
Use this when changing one axiom extractor, one fixture, or one diagnostic path.

`LEANUFO_AXIOMS=ax68,ax72 lake test` is useful for checking the current positive
coverage and the explicit blocked status for direct negative coverage on those
axioms.

## Direct Negative Witness Audit

```bash
LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test
```

This fails if any registered axiom lacks a direct negative witness unless it is
classified as compiler-enforced or blocked in the manifest.

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

Timeout-style proof-search limits and unclassified generated-proof/search
failures do not count as direct negative coverage.

[Docs home](README.md) · [Project README](../README.md)
