# Current status

[Docs home](README.md) · [Project README](../README.md)

## Overview

The DSL certifies finite models through UFO §4, with 116 registered checks.
It also reports failures and supports certificate reuse for model extensions.
All user-facing examples, including Relator, pass the final test profile.

This inventory draws its evidence from Lean theorems and regression tests.
[Theoretical notes](theory.md) explain the ontology choices, and
[Formal guarantees](guarantees.md) separates proved results from trusted code.
The limits below include the explicit witness data required for axiom 99 and
the work excluded from the complexity bound.

This page records implemented coverage and known limits. The theorem-level
contract is in [Formal guarantees](guarantees.md).

The 2026-09-13 local verification covers the compiler, checker, diagnostics,
and certificate-tool repairs described here. Source checkouts use the development
artifact version `0.0.0-dev`; the release workflow sets that metadata to the
release tag. Release notes record the corresponding GitHub Actions results.

| Area | Status |
| --- | --- |
| Core UFO fragments | Active mechanization with semantic witness models |
| Relator repair | Part-based (a73) active in the core package and witnessed by a nonempty-relator model |
| Finite DSL | Certified models through `UFOAxioms4` |
| Reflective checker | All registered axiom fields through §4; ax99 uses explicit product-family witnesses |
| Diagnostics | Checker-aware counterexamples for direct-complete checker fields |
| Tests | Syntax, certification, diagnostics, and coverage manifest checks |
| ax68 negative witness | Direct managed closure counterexample covered |

## Implemented

- Core UFO fragments are mechanized as Lean semantic signatures, axiom packages,
  and theorems.
- Concrete witness models establish satisfiability checkpoints for implemented
  fragments.
- The axiomatic analysis proves that the printed (a73), independently of (a79),
  conflicts with a qua-individual proper part of a relator. It records the
  distinctness-guard and guarded-overlap experiments and their limitations,
  selects the part-based (a73), proves preservation of (t31)-(t33), and
  constructs a finite nonempty-relator witness model.
- The active `UFOAxioms3_10` package uses the part-based (a73). The printed
  overlap formula remains available as `ax_a73_printed`, and its forced-empty
  consequence is packaged separately as `UFOAxioms3_10PrintedA73`.
- Anti-vacuity analysis is separate from ordinary joint satisfiability. The
  `FormalAnalysis/AntiVacuity` modules provide one file per section through §4.
  For each section, a cumulative axiom model simultaneously inhabits every
  predicate introduced in that section; named derived predicates are covered
  as well. `AntiVacuity.lean` imports these checked interpretations without
  changing the sparse `FormalAnalysis/Satisfiability/ModelX` checkpoints.
- The finite DSL accepts named worlds, named things, scoped facts, taxonomy
  classifications, instantiation, specialization, primitive relations, and
  selected derived assertions.
- Predicate and relation facts use call syntax: `Object(Alice)`,
  `Part(Wheel, Car)`, `Distance(RedValue, BlueValue, ColorDistance)`.
- Instantiation and specialization keep UFO notation: `Alice :: Person`,
  `Student ⊑ Person`.
- Successful DSL models generate Lean certificate theorems through
  `UFOAxioms4`.
- Successful DSL models also emit `Model.source`, per-field
  `Model.checked_axN` Boolean check theorems, and
  `Model.certificateManifest` provenance metadata. Ordinary `certify` reuses
  parent checks for exact-source extension aliases and for registered
  footprint-backed fields in `Certificate/Reuse.lean`; `certify_fresh` forces
  fresh check generation. Reuse remains Lean-checked: the child theorem proves
  equality with the parent checker result before using the parent
  `checked_axN` theorem, otherwise generation falls back fresh.
- Certificate manifests can be exported after building the source module with
  `lake build Module.Name`, then
  `lake exe export-certificates --module Module.Name --out ...`.
  `lake exe validate-certificate manifest.json --structure-only` checks only
  JSON structure. The default validation path requires
  `--module Module.Name`; it rebuilds the Lean module, checks the generated
  theorem declarations at their expected certificate types, and compares
  regenerated SHA-256 source/model digests and theorem names.
  `export_certificate ModelName` marks selected models for export.
- Release-time certificate publishing is automated by the
  `Certificate Manifests` workflow. On a published GitHub release, it writes the
  tag into `Version.lean` in the runner workspace, exports marked manifests,
  rechecks them against Lean proof declarations, and uploads the JSON manifests
  to the release.
- The DSL has a conservative `extends` form for models elaborated earlier in
  the same module or imported from another module. Extensions may add things,
  facts, and product-family witnesses, but not worlds.
- The reflective checker certifies all registered axiom fields through §4. For
  `ax68`, the checker uses a bounded finite closure proved equivalent to the
  inductive `MomentOf` relation used by `UltimateBearerOf`.
- The checker includes the §3.2 bridge axioms `ax_instEndurant`,
  `ax_sub_kind_sortal`, `ax_nonSortal_up`, and `ax_kindStable`, through reusable
  Boolean checker soundness theorems instead of per-model tactic proof search.
  The §3.3 `Quality` definition is checked through an executable finite
  uniqueness predicate, and the §3.4 type schema is checked through reusable
  necessary-instance helpers.
- The checker-backed §3.10 fields include `ax69`, `ax70`, `ax71`,
  `ax72`, `ax73`, `ax74`, `ax75`, `ax76`, `ax77`, `ax78`, `ax79`, `ax80`, and
  `axQuaIndividualOfEndurant`. The part-based `ax73` proof uses
  `sameFoundationB` plus checker-backed `ax47`, `ax72`, and `ax75` to relate
  the finite common-foundation test to the core `FoundationOf` definition;
  overlap axiom `ax50` is no longer a prerequisite. `ax78` and `ax79` use the
  same foundation bridge with their explicit prerequisite checker calls.
- The checker-backed §3.11 fields cover `ax81` and `ax82` through executable
  finite existence/uniqueness checks over `Inst` and `InheresIn`.
- The checker-backed §3.12 fields cover `ax83`, `ax84`, `ax85`,
  `ax86`, `ax87`, `ax88`, `ax89`, `ax90`, `ax91`, `ax92`, `ax93`, `ax94`,
  `ax95`, `ax96`, `ax97`, `ax98`, `ax99`, `ax100`, `ax101`,
  `axDistanceIdentity`, `axDistanceSymmetry`, and `axDistanceTriangle`.
  Membership-dependent axioms use the executable `FiniteModel4.memberOf` table;
  semantic `SetExtension` is derived from that table. `ax99` is soundly checked
  from explicit finite `product_family` witnesses. The checker is complete for
  the finite stored-witness proposition `ax99Finite`, while direct negative
  coverage for the core `ax_a99` remains blocked unless the explicit
  representation-completeness condition `ProductFamilyWitnessTableComplete` is
  available. Missing product-family data is reported as an incomplete finite
  witness table rather than as a confirmed semantic counterexample.
- The checker-backed §3.13 and §4 fields cover `ax102`-`ax108`. The §4 fields
  are derived directly in `FiniteModel4.toUFOSignature4`, so their checker
  proofs establish that the generated semantic definitions satisfy the packaged
  axioms without per-model tactic search.
- The counted 116-entry checker registry has per-check bounds and proved
  short-circuit traversal costs. `Complexity/Certification.lean` composes
  successful source compilation, derived assertions, scheduled native checks,
  retries, and selected failure reports. Its scalar bound is
  `(439,182,619R + 109,798,953)N¹⁶ + D`: N is the larger complete child/parent
  source size, R is the number of registered fields, and D is the selected
  diagnostic allowance. Root models use only their own source size. The
  [complexity guide](dsl/complexity.md#source-to-workflow-composition) gives the
  assumptions and component derivations. Lean proof processing, code emission,
  and native instructions remain outside the bound.
- Compiled models use typed dense lookups in native execution and compact
  sparse definitions in kernel proofs. `ExplicitTableCorrespondence` proves
  equal lookup values for well-bounded finite input, not equal step counts.
  Full value/cost equalities connect 112 checks to the concrete table
  evaluators; axioms 105–108 return `⟨true, 0⟩`. The eleven checks identified
  as 1, 53–55, 58–59, 63–64, 69–70, and 74 bind each shared predicate once
  and charge it once per assignment.
- Generated models carry a proved inherence cache. Compilation charges its
  construction, and axiom 68 reads its arrays directly. Source-to-model proofs
  also cover product-family conversion and the resulting model size.
  Diagnostic and checker family searches have proved equal answers, with
  separate costs. `lake exe complexity-benchmarks` exercises sparse, dense,
  cyclic, product-family, and projection-heavy inputs.
- Certificate tools validate complete manifest provenance and discover exports
  from module-owned Lean declarations. The final cross-stage review and single
  all-inclusive profile passed on 2026-09-13, including the user-facing examples
  and Relator. The run took 362.58 seconds with an incremental build.
  [Testing](testing.md) describes the profile, and
  [Formal guarantees](guarantees.md) states the trust assumptions.
- The diagnostic interpreter has a formula-size cost theorem. Its bound
  includes node count, quantifier depth, domain sizes, environment size, and
  atomic-query costs. The exponent grows with quantifier depth, so this does
  not claim a uniform polynomial for unrestricted formula/model input.
  [The derivation](dsl/complexity.md) is separate from the fixed-registry bound.
  Failure minimization and successful-context collection also have explicit
  formula-size cost bounds. The minimized environment and context have proved
  entry-count bounds. Generic reports have a composed formula-size bound for
  evidence, assignment search, registry selection, text, and retained output.
  Their selected report bound is included explicitly in the source-to-workflow
  theorem; it is not folded into a uniform polynomial for arbitrary formulas.
- Paths returned by diagnostic reconstruction from a successfully compiled
  source follow the produced model's inherence edges and end at the requested
  target. Reconstruction succeeds exactly for reachable pairs within the
  existing traversal limit.
- The diagnostics widget distinguishes confirmed semantic counterexamples,
  timeout-style counterexample-probe limits, and unclassified probe failures.
- The test suite covers syntax, certification fixtures, diagnostics rendering,
  and axiom coverage manifest checks.

## Current DSL caveats

- The aggregate anti-vacuity entry point imports checked interpretations for
  every section from §3.1 through §4. Coverage includes all primitive signature
  predicates, proper specialization, the full §3.2 modal taxonomy, the §3.3
  and §3.4 individual/type taxonomies, relation vocabularies through §3.10,
  characterization, quality structures, manifestation/life/meet, and all four
  §4 type-structure relations.
- The selected part-based (a73) is active in `Section3_10.lean`, the reflective
  checker, diagnostics, certificate generation, and reuse metadata. The
  certified `RelatorProbe` example supplies an end-to-end nonempty-relator
  witness and refutes the historical printed formula.
- Generated models use a universal S5 frame; custom accessibility relations are
  not surfaced.
- Extended models cannot add worlds yet. This avoids silently changing the
  expansion of parent `given everywhere:` facts.
- The DSL has one flat `things` namespace and one flat `::` table; level-aware
  higher-order type syntax is postponed.
- Rich §3.12 quality/product examples require low-level set, tuple-projection,
  membership, and distance facts. The membership table is
  executable and backs `SetExtension`; product-family witnesses are supported,
  while higher-level generation of all required quality-domain facts remains
  future work.
- Some diagnostic extractors remain conservative for product families and
  higher-arity relations. The `ax73` extractor reports both directions of
  the part characterization and separates constituent, bearer, foundation,
  missing-part, and missing-`QuaIndividualOf` failures.
- Several §3.10 fields still lack small managed direct negative fixtures:
  `ax72`, `ax75`, `ax76`, `ax78`, `ax79`, and
  `axQuaIndividualOfEndurant`. The checker-aware negative probe infrastructure
  covers checker-backed fields through §3.10, including the prerequisite-aware
  foundation checks for `ax73`, `ax78`, and `ax79`; the remaining gap is small
  direct fixtures, not probe support.

## Useful commands

```bash
lake build
lake test
LEANUFO_FULL_TESTS=1 lake test
LEANUFO_AXIOMS=ax66 lake test
```

The stricter `LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test` audit is currently
expected to fail until every registered axiom has a direct negative fixture.

## Documentation map

- [Overview](overview.md)
- [Theoretical notes](theory.md)
- [Project architecture](architecture.md)
- [DSL architecture](dsl/architecture.md)
- [Formal guarantees](guarantees.md)
- [DSL quickstart](dsl/quickstart.md)
- [DSL syntax](dsl/syntax.md)
- [Diagnostics](dsl/diagnostics.md)
- [Testing](testing.md)
- [Roadmap](roadmap.md)

[Docs home](README.md) · [Project README](../README.md)
