# Current Status

[Docs home](README.md) · [Project README](../README.md)

Compact implementation snapshot.

For the theorem-backed contract behind these features, see
[Formal guarantees](guarantees.md).

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
- Successful DSL models now also emit `Model.source`, per-field
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
  available. Missing product-family data is now reported as an incomplete finite
  witness table rather than as a confirmed semantic counterexample.
- The checker-backed §3.13 and §4 fields cover `ax102`-`ax108`. The §4 fields
  are derived directly in `FiniteModel4.toUFOSignature4`, so their checker
  proofs establish that the generated semantic definitions satisfy the packaged
  axioms without per-model tactic search.
- The production checker is the erasure of a counted 116-entry registry. Each
  entry carries its own proved operational formula, and the aggregate theorem
  sums those heterogeneous bounds plus actual short-circuit traversal charges.
  The counted source compiler also has a derived `80·inputSize⁴` scalar corollary. The
  checker has a `2940·modelSize⁸` corollary, and the composed bound is
  `3020·(sourceSize+modelSize)⁸`; the [complexity guide](dsl/complexity.md)
  defines these metrics and records the theorem inventory.
  A reproducible `lake exe complexity-benchmarks` target now emits CSV for
  sparse, dense, cyclic, product-family, and projection-heavy generated inputs.
  Native finite relation lookup uses typed dense arrays. Kernel reduction uses
  compact sparse definitions for generated certificates. The cost theorem
  covers the dense native path. `ExplicitTableCorrespondence` proves that the
  sparse and dense unary, binary, ternary, and projection lookups return equal
  values for a well-bounded finite AST. It does not claim equal step counts.
  Finite quantifiers are erasures of counted short-circuit scans.
- The diagnostics widget distinguishes confirmed semantic counterexamples,
  timeout-style counterexample-probe limits, and unclassified probe failures.
- The test suite covers syntax, certification fixtures, diagnostics rendering,
  and axiom coverage manifest checks.

## Current DSL Caveats

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
- Rich §3.12 quality/product examples still require low-level set,
  tuple-projection, membership, and distance facts. The membership table is now
  executable and backs `SetExtension`; product-family witnesses are supported,
  while higher-level generation of all required quality-domain facts remains
  future work.
- Some diagnostic extractors remain conservative for product families and
  higher-arity relations. The `ax73` extractor now reports both directions of
  the part characterization and separates constituent, bearer, foundation,
  missing-part, and missing-`QuaIndividualOf` failures.
- Several §3.10 fields still lack small managed direct negative fixtures:
  `ax72`, `ax75`, `ax76`, `ax78`, `ax79`, and
  `axQuaIndividualOfEndurant`. The checker-aware negative probe infrastructure
  covers checker-backed fields through §3.10, including the prerequisite-aware
  foundation checks for `ax73`, `ax78`, and `ax79`; the remaining gap is small
  direct fixtures, not probe support.

## Useful Commands

```bash
lake build
lake test
LEANUFO_FULL_TESTS=1 lake test
LEANUFO_AXIOMS=ax66 lake test
```

The stricter `LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test` audit is currently
expected to fail until every registered axiom has a direct negative fixture.

## Documentation Map

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
