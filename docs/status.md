# Current Status

[Docs home](README.md) · [Project README](../README.md)

Compact implementation snapshot.

| Area | Status |
| --- | --- |
| Core UFO fragments | Active mechanization with semantic witness models |
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
- The finite DSL accepts named worlds, named things, scoped facts, taxonomy
  classifications, instantiation, specialization, primitive relations, and
  selected derived assertions.
- Predicate and relation facts use call syntax: `Object(Alice)`,
  `Part(Wheel, Car)`, `Distance(RedValue, BlueValue, ColorDistance)`.
- Instantiation and specialization keep UFO notation: `Alice :: Person`,
  `Student ⊑ Person`.
- Successful DSL models generate Lean certificate theorems through
  `UFOAxioms4`.
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
  `axQuaIndividualOfEndurant`. The `ax73` proof uses `sameFoundationB` plus
  the already checker-backed unique-foundation premises needed to relate it to
  the core `FoundationOf` definition; `ax78` and `ax79` use the same bridge
  with explicit prerequisite checker calls.
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
- The checker includes a formal `Stepped` step model and conservative
  polynomial step bounds for the full aggregate checker.
- The diagnostics widget distinguishes confirmed semantic counterexamples,
  timeout-style counterexample-probe limits, and unclassified probe failures.
- The test suite covers syntax, certification fixtures, diagnostics rendering,
  and axiom coverage manifest checks.

## Current DSL Caveats

- Generated models use a universal S5 frame; custom accessibility relations are
  not surfaced.
- The DSL has one flat `things` namespace and one flat `::` table; level-aware
  higher-order type syntax is postponed.
- Rich §3.12 quality/product examples still require low-level set,
  tuple-projection, membership, and distance facts. The membership table is now
  executable and backs `SetExtension`; product-family witnesses are supported,
  while higher-level generation of all required quality-domain facts remains
  future work.
- Some diagnostic extractors remain conservative for product families,
  higher-arity relations, and foundation/equality cases.
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
