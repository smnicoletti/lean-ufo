# Current Status

[Docs home](README.md) · [Project README](../README.md)

Compact implementation snapshot.

| Area | Status |
| --- | --- |
| Core UFO fragments | Active mechanization with semantic witness models |
| Finite DSL | Certified models through `UFOAxioms4` |
| Diagnostics | Confirmed counterexamples where negation probes succeed |
| Tests | Syntax, certification, diagnostics, and coverage manifest checks |
| ax68 negative witness | Blocked: closure evidence exists, negation proof still missing |

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
- The diagnostics widget distinguishes confirmed semantic counterexamples,
  timeout-style proof-search limits, and unclassified generated-proof/search
  failures.
- The test suite covers syntax, certification fixtures, diagnostics rendering,
  and axiom coverage manifest checks.

## Current DSL Caveats

- Generated models use a universal S5 frame; custom accessibility relations are
  not surfaced.
- The DSL has one flat `things` namespace and one flat `::` table; level-aware
  higher-order type syntax is postponed.
- Rich §3.12 quality/product examples still require low-level set,
  tuple-projection, and distance facts.
- Some diagnostic extractors remain conservative for product families,
  higher-arity relations, and foundation/equality cases.
- `ax68` and `ax72` have direct positive coverage, but no managed direct
  negative fixtures with Lean-confirmed counterexamples yet.

## Useful Commands

```bash
lake build
lake test
LEANUFO_FULL_TESTS=1 lake test
LEANUFO_AXIOMS=ax66 lake test
LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test
```

## Documentation Map

- [Overview](overview.md)
- [Theoretical notes](theory.md)
- [Architecture](architecture.md)
- [Formal guarantees](guarantees.md)
- [DSL quickstart](dsl/quickstart.md)
- [DSL syntax](dsl/syntax.md)
- [Diagnostics](dsl/diagnostics.md)
- [Testing](testing.md)
- [Roadmap](roadmap.md)

[Docs home](README.md) · [Project README](../README.md)
