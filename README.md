# Lean UFO

[![Lean](https://img.shields.io/badge/Lean-4.28.0--rc1-blue)](lean-toolchain)
[![License](https://img.shields.io/badge/license-AGPL--3.0-blue)](LICENSE)
[![Docs](https://img.shields.io/badge/docs-project%20guide-informational)](docs/README.md)
[![Lean CI](https://github.com/smnicoletti/lean-ufo/actions/workflows/lean.yml/badge.svg?branch=dev)](https://github.com/smnicoletti/lean-ufo/actions/workflows/lean.yml?query=branch%3Adev)

Lean UFO is a machine-checked formalization of the Unified Foundational
Ontology (UFO) in Lean 4. It also provides a small modeling language for finite
UFO examples: write a named model, ask Lean to certify it, and get structured
feedback when the model violates an axiom.

The project is aimed at researchers and modelers who want UFO axioms to be more
than informal constraints: each successful DSL model produces an ordinary Lean
certificate, and each confirmed failure is traced back to the finite model data.

| If You Want To... | Lean UFO Provides |
| --- | --- |
| Study UFO's axioms precisely | Section-by-section Lean signatures, axioms, and theorem packages |
| Check small ontology scenarios | A compact `ufo_model ... certify` DSL with named worlds and named things |
| Know why a model fails | Diagnostics that identify the first failed axiom and show DSL-level evidence |
| Trust the result | Generated Lean theorems checked against `UFOAxioms4` |
| Keep changes from regressing | A `lake test` suite for syntax, certification, diagnostics, and coverage |

## Start Here

| Goal | Link |
| --- | --- |
| Understand the project | [Project overview](docs/overview.md) |
| Write a model | [DSL quickstart](docs/dsl/quickstart.md) |
| Check the syntax | [DSL syntax reference](docs/dsl/syntax.md) |
| Interpret failures | [Diagnostics guide](docs/dsl/diagnostics.md) |
| Run tests | [Testing guide](docs/testing.md) |
| Inspect current status | [Current status](docs/status.md) |
| Work on DSL internals | [DSL developer guide](docs/dsl/developer-guide.md) |

## Contribution Highlights

Technical highlights:

1. **A Lean mechanization of UFO fragments.** Each section introduces a semantic
   signature, packages the corresponding axioms, and proves concrete
   satisfiability checkpoints by constructing witness models.
2. **S5 Kripke semantics.** Modal operators are interpreted semantically over
   constant-domain S5 frames, making the modal assumptions explicit in Lean.
3. **A certified finite DSL.** A `ufo_model ... certify` command compiles named
   worlds, named things, and UFO facts into a finite `UFOSignature4`.
4. **Generated Lean certificates.** Successful DSL models elaborate to ordinary
   Lean declarations, including one theorem per registered axiom and a final
   `UFOAxioms4` certificate.
5. **DSL-level diagnostics.** Failed models report whether Lean confirmed a
   finite counterexample, hit a timeout-style proof-search limit, or reached an
   unclassified generated-proof/search failure. Many failures are reconstructed
   in source-level DSL terms.
6. **Regression tests.** The `lake test` suite checks syntax, positive
   certification fixtures, negative counterexample fixtures, diagnostics
   rendering, and axiom registry coverage.

## Quick Example

A tiny model can state that `Person` is an object kind and that `Alice` is an
object instantiating that kind in the actual world. The `certify` directive asks
Lean to check that the resulting finite interpretation satisfies the encoded UFO
axioms.

```lean
import LeanUfo.UFO.DSL.Syntax

open LeanUfo.UFO.DSL

ufo_model PersonExample : UFO where
  worlds actual
  things Person Alice
  given actual:
    ObjectKind(Person)
    Object(Alice)
    Alice :: Person
  derive_relations
  certify
```

If this command elaborates successfully, Lean has checked a generated theorem:

```lean
PersonExample.certified : UFOAxioms4 PersonExample.sig
```

The DSL keeps UFO notation for instantiation and specialization:

```lean
Alice :: Person
Employee ⊑ Person
```

Predicate and relation facts use call syntax:

```lean
Object(Alice)
Part(Wheel, Car)
Distance(RedValue, BlueValue, ColorDistance)
TupleProjection(ColorTuple, 0, HueValue)
```

## Diagnostics At A Glance

Opening a `ufo_model ... certify` command in VS Code shows a diagnostics widget
with input facts, expanded finite facts, certificate status, and failure
analysis.

For example, this model makes `EnrollmentClassifier` a rigid sortal object type
but never classifies it as either a kind or a subkind:

```lean
ufo_model FailedEnrollmentClassifier : UFO where
  worlds actual
  things PersonKind EnrollmentClassifier Alice
  given actual:
    ObjectKind(PersonKind)
    ObjectType(EnrollmentClassifier)
    Rigid(EnrollmentClassifier)
    Sortal(EnrollmentClassifier)
    EnrollmentClassifier ⊑ PersonKind
    Object(Alice)
    Alice :: EnrollmentClassifier
    Alice :: PersonKind
  derive_relations
  certify
```

When Lean confirms the semantic counterexample, the widget reports the first
failed axiom and shows the failed obligation in DSL-level terms:

![Diagnostic card showing the ax26 counterexample for EnrollmentClassifier](docs/assets/diagnostic-card.svg)

Current headings include `Required but missing`, `Need one of`,
`Required together`, `Missing witness requirements`, and
`Forbidden condition`.

## Build And Test

Requires Lean 4, Lake, and mathlib.

```bash
lake build
lake test
```

Useful test modes:

```bash
LEANUFO_FULL_TESTS=1 lake test
LEANUFO_AXIOMS=ax13 lake test
LEANUFO_AXIOMS=ax66 lake test
LEANUFO_AXIOMS=ax68 lake test
LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test
```

## Documentation

| Document | Purpose |
| --- | --- |
| [Documentation home](docs/README.md) | Guide map and reading paths |
| [Architecture](docs/architecture.md) | Compiler pipeline and trust boundary |
| [Formal guarantees](docs/guarantees.md) | Theorem-backed DSL pipeline facts |
| [DSL quickstart](docs/dsl/quickstart.md) | First certified model |
| [DSL syntax](docs/dsl/syntax.md) | Accepted surface syntax |
| [Diagnostics](docs/dsl/diagnostics.md) | Failure analysis and counterexamples |
| [DSL developer guide](docs/dsl/developer-guide.md) | Internal DSL module map and generated-certificate workflow |
| [Diagnostics internals](docs/dsl/diagnostics-internals.md) | How failed generated checks become source-level explanations |
| [Testing](docs/testing.md) | `lake test` profiles and coverage |
| [Current status](docs/status.md) | Implemented features and current caveats |
| [Roadmap](docs/roadmap.md) | Known limitations and next steps |

## Repository Map

```text
LeanUfo/
  UFO/
    Core/              -- semantic signatures, axioms, and theorems
    Models/            -- concrete satisfiability witness models
    DSL/               -- finite DSL public entry point, backend, and examples
      Frontend/        -- surface grammar and text rendering
      Compiler/        -- compiler vocabulary and AST support
      Certificate/     -- generated certificate source and tactic support
      Diagnostic/      -- source-level failure analysis and editor widget
  Test/                -- DSL syntax, certification, diagnostics, and coverage tests
docs/                  -- human-facing documentation
LeanUfoTest.lean       -- executable lake test driver
```

## Source Material

This formalization follows:

Guizzardi, Giancarlo, et al. "UFO: Unified Foundational Ontology." Applied
Ontology 17(2): 167-210, 2022. https://doi.org/10.3233/AO-210256

```bibtex
@article{guizzardi2022ufo,
  author  = {Guizzardi, Giancarlo and Benevides, Alessander Botti and
             Fonseca, Claudenir M. and Porello, Daniele and
             Almeida, Jo{\~a}o Paulo A. and Sales, Tiago Prince},
  title   = {UFO: Unified Foundational Ontology},
  journal = {Applied Ontology},
  volume  = {17},
  number  = {2},
  pages   = {167--210},
  year    = {2022},
  doi     = {10.3233/AO-210256}
}
```

## Status

Active research development. The mechanization, finite DSL, diagnostics, and
test suite are evolving together. See [docs/status.md](docs/status.md) for the
current implementation snapshot.
