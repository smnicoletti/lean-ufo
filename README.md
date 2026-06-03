# Lean UFO

[![Lean](https://img.shields.io/badge/Lean-4.30.0-blue)](lean-toolchain)
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
| Study theoretical findings | [Theoretical notes](docs/theory.md) |
| Write a model | [DSL quickstart](docs/dsl/quickstart.md) |
| Check the syntax | [DSL syntax reference](docs/dsl/syntax.md) |
| Interpret failures | [Diagnostics guide](docs/dsl/diagnostics.md) |
| Run tests | [Testing guide](docs/testing.md) |
| Inspect current status | [Current status](docs/status.md) |
| Check theorem-backed guarantees | [Formal guarantees](docs/guarantees.md) |
| Understand the implementation | [Project architecture](docs/architecture.md) |
| Work on DSL internals | [DSL architecture](docs/dsl/architecture.md) and [DSL developer guide](docs/dsl/developer-guide.md) |

## Contribution Highlights

Technical highlights:

1. **A Lean mechanization of UFO fragments.** Each section introduces a semantic
   signature, packages the corresponding axioms, and proves concrete
   satisfiability checkpoints by constructing witness models.
2. **S5 Kripke semantics.** Modal operators are interpreted semantically over
   constant-domain S5 frames, making the modal assumptions explicit in Lean.
3. **A certified finite DSL.** A `ufo_model ... certify` command compiles named
   worlds, named things, and UFO facts into a finite `UFOSignature4`.
4. **Reflective checker-backed Lean certificates.** Successful DSL models
   elaborate to ordinary Lean declarations, including one theorem per registered
   axiom, stored Boolean check theorems (`checked_axN`), reusable model source
   data, a certificate manifest, and a final `UFOAxioms4` certificate. The
   reflective checker now covers all registered axiom fields through §4. In
   particular, `ax68` uses a proved bounded finite closure checker for
   `MomentOf`, and `ax99` uses explicit finite product-family witnesses.
5. **DSL-level diagnostics.** Failed models report whether Lean confirmed a
   finite counterexample, hit a timeout-style counterexample-probe limit, or
   reached an unclassified probe failure. Many failures are reconstructed in
   source-level DSL terms.
6. **Regression tests.** The `lake test` suite checks syntax, positive
   certification fixtures, negative counterexample fixtures, diagnostics
   rendering, and axiom registry coverage. CI also builds the concrete DSL
   example collection.

## Quick Example

A model can state that `PhysicalObject` is an object kind and that `Car` is an
object instantiating that kind in the actual world. The `certify` directive asks
Lean to check that the resulting finite interpretation satisfies the encoded UFO
axioms.

```lean
import LeanUfo.UFO.DSL.Syntax

open LeanUfo.UFO.DSL

ufo_model CarBase : UFO where
  worlds actual
  things PhysicalObject Car
  given actual:
    ObjectKind(PhysicalObject)
    Object(Car)
    Car :: PhysicalObject
  derive_relations
  certify

export_certificate CarBase
```

If this command elaborates successfully, Lean has checked a generated theorem:

```lean
CarBase.certified : UFOAxioms4 CarBase.sig
```

It also leaves reusable certificate artifacts in the environment:

```lean
CarBase.source              : ModelSource
CarBase.checked_ax1         : Checker.checkAx1 CarBase.data = true
CarBase.certificateManifest : CertificateManifest
```

Models can extend earlier models without adding worlds. Here the child keeps the
same car scenario and adds a window and a body as proper parts of the car.
`Body` is not decorative: the UFO mereology axioms include strong
supplementation, so a car with `Window` as a proper part also needs another part
that does not overlap the window.

```lean
ufo_model CarWithWindow : UFO extends CarBase : UFO where
  things Window Body
  given actual:
    Window :: PhysicalObject
    Body :: PhysicalObject
    Object(Window)
    Object(Body)
    Part(Window, Car)
    Part(Body, Car)
    Overlap(Window, Car)
    Overlap(Car, Window)
    Overlap(Body, Car)
    Overlap(Car, Body)

    ProperPart(Window, Car)
    ProperPart(Body, Car)
  derive_relations
  certify

export_certificate CarWithWindow
```

Ordinary `certify` may reuse any parent per-axiom checks whose registered
finite-table footprint is unchanged; fields affected by the new objects or
mereology facts are checked freshly.

Use `certify_fresh` when you want to bypass reuse and regenerate all checker
proofs for the child:

```lean
ufo_model CarWithWindowFresh : UFO extends CarBase : UFO where
  things Window Body
  given actual:
    Window :: PhysicalObject
    Body :: PhysicalObject
    Object(Window)
    Object(Body)
    Part(Window, Car)
    Part(Body, Car)
    Overlap(Window, Car)
    Overlap(Car, Window)
    Overlap(Body, Car)
    Overlap(Car, Body)

    ProperPart(Window, Car)
    ProperPart(Body, Car)
  derive_relations
  certify_fresh
```

Reuse is not a trusted cache hit. The generated child theorem first proves that
the child checker result equals the parent checker result, and only then uses
the parent's `checked_axN` theorem. If that equality proof fails, the generator
falls back to a fresh check.

The parent can also live in another module:

```lean
import MyModels.CarBase

open LeanUfo.UFO.DSL

ufo_model CarWithWindow : UFO extends CarBase : UFO where
  -- add the child things and facts here
  derive_relations
  certify
```

Certificate manifests can be exported and later validated:

```bash
lake build LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension
lake exe export-certificates --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension --out certificates/
lake exe validate-certificate certificates/CarBase.certificate.json --structure-only
lake exe validate-certificate certificates/CarWithWindow.certificate.json --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension
```

`--structure-only` checks just the JSON manifest shape. The default validation
path requires `--module`: it rebuilds the Lean module, checks the named theorem
declarations at their expected types, and compares regenerated SHA-256 digests
for the source and finite model representations. The manifest is provenance
metadata; the Lean theorems remain the proof artifact.

The concrete example collection also includes reuse examples for role extension
and mode/inherence extension:

```text
LeanUfo/UFO/DSL/ConcreteExamples/ReuseRoleExtension.lean
LeanUfo/UFO/DSL/ConcreteExamples/ReuseModeExtension.lean
```

The DSL keeps UFO notation for instantiation and specialization:

```lean
Car :: PhysicalObject
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
LEANUFO_AXIOMS=ax1,ax2,ax3,ax4,ax5,ax6,ax7,ax8,ax9,ax10,ax11,ax12,ax13,ax14,ax15,ax16,ax17,ax61,ax71,ax77 lake test
LEANUFO_AXIOMS=ax65,ax66,ax67,ax68 lake test
LEANUFO_AXIOMS=ax69,ax70,ax71,ax72,ax73,ax74,ax75,ax76,ax77,ax78,ax79,ax80,axQuaIndividualOfEndurant lake test
```

The stricter direct-negative audit is intentionally not part of the green fast
profile yet:

```bash
LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test
```

It fails until every registered axiom has a direct negative witness, including
axioms currently classified as compiler-enforced or blocked.

## Documentation

| Document | Purpose |
| --- | --- |
| [Documentation home](docs/README.md) | Guide map and reading paths |
| [Theoretical notes](docs/theory.md) | Modal choices, formal milestones, S5 consequences, and explicit bridge axioms |
| [Project architecture](docs/architecture.md) | Core formalization, DSL layer, certificates, tests, and trust boundary |
| [Formal guarantees](docs/guarantees.md) | Theorem-backed guarantees for core, DSL, checker, reuse, diagnostics, and complexity |
| [DSL quickstart](docs/dsl/quickstart.md) | First certified model |
| [DSL syntax](docs/dsl/syntax.md) | Accepted surface syntax |
| [DSL architecture](docs/dsl/architecture.md) | Syntax-to-certificate pipeline, checker, diagnostics, and complexity |
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
      Checker/         -- reflective Boolean checks and formal step bounds
      Certificate/     -- generated certificate source and probe support
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
