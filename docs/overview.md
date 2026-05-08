# Project Overview

[Docs home](README.md) · [Project README](../README.md)

Lean UFO formalizes fragments of the Unified Foundational Ontology in Lean 4 and
adds a finite DSL for writing small named UFO models.

| Layer | Role |
| --- | --- |
| Core formalization | Semantic signatures, axioms, theorems, and witness models |
| Finite DSL | Named finite models compiled into `UFOSignature4` |
| Certificate generation | One theorem per registered axiom plus `UFOAxioms4` |
| Diagnostics | Counterexample/probe distinction with DSL-level evidence |

The repository has two layers:

- **Core mechanization.** The `LeanUfo/UFO/Core` files define semantic
  signatures and axioms section by section. The `LeanUfo/UFO/Models` files build
  concrete models that witness joint satisfiability of those fragments.
- **Certified finite DSL.** The `LeanUfo/UFO/DSL` backend compiles a small
  `ufo_model` command into a finite semantic signature and generates Lean
  certificate theorems for the encoded axiom package.

## What Counts As A Certified DSL Model

A DSL command such as:

```lean
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

elaborates to ordinary Lean declarations:

```lean
PersonExample.ast
PersonExample.tables
PersonExample.data
PersonExample.sig
PersonExample.certified_ax1
-- ...
PersonExample.certified
PersonExample.certifiedModel
```

The important result is:

```lean
PersonExample.certified : UFOAxioms4 PersonExample.sig
```

Successful certification means Lean has checked generated proof terms against
the existing Prop-valued UFO axiom package.

## What Failing Models Provide

If certification fails, the diagnostics layer stops at the first failed axiom.
It then runs a separate negative probe:

- if Lean proves the negation of the generated axiom for the finite model, the
  diagnostic reports a confirmed semantic counterexample;
- if both the certificate proof and the negation probe fail, the diagnostic
  reports either a timeout-style proof-search limit or an unclassified
  generated-proof/search failure.

Where structured extractors exist, the counterexample is rendered using DSL
world and thing names, with evidence and repair suggestions.

## Where To Read Next

- [Theoretical notes](theory.md)
- [Architecture and trust boundary](architecture.md)
- [DSL quickstart](dsl/quickstart.md)
- [Diagnostics guide](dsl/diagnostics.md)
- [Testing guide](testing.md)
- [Current status](status.md)

[Docs home](README.md) · [Project README](../README.md)
