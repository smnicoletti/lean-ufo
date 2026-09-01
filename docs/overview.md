# Project overview

[Docs home](README.md) · [Project README](../README.md)

Lean UFO formalizes fragments of the Unified Foundational Ontology in Lean 4.
Its finite DSL compiles small named models and asks Lean to certify them against
the formalized axioms.

| Layer | Role |
| --- | --- |
| Core formalization | Semantic signatures, axioms, theorems, and witness models |
| Finite DSL | Named finite models compiled into `UFOSignature4` |
| Certificate generation | One theorem per registered axiom plus `UFOAxioms4` |
| Diagnostics | Counterexample/probe distinction with DSL-level evidence |

The repository has two layers:

- **Core mechanization.** The `LeanUfo/UFO/Core` files define semantic
  signatures and axioms section by section. The
  `LeanUfo/UFO/FormalAnalysis/Satisfiability` files build
  concrete models that witness joint satisfiability of those fragments.
- **Certified finite DSL.** The `LeanUfo/UFO/DSL` backend compiles a small
  `ufo_model` command into a finite semantic signature and generates Lean
  certificate theorems for the encoded axiom package.

## What counts as a certified DSL model

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

The resulting theorem is:

```lean
PersonExample.certified : UFOAxioms4 PersonExample.sig
```

Successful certification means Lean has checked generated theorem declarations
against the existing Prop-valued UFO axiom package.

## What failing models provide

If certification fails, the diagnostics layer stops at the first failed axiom.
It then runs a separate negative probe:

- if Lean proves the negation of the generated axiom for the finite model, the
  diagnostic reports a confirmed semantic counterexample;
- if both the certificate check and the negation probe fail, the diagnostic
  reports either a timeout-style counterexample-probe limit or an unclassified
  probe failure.

Where structured extractors exist, the counterexample is rendered using DSL
world and thing names, with evidence and repair suggestions.

## Where to read next

- [Theoretical notes](theory.md)
- [Project architecture](architecture.md)
- [DSL architecture](dsl/architecture.md)
- [DSL quickstart](dsl/quickstart.md)
- [Diagnostics guide](dsl/diagnostics.md)
- [Testing guide](testing.md)
- [Current status](status.md)

[Docs home](README.md) · [Project README](../README.md)
