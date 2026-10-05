# DSL quickstart

[Docs home](../README.md) · [Project README](../../README.md)

> [!TIP]
> **Fast path.** Import `LeanUfo.UFO.DSL.Syntax`, declare a finite model, and
> end it with `certify`. A successful command creates
> `ModelName.certified : UFOAxioms4 ModelName.sig`.

Import the DSL frontend:

```lean
import LeanUfo.UFO.DSL.Syntax

open LeanUfo.UFO.DSL
```

Write a finite model:

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

Build the file with Lake or open it in VS Code with the Lean extension.

If the command succeeds, Lean generated and checked:

```lean
PersonExample.certified : UFOAxioms4 PersonExample.sig
```

## Multiple worlds

```lean
ufo_model RoleExample : UFO where
  worlds summer autumn
  things Person Student Alice

  given everywhere:
    ObjectKind(Person)
    Role(Student)
    ObjectType(Student)
    Student ⊑ Person
    Object(Alice)
    Alice :: Person

  given summer:
    Alice :: Student

  derive_relations
  certify
```

`given everywhere:` is copied to every declared world by the pure compiler
pipeline. Alice is a Person in both worlds and a Student only in summer.
`ObjectType(Student)` supplies the role's object classification. Specialization
requires every Student to be a Person, including in summer.

## Examples from the UFO axiomatization

The following examples adapt cases from Section 4 of Guizzardi et al. (2022).
Each file requests a certificate for its complete finite model. The models
retain selected mechanisms from the source cases:

| Example | What it models | Scope |
| --- | --- | --- |
| [FlowerPropertyChange](../../LeanUfo/UFO/DSL/ConcreteExamples/FlowerPropertyChange.lean) | A quality inheres in one flower and changes from red to brown across two worlds. | Two values in a finite quality dimension; no full flower or color hierarchy. |
| [RedirectedWalk](../../LeanUfo/UFO/DSL/ConcreteExamples/RedirectedWalk.lean) | A walk mode inheres in Paul and changes phase across two worlds. | No destinations, intentions, arrival relation, or full phase hierarchy. |
| [WoodenTable](../../LeanUfo/UFO/DSL/ConcreteExamples/WoodenTable.lean) | Wood constitutes a component in one world and exists in two others without that component. | One component; no complete table or replacement sequence. |

Worlds represent possible situations. Their names do not introduce a temporal
ordering. The source is [*UFO: Unified Foundational Ontology*](https://doi.org/10.3233/AO-210256),
Sections 4.1, 4.3, and 4.4.

## Failure workflow

Negative examples are expected to fail:

```bash
lake env lean LeanUfo/Test/Certification/Negative/Ax66InherenceFromNonMoment.lean
```

The terminal error and VS Code diagnostics widget report whether the failure is
a confirmed finite counterexample, a timeout-style counterexample-probe limit,
or an unclassified probe failure.

[Docs home](../README.md) · [Project README](../../README.md)
