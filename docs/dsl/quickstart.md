# DSL Quickstart

[Docs home](../README.md) · [Project README](../../README.md)

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

## Multiple Worlds

```lean
ufo_model RoleExample : UFO where
  worlds summer autumn
  things Person Student Alice

  given everywhere:
    ObjectKind(Person)
    Role(Student)
    Student ⊑ Person

  given summer:
    Object(Alice)
    Alice :: Student

  given autumn:
    Object(Alice)
    Alice :: Person

  derive_relations
  certify
```

`given everywhere:` is copied to every declared world by the pure compiler
pipeline.

## Failure Workflow

Negative examples are expected to fail:

```bash
lake env lean LeanUfo/Test/Certification/Negative/Ax66InherenceFromNonMoment.lean
```

The terminal error and VS Code diagnostics widget report whether the failure is
a confirmed finite counterexample, a timeout-style proof-search limit, or an
unclassified generated-proof/search failure.

[Docs home](../README.md) · [Project README](../../README.md)
