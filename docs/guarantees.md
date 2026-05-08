# Formal Guarantees

[Docs home](README.md) · [Project README](../README.md)

The DSL has a trusted frontend, but the central compiler pipeline is ordinary
Lean code with generic theorem-backed guarantees.

The theorem statements live in:

```text
LeanUfo/UFO/DSL/Guarantees.lean
```

## Covered Areas

`Guarantees.lean` currently records generic facts about:

- name resolution;
- scope expansion;
- taxonomy expansion;
- reflexive specialization expansion;
- explicit fact compilation;
- finite model construction;
- the bridge from `FiniteModel4.Certified` to `UFOAxioms4`;
- pure diagnostic-status classification.

These theorems are not a full metatheory of the DSL. They are targeted
engineering guarantees for the pure pipeline boundary.

## What The Guarantees Mean

Examples of current guarantee types:

- unknown names produce explicit resolver errors;
- `given everywhere` expansion is handled by the pure scope-expansion pass;
- generated models compile from an already-expanded `ModelAST`;
- expanded unary and binary facts become table insertions;
- a field is rendered as `success`, `failed`, or `unchecked` according to the
  completed-field list and first failed field.

## What Is Still Trusted

The parser and declaration emitter in `Syntax.lean` remain trusted
metaprogramming. In particular, the concrete `ModelAST` value emitted for each
DSL command is produced by the frontend. A future tightening could replay more
of that construction inside generated Lean declarations.

Generated proof terms are checked by Lean.

[Docs home](README.md) · [Project README](../README.md)
