# Architecture And Trust Boundary

[Docs home](README.md) · [Project README](../README.md)

This page describes the finite DSL backend. The core UFO formalization in
`LeanUfo/UFO/Core` is ordinary Lean code; the DSL adds a command frontend and a
finite compiler around that core.

## Pipeline

```text
ufo_model concrete syntax
  -> NamedScopedFact
  -> resolveNamedFacts
  -> ScopedCompiledFact
  -> expandScopedFacts
  -> CompiledFact
  -> addTaxonomyFacts
  -> addReflexiveSpecializationFacts
  -> ModelAST
  -> compileExplicitModelAST
  -> FactTables
  -> compileExplicitModel
  -> FiniteModel4
  -> FiniteModel4.toUFOSignature4
  -> generated UFOAxioms4 certificate
```

## Stage Summary

- `NamedScopedFact`: parser output with user-facing world and thing names.
- `resolveNamedFacts`: pure duplicate-name and unknown-name checking.
- `ScopedCompiledFact`: resolved facts that still remember whether they are
  scoped to one world or `everywhere`.
- `expandScopedFacts`: pure expansion from `everywhere` to all worlds.
- `CompiledFact`: ordinary world-indexed finite facts.
- `addTaxonomyFacts`: deterministic unary taxonomy closure.
- `addReflexiveSpecializationFacts`: insertion of reflexive specialization
  facts such as `Person ⊑ Person` for instantiated types.
- `ModelAST`: the expanded finite syntax tree emitted by the command frontend.
- `compileExplicitModelAST`: pure compilation into compact finite tables.
- `FiniteModel4`: finite backend representation.
- `FiniteModel4.toUFOSignature4`: semantic bridge into the Prop-valued UFO
  signature checked by the core axioms.
- generated certificate: one theorem per registered axiom and one bundled
  `UFOAxioms4` theorem.

## Trust Boundary

The concrete `ufo_model ... where ...` parser and declaration emitter live in
`Syntax.lean` and are trusted metaprogramming.

After parsing, the main pipeline is implemented as ordinary Lean functions in
`Compiler.lean`, `FiniteModel.lean`, and related modules. Generic properties of
that pipeline are proved in `Guarantees.lean`.

The generated certificate is checked by the Lean kernel. The diagnostics widget
is a presentation layer over elaboration results; it is not the proof object.

## Generated Declaration Shape

For a model named `M`, the frontend emits declarations similar to:

```lean
M.ast       : ModelAST
M.tables    : FactTables
M.data      : FiniteModel4
M.sig       : UFOSignature4
M.certified_ax1 : ax_a1 M.sig.toUFOSignature3_1
-- ...
M.certified : UFOAxioms4 M.sig
M.certifiedModel : FiniteModel4.Certified M.data
```

Failed models stop before the final bundled certificate.

[Docs home](README.md) · [Project README](../README.md)
