# DSL Developer Guide

[Docs home](../README.md) · [Project README](../../README.md)

This page is for contributors who need to change the finite UFO DSL internals.
Examples live under `LeanUfo/UFO/DSL/ConcreteExamples` and are intentionally not
covered here.

## File Map

| File | Responsibility |
| --- | --- |
| `LeanUfo/UFO/DSL/Frontend/SurfaceSyntax.lean` | Concrete `ufo_model` grammar and fact forms. No compilation or proof logic. |
| `LeanUfo/UFO/DSL/Frontend/ModelText.lean` | Name translation and text rendering for DSL facts, generated `ModelAST` declarations, and diagnostics summaries. |
| `LeanUfo/UFO/DSL/Certificate/Tactic.lean` | Shared simplification tactic used by generated certificate proofs. |
| `LeanUfo/UFO/DSL/Certificate/Generation.lean` | Certificate registry, generated theorem source, ax68 proof-source special case, and certificate packaging source. |
| `LeanUfo/UFO/DSL/Diagnostic/Analysis.lean` | Source-level counterexample reconstruction, diagnostic formula evaluation, evidence, suggestions, and derived-assertion analysis. |
| `LeanUfo/UFO/DSL/Syntax.lean` | Command elaborator: parse grammar nodes, call the pure compiler, emit declarations, run generated certificate checks, and save diagnostics. |
| `LeanUfo/UFO/DSL/Diagnostic/Widget.lean` | Editor-side Lean widget for displaying finite-model diagnostics in VS Code. |
| `LeanUfo/UFO/DSL/Compiler.lean` | Pure named-fact resolution, scope expansion, taxonomy closure, derived-fact bookkeeping, and finite table construction. |
| `LeanUfo/UFO/DSL/Compiler/Fields.lean` | Primitive field enums and stable internal table-field names. |
| `LeanUfo/UFO/DSL/Compiler/AST.lean` | Named and resolved DSL fact data structures shared by parser and compiler stages. |
| `LeanUfo/UFO/DSL/FiniteModel.lean` | Finite model representation and semantic bridge into `UFOSignature4`. |
| `LeanUfo/UFO/DSL/Certification.lean` | Certified finite-model packaging and related theorem-facing definitions. |
| `LeanUfo/UFO/DSL/Guarantees.lean` | Theorems about the compiler and finite-model pipeline. |

If a file starts owning a second row of this table, prefer splitting that new
responsibility into a small module with a narrow import surface.

## Command Pipeline

The user-facing command follows this path:

```text
Frontend/SurfaceSyntax grammar
  -> Syntax parser bridge
  -> Frontend/ModelText name-to-field mapping
  -> NamedScopedFact
  -> Compiler.resolveNamedFacts
  -> Compiler.expandScopedFacts
  -> Compiler.addTaxonomyFacts
  -> Compiler.addReflexiveSpecializationFacts
  -> ModelAST
  -> FactTables
  -> FiniteModel4
  -> UFOSignature4
  -> generated per-axiom theorems
  -> generated UFOAxioms4 certificate
  -> Diagnostic/Analysis source-level witness reconstruction on failure
```

`Syntax.lean` is allowed to use metaprogramming because it is the command
frontend.  The middle of the pipeline should stay pure Lean data transformation
where possible, so it can be tested and proved about without elaborator state.

## Diagnostics Versus Certification

Certification is the trusted path: generated Lean declarations are elaborated
and checked by the kernel.

Diagnostics are explanatory: they reconstruct source-level evidence from the
compiled finite tables and send JSON props to the editor widget.  Diagnostics
must not be treated as proof obligations.  If a diagnostic formula mirrors an
axiom, keep the comment local and descriptive about which user-facing failure it
explains.

## Generated Proofs

The certificate generator proves one theorem per registered axiom field.
`Certificate/Tactic.lean` owns the shared generated simplifier.
`Certificate/Generation.lean` owns theorem names, widget ordering, and final
`UFOAxioms4` packaging source.

For performance work:

```bash
LEANUFO_CERT_PROFILE=1 lake env lean LeanUfo/Test/Certification/Positive/Minimal.lean
LEANUFO_AXIOMS=ax73 lake test
LEANUFO_AXIOMS=ax86,ax91 lake test
lake test
```

Use targeted `LEANUFO_AXIOMS=...` runs before a full `lake test` when changing a
specific generated proof path.  A successful term preflight is only a quick
check; theorem commands are the authoritative generated declarations.


[Docs home](../README.md) · [Project README](../../README.md)
