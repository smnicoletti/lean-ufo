# DSL Developer Guide

[Docs home](../README.md) · [Project README](../../README.md)

This page is for contributors who need to change the finite UFO DSL internals.
For the conceptual pipeline, first read the [DSL architecture](architecture.md).
For theorem statements and what they guarantee, use
[Formal guarantees](../guarantees.md). Examples live under
`LeanUfo/UFO/DSL/ConcreteExamples` and are intentionally not covered here.

## File Map

| File | Responsibility |
| --- | --- |
| `LeanUfo/UFO/DSL/Frontend/SurfaceSyntax.lean` | Concrete `ufo_model` grammar and fact forms. No compilation or proof logic. |
| `LeanUfo/UFO/DSL/Frontend/ModelText.lean` | Name translation and text rendering for DSL facts, generated `ModelSource`/`ModelAST` declarations, and diagnostics summaries. |
| `LeanUfo/UFO/DSL/Certificate/Tactic.lean` | Shared simplification support used by derived-fact assertions, diagnostic probes, and fallback helper fragments. |
| `LeanUfo/UFO/DSL/Certificate/Generation.lean` | Certificate registry, generated theorem source, checker-backed field selection, and certificate packaging source. |
| `LeanUfo/UFO/DSL/Certificate/Reuse.lean` | Conservative footprint registry for deciding when generated `checked_axN` theorems can reuse parent checks. |
| `LeanUfo/UFO/DSL/Checker/` | Reflective Boolean checker, step model, checker-backed axiom proofs, and polynomial step bounds. |
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
  -> ModelSource
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
  -> checked_axN Boolean check theorems
  -> checker-backed per-axiom theorems
  -> certificateManifest provenance record
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

## Checker-Backed Certificates

The certificate generator emits one stored Boolean check theorem and one
semantic theorem per registered axiom field. The stored check theorem is named
`checked_axN` and has type:

```lean
checkAxN Model.data = true
```

The public semantic theorem is still named `certified_axN`. These public names
are compatibility API and should not be renamed. The semantic theorem calls a
reusable Boolean checker soundness theorem and evaluates the concrete model
with `native_decide`.

`Checker/` owns the reflective Boolean checks, `Stepped` step model, soundness
and completeness theorems, and conservative polynomial step bounds for the
registered checker-backed fields. `Certificate/Tactic.lean` still provides
shared simplification support for derived-fact assertions, diagnostic probes,
and fallback helper fragments. `Certificate/Generation.lean` owns theorem names, widget ordering,
checker-backed theorem source, manifest source, and final `UFOAxioms4`
packaging source.

Each successful model also emits:

```lean
Model.source              : ModelSource
Model.certificateManifest : CertificateManifest
```

`Model.source` is the parsed, reusable source artifact before name resolution.
`Model.certificateManifest` is provenance/export metadata. It is not proof
evidence; the proof evidence remains the generated Lean theorems.

Exact-source extension aliases may reuse a parent's `checked_axN` theorem under
ordinary `certify`. `certify_fresh` disables that reuse and regenerates the
Boolean check theorem. Extensions that add things or facts may also reuse a
field when the field's registered finite-table footprint is unchanged.

Footprint-backed reuse is registered in `Certificate/Reuse.lean`. The registry
has one row per certificate field and lists the primitive finite tables read by
that field's checker. A field is marked reused only when the planner selects a
parent and the generated theorem successfully proves equality of the child and
parent checker results before using the parent `checked_axN` theorem. If that
equality proof fails, the command generator falls back to a fresh checker proof
and the manifest records the field as fresh.

`Guarantees.lean` records the formal proof pattern behind reuse:

```lean
CertificateReuse.reused_checker_result_sound
CertificateReuse.reused_checker_semantic_sound
CertificateReuse.reused_aggregate_checker_certified_sound
CertificateReuse.certificateReuseSource_fresh_none
```

The important point is that footprints are planning metadata. They do not prove
an axiom and they are not trusted as cache hits. Reuse remains correct because
Lean checks the concrete Boolean equality needed to transport a parent
`checked_axN` theorem to the child.

To add a reusable footprint:

1. inspect the `checkAxN` implementation in `Checker/Axioms.lean`;
2. list every primitive table field read by that checker in
   `reusableFieldFootprints`;
3. add or update a positive extension fixture showing the expected fresh/reused
   manifest status;
4. keep the generated proof shape unchanged, so reuse remains Lean-checked.

Manifest export starts as Lean data: `CertificateManifest.toJson` converts the
manifest to a JSON value. The supported command-line path is:

```bash
lake exe export-certificates --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension --out certificates/
lake exe validate-certificate certificates/CarBase.certificate.json --structure-only
lake exe validate-certificate certificates/CarBase.certificate.json --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension
```

Use `export_certificate ModelName` in a module to request export of selected
models. If no export marker is present, the exporter attempts to export all
certified models declared in the module source. `--structure-only` checks only
manifest structure. The default validation path requires `--module`; it
rebuilds the Lean module, checks the theorem declarations at their expected
types, and compares regenerated SHA-256 source/model digests. Do not treat the
JSON as proof evidence.

Version metadata comes from `LeanUfo/UFO/DSL/Version.lean`. Development builds
use a `-dev` artifact version; release automation should replace it with the
release tag before publishing certificate manifests.

The repository includes a minimal release helper for this:

```bash
scripts/set-artifact-version.sh vX.Y.Z
```

The `Certificate Manifests` GitHub workflow runs this helper in the release
runner workspace, exports marked certificate manifests, rechecks them against
the Lean declarations, and uploads the JSON files as release assets. The helper
does not need to commit back to `dev`; it only ensures that manifests published
for a tag carry that tag as their artifact version.

The current checker-backed fields are all registered fields through §4:

```text
ax1-ax17
ax18-ax33
ax_instEndurant, ax_sub_kind_sortal, ax_nonSortal_up, ax_kindStable
ax34-ax43
ax44-ax46
ax47-ax52
ax53-ax55
ax56-ax61
ax62-ax64
ax65-ax68
ax69-ax73
ax74-ax80
axQuaIndividualOfEndurant
ax81-ax82
ax83-ax101
axDistanceIdentity
axDistanceSymmetry
axDistanceTriangle
ax102-ax104
ax105-ax108
```

`ax68` is checker-backed through a bounded finite closure checker for
`MomentOf`. The executable closure is proved sound and complete with respect to
the inductive transitive-closure encoding used by the core `UltimateBearerOf`
definition. `ax73` uses
`sameFoundationB`, which is proved equivalent to `FoundationOf` only under the
unique-foundation premises supplied by `ax72` and `ax75`. `ax78` and `ax79`
use the same finite foundation bridge; their soundness theorems make the
required prerequisite checker calls explicit.

The negative probe generator mirrors this shape. Direct-complete fields use
`checkAxN_complete`; `ax73`, `ax78`, and `ax79` use prerequisite-aware
completeness lemmas after first checking the required earlier fields with
`native_decide`.

When adding a checker-backed axiom, keep the public `certified_axN` theorem name
stable and add the Boolean checker, stepped checker, soundness proof, and
targeted `LEANUFO_AXIOMS=axN lake test` run. Add completeness and direct
negative-probe routing when the checker is equivalent to the core axiom without
extra representation assumptions.

When touching model-extension code, keep `extendModelSource` as the only merge
point. It currently rejects child-added worlds so parent `everywhere` facts keep
their original expansion. Do not add implicit re-expansion in the frontend until
the scoping semantics is explicitly decided.

The §3.12 checker-backed fields include membership-dependent obligations
whose finite content is available through `FiniteModel4.memberOf`. The semantic
`SetExtension` field is derived from that table, so `MemberOf` and
`NonEmptySet` proofs can be related back to executable Boolean scans. This now
covers the proper-subset obligation in `ax90` and the simple/complex
quality-type obligations in `ax95`-`ax98`.

`ax99` is checker-backed by explicit product-family witnesses stored in the
finite model. The syntax:

```lean
product_family ColorSpace for ColorQuality:
  dimensions HueSpace SaturationSpace BrightnessSpace
  types Hue Saturation Brightness
```

records the finite family used to instantiate the `∃ n, ∃ ys zs` part of the
core axiom. The checker proves soundness from such witnesses. Full
completeness is proved for the finite stored-witness semantics:

```lean
checkAx99 M = true ↔ ax99Finite M
```

The core certificate remains unchanged:

```lean
checkAx99 M = true → ax_a99 M.toUFOSignature4.toUFOSignature3_12
```

The converse for the core `ax_a99` is intentionally not claimed: the core axiom
quantifies over arbitrary tuple arities, while the finite model can only check
the product-family witnesses it stores.

For this reason the checker exposes an explicit representation-completeness
contract:

```lean
ProductFamilyWitnessTableComplete M
```

This condition means that, if the semantic core axiom `ax_a99` holds, the
finite `productFamilies` table is rich enough to represent the required
product-family witness. Under that condition, checker failure can be read as a
semantic failure:

```lean
ProductFamilyWitnessTableComplete M →
checkAx99 M = false →
¬ ax_a99 M.toUFOSignature4.toUFOSignature3_12
```

Without this condition, `checkAx99 M = false` has a weaker meaning: the checker
did not find a stored witness. Diagnostics therefore report missing
product-family data separately from confirmed semantic counterexamples, and
point to the missing `product_family`, `Characterization`, `AssociatedWith`,
`MemberOf`, and `TupleProjection` facts needed to make the finite witness
checkable.

## Hard Checker Case: ax68

`ax68` is the first checker-backed axiom that cannot be reduced to a fixed
first-order table scan. The core theory defines `MomentOf` as an inductive
transitive closure over `InheresIn`, and `UltimateBearerOf(b, m)` means:

```lean
¬ Moment b w ∧ MomentOf m b w
```

The checker cannot ask Lean to decide `MomentOf` directly, because the
inductive relation has no automatic `Decidable` instance for generated finite
models. Instead, `Checker/Axioms.lean` defines an executable finite closure:

```lean
reachableInheresInVia M pivots m b w
reachableInheresInB M m b w
ultimateBearerOfB M b m w
existsUniqueUltimateBearerB M m w
checkAx68 M
```

`reachableInheresInVia` is Warshall-style rather than depth-first search. It
folds over the finite list of possible intermediate things. At each pivot it
keeps the previously known reachability relation and adds all paths that go
through that pivot. This form is deliberately chosen because the proof follows
the algorithm:

- the base relation contains the finite `InheresIn` table;
- each pivot step is closed under composition through that pivot;
- after all finite things have been used as pivots, every finite transitive
  closure path is represented;
- the Boolean closure is also sound: every reported non-reflexive path gives a
  core `MomentOf` proof.

`Checker/Soundness.lean` proves the semantic bridge:

```lean
reachableInheresInB_complete
ultimateBearerOfB_sound
ultimateBearerOfB_complete
existsUniqueUltimateBearerB_eq_true_iff
checkAx68_sound
checkAx68_complete
checkAx68_correct
```

The `checkAx68_sound` theorem is what generated certificates use. The
`checkAx68_complete` theorem is equally important: it says that if the core
semantic axiom holds, the Boolean checker must return `true`. That theorem fits
the general checker-aware negative probe pattern: when `checkAxN data = false`
and `checkAxN_complete` is available, Lean proves `¬ axN` by contradiction
using completeness.

Two caveats are worth keeping explicit:

- The closure checker proves semantic finite-model correctness, not a wall-clock
  runtime bound for Lean, Lake, or compiled native code.
- The generic generated simplifier is not the right proof path for hard
  checker-backed counterexamples such as transitive closure. Prefer a
  checker-aware negative probe whenever a direct completeness theorem is
  available.

For performance work:

```bash
LEANUFO_CERT_PROFILE=1 lake env lean LeanUfo/Test/Certification/Positive/Minimal.lean
LEANUFO_AXIOMS=ax73 lake test
LEANUFO_AXIOMS=ax86,ax91 lake test
lake test
```

Use targeted `LEANUFO_AXIOMS=...` runs before a full `lake test` when changing a
specific checker, generated declaration, or diagnostic path. A successful term
preflight is only a quick check; theorem commands are the authoritative
generated declarations.


[Docs home](../README.md) · [Project README](../../README.md)
