import LeanUfo.UFO.DSL.Syntax

/-!
# Formal guarantees for the finite DSL backend

This module records the object-level guarantees that are already available for
the finite DSL pipeline.

The statements are intentionally modest. They document and prove the key
semantic facts that make the generated artifacts useful:

* named fact resolution is a pure function with explicit duplicate-name and
  unknown-name errors;
* `given everywhere` scope expansion is implemented by the pure compiler, not
  by ad-hoc command elaborator loops;
* generated models are compiled through ordinary Lean functions from expanded
  facts to finite tables and then to `FiniteModel4`;
* `FiniteModel4.Certified M` is exactly the existing `UFOAxioms4` proposition
  applied to the compiled semantic signature.
* The finite compiler uses the intended universal S5 frame.
* Core compiled predicates in `UFOSignature4` are definitionally connected to
  the finite tables and semantic functions in `FiniteModel4`.
* New §3.12 surface tables for set membership, tuple projection, and distance
  are compiled into the corresponding finite-model fields.
* The diagnostics widget's certificate status labels are a faithful rendering
  of the elaborator state: completed checks are shown as `success`, the first
  recorded failure is shown as `failed`, and later checks are shown as
  `unchecked`.

For each concrete `ufo_model ... certify` command, Lean additionally emits
ordinary theorems:

* `ModelName.certified : UFOAxioms4 ModelName.sig`
* `ModelName.certifiedModel : FiniteModel4.Certified ModelName.data`

Those per-model certificates are the executable instances of the generic
guarantees proved here.  Thus the DSL is sound in the usual certified-frontend
sense: if the command elaborates successfully through `certify`, the generated
finite model has a Lean proof that its compiled signature satisfies the encoded
UFO axioms.
-/

namespace LeanUfo.UFO.DSL

/-!
## Diagnostics guarantees

The widget is intentionally not a proof oracle. The command elaborator obtains
its state by asking Lean to elaborate each generated certificate proof term in
order. The guarantees below cover the pure boundary between that checked state
and the diagnostic label rendered in the widget.

Thus there are no diagnostic false positives at this boundary: a field is shown
as `success` exactly when it appears in the completed list. For fields not in
that completed list, there are no diagnostic false negatives for the first
recorded failure: the field is shown as `failed` exactly when `failed?` records
that field, and otherwise it is shown as `unchecked`.
-/

namespace Diagnostics

/--
The diagnostics widget reports `success` exactly for certificate fields already
recorded as completed by the command elaborator.
-/
theorem diagnostic_success_iff_completed
    (completed : Array String) (failed? : Option String) (field : String) :
    diagnosticCertStatus completed failed? field = "success" ↔
      field ∈ completed := by
  unfold diagnosticCertStatus
  by_cases h : field ∈ completed
  · simp [h]
  · simp [h]
    split <;> decide

/--
Once a certificate field has not completed, the diagnostics widget reports
`failed` exactly for the first field recorded as failed by the command
elaborator.
-/
theorem diagnostic_failed_iff_recorded_failure_of_not_completed
    (completed : Array String) (failed? : Option String) (field : String)
    (h : field ∉ completed) :
    diagnosticCertStatus completed failed? field = "failed" ↔
      failed? = some field := by
  unfold diagnosticCertStatus
  simp [h]

/--
Once a certificate field has not completed, the diagnostics widget reports
`unchecked` exactly when that field is not the first recorded failure.
-/
theorem diagnostic_unchecked_iff_not_recorded_failure_of_not_completed
    (completed : Array String) (failed? : Option String) (field : String)
    (h : field ∉ completed) :
    diagnosticCertStatus completed failed? field = "unchecked" ↔
      failed? ≠ some field := by
  unfold diagnosticCertStatus
  simp [h]

/--
If the command elaborator has recorded a first failing field, then every
non-completed field other than that one is rendered as `unchecked`, not as a
spurious success or failure.
-/
theorem diagnostic_unchecked_after_first_failure
    (completed : Array String) (failed field : String)
    (hNotCompleted : field ∉ completed)
    (hOther : field ≠ failed) :
    diagnosticCertStatus completed (some failed) field = "unchecked" := by
  have hFailedNe : failed ≠ field := fun h => hOther h.symm
  unfold diagnosticCertStatus
  simp [hNotCompleted, hFailedNe]

/--
The Lean-side status classifier sent to the widget is total over the three
displayed states.  The JavaScript widget only renders these strings; it does
not invent additional certification states.
-/
theorem diagnostic_status_exhaustive
    (completed : Array String) (failed? : Option String) (field : String) :
    diagnosticCertStatus completed failed? field = "success" ∨
      diagnosticCertStatus completed failed? field = "failed" ∨
      diagnosticCertStatus completed failed? field = "unchecked" := by
  unfold diagnosticCertStatus
  by_cases hCompleted : field ∈ completed
  · simp [hCompleted]
  · simp [hCompleted]
    by_cases hFailed : failed? = some field
    · simp [hFailed]
    · simp [hFailed]

/--
Completed certificate fields have priority in the widget status classifier:
even if inconsistent caller data also records the same field as failed, the
rendered status is still `success`.
-/
theorem diagnostic_completed_priority
    (completed : Array String) (failed? : Option String) (field : String)
    (hCompleted : field ∈ completed) :
    diagnosticCertStatus completed failed? field = "success" := by
  exact (diagnostic_success_iff_completed completed failed? field).2 hCompleted

/--
A recorded failure is rendered as `failed` exactly when that field has not
already completed.
-/
theorem diagnostic_recorded_failure_is_failed_of_not_completed
    (completed : Array String) (field : String)
    (hNotCompleted : field ∉ completed) :
    diagnosticCertStatus completed (some field) field = "failed" := by
  exact
    (diagnostic_failed_iff_recorded_failure_of_not_completed
      completed (some field) field hNotCompleted).2 rfl

/--
If a field has neither completed nor been recorded as the first failure, the
widget classifier renders it as `unchecked`.
-/
theorem diagnostic_unchecked_of_not_completed_and_not_failed
    (completed : Array String) (failed? : Option String) (field : String)
    (hNotCompleted : field ∉ completed)
    (hNotFailed : failed? ≠ some field) :
    diagnosticCertStatus completed failed? field = "unchecked" := by
  exact
    (diagnostic_unchecked_iff_not_recorded_failure_of_not_completed
      completed failed? field hNotCompleted).2 hNotFailed

end Diagnostics

/-!
## Pure compiler guarantees

The concrete command parser in `Syntax.lean` produces named ASTs. Name
resolution, scope expansion, taxonomy closure, reflexive specialization
closure, table compilation, and finite-model construction live in
`Compiler.lean` as ordinary Lean functions. The theorems below record the
compiler contract at that pure boundary.
-/

namespace NameResolution

/-- Thing-name resolution succeeds exactly at the index returned by `nameIndex?`. -/
theorem resolveThing_of_nameIndex_eq_some
    (ts : Array String) (thing : String) (idx : Nat)
    (h : nameIndex? ts thing = some idx) :
    resolveThing ts thing = Except.ok idx := by
  rw [resolveThing, h]
  rfl

/-- Thing-name resolution rejects names absent from the declaration list. -/
theorem resolveThing_of_nameIndex_eq_none
    (ts : Array String) (thing : String)
    (h : nameIndex? ts thing = none) :
    resolveThing ts thing = Except.error (.unknownThing thing) := by
  rw [resolveThing, h]
  rfl

/-- World-name resolution succeeds exactly at the index returned by `nameIndex?`. -/
theorem resolveWorld_of_nameIndex_eq_some
    (ws : Array String) (world : String) (idx : Nat)
    (h : nameIndex? ws world = some idx) :
    resolveWorld ws world = Except.ok idx := by
  rw [resolveWorld, h]
  rfl

/-- World-name resolution rejects names absent from the declaration list. -/
theorem resolveWorld_of_nameIndex_eq_none
    (ws : Array String) (world : String)
    (h : nameIndex? ws world = none) :
    resolveWorld ws world = Except.error (.unknownWorld world) := by
  rw [resolveWorld, h]
  rfl

/-- The reserved `everywhere` scope is preserved by name resolution. -/
theorem resolveScope_everywhere (ws : Array String) :
    resolveScope ws .everywhere = Except.ok .everywhere :=
  rfl

/-- A world-scoped fact resolves to the resolved world index when lookup succeeds. -/
theorem resolveScope_at_of_resolveWorld_eq_ok
    (ws : Array String) (world : String) (idx : Nat)
    (h : resolveWorld ws world = Except.ok idx) :
    resolveScope ws (.at world) = Except.ok (.at idx) := by
  simp [resolveScope, h]

/-- Unary named fact resolution succeeds when its thing and scope resolutions succeed. -/
theorem resolveNamedFact_unary_of_resolved
    (ws ts : Array String) (field : UnaryField) (thing : String)
    (namedScope : NamedFactScope) (thingIdx : Nat) (scope : FactScope)
    (hThing : resolveThing ts thing = Except.ok thingIdx)
    (hScope : resolveScope ws namedScope = Except.ok scope) :
    resolveNamedFact ws ts (.unary field thing namedScope) =
      Except.ok (.unary field thingIdx scope) := by
  simp [resolveNamedFact, hThing, hScope]
  rfl

/-- Binary named fact resolution succeeds when both things and the scope resolve. -/
theorem resolveNamedFact_binary_of_resolved
    (ws ts : Array String) (field : BinaryField) (left right : String)
    (namedScope : NamedFactScope) (leftIdx rightIdx : Nat) (scope : FactScope)
    (hLeft : resolveThing ts left = Except.ok leftIdx)
    (hRight : resolveThing ts right = Except.ok rightIdx)
    (hScope : resolveScope ws namedScope = Except.ok scope) :
    resolveNamedFact ws ts (.binary field left right namedScope) =
      Except.ok (.binary field leftIdx rightIdx scope) := by
  simp [resolveNamedFact, hLeft, hRight, hScope]
  rfl

/-- Ternary named fact resolution succeeds when all things and the scope resolve. -/
theorem resolveNamedFact_ternary_of_resolved
    (ws ts : Array String) (field : TernaryField) (first second third : String)
    (namedScope : NamedFactScope) (firstIdx secondIdx thirdIdx : Nat) (scope : FactScope)
    (hFirst : resolveThing ts first = Except.ok firstIdx)
    (hSecond : resolveThing ts second = Except.ok secondIdx)
    (hThird : resolveThing ts third = Except.ok thirdIdx)
    (hScope : resolveScope ws namedScope = Except.ok scope) :
    resolveNamedFact ws ts (.ternary field first second third namedScope) =
      Except.ok (.ternary field firstIdx secondIdx thirdIdx scope) := by
  simp [resolveNamedFact, hFirst, hSecond, hThird, hScope]
  rfl

/-- Tuple-projection fact resolution succeeds when tuple/result names and scope resolve. -/
theorem resolveNamedFact_tupleProjection_of_resolved
    (ws ts : Array String) (tuple result : String) (index : Nat)
    (namedScope : NamedFactScope) (tupleIdx resultIdx : Nat) (scope : FactScope)
    (hTuple : resolveThing ts tuple = Except.ok tupleIdx)
    (hResult : resolveThing ts result = Except.ok resultIdx)
    (hScope : resolveScope ws namedScope = Except.ok scope) :
    resolveNamedFact ws ts (.tupleProjection tuple index result namedScope) =
      Except.ok (.tupleProjection tupleIdx index resultIdx scope) := by
  simp [resolveNamedFact, hTuple, hResult, hScope]
  rfl

/-- Batch resolution delegates to the pure single-fact resolver after duplicate checks. -/
theorem resolveNamedFacts_of_checks_ok
    (ws ts : Array String) (facts : Array NamedScopedFact)
    (hWorlds : checkWorldNames ws = Except.ok ())
    (hThings : checkThingNames ts = Except.ok ()) :
    resolveNamedFacts ws ts facts = facts.mapM (resolveNamedFact ws ts) := by
  unfold resolveNamedFacts
  rw [hWorlds, hThings]
  rfl

end NameResolution

namespace ScopedCompiledFact

/-- A unary fact scoped to one world expands to exactly one world-indexed fact. -/
theorem unary_at_expands_to_singleton
    (worldCount : Nat) (field : UnaryField) (x w : Nat) :
    expandScopedFact worldCount (.unary field x (.at w)) =
      #[CompiledFact.unary field x w] :=
  rfl

/-- A binary fact scoped to one world expands to exactly one world-indexed fact. -/
theorem binary_at_expands_to_singleton
    (worldCount : Nat) (field : BinaryField) (x y w : Nat) :
    expandScopedFact worldCount (.binary field x y (.at w)) =
      #[CompiledFact.binary field x y w] :=
  rfl

/-- A derived assertion scoped to one world expands by applying its proposition builder. -/
theorem derived_at_expands_to_singleton
    (worldCount : Nat) (propAtWorld : Nat → String) (w : Nat) :
    expandScopedFact worldCount (.derived propAtWorld (.at w)) =
      #[CompiledFact.derived (propAtWorld w)] :=
  rfl

/-- A ternary fact scoped to one world expands to exactly one world-indexed fact. -/
theorem ternary_at_expands_to_singleton
    (worldCount : Nat) (field : TernaryField) (x y z w : Nat) :
    expandScopedFact worldCount (.ternary field x y z (.at w)) =
      #[CompiledFact.ternary field x y z w] :=
  rfl

/-- A tuple-projection fact scoped to one world expands to exactly one world-indexed fact. -/
theorem tupleProjection_at_expands_to_singleton
    (worldCount : Nat) (tuple index result w : Nat) :
    expandScopedFact worldCount (.tupleProjection tuple index result (.at w)) =
      #[CompiledFact.tupleProjection tuple index result w] :=
  rfl

/--
Expansion of all scoped facts is ordinary folding over the pure scoped fact
expander. This is where the `given everywhere` semantics now lives.
-/
theorem scoped_expansion_pipeline
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    expandScopedFacts worldCount facts =
      facts.foldl (fun out fact => out ++ expandScopedFact worldCount fact) #[] :=
  rfl

end ScopedCompiledFact

namespace CompiledFact

/--
Unary facts are compiled by inserting the user fact and deterministic taxonomy
ancestors. Thus taxonomy closure is part of the verified compiler core rather
than ad-hoc command elaborator behavior.
-/
theorem unary_compiles_with_taxonomy
    (tables : FactTables) (field : UnaryField) (x w : Nat) :
    compileFact tables (.unary field x w) =
      addUnaryWithTaxonomy tables field.toTableField x w :=
  compileFact_unary_eq tables field x w

/-- Binary facts are compiled by inserting exactly one binary table entry. -/
theorem binary_compiles_to_table
    (tables : FactTables) (field : BinaryField) (x y w : Nat) :
    compileFact tables (.binary field x y w) =
      addBinary tables field.toTableField x y w :=
  compileFact_binary_eq tables field x y w

/-- Ternary facts are compiled by inserting exactly one ternary table entry. -/
theorem ternary_compiles_to_table
    (tables : FactTables) (field : TernaryField) (x y z w : Nat) :
    compileFact tables (.ternary field x y z w) =
      addTernary tables field.toTableField x y z w :=
  compileFact_ternary_eq tables field x y z w

/-- Tuple-projection facts are compiled by inserting exactly one projection table entry. -/
theorem tupleProjection_compiles_to_table
    (tables : FactTables) (tuple index result w : Nat) :
    compileFact tables (.tupleProjection tuple index result w) =
      addTupleProjection tables tuple index result w :=
  compileFact_tupleProjection_eq tables tuple index result w

/--
Derived-relation assertions are not primitive semantic tables. They compile to
generated propositions that Lean checks against the derived semantic relations.
-/
theorem derived_compiles_to_assertion
    (tables : FactTables) (prop : String) :
    compileFact tables (.derived prop) = addDerivedProp tables prop :=
  compileFact_derived_eq tables prop

/--
Once taxonomy closure has been made explicit in the AST, unary facts compile to
direct unary table insertions. Generated models use this expanded path so
certificates normalize to small Boolean table checks.
-/
theorem explicit_unary_compiles_to_table
    (tables : FactTables) (field : UnaryField) (x w : Nat) :
    compileExplicitFact tables (.unary field x w) =
      addUnary tables field.toTableField x w :=
  rfl

/-- Explicit binary facts compile to direct binary table insertions. -/
theorem explicit_binary_compiles_to_table
    (tables : FactTables) (field : BinaryField) (x y w : Nat) :
    compileExplicitFact tables (.binary field x y w) =
      addBinary tables field.toTableField x y w :=
  rfl

/-- Explicit ternary facts compile to direct ternary table insertions. -/
theorem explicit_ternary_compiles_to_table
    (tables : FactTables) (field : TernaryField) (x y z w : Nat) :
    compileExplicitFact tables (.ternary field x y z w) =
      addTernary tables field.toTableField x y z w :=
  rfl

/-- Explicit tuple-projection facts compile to direct projection table insertions. -/
theorem explicit_tupleProjection_compiles_to_table
    (tables : FactTables) (tuple index result w : Nat) :
    compileExplicitFact tables (.tupleProjection tuple index result w) =
      addTupleProjection tables tuple index result w :=
  rfl

/-- Explicit derived assertions compile to generated propositions. -/
theorem explicit_derived_compiles_to_assertion
    (tables : FactTables) (prop : String) :
    compileExplicitFact tables (.derived prop) = addDerivedProp tables prop :=
  rfl

end CompiledFact

namespace ModelAST

/-- Generated models make deterministic taxonomy sugar explicit before table compilation. -/
theorem taxonomy_expansion_pipeline (facts : Array CompiledFact) :
    addTaxonomyFacts facts =
      facts.foldl
        (fun acc fact =>
          match fact with
          | .unary field x w => acc ++ expandUnaryTaxonomyFact field x w
          | _ => acc.push fact)
        #[] :=
  rfl

/--
Generated models make reflexive specialization sugar explicit before table
compilation.
-/
theorem reflexive_specialization_expansion_pipeline
    (worldCount : Nat) (facts : Array CompiledFact) :
    addReflexiveSpecializationFacts worldCount facts =
      let typeTargets :=
        facts.foldl
          (fun (seen : Std.HashSet Nat) fact =>
            match fact with
            | .binary .inst _ t _ => seen.insert t
            | _ => seen)
          {}
      typeTargets.toArray.foldl
        (fun facts t =>
          Id.run do
            let mut facts := facts
            for w in [:worldCount] do
              facts := facts.push (.binary .sub t t w)
            pure facts)
        facts :=
  rfl

/--
Resolved model compilation is exactly:

1. fold resolved facts into finite tables;
2. close specialization reflexively for instantiated types.
-/
theorem compilation_pipeline (ast : ModelAST) :
    compileModelAST ast =
      closeReflexiveSpecialization ast.worldCount (compileFacts ast.facts) :=
  compileModelAST_eq ast

/--
Compilation of an already-expanded AST is exactly a fold of explicit facts.
This is the path used by generated model declarations after `Syntax.lean`
materializes taxonomy and reflexive-specialization sugar in the emitted AST.
-/
theorem explicit_compilation_pipeline (ast : ModelAST) :
    compileExplicitModelAST ast = ast.facts.foldl compileExplicitFact {} :=
  rfl

/--
The generated model construction path is ordinary compilation from explicit AST
facts to finite tables and then to `FiniteModel4`.
-/
theorem explicit_model_pipeline
    (ast : ModelAST) (hw : 0 < ast.worldCount) (ht : 0 < ast.thingCount) :
    compileExplicitModel ast hw ht =
      (compileExplicitModelAST ast).toFiniteModel4
        ast.worldCount ast.thingCount hw ht :=
  rfl

end ModelAST

namespace FactTables

/-- `toFiniteModel4` reads instantiation from the compiled binary table. -/
theorem toFiniteModel4_inst_eq
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (x y : Fin tc) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).inst x y w =
      tables.binaryTable "inst" x y w :=
  rfl

/-- `toFiniteModel4` reads specialization from the compiled binary table. -/
theorem toFiniteModel4_sub_eq
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (x y : Fin tc) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).sub x y w =
      tables.binaryTable "sub" x y w :=
  rfl

/-- `toFiniteModel4` gives identity by default for parthood. -/
theorem toFiniteModel4_part_eq
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (x y : Fin tc) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).part x y w =
      tables.identityBinaryTable "part" x y w :=
  rfl

/-- `toFiniteModel4` reads set membership from the compiled `MemberOf` table. -/
theorem toFiniteModel4_setExtension_iff_memberOf
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (x s : Fin tc) (w : Fin wc) :
    x ∈ (tables.toFiniteModel4 wc tc hw ht).setExtension s w ↔
      tables.binaryTable "memberOf" x s w = true :=
  Iff.rfl

/-- `toFiniteModel4` reads tuple projection from the compiled projection table. -/
theorem toFiniteModel4_tupleProjection_eq
    (tables : FactTables) (wc tc n : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (p : Fin tc) (i : Fin n) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).tupleProjection p i w =
      tables.tupleProjectionTable p i.val w :=
  rfl

/-- `toFiniteModel4` reads distance from the compiled ternary table. -/
theorem toFiniteModel4_distance_eq
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (x y r : Fin tc) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).distance x y r w =
      tables.ternaryTable "distance" x y r w :=
  rfl

/-- `toFiniteModel4` reads zero-distance values from the compiled unary table. -/
theorem toFiniteModel4_distanceZero_eq
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (r : Fin tc) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).distanceZero r w =
      tables.unaryTable "distanceZero" r w :=
  rfl

/-- `toFiniteModel4` reads distance sums from the compiled ternary table. -/
theorem toFiniteModel4_distanceSum_eq
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (r0 r1 s : Fin tc) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).distanceSum r0 r1 s w =
      tables.ternaryTable "distanceSum" r0 r1 s w :=
  rfl

/-- `toFiniteModel4` reads distance ordering from the compiled binary table. -/
theorem toFiniteModel4_distanceGreaterEq_eq
    (tables : FactTables) (wc tc : Nat) (hw : 0 < wc) (ht : 0 < tc)
    (s r : Fin tc) (w : Fin wc) :
    (tables.toFiniteModel4 wc tc hw ht).distanceGreaterEq s r w =
      tables.binaryTable "distanceGreaterEq" s r w :=
  rfl

end FactTables

namespace FiniteModel4

/--
Certification for a finite DSL model is not a new semantic notion: it is exactly
the original UFO axiom package applied to the compiled signature.
-/
theorem certified_iff_ufoAxioms4 (M : FiniteModel4) :
    M.Certified ↔ UFOAxioms4 M.toUFOSignature4 :=
  Iff.rfl

/--
Soundness of a finite certificate, stated as an elimination rule.

Given a certificate for the finite model, downstream proofs may use the original
Prop-level UFO axiom package for the compiled signature.
-/
theorem certified_sound (M : FiniteModel4) :
    M.Certified → UFOAxioms4 M.toUFOSignature4 :=
  fun h => h

/--
Introduction rule for `Certified`.

This is useful when a proof has already established the original axiom package
for the compiled signature and wants to package it as a finite-model
certificate.
-/
theorem certified_of_ufoAxioms4 (M : FiniteModel4) :
    UFOAxioms4 M.toUFOSignature4 → M.Certified :=
  fun h => h

/--
The finite compiler uses a universal accessibility relation: every
declared world sees every declared world.  This is the DSL default used here,
not a restriction of the semantic kernel.
-/
theorem compiled_frame_universal
    (M : FiniteModel4) (w v : M.toS5Frame.World) :
    M.toS5Frame.R w v :=
  trivial

/-- The compiled frame is reflexive because it is an S5 frame. -/
theorem compiled_frame_refl (M : FiniteModel4) (w : M.toS5Frame.World) :
    M.toS5Frame.R w w :=
  M.toS5Frame.refl w

/-- The compiled frame is symmetric because it is an S5 frame. -/
theorem compiled_frame_symm
    (M : FiniteModel4) {w v : M.toS5Frame.World} :
    M.toS5Frame.R w v → M.toS5Frame.R v w :=
  fun h => M.toS5Frame.symm h

/-- The compiled frame is transitive because it is an S5 frame. -/
theorem compiled_frame_trans
    (M : FiniteModel4) {w v u : M.toS5Frame.World} :
    M.toS5Frame.R w v → M.toS5Frame.R v u → M.toS5Frame.R w u :=
  fun h₁ h₂ => M.toS5Frame.trans h₁ h₂

/--
The compiled signature has the same universal accessibility relation as the
finite model's generated S5 frame.
-/
theorem compiled_signature_frame_universal
    (M : FiniteModel4) (w v : M.toUFOSignature4.F.World) :
    M.toUFOSignature4.F.R w v :=
  trivial

/--
`Type` in the compiled signature is the semantic finite definition
`FiniteModel4.typeSem`.
-/
theorem compiled_type_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.Type_ x w ↔ M.typeSem x w :=
  Iff.rfl

/--
`Individual` in the compiled signature is the semantic finite definition
`FiniteModel4.individualSem`.
-/
theorem compiled_individual_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.Individual x w ↔ M.individualSem x w :=
  Iff.rfl

/-- Instantiation in the compiled signature is read directly from the table. -/
theorem compiled_inst_iff
    (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.Inst x y w ↔ M.inst x y w = true :=
  Iff.rfl

/-- Specialization in the compiled signature is read directly from the table. -/
theorem compiled_sub_iff
    (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.Sub x y w ↔ M.sub x y w = true :=
  Iff.rfl

/-- Parthood in the compiled signature is read directly from the table. -/
theorem compiled_part_iff
    (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.Part x y w ↔ M.part x y w = true :=
  Iff.rfl

/-- Set membership in the compiled signature is exactly finite set-extension membership. -/
theorem compiled_memberOf_iff_setExtension
    (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) :
    MemberOf M.toUFOSignature4.toUFOSignature3_12 x s w ↔
      x ∈ M.setExtension s w :=
  Iff.rfl

/-- Distance in the compiled signature is read directly from the finite table. -/
theorem compiled_distance_iff
    (M : FiniteModel4)
    (x y r : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.Distance x y r w ↔ M.distance x y r w = true :=
  Iff.rfl

/-- Zero-distance values in the compiled signature are read directly from the finite table. -/
theorem compiled_distanceZero_iff
    (M : FiniteModel4)
    (r : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.DistanceZero r w ↔ M.distanceZero r w = true :=
  Iff.rfl

/-- Distance sums in the compiled signature are read directly from the finite table. -/
theorem compiled_distanceSum_iff
    (M : FiniteModel4)
    (r0 r1 s : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.DistanceSum r0 r1 s w ↔ M.distanceSum r0 r1 s w = true :=
  Iff.rfl

/-- Distance ordering in the compiled signature is read directly from the finite table. -/
theorem compiled_distanceGreaterEq_iff
    (M : FiniteModel4)
    (s r : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.DistanceGreaterEq s r w ↔
      M.distanceGreaterEq s r w = true :=
  Iff.rfl

/--
The semantic compiler, not the user table, defines `Constitution` in the
compiled signature.
-/
theorem compiled_constitution_iff
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    M.toUFOSignature4.Constitution x x' y y' w ↔
      M.inst x x' w = true ∧ M.inst y y' w = true ∧
      (∀ z : Fin M.thingCount,
        M.inst z x' w = true →
          ∃ q : Fin M.thingCount,
            M.inst q y' w = true ∧ M.constitutedBy z q w = true) ∧
      M.constitutedBy x y w = true :=
  Iff.rfl

end FiniteModel4

end LeanUfo.UFO.DSL
