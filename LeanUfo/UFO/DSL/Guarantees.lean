import LeanUfo.UFO.DSL.Syntax

/-!
# Formal guarantees for the Phase 1 DSL backend

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
* The Phase 1 compiler uses the intended universal S5 frame.
* Core compiled predicates in `UFOSignature4` are definitionally connected to
  the finite tables and semantic functions in `FiniteModel4`.

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
## Pure compiler guarantees

The concrete command parser in `Syntax.lean` produces named ASTs. Name
resolution, scope expansion, taxonomy closure, reflexive specialization
closure, table compilation, and finite-model construction live in
`Compiler.lean` as ordinary Lean functions. The theorems below record the
current compiler contract at that pure boundary.
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
The Phase 1 finite compiler uses a universal accessibility relation: every
declared world sees every declared world.  This is the current DSL default, not
a restriction of the semantic kernel.
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
