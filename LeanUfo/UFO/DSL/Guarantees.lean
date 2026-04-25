import LeanUfo.UFO.DSL.Syntax

/-!
# Formal guarantees for the Phase 1 DSL backend

This module records the object-level guarantees that are already available for
the finite DSL pipeline.

The statements are intentionally modest. They document and prove the key
semantic facts that make the generated artifacts useful:

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
