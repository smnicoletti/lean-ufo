import Lean
import LeanUfo.UFO.DSL.Compiler

/-!
# Generated certificate tactic support

This module contains the common simplification script used by generated finite
UFO certificate proofs.  It owns only tactic construction; it does not know
which model is being emitted, which axiom field is being checked, or how
diagnostics are rendered.
-/

open Lean Elab Command Parser

namespace LeanUfo.UFO.DSL

def certificateModelSimpDefs : String :=
  "sig, data, tables, ast, compileModel, compileModelAST, compileFacts, compileFact,
    compileExplicitModel, compileExplicitModelAST, compileExplicitFact,
    FactTables.toFiniteModel4, FactTables.unaryTable, FactTables.binaryTable, FactTables.ternaryTable,
    FactTables.tupleProjectionTable, FactTables.identityBinaryTable, addUnary, addUnaryWithTaxonomy,
    addUnaryWithTaxonomyAux, addBinary, addTernary, addTupleProjection, addDerivedProp,
    closeReflexiveSpecialization, unaryTaxonomyParents,
    UnaryField.toTableField, BinaryField.toTableField, TernaryField.toTableField,
    FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame,
    FiniteModel4.typeSem, FiniteModel4.individualSem, Frame.Dia, Frame.Box,
    forallFinSucc, existsFinSucc"

def certificateSimp : String :=
  s!"simp [{certificateModelSimpDefs},
    ax_a1, ax_a2, ax_a3, ax_a4, ax_a5, ax_a6, ax_a7, ax_a8, ax_a9, ax_a10, ax_a11, ax_a12,
    ax_a13, ax_a14, ax_a15, ax_a16, ax_a17, ax_a18, ax_a19, ax_a20, ax_a21, ax_a22, ax_a23,
    ax_a24, ax_a25, ax_a26, ax_a27, ax_a28, ax_a29, ax_a30, ax_a31, ax_a32, ax_a33, ax_a34,
    ax_a35, ax_a36, ax_a37, ax_a38, ax_a39, ax_a40, ax_a41, ax_a42, ax_a43,
    ax_instEndurant_of_EndurantType, ax_sub_of_kind_is_sortal, ax_nonSortal_upward, ax_kindStable,
    ax_a44_endurantType, ax_a44_perdurantType, ax_a44_substantialType, ax_a44_momentType,
    ax_a44_objectType, ax_a44_collectiveType, ax_a44_quantityType, ax_a44_relatorType,
    ax_a44_modeType, ax_a44_qualityType, ax_a44, ax_a45_objectKind, ax_a45_collectiveKind,
    ax_a45_quantityKind, ax_a45_relatorKind, ax_a45_modeKind, ax_a45_qualityKind, ax_a45, ax_a46,
    ax_a47, ax_a48, ax_a49, ax_a50, ax_a51, ax_a52, ax_a53, ax_a54, ax_a55, ax_a56, ax_a57,
    ax_a58, ax_a59, ax_a60, ax_a61, ax_a62, ax_a63, ax_a64, ax_a65, ax_a66, ax_a67, ax_a68,
    ax_a69, ax_a70, ax_a71, ax_a72, ax_a73, ax_a74, ax_a75, ax_a76, ax_a77, ax_a78, ax_a79,
    ax_a80, ax_a81, ax_quaIndividualOf_endurant, ax_a82, ax_a83, ax_a84, ax_a85, ax_a86, ax_a87,
    ax_a88, ax_a89, ax_a90, ax_a91, ax_a92, ax_a93, ax_a94, ax_a95, ax_a96, ax_a97, ax_a98,
    ax_a99, ax_a100, ax_a101, ax_distance_identity, ax_distance_symmetry, ax_distance_triangle,
    ax_a102, ax_a103, ax_a104, ax_a105, ax_a106, ax_a107, ax_a108, ProperSub, Quality,
    MomentOf, UltimateBearerOf, not_momentOf_of_no_inheres, momentOf_eq_of_unique_direct_bearer,
    MemberOf, SubsetOf, ProperSubsetOf, NonEmptySet, QualityStructure,
    SimpleQuality, ComplexQuality, SimpleQualityType, ComplexQualityType, ExistsUnique]"

/--
Build the common certificate simplifier with a small axiom-specific tail.

Most certificate fields only need their own axiom definition in addition to the
finite-model compiler definitions. The shared `certificateSimp` remains useful
for diagnostic counterexample probes and legacy helper fragments even though
ordinary registered certificate fields are checker-backed.
-/
def certificateSimpSelected (defs : String) : String :=
  s!"simp [{certificateModelSimpDefs}, {defs}]"

syntax (name := ufoCertTactic) "ufo_cert_tac" : tactic

@[tactic ufoCertTactic] def evalUFOCertTactic : Lean.Elab.Tactic.Tactic := fun _ => do
  let source := s!"{certificateSimp} <;> (try omega) <;> (try grind) <;> (decide +revert)"
  match Parser.runParserCategory (← getEnv) `tactic source with
  | .ok stx =>
      Lean.Elab.Term.withoutErrToSorry <|
        Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic stx
  | .error err => throwError "failed to parse generated UFO certificate tactic:\n{err}"

end LeanUfo.UFO.DSL
