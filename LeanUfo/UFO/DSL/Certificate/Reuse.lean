import Lean
import LeanUfo.UFO.DSL.Compiler

/-!
# Certificate reuse footprints

This module owns the conservative field-level reuse registry used by the DSL
command frontend.  Reuse here is intentionally syntactic and table-based: a
field is reusable only when the finite tables read by its Boolean checker are
unchanged between parent and child models.

The registry is metadata for generated proof construction, not a trusted proof.
Generated `checked_axN` declarations still ask Lean to prove that the child and
parent checker results are equal before reusing a parent theorem.
-/

open Lean

namespace LeanUfo.UFO.DSL

structure ReusableFieldFootprint where
  field : String
  unary : Array String := #[]
  binary : Array String := #[]
  ternary : Array String := #[]
  tupleProjection : Bool := false
  productFamilies : Bool := false
  deriving Inhabited, Repr

/--
Field-level reuse registry.

Each row names the compiled table fields read by the corresponding checker.
The registry is exhaustive over the registered certificate fields, but it is
still only a planning aid.  Generated reuse proofs separately ask Lean to check
that the child and parent checker results are equal before reusing a parent
`checked_axN` theorem.
-/
def reusableFieldFootprints : Array ReusableFieldFootprint :=
  #[
    { field := "ax1", binary := #["inst"] },
    { field := "ax2", binary := #["inst"] },
    { field := "ax3", binary := #["inst"] },
    { field := "ax4", binary := #["inst"] },
    { field := "ax5", binary := #["sub", "inst"] },
    { field := "ax6", binary := #["inst", "sub"] },
    { field := "ax7", unary := #["concreteIndividual"], binary := #["inst"] },
    { field := "ax8", unary := #["abstractIndividual"], binary := #["inst"] },
    { field := "ax9", unary := #["concreteIndividual", "abstractIndividual"] },
    { field := "ax10", unary := #["concreteIndividual", "abstractIndividual"], binary := #["inst"] },
    { field := "ax11", unary := #["endurant", "concreteIndividual"] },
    { field := "ax12", unary := #["perdurant", "concreteIndividual"] },
    { field := "ax13", unary := #["endurant", "perdurant"] },
    { field := "ax14", unary := #["concreteIndividual", "endurant", "perdurant"] },
    { field := "ax15", unary := #["endurantType"], binary := #["inst"] },
    { field := "ax16", unary := #["perdurantType"], binary := #["inst"] },
    { field := "ax17", unary := #["endurantType", "perdurantType"] },
    { field := "ax18", unary := #["rigid", "endurantType"], binary := #["inst"] },
    { field := "ax19", unary := #["antiRigid", "endurantType"], binary := #["inst"] },
    { field := "ax20", unary := #["semiRigid", "endurantType", "rigid", "antiRigid"] },
    { field := "ax21", unary := #["endurant", "kind"], binary := #["inst"] },
    { field := "ax22", unary := #["kind"], binary := #["inst"] },
    { field := "ax23", unary := #["sortal", "endurantType", "kind"], binary := #["inst"] },
    { field := "ax24", unary := #["nonSortal", "endurantType", "sortal"] },
    { field := "ax25", unary := #["kind", "subKind"] },
    { field := "ax26", unary := #["kind", "subKind", "rigid", "sortal"] },
    { field := "ax27", unary := #["phase", "role"] },
    { field := "ax28", unary := #["phase", "role", "antiRigid", "sortal"] },
    { field := "ax29", unary := #["semiRigidSortal", "semiRigid", "sortal"] },
    { field := "ax30", unary := #["category", "rigid", "nonSortal"] },
    { field := "ax31", unary := #["mixin", "semiRigid", "nonSortal"] },
    { field := "ax32", unary := #["phaseMixin", "roleMixin"] },
    { field := "ax33", unary := #["phaseMixin", "roleMixin", "antiRigid", "nonSortal"] },
    { field := "ax_instEndurant", unary := #["endurantType", "endurant"], binary := #["inst"] },
    { field := "ax_sub_kind_sortal", unary := #["kind", "sortal"], binary := #["sub"] },
    { field := "ax_nonSortal_up", unary := #["nonSortal"], binary := #["sub"] },
    { field := "ax_kindStable", unary := #["kind"] },
    { field := "ax34", unary := #["substantial", "moment", "endurant"] },
    { field := "ax35", unary := #["substantial", "moment"] },
    { field := "ax36", unary := #["object", "collective", "quantity", "substantial"] },
    { field := "ax37", unary := #["object", "collective"] },
    { field := "ax38", unary := #["object", "quantity"] },
    { field := "ax39", unary := #["collective", "quantity"] },
    { field := "ax40", unary := #["relator", "intrinsicMoment", "moment"] },
    { field := "ax41", unary := #["relator", "intrinsicMoment"] },
    { field := "ax42", unary := #["mode", "intrinsicMoment", "qualityKind"], binary := #["inst"] },
    { field := "ax43", unary := #["mode", "qualityKind"], binary := #["inst"] },
    { field := "ax44",
      unary := #[
        "endurantType", "endurant", "perdurantType", "perdurant",
        "substantialType", "substantial", "momentType", "moment",
        "objectType", "object", "collectiveType", "collective",
        "quantityType", "quantity", "relatorType", "relator",
        "modeType", "mode", "qualityType", "qualityKind"
      ],
      binary := #["inst"] },
    { field := "ax45",
      unary := #[
        "objectKind", "objectType", "collectiveKind", "collectiveType",
        "quantityKind", "quantityType", "relatorKind", "relatorType",
        "modeKind", "modeType", "qualityKind", "qualityType", "kind"
      ] },
    { field := "ax46",
      unary := #["endurant", "objectKind", "collectiveKind", "quantityKind", "relatorKind", "modeKind", "qualityKind"],
      binary := #["inst"] },
    { field := "ax47", binary := #["part"] },
    { field := "ax48", binary := #["part"] },
    { field := "ax49", binary := #["part"] },
    { field := "ax50", binary := #["overlap", "part"] },
    { field := "ax51", binary := #["part", "overlap"] },
    { field := "ax52", binary := #["properPart", "part"] },
    { field := "ax53", binary := #["inst", "functionsAs"] },
    { field := "ax54", binary := #["inst", "functionsAs"] },
    { field := "ax55", binary := #["properPart", "inst", "functionsAs"] },
    { field := "ax56", unary := #["endurant", "perdurant"], binary := #["constitutedBy"] },
    { field := "ax57", unary := #["kind"], binary := #["constitutedBy", "inst"] },
    { field := "ax58", binary := #["inst", "constitutedBy"] },
    { field := "ax59", binary := #["inst", "constitutedBy"] },
    { field := "ax60", unary := #["perdurant", "ex"], binary := #["constitutedBy"] },
    { field := "ax61", binary := #["constitutedBy"] },
    { field := "ax62" },
    { field := "ax63", unary := #["ex"] },
    { field := "ax64", unary := #["ex"] },
    { field := "ax65", unary := #["ex"], binary := #["inheresIn"] },
    { field := "ax66", unary := #["moment", "concreteIndividual"], binary := #["inheresIn", "inst"] },
    { field := "ax67", binary := #["inheresIn"] },
    { field := "ax68", unary := #["moment"], binary := #["inheresIn"] },
    { field := "ax69", unary := #["ex"], binary := #["inheresIn"] },
    { field := "ax70", unary := #["mode", "ex"], binary := #["inheresIn"] },
    { field := "ax71", unary := #["mode", "relator", "perdurant", "ex"], binary := #["foundedBy", "inheresIn"] },
    { field := "ax72", unary := #["mode", "ex"], binary := #["inheresIn", "foundedBy"] },
    { field := "ax73", unary := #["mode", "ex"], binary := #["overlap", "inheresIn", "foundedBy", "quaIndividualOf"] },
    { field := "ax74", binary := #["quaIndividualOf"] },
    { field := "ax75", unary := #["mode", "ex"], binary := #["quaIndividualOf", "inheresIn"] },
    { field := "ax76", binary := #["quaIndividualOf"] },
    { field := "ax77", unary := #["relator"], binary := #["foundedBy"] },
    { field := "ax78", unary := #["relator"], binary := #["part", "foundedBy"] },
    { field := "ax79", unary := #["relator", "ex"], binary := #["properPart", "quaIndividualOf", "foundedBy"] },
    { field := "ax80", unary := #["relator", "endurant"], binary := #["mediates", "quaIndividualOf", "part"] },
    { field := "axQuaIndividualOfEndurant", unary := #["endurant"], binary := #["quaIndividualOf"] },
    { field := "ax81", unary := #["endurantType", "momentType"], binary := #["characterization", "inst", "inheresIn"] },
    { field := "ax82", unary := #["qualityType"], binary := #["characterization", "inst", "inheresIn"] },
    { field := "ax83", unary := #["quale", "abstractIndividual"] },
    { field := "ax84", unary := #["set_", "abstractIndividual"] },
    { field := "ax85", unary := #["quale", "set_"] },
    { field := "ax86", unary := #["qualityType", "set_"], binary := #["associatedWith", "memberOf"] },
    { field := "ax87", unary := #["quale", "qualityType"], binary := #["associatedWith", "memberOf"] },
    { field := "ax88", unary := #["qualityDomain", "qualityDimension", "qualityType"], binary := #["associatedWith"] },
    { field := "ax89", unary := #["qualityDomain", "qualityDimension"] },
    { field := "ax90", binary := #["associatedWith", "sub", "memberOf"] },
    { field := "ax91", unary := #["qualityType", "intrinsicMomentType"], binary := #["associatedWith"] },
    { field := "ax92", unary := #["qualityKind", "quale"], binary := #["hasValue", "inst"] },
    { field := "ax93", unary := #["qualityKind"], binary := #["inst", "hasValue"] },
    { field := "ax94", binary := #["hasValue", "inst", "associatedWith", "memberOf"] },
    { field := "ax95", unary := #["qualityDimension", "qualityType", "qualityKind"], binary := #["associatedWith", "inst", "inheresIn"] },
    { field := "ax96", unary := #["qualityDomain", "qualityType", "qualityKind"], binary := #["associatedWith", "inst", "inheresIn"] },
    { field := "ax97", unary := #["qualityType", "qualityKind"], binary := #["inst", "inheresIn"] },
    { field := "ax98", unary := #["qualityType", "qualityKind"], binary := #["inst", "inheresIn"] },
    { field := "ax99",
      unary := #["qualityDomain"],
      binary := #["associatedWith", "memberOf", "characterization"],
      tupleProjection := true,
      productFamilies := true },
    { field := "ax100", unary := #["quale"], binary := #["memberOf"], ternary := #["distance"] },
    { field := "ax101", unary := #["quale"], ternary := #["distance"] },
    { field := "axDistanceIdentity", unary := #["distanceZero"], ternary := #["distance"] },
    { field := "axDistanceSymmetry", ternary := #["distance"] },
    { field := "axDistanceTriangle", binary := #["distanceGreaterEq"], ternary := #["distance", "distanceSum"] },
    { field := "ax102", unary := #["perdurant", "endurant"], binary := #["manifests"] },
    { field := "ax103", unary := #["perdurant", "endurant"], binary := #["lifeOf", "overlap", "manifests"] },
    { field := "ax104", unary := #["perdurant"], binary := #["meet"] },
    { field := "ax105" },
    { field := "ax106" },
    { field := "ax107" },
    { field := "ax108" }
  ]

def reusableFieldFootprint? (field : String) : Option ReusableFieldFootprint :=
  reusableFieldFootprints.find? fun footprint => footprint.field == field

def sameUnaryFootprint (fields : Array String) (left right : FactTables) : Bool :=
  fields.all fun field => left.unary.getD field #[] == right.unary.getD field #[]

def sameBinaryFootprint (fields : Array String) (left right : FactTables) : Bool :=
  fields.all fun field => left.binary.getD field #[] == right.binary.getD field #[]

def sameTernaryFootprint (fields : Array String) (left right : FactTables) : Bool :=
  fields.all fun field => left.ternary.getD field #[] == right.ternary.getD field #[]

def footprintUnchanged
    (footprint : ReusableFieldFootprint) (parentTables childTables : FactTables) :
    Bool :=
  sameUnaryFootprint footprint.unary parentTables childTables &&
    sameBinaryFootprint footprint.binary parentTables childTables &&
    sameTernaryFootprint footprint.ternary parentTables childTables &&
    (!footprint.tupleProjection || parentTables.tupleProjection == childTables.tupleProjection) &&
    (!footprint.productFamilies || parentTables.productFamilies == childTables.productFamilies)

def fieldFootprintReusable
    (field : String) (parentTables childTables : FactTables) : Bool :=
  match reusableFieldFootprint? field with
  | none => false
  | some footprint => footprintUnchanged footprint parentTables childTables

def certificateReuseSource?
    (parentName : Name) (parentSource childSource : ModelSource)
    (parentTables childTables : FactTables) (fresh : Bool) (field : String) :
    Option Name :=
  if fresh then
    none
  else if childSource == parentSource || fieldFootprintReusable field parentTables childTables then
    some parentName
  else
    none

end LeanUfo.UFO.DSL
