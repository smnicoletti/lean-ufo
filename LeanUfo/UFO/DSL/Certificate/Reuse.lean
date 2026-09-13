import Lean
import LeanUfo.UFO.DSL.Compiler

/-!
# Certificate reuse footprints

This module owns the conservative field-level reuse registry used by the DSL
command frontend. It selects a candidate parent when source records are equal
or the tables named by the field's footprint are unchanged. Equality preserves
array order and duplicates. Each scan stops at the first mismatch.

The registry is metadata for generated proof construction, not a trusted proof.
Generated `checked_axN` declarations still ask Lean to prove that the child and
parent checker results are equal before reusing a parent theorem.

Production entry points erase costs from the counted comparisons below.
`Complexity/Reuse.lean` proves value equivalence and bounds the visited source
components, relation rows, and family slots. This composition follows the
cost-aware semantics of Niu et al. (POPL 2022, doi:10.1145/3498670). String
comparisons and map lookups use the documented abstract primitive interface;
the theorem does not bound native hashing or character processing.
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
    { field := "ax73", unary := #["mode", "ex"], binary := #["part", "inheresIn", "foundedBy", "quaIndividualOf"] },
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

open Complexity

private def pairEqCosted (first : α → α → Costed Bool) (second : β → β → Costed Bool)
    (a b : α × β) : Costed Bool :=
  (first a.1 b.1).andThen fun _ => second a.2 b.2

private def natPairEqCosted : (Nat × Nat) → (Nat × Nat) → Costed Bool :=
  pairEqCosted (fun a b => Costed.tick (a == b)) (fun a b => Costed.tick (a == b))

private def natTripleEqCosted : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Costed Bool :=
  pairEqCosted (fun a b => Costed.tick (a == b)) natPairEqCosted

private def natQuadEqCosted : (Nat × Nat × Nat × Nat) → (Nat × Nat × Nat × Nat) → Costed Bool :=
  pairEqCosted (fun a b => Costed.tick (a == b)) natTripleEqCosted

private def namedScopeEqCosted : NamedFactScope → NamedFactScope → Costed Bool
  | .at a, .at b => Costed.charge 1 (Costed.tick (a == b))
  | .everywhere, .everywhere => Costed.tick true
  | _, _ => Costed.tick false

private def namedDerivedEqCosted : NamedDerivedFact → NamedDerivedFact → Costed Bool
  | .unary afield athing, .unary bfield bthing =>
    Costed.charge 1 <| (Costed.tick (afield == bfield)).andThen fun _ =>
    Costed.tick (athing == bthing)
  | .binary afield aleft aright, .binary bfield bleft bright =>
    Costed.charge 1 <| (Costed.tick (afield == bfield)).andThen fun _ =>
    (Costed.tick (aleft == bleft)).andThen fun _ =>
    Costed.tick (aright == bright)
  | .ternary afield afirst asecond athird, .ternary bfield bfirst bsecond bthird =>
    Costed.charge 1 <| (Costed.tick (afield == bfield)).andThen fun _ =>
    (Costed.tick (afirst == bfirst)).andThen fun _ =>
    (Costed.tick (asecond == bsecond)).andThen fun _ =>
    Costed.tick (athird == bthird)
  | .quaternary afield afirst asecond athird afourth, .quaternary bfield bfirst bsecond bthird bfourth =>
    Costed.charge 1 <| (Costed.tick (afield == bfield)).andThen fun _ =>
    (Costed.tick (afirst == bfirst)).andThen fun _ =>
    (Costed.tick (asecond == bsecond)).andThen fun _ =>
    (Costed.tick (athird == bthird)).andThen fun _ =>
    Costed.tick (afourth == bfourth)
  | _, _ => Costed.tick false

private def namedFactEqCosted : NamedScopedFact → NamedScopedFact → Costed Bool
  | .unary afield athing ascope, .unary bfield bthing bscope =>
    Costed.charge 1 <| (Costed.tick (afield == bfield)).andThen fun _ =>
    (Costed.tick (athing == bthing)).andThen fun _ =>
    namedScopeEqCosted ascope bscope
  | .binary afield aleft aright ascope, .binary bfield bleft bright bscope =>
    Costed.charge 1 <| (Costed.tick (afield == bfield)).andThen fun _ =>
    (Costed.tick (aleft == bleft)).andThen fun _ =>
    (Costed.tick (aright == bright)).andThen fun _ =>
    namedScopeEqCosted ascope bscope
  | .ternary afield afirst asecond athird ascope, .ternary bfield bfirst bsecond bthird bscope =>
    Costed.charge 1 <| (Costed.tick (afield == bfield)).andThen fun _ =>
    (Costed.tick (afirst == bfirst)).andThen fun _ =>
    (Costed.tick (asecond == bsecond)).andThen fun _ =>
    (Costed.tick (athird == bthird)).andThen fun _ =>
    namedScopeEqCosted ascope bscope
  | .tupleProjection atuple aindex aresult ascope, .tupleProjection btuple bindex bresult bscope =>
    Costed.charge 1 <| (Costed.tick (atuple == btuple)).andThen fun _ =>
    (Costed.tick (aindex == bindex)).andThen fun _ =>
    (Costed.tick (aresult == bresult)).andThen fun _ =>
    namedScopeEqCosted ascope bscope
  | .derived afact ascope, .derived bfact bscope =>
    Costed.charge 1 <| (namedDerivedEqCosted afact bfact).andThen fun _ =>
    namedScopeEqCosted ascope bscope
  | _, _ => Costed.tick false

private def namedFamilyEqCosted (a b : NamedProductFamily) : Costed Bool :=
  (Costed.tick (a.domain == b.domain)).andThen fun _ =>
  (Costed.tick (a.qualityType == b.qualityType)).andThen fun _ =>
  (arrayEqCosted a.dimensionThings b.dimensionThings (fun x y => Costed.tick (x == y))).andThen fun _ =>
  arrayEqCosted a.typeThings b.typeThings (fun x y => Costed.tick (x == y))

private def familyEqCosted (a b : ProductFamilySpec) : Costed Bool :=
  (Costed.tick (a.domain == b.domain)).andThen fun _ =>
  (Costed.tick (a.qualityType == b.qualityType)).andThen fun _ =>
  (arrayEqCosted a.dimensionThings b.dimensionThings (fun x y => Costed.tick (x == y))).andThen fun _ =>
  arrayEqCosted a.typeThings b.typeThings (fun x y => Costed.tick (x == y))

/-- Compare source components in declaration order. Arrays retain order and
duplicates; unequal lengths and the first unequal item stop the comparison.
Strings and field constructors are primitive comparisons. Families include
both variable-length slot arrays. No whole-record comparison is a primitive. -/
def modelSourceEqCosted (a b : ModelSource) : Costed Bool :=
  (arrayEqCosted a.worlds b.worlds (fun x y => Costed.tick (x == y))).andThen fun _ =>
  (arrayEqCosted a.things b.things (fun x y => Costed.tick (x == y))).andThen fun _ =>
  (arrayEqCosted a.facts b.facts namedFactEqCosted).andThen fun _ =>
  (arrayEqCosted a.productFamilies b.productFamilies namedFamilyEqCosted).andThen fun _ =>
  Costed.tick (a.deriveRelations == b.deriveRelations)

/-- Map operations use the compiler's abstract map interface. The cost is
not a native hash-table bound. Relation rows are compared by coordinate,
with both table lookups and all visited array cells included. -/
private def sameTableFieldsCosted (fields : Array String)
    (left right : Std.HashMap String (Array α)) (compare : α → α → Costed Bool) : Costed Bool :=
  allArrayCosted fields fun field => do
    let a ← Costed.tick (left.getD field #[])
    let b ← Costed.tick (right.getD field #[])
    arrayEqCosted a b compare

def reusableFieldFootprintCosted (field : String) : Costed (Option ReusableFieldFootprint) :=
  Costed.charge 1 <|
    (Costed.foldArrayExcept reusableFieldFootprints () fun _ footprint =>
      Costed.tick (if footprint.field == field then .error footprint else .ok ()) 2).map
      (fun result => match result with | .error footprint => some footprint | .ok _ => none)

def reusableFieldFootprint? (field : String) : Option ReusableFieldFootprint :=
  (reusableFieldFootprintCosted field).value

def sameUnaryFootprintCosted (fields : Array String) (left right : FactTables) : Costed Bool :=
  sameTableFieldsCosted fields left.unary right.unary natPairEqCosted

def sameUnaryFootprint (fields : Array String) (left right : FactTables) : Bool :=
  (sameUnaryFootprintCosted fields left right).value

def sameBinaryFootprintCosted (fields : Array String) (left right : FactTables) : Costed Bool :=
  sameTableFieldsCosted fields left.binary right.binary natTripleEqCosted

def sameBinaryFootprint (fields : Array String) (left right : FactTables) : Bool :=
  (sameBinaryFootprintCosted fields left right).value

def sameTernaryFootprintCosted (fields : Array String) (left right : FactTables) : Costed Bool :=
  sameTableFieldsCosted fields left.ternary right.ternary natQuadEqCosted

def sameTernaryFootprint (fields : Array String) (left right : FactTables) : Bool :=
  (sameTernaryFootprintCosted fields left right).value

def footprintUnchangedCosted (footprint : ReusableFieldFootprint)
    (parentTables childTables : FactTables) : Costed Bool :=
  (sameUnaryFootprintCosted footprint.unary parentTables childTables).andThen fun _ =>
  (sameBinaryFootprintCosted footprint.binary parentTables childTables).andThen fun _ =>
  (sameTernaryFootprintCosted footprint.ternary parentTables childTables).andThen fun _ =>
  (Costed.branch (Costed.pure footprint.tupleProjection)
    (fun _ => arrayEqCosted parentTables.tupleProjection childTables.tupleProjection natQuadEqCosted)
    (fun _ => Costed.pure true)).andThen fun _ =>
    Costed.branch (Costed.pure footprint.productFamilies)
      (fun _ => arrayEqCosted parentTables.productFamilies childTables.productFamilies familyEqCosted)
      (fun _ => Costed.pure true)

def footprintUnchanged (footprint : ReusableFieldFootprint)
    (parentTables childTables : FactTables) : Bool :=
  (footprintUnchangedCosted footprint parentTables childTables).value

def fieldFootprintReusableCosted
    (field : String) (parentTables childTables : FactTables) : Costed Bool := do
  let found ← reusableFieldFootprintCosted field
  match found with
  | none => Costed.tick false
  | some footprint => Costed.charge 1 (footprintUnchangedCosted footprint parentTables childTables)

def fieldFootprintReusable
    (field : String) (parentTables childTables : FactTables) : Bool :=
  (fieldFootprintReusableCosted field parentTables childTables).value

def certificateReuseSourceCosted
    (parentName : Name) (parentSource childSource : ModelSource)
    (parentTables childTables : FactTables) (fresh : Bool) (field : String) :
    Costed (Option Name) :=
  Costed.branch (Costed.pure fresh) (fun _ => Costed.pure none) fun _ => do
    let reusable ← (modelSourceEqCosted childSource parentSource).orElse fun _ =>
      fieldFootprintReusableCosted field parentTables childTables
    Costed.tick (if reusable then some parentName else none)

def certificateReuseSource?
    (parentName : Name) (parentSource childSource : ModelSource)
    (parentTables childTables : FactTables) (fresh : Bool) (field : String) : Option Name :=
  (certificateReuseSourceCosted parentName parentSource childSource parentTables childTables fresh field).value

end LeanUfo.UFO.DSL
