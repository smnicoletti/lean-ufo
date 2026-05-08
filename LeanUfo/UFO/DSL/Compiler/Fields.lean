import Lean

/-!
# Finite DSL field vocabulary

This module contains the typed names for primitive finite-table fields and their
stable internal table-string representation.  The rest of the compiler uses
these constructors instead of raw strings at the AST boundary.
-/

namespace LeanUfo.UFO.DSL

/-- Primitive unary finite-table fields accepted by the resolved DSL AST. -/
inductive UnaryField where
  | concreteIndividual | abstractIndividual | endurant | perdurant
  | endurantType | perdurantType
  | rigid | antiRigid | semiRigid | kind | sortal | nonSortal
  | subKind | phase | role | semiRigidSortal
  | category | mixin | phaseMixin | roleMixin
  | substantial | moment | object | collective | quantity | relator
  | intrinsicMoment | mode | qualityKind
  | substantialType | momentType | objectType | collectiveType | quantityType
  | relatorType | modeType | qualityType
  | objectKind | collectiveKind | quantityKind | relatorKind | modeKind
  | ex | quale | set_ | qualityDomain | qualityDimension | intrinsicMomentType
  | distanceZero
  deriving Repr, Inhabited, DecidableEq

/-- Finite table field name for a unary AST field. -/
def UnaryField.toTableField : UnaryField → String
  | .concreteIndividual => "concreteIndividual"
  | .abstractIndividual => "abstractIndividual"
  | .endurant => "endurant"
  | .perdurant => "perdurant"
  | .endurantType => "endurantType"
  | .perdurantType => "perdurantType"
  | .rigid => "rigid"
  | .antiRigid => "antiRigid"
  | .semiRigid => "semiRigid"
  | .kind => "kind"
  | .sortal => "sortal"
  | .nonSortal => "nonSortal"
  | .subKind => "subKind"
  | .phase => "phase"
  | .role => "role"
  | .semiRigidSortal => "semiRigidSortal"
  | .category => "category"
  | .mixin => "mixin"
  | .phaseMixin => "phaseMixin"
  | .roleMixin => "roleMixin"
  | .substantial => "substantial"
  | .moment => "moment"
  | .object => "object"
  | .collective => "collective"
  | .quantity => "quantity"
  | .relator => "relator"
  | .intrinsicMoment => "intrinsicMoment"
  | .mode => "mode"
  | .qualityKind => "qualityKind"
  | .substantialType => "substantialType"
  | .momentType => "momentType"
  | .objectType => "objectType"
  | .collectiveType => "collectiveType"
  | .quantityType => "quantityType"
  | .relatorType => "relatorType"
  | .modeType => "modeType"
  | .qualityType => "qualityType"
  | .objectKind => "objectKind"
  | .collectiveKind => "collectiveKind"
  | .quantityKind => "quantityKind"
  | .relatorKind => "relatorKind"
  | .modeKind => "modeKind"
  | .ex => "ex"
  | .quale => "quale"
  | .set_ => "set_"
  | .qualityDomain => "qualityDomain"
  | .qualityDimension => "qualityDimension"
  | .intrinsicMomentType => "intrinsicMomentType"
  | .distanceZero => "distanceZero"

/-- Parse an internal unary table field name back into a typed AST field. -/
def UnaryField.fromTableField? (field : String) : Option UnaryField :=
  match field with
  | "concreteIndividual" => some .concreteIndividual
  | "abstractIndividual" => some .abstractIndividual
  | "endurant" => some .endurant
  | "perdurant" => some .perdurant
  | "endurantType" => some .endurantType
  | "perdurantType" => some .perdurantType
  | "rigid" => some .rigid
  | "antiRigid" => some .antiRigid
  | "semiRigid" => some .semiRigid
  | "kind" => some .kind
  | "sortal" => some .sortal
  | "nonSortal" => some .nonSortal
  | "subKind" => some .subKind
  | "phase" => some .phase
  | "role" => some .role
  | "semiRigidSortal" => some .semiRigidSortal
  | "category" => some .category
  | "mixin" => some .mixin
  | "phaseMixin" => some .phaseMixin
  | "roleMixin" => some .roleMixin
  | "substantial" => some .substantial
  | "moment" => some .moment
  | "object" => some .object
  | "collective" => some .collective
  | "quantity" => some .quantity
  | "relator" => some .relator
  | "intrinsicMoment" => some .intrinsicMoment
  | "mode" => some .mode
  | "qualityKind" => some .qualityKind
  | "substantialType" => some .substantialType
  | "momentType" => some .momentType
  | "objectType" => some .objectType
  | "collectiveType" => some .collectiveType
  | "quantityType" => some .quantityType
  | "relatorType" => some .relatorType
  | "modeType" => some .modeType
  | "qualityType" => some .qualityType
  | "objectKind" => some .objectKind
  | "collectiveKind" => some .collectiveKind
  | "quantityKind" => some .quantityKind
  | "relatorKind" => some .relatorKind
  | "modeKind" => some .modeKind
  | "ex" => some .ex
  | "quale" => some .quale
  | "set_" => some .set_
  | "qualityDomain" => some .qualityDomain
  | "qualityDimension" => some .qualityDimension
  | "intrinsicMomentType" => some .intrinsicMomentType
  | "distanceZero" => some .distanceZero
  | _ => none

/-- Primitive binary finite-table fields accepted by the resolved DSL AST. -/
inductive BinaryField where
  | inst | sub | part | overlap | properPart | functionsAs | constitutedBy
  | inheresIn | foundedBy | quaIndividualOf | mediates | characterization
  | associatedWith | hasValue | memberOf | manifests | lifeOf | meet | distanceGreaterEq
  deriving Repr, Inhabited, DecidableEq

/-- Finite table field name for a binary AST field. -/
def BinaryField.toTableField : BinaryField → String
  | .inst => "inst"
  | .sub => "sub"
  | .part => "part"
  | .overlap => "overlap"
  | .properPart => "properPart"
  | .functionsAs => "functionsAs"
  | .constitutedBy => "constitutedBy"
  | .inheresIn => "inheresIn"
  | .foundedBy => "foundedBy"
  | .quaIndividualOf => "quaIndividualOf"
  | .mediates => "mediates"
  | .characterization => "characterization"
  | .associatedWith => "associatedWith"
  | .hasValue => "hasValue"
  | .memberOf => "memberOf"
  | .manifests => "manifests"
  | .lifeOf => "lifeOf"
  | .meet => "meet"
  | .distanceGreaterEq => "distanceGreaterEq"

/-- Primitive ternary finite-table fields accepted by the resolved DSL AST. -/
inductive TernaryField where
  | distance | distanceSum
  deriving Repr, Inhabited, DecidableEq

/-- Finite table field name for a ternary AST field. -/
def TernaryField.toTableField : TernaryField → String
  | .distance => "distance"
  | .distanceSum => "distanceSum"


end LeanUfo.UFO.DSL
