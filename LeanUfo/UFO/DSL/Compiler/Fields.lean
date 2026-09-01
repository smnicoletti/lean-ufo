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
  deriving Repr, Inhabited, DecidableEq, BEq

/-- Stable dense-table order for unary fields. -/
def UnaryField.all : Array UnaryField := #[
  .concreteIndividual, .abstractIndividual, .endurant, .perdurant,
  .endurantType, .perdurantType, .rigid, .antiRigid, .semiRigid, .kind,
  .sortal, .nonSortal, .subKind, .phase, .role, .semiRigidSortal,
  .category, .mixin, .phaseMixin, .roleMixin, .substantial, .moment,
  .object, .collective, .quantity, .relator, .intrinsicMoment, .mode,
  .qualityKind, .substantialType, .momentType, .objectType, .collectiveType,
  .quantityType, .relatorType, .modeType, .qualityType, .objectKind,
  .collectiveKind, .quantityKind, .relatorKind, .modeKind, .ex, .quale,
  .set_, .qualityDomain, .qualityDimension, .intrinsicMomentType, .distanceZero]

def UnaryField.index : UnaryField → Nat
  | .concreteIndividual => 0
  | .abstractIndividual => 1
  | .endurant => 2
  | .perdurant => 3
  | .endurantType => 4
  | .perdurantType => 5
  | .rigid => 6
  | .antiRigid => 7
  | .semiRigid => 8
  | .kind => 9
  | .sortal => 10
  | .nonSortal => 11
  | .subKind => 12
  | .phase => 13
  | .role => 14
  | .semiRigidSortal => 15
  | .category => 16
  | .mixin => 17
  | .phaseMixin => 18
  | .roleMixin => 19
  | .substantial => 20
  | .moment => 21
  | .object => 22
  | .collective => 23
  | .quantity => 24
  | .relator => 25
  | .intrinsicMoment => 26
  | .mode => 27
  | .qualityKind => 28
  | .substantialType => 29
  | .momentType => 30
  | .objectType => 31
  | .collectiveType => 32
  | .quantityType => 33
  | .relatorType => 34
  | .modeType => 35
  | .qualityType => 36
  | .objectKind => 37
  | .collectiveKind => 38
  | .quantityKind => 39
  | .relatorKind => 40
  | .modeKind => 41
  | .ex => 42
  | .quale => 43
  | .set_ => 44
  | .qualityDomain => 45
  | .qualityDimension => 46
  | .intrinsicMomentType => 47
  | .distanceZero => 48

def UnaryField.count : Nat := UnaryField.all.size

theorem UnaryField.index_lt_count (field : UnaryField) : field.index < UnaryField.count := by
  cases field <;> native_decide

theorem UnaryField.index_injective : Function.Injective UnaryField.index := by
  intro left right
  cases left <;> cases right <;> native_decide

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

@[simp] theorem UnaryField.fromTableField?_toTableField (field : UnaryField) :
    UnaryField.fromTableField? field.toTableField = some field := by
  cases field <;> rfl

theorem UnaryField.toTableField_injective :
    Function.Injective UnaryField.toTableField := by
  intro left right h
  have := congrArg UnaryField.fromTableField? h
  simpa using this

/-- Primitive binary finite-table fields accepted by the resolved DSL AST. -/
inductive BinaryField where
  | inst | sub | part | overlap | properPart | functionsAs | constitutedBy
  | inheresIn | foundedBy | quaIndividualOf | mediates | characterization
  | associatedWith | hasValue | memberOf | manifests | lifeOf | meet | distanceGreaterEq
  deriving Repr, Inhabited, DecidableEq, BEq

/-- Stable dense-table order for binary fields. -/
def BinaryField.all : Array BinaryField := #[
  .inst, .sub, .part, .overlap, .properPart, .functionsAs, .constitutedBy,
  .inheresIn, .foundedBy, .quaIndividualOf, .mediates, .characterization,
  .associatedWith, .hasValue, .memberOf, .manifests, .lifeOf, .meet,
  .distanceGreaterEq]

def BinaryField.index : BinaryField → Nat
  | .inst => 0
  | .sub => 1
  | .part => 2
  | .overlap => 3
  | .properPart => 4
  | .functionsAs => 5
  | .constitutedBy => 6
  | .inheresIn => 7
  | .foundedBy => 8
  | .quaIndividualOf => 9
  | .mediates => 10
  | .characterization => 11
  | .associatedWith => 12
  | .hasValue => 13
  | .memberOf => 14
  | .manifests => 15
  | .lifeOf => 16
  | .meet => 17
  | .distanceGreaterEq => 18

def BinaryField.count : Nat := BinaryField.all.size

theorem BinaryField.index_lt_count (field : BinaryField) : field.index < BinaryField.count := by
  cases field <;> native_decide

theorem BinaryField.index_injective : Function.Injective BinaryField.index := by
  intro left right
  cases left <;> cases right <;> native_decide

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

theorem BinaryField.toTableField_injective :
    Function.Injective BinaryField.toTableField := by
  intro left right
  cases left <;> cases right <;> simp [BinaryField.toTableField]

/-- Primitive ternary finite-table fields accepted by the resolved DSL AST. -/
inductive TernaryField where
  | distance | distanceSum
  deriving Repr, Inhabited, DecidableEq, BEq

def TernaryField.all : Array TernaryField := #[.distance, .distanceSum]

def TernaryField.index : TernaryField → Nat
  | .distance => 0
  | .distanceSum => 1

def TernaryField.count : Nat := TernaryField.all.size

theorem TernaryField.index_lt_count (field : TernaryField) : field.index < TernaryField.count := by
  cases field <;> native_decide

theorem TernaryField.index_injective : Function.Injective TernaryField.index := by
  intro left right
  cases left <;> cases right <;> native_decide

/-- Finite table field name for a ternary AST field. -/
def TernaryField.toTableField : TernaryField → String
  | .distance => "distance"
  | .distanceSum => "distanceSum"

theorem TernaryField.toTableField_injective :
    Function.Injective TernaryField.toTableField := by
  intro left right
  cases left <;> cases right <;> simp [TernaryField.toTableField]


end LeanUfo.UFO.DSL
