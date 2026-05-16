import Lean
import LeanUfo.UFO.DSL.Compiler

/-!
# Textual model helpers for the finite UFO DSL

This module owns name translation and text rendering for finite DSL facts.  It
maps user-facing relation names to compiler fields, renders compiler fields back
to DSL labels, and builds the Lean source for generated `ModelAST` declarations.
It intentionally does not elaborate commands or prove certificates.
-/

open Lean

namespace LeanUfo.UFO.DSL

def derivedUnaryField? (p : Name) : Option String :=
  match p.toString with
  | "Quality" => some "Quality"
  | "ExternallyDependentMode" => some "ExternallyDependentMode"
  | "QuaIndividual" => some "QuaIndividual"
  | "NonEmptySet" => some "NonEmptySet"
  | "QualityStructure" => some "QualityStructure"
  | "SimpleQuality" => some "SimpleQuality"
  | "ComplexQuality" => some "ComplexQuality"
  | "SimpleQualityType" => some "SimpleQualityType"
  | "ComplexQualityType" => some "ComplexQualityType"
  | _ => none

def derivedBinaryField? (p : Name) : Option String :=
  match p.toString with
  | "ProperSub" => some "ProperSub"
  | "GenericFunctionalDependence" => some "GenericFunctionalDependence"
  | "GenericConstitutionalDependence" => some "GenericConstitutionalDependence"
  | "ExistentialDependence" => some "ExistentialDependence"
  | "ExistentialIndependence" => some "ExistentialIndependence"
  | "ExternallyDependent" => some "ExternallyDependent"
  | "UltimateBearerOf" => some "UltimateBearerOf"
  | "SubsetOf" => some "SubsetOf"
  | "ProperSubsetOf" => some "ProperSubsetOf"
  | "IsDisjointWith" => some "IsDisjointWith"
  | "Categorizes" => some "Categorizes"
  | _ => none

def derivedTernaryField? (p : Name) : Option String :=
  match p.toString with
  | "IsCompletelyCoveredBy" => some "IsCompletelyCoveredBy"
  | "IsPartitionedInto" => some "IsPartitionedInto"
  | _ => none

def derivedQuaternaryField? (p : Name) : Option String :=
  match p.toString with
  | "IndividualFunctionalDependence" => some "IndividualFunctionalDependence"
  | "ComponentOf" => some "ComponentOf"
  | "Constitution" => some "Constitution"
  | _ => none

def unaryField? (p : Name) : Option UnaryField :=
  match p.toString with
  | "ConcreteIndividual" => some .concreteIndividual
  | "AbstractIndividual" => some .abstractIndividual
  | "Endurant" => some .endurant
  | "Perdurant" => some .perdurant
  | "EndurantType" => some .endurantType
  | "PerdurantType" => some .perdurantType
  | "Rigid" => some .rigid
  | "AntiRigid" => some .antiRigid
  | "SemiRigid" => some .semiRigid
  | "Kind" => some .kind
  | "Sortal" => some .sortal
  | "NonSortal" => some .nonSortal
  | "SubKind" => some .subKind
  | "Phase" => some .phase
  | "Role" => some .role
  | "SemiRigidSortal" => some .semiRigidSortal
  | "Category" => some .category
  | "Mixin" => some .mixin
  | "PhaseMixin" => some .phaseMixin
  | "RoleMixin" => some .roleMixin
  | "Substantial" => some .substantial
  | "Moment" => some .moment
  | "Object" => some .object
  | "Collective" => some .collective
  | "Quantity" => some .quantity
  | "Relator" => some .relator
  | "IntrinsicMoment" => some .intrinsicMoment
  | "Mode" => some .mode
  | "QualityKind" => some .qualityKind
  | "SubstantialType" => some .substantialType
  | "MomentType" => some .momentType
  | "ObjectType" => some .objectType
  | "CollectiveType" => some .collectiveType
  | "QuantityType" => some .quantityType
  | "RelatorType" => some .relatorType
  | "ModeType" => some .modeType
  | "QualityType" => some .qualityType
  | "ObjectKind" => some .objectKind
  | "CollectiveKind" => some .collectiveKind
  | "QuantityKind" => some .quantityKind
  | "RelatorKind" => some .relatorKind
  | "ModeKind" => some .modeKind
  | "Ex" => some .ex
  | "Quale" => some .quale
  | "Set" => some .set_
  | "Set_" => some .set_
  | "QualityDomain" => some .qualityDomain
  | "QualityDimension" => some .qualityDimension
  | "IntrinsicMomentType" => some .intrinsicMomentType
  | "DistanceZero" => some .distanceZero
  | _ => none

def binaryField? (p : Name) : Option BinaryField :=
  match p.toString with
  | "Part" => some .part
  | "Overlap" => some .overlap
  | "ProperPart" => some .properPart
  | "FunctionsAs" => some .functionsAs
  | "ConstitutedBy" => some .constitutedBy
  | "InheresIn" => some .inheresIn
  | "FoundedBy" => some .foundedBy
  | "QuaIndividualOf" => some .quaIndividualOf
  | "Mediates" => some .mediates
  | "Characterization" => some .characterization
  | "AssociatedWith" => some .associatedWith
  | "HasValue" => some .hasValue
  | "MemberOf" => some .memberOf
  | "Manifests" => some .manifests
  | "LifeOf" => some .lifeOf
  | "Meet" => some .meet
  | "DistanceGreaterEq" => some .distanceGreaterEq
  | _ => none

def ternaryField? (p : Name) : Option TernaryField :=
  match p.toString with
  | "Distance" => some .distance
  | "DistanceSum" => some .distanceSum
  | _ => none

def dataField (name value : String) : String :=
  s!"  {name} := {value}\n"

def unaryFieldTerm : UnaryField → String
  | .concreteIndividual => ".concreteIndividual"
  | .abstractIndividual => ".abstractIndividual"
  | .endurant => ".endurant"
  | .perdurant => ".perdurant"
  | .endurantType => ".endurantType"
  | .perdurantType => ".perdurantType"
  | .rigid => ".rigid"
  | .antiRigid => ".antiRigid"
  | .semiRigid => ".semiRigid"
  | .kind => ".kind"
  | .sortal => ".sortal"
  | .nonSortal => ".nonSortal"
  | .subKind => ".subKind"
  | .phase => ".phase"
  | .role => ".role"
  | .semiRigidSortal => ".semiRigidSortal"
  | .category => ".category"
  | .mixin => ".mixin"
  | .phaseMixin => ".phaseMixin"
  | .roleMixin => ".roleMixin"
  | .substantial => ".substantial"
  | .moment => ".moment"
  | .object => ".object"
  | .collective => ".collective"
  | .quantity => ".quantity"
  | .relator => ".relator"
  | .intrinsicMoment => ".intrinsicMoment"
  | .mode => ".mode"
  | .qualityKind => ".qualityKind"
  | .substantialType => ".substantialType"
  | .momentType => ".momentType"
  | .objectType => ".objectType"
  | .collectiveType => ".collectiveType"
  | .quantityType => ".quantityType"
  | .relatorType => ".relatorType"
  | .modeType => ".modeType"
  | .qualityType => ".qualityType"
  | .objectKind => ".objectKind"
  | .collectiveKind => ".collectiveKind"
  | .quantityKind => ".quantityKind"
  | .relatorKind => ".relatorKind"
  | .modeKind => ".modeKind"
  | .ex => ".ex"
  | .quale => ".quale"
  | .set_ => ".set_"
  | .qualityDomain => ".qualityDomain"
  | .qualityDimension => ".qualityDimension"
  | .intrinsicMomentType => ".intrinsicMomentType"
  | .distanceZero => ".distanceZero"

def binaryFieldTerm : BinaryField → String
  | .inst => ".inst"
  | .sub => ".sub"
  | .part => ".part"
  | .overlap => ".overlap"
  | .properPart => ".properPart"
  | .functionsAs => ".functionsAs"
  | .constitutedBy => ".constitutedBy"
  | .inheresIn => ".inheresIn"
  | .foundedBy => ".foundedBy"
  | .quaIndividualOf => ".quaIndividualOf"
  | .mediates => ".mediates"
  | .characterization => ".characterization"
  | .associatedWith => ".associatedWith"
  | .hasValue => ".hasValue"
  | .memberOf => ".memberOf"
  | .manifests => ".manifests"
  | .lifeOf => ".lifeOf"
  | .meet => ".meet"
  | .distanceGreaterEq => ".distanceGreaterEq"

def ternaryFieldTerm : TernaryField → String
  | .distance => ".distance"
  | .distanceSum => ".distanceSum"

def UnaryField.toSurfaceName (field : UnaryField) : String :=
  match field with
  | .concreteIndividual => "ConcreteIndividual"
  | .abstractIndividual => "AbstractIndividual"
  | .endurant => "Endurant"
  | .perdurant => "Perdurant"
  | .endurantType => "EndurantType"
  | .perdurantType => "PerdurantType"
  | .rigid => "Rigid"
  | .antiRigid => "AntiRigid"
  | .semiRigid => "SemiRigid"
  | .kind => "Kind"
  | .sortal => "Sortal"
  | .nonSortal => "NonSortal"
  | .subKind => "SubKind"
  | .phase => "Phase"
  | .role => "Role"
  | .semiRigidSortal => "SemiRigidSortal"
  | .category => "Category"
  | .mixin => "Mixin"
  | .phaseMixin => "PhaseMixin"
  | .roleMixin => "RoleMixin"
  | .substantial => "Substantial"
  | .moment => "Moment"
  | .object => "Object"
  | .collective => "Collective"
  | .quantity => "Quantity"
  | .relator => "Relator"
  | .intrinsicMoment => "IntrinsicMoment"
  | .mode => "Mode"
  | .qualityKind => "QualityKind"
  | .substantialType => "SubstantialType"
  | .momentType => "MomentType"
  | .objectType => "ObjectType"
  | .collectiveType => "CollectiveType"
  | .quantityType => "QuantityType"
  | .relatorType => "RelatorType"
  | .modeType => "ModeType"
  | .qualityType => "QualityType"
  | .objectKind => "ObjectKind"
  | .collectiveKind => "CollectiveKind"
  | .quantityKind => "QuantityKind"
  | .relatorKind => "RelatorKind"
  | .modeKind => "ModeKind"
  | .ex => "Ex"
  | .quale => "Quale"
  | .set_ => "Set"
  | .qualityDomain => "QualityDomain"
  | .qualityDimension => "QualityDimension"
  | .intrinsicMomentType => "IntrinsicMomentType"
  | .distanceZero => "DistanceZero"

def BinaryField.toSurfaceName (field : BinaryField) : String :=
  match field with
  | .inst => "Inst"
  | .sub => "Sub"
  | .part => "Part"
  | .overlap => "Overlap"
  | .properPart => "ProperPart"
  | .functionsAs => "FunctionsAs"
  | .constitutedBy => "ConstitutedBy"
  | .inheresIn => "InheresIn"
  | .foundedBy => "FoundedBy"
  | .quaIndividualOf => "QuaIndividualOf"
  | .mediates => "Mediates"
  | .characterization => "Characterization"
  | .associatedWith => "AssociatedWith"
  | .hasValue => "HasValue"
  | .memberOf => "MemberOf"
  | .manifests => "Manifests"
  | .lifeOf => "LifeOf"
  | .meet => "Meet"
  | .distanceGreaterEq => "DistanceGreaterEq"

def TernaryField.toSurfaceName (field : TernaryField) : String :=
  match field with
  | .distance => "Distance"
  | .distanceSum => "DistanceSum"

def leanStringLit (s : String) : String :=
  reprStr s

def compiledFactTerm : CompiledFact → String
  | .unary field x w => s!"CompiledFact.unary {unaryFieldTerm field} {x} {w}"
  | .binary field x y w => s!"CompiledFact.binary {binaryFieldTerm field} {x} {y} {w}"
  | .ternary field x y z w => s!"CompiledFact.ternary {ternaryFieldTerm field} {x} {y} {z} {w}"
  | .tupleProjection tuple index result w => s!"CompiledFact.tupleProjection {tuple} {index} {result} {w}"
  | .derived prop => s!"CompiledFact.derived {leanStringLit prop}"

def natArrayTerm (xs : Array Nat) : String :=
  if xs.isEmpty then
    "#[]"
  else
    "#[" ++ String.intercalate ", " (xs.toList.map toString) ++ "]"

def productFamilyTerm (family : ProductFamilySpec) : String :=
    "{ " ++
    s!"domain := {family.domain}, " ++
    s!"qualityType := {family.qualityType}, " ++
    s!"dimensionThings := {natArrayTerm family.dimensionThings}, " ++
    s!"typeThings := {natArrayTerm family.typeThings}" ++
    " }"

def indexedNamesJson (names : Array Name) : Json :=
  Json.arr <| names.mapIdx fun idx name =>
    Json.mkObj [
      ("name", name.toString),
      ("index", idx)
    ]

def indexedName (names : Array Name) (idx : Nat) : String :=
  match names[idx]? with
  | some name => name.toString
  | none => s!"#{idx}"

def namedScopeSummary : NamedFactScope → String
  | .at world => world
  | .everywhere => "everywhere"

def namedDerivedFactSummary : NamedDerivedFact → String
  | .unary field thing => s!"{field}({thing})"
  | .binary field left right => s!"{field}({left}, {right})"
  | .ternary field first second third => s!"{field}({first}, {second}, {third})"
  | .quaternary field first second third fourth =>
      s!"{field}({first}, {second}, {third}, {fourth})"

def scopedWorldNames (worldNames : Array Name) : NamedFactScope → Array String
  | .at world => #[world]
  | .everywhere => worldNames.map (·.toString)

def namedFactSummary : NamedScopedFact → String
  | .unary field thing scope =>
      s!"[{namedScopeSummary scope}] {field.toSurfaceName}({thing})"
  | .binary .inst left right scope =>
      s!"[{namedScopeSummary scope}] {left} :: {right}"
  | .binary .sub left right scope =>
      s!"[{namedScopeSummary scope}] {left} ⊑ {right}"
  | .binary field left right scope =>
      s!"[{namedScopeSummary scope}] {field.toSurfaceName}({left}, {right})"
  | .ternary field first second third scope =>
      s!"[{namedScopeSummary scope}] {field.toSurfaceName}({first}, {second}, {third})"
  | .tupleProjection tuple index result scope =>
      s!"[{namedScopeSummary scope}] TupleProjection({tuple}, {index}, {result})"
  | .derived fact scope =>
      s!"[{namedScopeSummary scope}] {namedDerivedFactSummary fact}"

def derivedPropSummaryPairs
    (worldNames : Array Name)
    (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) : Array (String × String) :=
  Id.run do
    let mut out := #[]
    for i in [:namedFacts.size] do
      match namedFacts[i]?, scopedFacts[i]? with
      | some (.derived named scope), some (.derived propAtWorld resolvedScope) =>
          let worldIdxs : Array Nat :=
            match resolvedScope with
            | .at w => #[w]
            | .everywhere => (Array.range worldNames.size)
          let worldLabels := scopedWorldNames worldNames scope
          for j in [:worldIdxs.size] do
            let w := worldIdxs[j]!
            let worldLabel := worldLabels[j]?.getD (indexedName worldNames w)
            out := out.push (propAtWorld w, s!"[{worldLabel}] {namedDerivedFactSummary named}")
      | _, _ => pure ()
    pure out

def derivedPropSummary (pairs : Array (String × String)) (prop : String) : Option String :=
  pairs.findSome? fun pair =>
    if pair.1 == prop then some pair.2 else none

def compiledFactSummary
    (worldNames thingNames : Array Name) (derivedPairs : Array (String × String)) :
    CompiledFact → String
  | .unary field thing world =>
      s!"[{indexedName worldNames world}] {field.toSurfaceName}({indexedName thingNames thing})"
  | .binary .inst left right world =>
      s!"[{indexedName worldNames world}] {indexedName thingNames left} :: {indexedName thingNames right}"
  | .binary .sub left right world =>
      s!"[{indexedName worldNames world}] {indexedName thingNames left} ⊑ {indexedName thingNames right}"
  | .binary field left right world =>
      s!"[{indexedName worldNames world}] {field.toSurfaceName}({indexedName thingNames left}, {indexedName thingNames right})"
  | .ternary field first second third world =>
      s!"[{indexedName worldNames world}] {field.toSurfaceName}({indexedName thingNames first}, {indexedName thingNames second}, {indexedName thingNames third})"
  | .tupleProjection tuple index result world =>
      s!"[{indexedName worldNames world}] TupleProjection({indexedName thingNames tuple}, {index}, {indexedName thingNames result})"
  | .derived prop => (derivedPropSummary derivedPairs prop).getD prop

def stringsJson (xs : Array String) : Json :=
  Json.arr <| xs.map Json.str

def modelASTSource
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (productFamilies : Array ProductFamilySpec := #[]) : String :=
  let factTerms := facts.map compiledFactTerm
  let factArray :=
    if factTerms.isEmpty then
      "#[]"
    else
      "#[" ++ String.intercalate ", " factTerms.toList ++ "]"
  let productFamilyTerms := productFamilies.map productFamilyTerm
  let productFamilyArray :=
    if productFamilyTerms.isEmpty then
      "#[]"
    else
      "#[" ++ String.intercalate ", " productFamilyTerms.toList ++ "]"
  "def ast : ModelAST :=\n" ++
    "{\n" ++
    dataField "worldCount" (toString worldCount) ++
    dataField "thingCount" (toString thingCount) ++
    dataField "facts" factArray ++
    dataField "productFamilies" productFamilyArray ++
    "}\n"

end LeanUfo.UFO.DSL
