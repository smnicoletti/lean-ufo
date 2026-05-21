import Lean
import LeanUfo.UFO.DSL.Compiler
import LeanUfo.UFO.DSL.Frontend.ModelText

/-!
# Source-level diagnostics for finite UFO DSL models

This module reconstructs explanatory evidence from compiled finite tables after
a generated certificate fails.  Diagnostics are intentionally separate from the
trusted certificate path: they render counterexamples, missing assertions, and
source-level suggestions, but they are not proof obligations.
-/

open Lean

namespace LeanUfo.UFO.DSL

/-!
## Diagnostic formula language

The small formula language below mirrors selected UFO axiom shapes over finite
tables.  It lets diagnostics evaluate an axiom-like condition, minimize the
failing subformula, and render the result in DSL terms.
-/

private inductive DiagVarKind where
  | thing | world
  deriving Repr, Inhabited, DecidableEq

private structure DiagVar where
  name : String
  kind : DiagVarKind
  deriving Repr, Inhabited

/--
Small first-order diagnostic language used only by the widget.

The formulas below mirror selected UFO axioms over the generated finite tables.
They are deliberately separate from the trusted axiom statements: they are for
counterexample localization and user-facing explanations, not for certification.
-/
private inductive DiagAtom where
  | typeSem (thing world : String)
  | individualSem (thing world : String)
  | unary (field : UnaryField) (thing world : String)
  | derivedUnary (field thing world : String)
  | binary (field : BinaryField) (left right world : String)
  | ternary (field : TernaryField) (first second third world : String)
  | derivedBinary (field left right world : String)
  | quaternary (field first second third fourth world : String)
  deriving Repr, Inhabited

private inductive DiagFormula where
  | atom (atom : DiagAtom)
  | eqThing (left right : String)
  | eqWorld (left right : String)
  | not (p : DiagFormula)
  | and (p q : DiagFormula)
  | or (p q : DiagFormula)
  | imp (p q : DiagFormula)
  | iff (p q : DiagFormula)
  | forallThing (name : String) (body : DiagFormula)
  | forallWorld (name : String) (body : DiagFormula)
  | existsThing (name : String) (body : DiagFormula)
  | existsWorld (name : String) (body : DiagFormula)
  | box (currentWorld witnessWorld : String) (body : DiagFormula)
  | dia (currentWorld witnessWorld : String) (body : DiagFormula)
  deriving Repr, Inhabited

private def DiagFormula.forallVars : DiagFormula → Array DiagVar
  | .forallThing name body => #[⟨name, .thing⟩] ++ body.forallVars
  | .forallWorld name body => #[⟨name, .world⟩] ++ body.forallVars
  | _ => #[]

private def DiagFormula.stripForalls : DiagFormula → DiagFormula
  | .forallThing _ body => body.stripForalls
  | .forallWorld _ body => body.stripForalls
  | formula => formula

private def lookupVar (env : Array (String × Nat)) (name : String) : Nat :=
  (env.foldl
    (fun found entry => if entry.1 == name then some entry.2 else found)
    none).getD 0

private def diagFinThingTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)"

private def diagFinWorldTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.worldCount)"

private def hasPossibleInstance
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) : Bool :=
  Id.run do
    for w in [:worldCount] do
      for x in [:thingCount] do
        if tables.binaryLookup "inst" x thing w then
          return true
    return false

private def boxExImpLookup
    (worldCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  Id.run do
    for w in [:worldCount] do
      if tables.unaryLookup "ex" x w && !tables.unaryLookup "ex" y w then
        return false
    return true

private def existentialDependenceLookup
    (worldCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  boxExImpLookup worldCount tables x y

private def existentialIndependenceLookup
    (worldCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  !existentialDependenceLookup worldCount tables x y &&
    !existentialDependenceLookup worldCount tables y x

private def externallyDependentLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) : Bool :=
  boxExImpLookup worldCount tables x y &&
    Id.run do
      for z in [:thingCount] do
        if tables.binaryLookup "inheresIn" x z w then
          let yWithoutZ := Id.run do
            for w' in [:worldCount] do
              if tables.unaryLookup "ex" y w' && !tables.unaryLookup "ex" z w' then
                return true
            return false
          let zWithoutY := Id.run do
            for w' in [:worldCount] do
              if tables.unaryLookup "ex" z w' && !tables.unaryLookup "ex" y w' then
                return true
            return false
          if !(yWithoutZ && zWithoutY) then
            return false
      return true

private def externallyDependentModeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  tables.unaryLookup "mode" x w &&
    Id.run do
      for y in [:thingCount] do
        if externallyDependentLookup worldCount thingCount tables x y w then
          return true
      return false

private def genericFunctionalDependenceLookup
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x x' w && tables.binaryLookup "functionsAs" x x' w then
        let found := Id.run do
          for y in [:thingCount] do
            if y != x && tables.binaryLookup "inst" y y' w &&
                tables.binaryLookup "functionsAs" y y' w then
              return true
          return false
        if !found then
          return false
    return true

private def individualFunctionalDependenceLookup
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  genericFunctionalDependenceLookup thingCount tables x' y' w &&
    tables.binaryLookup "inst" x x' w &&
    tables.binaryLookup "inst" y y' w &&
    (!tables.binaryLookup "functionsAs" x x' w ||
      tables.binaryLookup "functionsAs" y y' w)

private def componentOfLookup
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  tables.binaryLookup "properPart" x y w &&
    individualFunctionalDependenceLookup thingCount tables x x' y y' w

private def genericConstitutionalDependenceLookup
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x x' w then
        let found := Id.run do
          for y in [:thingCount] do
            if tables.binaryLookup "inst" y y' w &&
                tables.binaryLookup "constitutedBy" x y w then
              return true
          return false
        if !found then
          return false
    return true

private def constitutionLookup
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  tables.binaryLookup "inst" x x' w &&
    tables.binaryLookup "inst" y y' w &&
    genericConstitutionalDependenceLookup thingCount tables x' y' w &&
    tables.binaryLookup "constitutedBy" x y w

private def quaIndividualLookup
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  Id.run do
    for y in [:thingCount] do
      if tables.binaryLookup "quaIndividualOf" x y w then
        return true
    return false

private def derivedUnaryLookup
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) : Bool :=
  match field with
  | "ExternallyDependentMode" => externallyDependentModeLookup worldCount thingCount tables x w
  | "QuaIndividual" => quaIndividualLookup thingCount tables x w
  | _ =>
      tables.derivedProps.any fun prop =>
        prop == s!"sig.{field} {diagFinThingTerm x} {diagFinWorldTerm w}"

private def derivedBinaryLookup
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x y w : Nat) : Bool :=
  match field with
  | "ExistentialDependence" => existentialDependenceLookup worldCount tables x y
  | "ExistentialIndependence" => existentialIndependenceLookup worldCount tables x y
  | "ExternallyDependent" => externallyDependentLookup worldCount thingCount tables x y w
  | "GenericFunctionalDependence" => genericFunctionalDependenceLookup thingCount tables x y w
  | "GenericConstitutionalDependence" => genericConstitutionalDependenceLookup thingCount tables x y w
  | _ =>
      tables.derivedProps.any fun prop =>
        prop == s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}"

private def assertedDerivedBinaryLookup
    (tables : FactTables) (field : String) (x y w : Nat) : Bool :=
  tables.derivedProps.any fun prop =>
    prop == s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}"

private def evalDiagAtom
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagAtom → Bool
  | .typeSem thing _world =>
      hasPossibleInstance worldCount thingCount tables (lookupVar env thing)
  | .individualSem thing _world =>
      !hasPossibleInstance worldCount thingCount tables (lookupVar env thing)
  | .unary field thing world =>
      tables.unaryLookup field.toTableField (lookupVar env thing) (lookupVar env world)
  | .derivedUnary field thing world =>
      let thingIdx := lookupVar env thing
      let worldIdx := lookupVar env world
      derivedUnaryLookup worldCount thingCount tables field thingIdx worldIdx
  | .binary (.part) left right world =>
      lookupVar env left == lookupVar env right ||
        tables.binaryLookup "part" (lookupVar env left) (lookupVar env right) (lookupVar env world)
  | .binary (.overlap) left right world =>
      lookupVar env left == lookupVar env right ||
        tables.binaryLookup "overlap" (lookupVar env left) (lookupVar env right) (lookupVar env world)
  | .binary field left right world =>
      tables.binaryLookup field.toTableField (lookupVar env left) (lookupVar env right) (lookupVar env world)
  | .ternary field first second third world =>
      tables.ternaryLookup field.toTableField (lookupVar env first) (lookupVar env second)
        (lookupVar env third) (lookupVar env world)
  | .derivedBinary field left right world =>
      let leftIdx := lookupVar env left
      let rightIdx := lookupVar env right
      let worldIdx := lookupVar env world
      derivedBinaryLookup worldCount thingCount tables field leftIdx rightIdx worldIdx
  | .quaternary field first second third fourth world =>
      let firstIdx := lookupVar env first
      let secondIdx := lookupVar env second
      let thirdIdx := lookupVar env third
      let fourthIdx := lookupVar env fourth
      let worldIdx := lookupVar env world
      tables.derivedProps.any fun prop =>
        prop ==
          s!"sig.{field} {diagFinThingTerm firstIdx} {diagFinThingTerm secondIdx} {diagFinThingTerm thirdIdx} {diagFinThingTerm fourthIdx} {diagFinWorldTerm worldIdx}"

private partial def evalDiagFormula
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → Bool
  | .atom atom => evalDiagAtom worldCount thingCount tables env atom
  | .eqThing left right => lookupVar env left == lookupVar env right
  | .eqWorld left right => lookupVar env left == lookupVar env right
  | .not p => !evalDiagFormula worldCount thingCount tables env p
  | .and p q =>
      evalDiagFormula worldCount thingCount tables env p &&
        evalDiagFormula worldCount thingCount tables env q
  | .or p q =>
      evalDiagFormula worldCount thingCount tables env p ||
        evalDiagFormula worldCount thingCount tables env q
  | .imp p q =>
      !evalDiagFormula worldCount thingCount tables env p ||
        evalDiagFormula worldCount thingCount tables env q
  | .iff p q =>
      evalDiagFormula worldCount thingCount tables env p ==
        evalDiagFormula worldCount thingCount tables env q
  | .forallThing name body =>
      Id.run do
        for x in [:thingCount] do
          if !evalDiagFormula worldCount thingCount tables (env.push (name, x)) body then
            return false
        return true
  | .forallWorld name body =>
      Id.run do
        for w in [:worldCount] do
          if !evalDiagFormula worldCount thingCount tables (env.push (name, w)) body then
            return false
        return true
  | .existsThing name body =>
      Id.run do
        for x in [:thingCount] do
          if evalDiagFormula worldCount thingCount tables (env.push (name, x)) body then
            return true
        return false
  | .existsWorld name body =>
      Id.run do
        for w in [:worldCount] do
          if evalDiagFormula worldCount thingCount tables (env.push (name, w)) body then
            return true
        return false
  | .box _currentWorld witnessWorld body =>
      Id.run do
        for w in [:worldCount] do
          if !evalDiagFormula worldCount thingCount tables (env.push (witnessWorld, w)) body then
            return false
        return true
  | .dia _currentWorld witnessWorld body =>
      Id.run do
        for w in [:worldCount] do
          if evalDiagFormula worldCount thingCount tables (env.push (witnessWorld, w)) body then
            return true
        return false

private def enumerateDiagEnvs
    (worldCount thingCount : Nat) (vars : Array DiagVar) : Array (Array (String × Nat)) :=
  vars.foldl
    (fun envs var =>
      Id.run do
        let bound :=
          match var.kind with
          | .thing => thingCount
          | .world => worldCount
        let mut next := #[]
        for env in envs do
          for i in [:bound] do
            next := next.push (env.push (var.name, i))
        return next)
    #[#[]]

private def unaryFieldDslLabel : UnaryField → String
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

private def binaryFieldDslLabel : BinaryField → String
  | .inst => "::"
  | .sub => "⊑"
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

private def ternaryFieldDslLabel : TernaryField → String
  | .distance => "Distance"
  | .distanceSum => "DistanceSum"

private def renderDiagAtom
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) : DiagAtom → String
  | .typeSem thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] Type({indexedName thingNames (lookupVar env thing)})"
  | .individualSem thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] Individual({indexedName thingNames (lookupVar env thing)})"
  | .unary field thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {unaryFieldDslLabel field}({indexedName thingNames (lookupVar env thing)})"
  | .derivedUnary field thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {field}({indexedName thingNames (lookupVar env thing)})"
  | .binary .inst left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {indexedName thingNames (lookupVar env left)} :: {indexedName thingNames (lookupVar env right)}"
  | .binary .sub left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {indexedName thingNames (lookupVar env left)} ⊑ {indexedName thingNames (lookupVar env right)}"
  | .binary field left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {binaryFieldDslLabel field}({indexedName thingNames (lookupVar env left)}, {indexedName thingNames (lookupVar env right)})"
  | .ternary field first second third world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {ternaryFieldDslLabel field}({indexedName thingNames (lookupVar env first)}, {indexedName thingNames (lookupVar env second)}, {indexedName thingNames (lookupVar env third)})"
  | .derivedBinary field left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {field}({indexedName thingNames (lookupVar env left)}, {indexedName thingNames (lookupVar env right)})"
  | .quaternary field first second third fourth world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {field}({indexedName thingNames (lookupVar env first)}, {indexedName thingNames (lookupVar env second)}, {indexedName thingNames (lookupVar env third)}, {indexedName thingNames (lookupVar env fourth)})"

private partial def renderDiagFormula
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) : DiagFormula → String
  | .atom atom => renderDiagAtom worldNames thingNames env atom
  | .eqThing left right =>
      s!"{indexedName thingNames (lookupVar env left)} = {indexedName thingNames (lookupVar env right)}"
  | .eqWorld left right =>
      s!"{indexedName worldNames (lookupVar env left)} = {indexedName worldNames (lookupVar env right)}"
  | .not p => s!"not ({renderDiagFormula worldNames thingNames env p})"
  | .and p q => s!"({renderDiagFormula worldNames thingNames env p}) and ({renderDiagFormula worldNames thingNames env q})"
  | .or p q => s!"({renderDiagFormula worldNames thingNames env p}) or ({renderDiagFormula worldNames thingNames env q})"
  | .imp p q => s!"({renderDiagFormula worldNames thingNames env p}) implies ({renderDiagFormula worldNames thingNames env q})"
  | .iff p q => s!"({renderDiagFormula worldNames thingNames env p}) iff ({renderDiagFormula worldNames thingNames env q})"
  | .forallThing name body => s!"for every thing {name}, {renderDiagFormula worldNames thingNames env body}"
  | .forallWorld name body => s!"for every world {name}, {renderDiagFormula worldNames thingNames env body}"
  | .existsThing name body => s!"there exists thing {name}, {renderDiagFormula worldNames thingNames env body}"
  | .existsWorld name body => s!"there exists world {name}, {renderDiagFormula worldNames thingNames env body}"
  | .box currentWorld witnessWorld body =>
      s!"from world {indexedName worldNames (lookupVar env currentWorld)}, in every accessible world {witnessWorld}, {renderDiagFormula worldNames thingNames env body}"
  | .dia currentWorld witnessWorld body =>
      s!"from world {indexedName worldNames (lookupVar env currentWorld)}, in some accessible world {witnessWorld}, {renderDiagFormula worldNames thingNames env body}"

private partial def flattenDiagAnd : DiagFormula → Array DiagFormula
  | .and p q => flattenDiagAnd p ++ flattenDiagAnd q
  | p => #[p]

private partial def flattenDiagOr : DiagFormula → Array DiagFormula
  | .or p q => flattenDiagOr p ++ flattenDiagOr q
  | p => #[p]

private def formulaHasDistinctnessRequirement : DiagFormula → Bool
  | .not (.eqThing _ _) => true
  | .not (.eqWorld _ _) => true
  | _ => false

private def diagnosticConditionLabel (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ => "Need one of"
  | .not _ => "Forbidden condition"
  | .atom _ => "Required but missing"
  | .eqThing _ _ => "Required but missing"
  | .eqWorld _ _ => "Required but missing"
  | .and _ _ =>
      if (flattenDiagAnd formula).any formulaHasDistinctnessRequirement then
        "Missing witness requirements"
      else
        "Required together"
  | .existsThing _ _ => "Missing witness requirements"
  | .existsWorld _ _ => "Missing witness requirements"
  | _ => "Failed condition"

private def renderDiagnosticCondition
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ =>
      String.intercalate "\n" <|
        (flattenDiagOr formula).toList.map fun option =>
          s!"- {renderDiagFormula worldNames thingNames env option}"
  | .and _ _ =>
      String.intercalate "\n" <|
        (flattenDiagAnd formula).toList.map fun requirement =>
          s!"- {renderDiagFormula worldNames thingNames env requirement}"
  | _ => renderDiagFormula worldNames thingNames env formula

private def envSummary
    (worldNames thingNames : Array Name) (vars : Array DiagVar) (env : Array (String × Nat)) :
    String :=
  String.intercalate ", " <| vars.toList.map fun var =>
    let idx := lookupVar env var.name
    match var.kind with
    | .thing => s!"{var.name} = {indexedName thingNames idx}"
    | .world => s!"{var.name} = {indexedName worldNames idx}"

private def envVarKind? (outerVars : Array DiagVar) (name : String) : Option DiagVarKind :=
  outerVars.findSome? fun var =>
    if var.name == name then some var.kind else none

private partial def formulaBoundVarKinds (formula : DiagFormula) : Array DiagVar :=
  match formula with
  | .atom _ => #[]
  | .eqThing _ _ => #[]
  | .eqWorld _ _ => #[]
  | .not p => formulaBoundVarKinds p
  | .and p q => formulaBoundVarKinds p ++ formulaBoundVarKinds q
  | .or p q => formulaBoundVarKinds p ++ formulaBoundVarKinds q
  | .imp p q => formulaBoundVarKinds p ++ formulaBoundVarKinds q
  | .iff p q => formulaBoundVarKinds p ++ formulaBoundVarKinds q
  | .forallThing name body => #[⟨name, .thing⟩] ++ formulaBoundVarKinds body
  | .forallWorld name body => #[⟨name, .world⟩] ++ formulaBoundVarKinds body
  | .existsThing name body => #[⟨name, .thing⟩] ++ formulaBoundVarKinds body
  | .existsWorld name body => #[⟨name, .world⟩] ++ formulaBoundVarKinds body
  | .box _ witnessWorld body => #[⟨witnessWorld, .world⟩] ++ formulaBoundVarKinds body
  | .dia _ witnessWorld body => #[⟨witnessWorld, .world⟩] ++ formulaBoundVarKinds body

private def diagnosticEnvVars (outerVars : Array DiagVar) (formula : DiagFormula)
    (env : Array (String × Nat)) : Array DiagVar :=
  Id.run do
    let candidates := outerVars ++ formulaBoundVarKinds formula
    let mut seen : Std.HashSet String := {}
    let mut out := #[]
    for entry in env do
      let name := entry.1
      if !seen.contains name then
        match envVarKind? candidates name with
        | some kind =>
            out := out.push ⟨name, kind⟩
            seen := seen.insert name
        | none => pure ()
    return out

private def firstFailureEnv
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) : Option (Array (String × Nat)) :=
  Id.run do
    let bound :=
      match kind with
      | .thing => thingCount
      | .world => worldCount
    for i in [:bound] do
      let env' := env.push (name, i)
      if !evalDiagFormula worldCount thingCount tables env' body then
        return some env'
    return none

private def firstSuccessEnv
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) : Option (Array (String × Nat)) :=
  Id.run do
    let bound :=
      match kind with
      | .thing => thingCount
      | .world => worldCount
    for i in [:bound] do
      let env' := env.push (name, i)
      if evalDiagFormula worldCount thingCount tables env' body then
        return some env'
    return none

private structure DiagTrace where
  formula : DiagFormula
  env : Array (String × Nat)
  deriving Inhabited

private structure MinimizedFailure where
  formula : DiagFormula
  env : Array (String × Nat)
  context : Array DiagTrace
  deriving Inhabited

private def failedHere (formula : DiagFormula) (env : Array (String × Nat)) :
    MinimizedFailure :=
  { formula, env, context := #[] }

private def withContext (context : Array DiagTrace) (failure : MinimizedFailure) :
    MinimizedFailure :=
  { failure with context := context ++ failure.context }

/--
Collect subformulas that succeeded on the current path to a failure.

The rendered diagnostic should not only say what is missing; it should also show
why the missing obligation applied.  These traces become the evidence section of
the widget and are deliberately explanatory rather than trusted proof data.
-/
private partial def successTraces
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Array DiagTrace :=
  if !evalDiagFormula worldCount thingCount tables env formula then
    #[]
  else
    match formula with
    | .atom _ => #[⟨formula, env⟩]
    | .eqThing _ _ => #[⟨formula, env⟩]
    | .eqWorld _ _ => #[⟨formula, env⟩]
    | .not _ => #[⟨formula, env⟩]
    | .and p q =>
        successTraces worldCount thingCount tables env p ++
          successTraces worldCount thingCount tables env q
    | .or p q =>
        if evalDiagFormula worldCount thingCount tables env p then
          successTraces worldCount thingCount tables env p
        else
          successTraces worldCount thingCount tables env q
    | .imp p q =>
        if evalDiagFormula worldCount thingCount tables env p then
          successTraces worldCount thingCount tables env q
        else
          #[⟨formula, env⟩]
    | .iff _ _ => #[⟨formula, env⟩]
    | .forallThing _ _ => #[⟨formula, env⟩]
    | .forallWorld _ _ => #[⟨formula, env⟩]
    | .existsThing name body =>
        match firstSuccessEnv worldCount thingCount tables env .thing name body with
        | some env' => successTraces worldCount thingCount tables env' body
        | none => #[⟨formula, env⟩]
    | .existsWorld name body =>
        match firstSuccessEnv worldCount thingCount tables env .world name body with
        | some env' => successTraces worldCount thingCount tables env' body
        | none => #[⟨formula, env⟩]
    | .box _ _ _ => #[⟨formula, env⟩]
    | .dia _ witnessWorld body =>
        match firstSuccessEnv worldCount thingCount tables env .world witnessWorld body with
        | some env' => successTraces worldCount thingCount tables env' body
        | none => #[⟨formula, env⟩]

/--
Find the smallest useful failed subformula for a counterexample environment.

For implications and biconditionals this keeps the successful antecedent/context
beside the failing consequent. For quantifiers and modal boxes it also records
the witness assignment that makes the failure concrete in DSL names.
-/
private partial def minimizeFailure
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → MinimizedFailure
  | formula@(.atom _) => failedHere formula env
  | formula@(.eqThing _ _) => failedHere formula env
  | formula@(.eqWorld _ _) => failedHere formula env
  | formula@(.not p) =>
      if evalDiagFormula worldCount thingCount tables env formula then
        failedHere formula env
      else
        match p with
        | .not q => minimizeFailure worldCount thingCount tables env q
        | .forallThing name body =>
            match firstFailureEnv worldCount thingCount tables env .thing name body with
            | some env' => minimizeFailure worldCount thingCount tables env' body
            | none => failedHere formula env
        | .forallWorld name body =>
            match firstFailureEnv worldCount thingCount tables env .world name body with
            | some env' => minimizeFailure worldCount thingCount tables env' body
            | none => failedHere formula env
        | .existsThing name body =>
            match firstSuccessEnv worldCount thingCount tables env .thing name body with
            | some env' => minimizeFailure worldCount thingCount tables env' body
            | none => failedHere formula env
        | .existsWorld name body =>
            match firstSuccessEnv worldCount thingCount tables env .world name body with
            | some env' => minimizeFailure worldCount thingCount tables env' body
            | none => failedHere formula env
        | .box _ witnessWorld body =>
            match firstFailureEnv worldCount thingCount tables env .world witnessWorld body with
            | some env' => minimizeFailure worldCount thingCount tables env' body
            | none => failedHere formula env
        | .dia _ witnessWorld body =>
            match firstSuccessEnv worldCount thingCount tables env .world witnessWorld body with
            | some env' => minimizeFailure worldCount thingCount tables env' body
            | none => failedHere formula env
        | _ => failedHere formula env
  | formula@(.and p q) =>
      if !evalDiagFormula worldCount thingCount tables env p then
        minimizeFailure worldCount thingCount tables env p
      else if !evalDiagFormula worldCount thingCount tables env q then
        withContext
          (successTraces worldCount thingCount tables env p)
          (minimizeFailure worldCount thingCount tables env q)
      else
        failedHere formula env
  | formula@(.or p q) =>
      if evalDiagFormula worldCount thingCount tables env formula then
        failedHere formula env
      else
        let pFailure := minimizeFailure worldCount thingCount tables env p
        let qFailure := minimizeFailure worldCount thingCount tables env q
        {
          formula := .or pFailure.formula qFailure.formula,
          env := pFailure.env ++ qFailure.env,
          context := pFailure.context ++ qFailure.context
        }
  | formula@(.imp p q) =>
      if evalDiagFormula worldCount thingCount tables env formula then
        failedHere formula env
      else
        withContext
          (successTraces worldCount thingCount tables env p)
          (minimizeFailure worldCount thingCount tables env q)
  | formula@(.iff p q) =>
      if evalDiagFormula worldCount thingCount tables env formula then
        failedHere formula env
      else if evalDiagFormula worldCount thingCount tables env p then
        withContext
          (successTraces worldCount thingCount tables env p)
          (minimizeFailure worldCount thingCount tables env q)
      else if evalDiagFormula worldCount thingCount tables env q then
        withContext
          (successTraces worldCount thingCount tables env q)
          (minimizeFailure worldCount thingCount tables env p)
      else
        failedHere formula env
  | formula@(.forallThing name body) =>
      let candidate? := firstFailureEnv worldCount thingCount tables env .thing name body
      match candidate? with
      | some env' => minimizeFailure worldCount thingCount tables env' body
      | none => failedHere formula env
  | formula@(.forallWorld name body) =>
      let candidate? := firstFailureEnv worldCount thingCount tables env .world name body
      match candidate? with
      | some env' => minimizeFailure worldCount thingCount tables env' body
      | none => failedHere formula env
  | formula@(.existsThing name body) =>
      if evalDiagFormula worldCount thingCount tables env formula then
        match firstSuccessEnv worldCount thingCount tables env .thing name body with
        | some env' => minimizeFailure worldCount thingCount tables env' body
        | none => failedHere formula env
      else
        failedHere formula env
  | formula@(.existsWorld name body) =>
      if evalDiagFormula worldCount thingCount tables env formula then
        match firstSuccessEnv worldCount thingCount tables env .world name body with
        | some env' => minimizeFailure worldCount thingCount tables env' body
        | none => failedHere formula env
      else
        failedHere formula env
  | formula@(.box _ witnessWorld body) =>
      let candidate? := firstFailureEnv worldCount thingCount tables env .world witnessWorld body
      match candidate? with
      | some env' => minimizeFailure worldCount thingCount tables env' body
      | none => failedHere formula env
  | formula@(.dia _ witnessWorld body) =>
      if evalDiagFormula worldCount thingCount tables env formula then
        match firstSuccessEnv worldCount thingCount tables env .world witnessWorld body with
        | some env' => minimizeFailure worldCount thingCount tables env' body
        | none => failedHere formula env
      else
        failedHere formula env

private def scopeCoversWorld (worldNames : Array Name) (scope : NamedFactScope) (worldIdx : Nat) :
    Bool :=
  match scope with
  | .everywhere => true
  | .at world => world == indexedName worldNames worldIdx

private def unaryFactImplies (source target : UnaryField) : Bool :=
  (expandUnaryTaxonomyFact source 0 0).any fun
    | .unary field _ _ => field == target
    | _ => false

private def unaryEvidence
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) : Array String :=
  let thing := indexedName thingNames thingIdx
  Id.run do
    let mut out := #[]
    for fact in namedFacts do
      match fact with
      | .unary sourceField sourceThing scope =>
          if sourceThing == thing && scopeCoversWorld worldNames scope worldIdx &&
              unaryFactImplies sourceField field then
            let suffix :=
              if sourceField == field then
                ""
              else
                s!" (taxonomy expansion implies {field.toTableField})"
            out := out.push s!"{namedFactSummary fact}{suffix}"
      | _ => pure ()
    return out

private def atomEvidence
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) : DiagAtom → Array String
  | .unary field thing world =>
      unaryEvidence worldNames thingNames namedFacts
        (lookupVar env thing) (lookupVar env world) field
  | .derivedUnary field thing world =>
      Id.run do
        let thingName := indexedName thingNames (lookupVar env thing)
        let worldIdx := lookupVar env world
        let mut out := #[]
        for fact in namedFacts do
          match fact with
          | .derived (.unary sourceField sourceThing) scope =>
              if sourceField == field && sourceThing == thingName &&
                  scopeCoversWorld worldNames scope worldIdx then
                out := out.push (namedFactSummary fact)
          | _ => pure ()
        return out
  | .typeSem thing world =>
      Id.run do
        let thingIdx := lookupVar env thing
        let worldIdx := lookupVar env world
        let mut out := #[]
        for fact in namedFacts do
          match fact with
          | .binary .inst _ target scope =>
              if target == indexedName thingNames thingIdx &&
                  scopeCoversWorld worldNames scope worldIdx then
                out := out.push s!"{namedFactSummary fact} (makes {indexedName thingNames thingIdx} a possible type)"
          | _ => pure ()
        return out
  | .binary field left right world =>
      Id.run do
        let leftName := indexedName thingNames (lookupVar env left)
        let rightName := indexedName thingNames (lookupVar env right)
        let worldIdx := lookupVar env world
        let mut out := #[]
        for fact in namedFacts do
          match fact with
          | .binary sourceField sourceLeft sourceRight scope =>
              if sourceField == field && sourceLeft == leftName && sourceRight == rightName &&
                  scopeCoversWorld worldNames scope worldIdx then
                out := out.push (namedFactSummary fact)
          | _ => pure ()
        return out
  | .derivedBinary field left right world =>
      Id.run do
        let leftName := indexedName thingNames (lookupVar env left)
        let rightName := indexedName thingNames (lookupVar env right)
        let worldIdx := lookupVar env world
        let mut out := #[]
        for fact in namedFacts do
          match fact with
          | .derived (.binary sourceField sourceLeft sourceRight) scope =>
              if sourceField == field && sourceLeft == leftName && sourceRight == rightName &&
                  scopeCoversWorld worldNames scope worldIdx then
                out := out.push (namedFactSummary fact)
          | _ => pure ()
        return out
  | .ternary field first second third world =>
      Id.run do
        let firstName := indexedName thingNames (lookupVar env first)
        let secondName := indexedName thingNames (lookupVar env second)
        let thirdName := indexedName thingNames (lookupVar env third)
        let worldIdx := lookupVar env world
        let mut out := #[]
        for fact in namedFacts do
          match fact with
          | .ternary sourceField sourceFirst sourceSecond sourceThird scope =>
              if sourceField == field &&
                  sourceFirst == firstName && sourceSecond == secondName &&
                  sourceThird == thirdName &&
                  scopeCoversWorld worldNames scope worldIdx then
                out := out.push (namedFactSummary fact)
          | _ => pure ()
        return out
  | .quaternary field first second third fourth world =>
      Id.run do
        let firstName := indexedName thingNames (lookupVar env first)
        let secondName := indexedName thingNames (lookupVar env second)
        let thirdName := indexedName thingNames (lookupVar env third)
        let fourthName := indexedName thingNames (lookupVar env fourth)
        let worldIdx := lookupVar env world
        let mut out := #[]
        for fact in namedFacts do
          match fact with
          | .derived (.quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth) scope =>
              if sourceField == field &&
                  sourceFirst == firstName && sourceSecond == secondName &&
                  sourceThird == thirdName && sourceFourth == fourthName &&
                  scopeCoversWorld worldNames scope worldIdx then
                out := out.push (namedFactSummary fact)
          | _ => pure ()
        return out
  | _ => #[]

private partial def collectAtoms : DiagFormula → Array DiagAtom
  | .atom atom => #[atom]
  | .eqThing _ _ => #[]
  | .eqWorld _ _ => #[]
  | .not p => collectAtoms p
  | .and p q => collectAtoms p ++ collectAtoms q
  | .or p q => collectAtoms p ++ collectAtoms q
  | .imp p q => collectAtoms p ++ collectAtoms q
  | .iff p q => collectAtoms p ++ collectAtoms q
  | .forallThing _ body => collectAtoms body
  | .forallWorld _ body => collectAtoms body
  | .existsThing _ body => collectAtoms body
  | .existsWorld _ body => collectAtoms body
  | .box _ _ body => collectAtoms body
  | .dia _ _ body => collectAtoms body

private partial def failingAtoms
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → Array DiagAtom
  | .atom atom =>
      if evalDiagAtom worldCount thingCount tables env atom then #[] else #[atom]
  | .eqThing _ _ => #[]
  | .eqWorld _ _ => #[]
  | .not p =>
      if evalDiagFormula worldCount thingCount tables env (.not p) then #[] else
        match p with
        | .atom atom => #[atom]
        | _ => #[]
  | .and p q => failingAtoms worldCount thingCount tables env p ++ failingAtoms worldCount thingCount tables env q
  | .or p q =>
      if evalDiagFormula worldCount thingCount tables env (.or p q) then #[] else
        failingAtoms worldCount thingCount tables env p ++ failingAtoms worldCount thingCount tables env q
  | .imp p q =>
      if evalDiagFormula worldCount thingCount tables env (.imp p q) then #[] else
        collectAtoms p ++ failingAtoms worldCount thingCount tables env q
  | .iff p q =>
      if evalDiagFormula worldCount thingCount tables env (.iff p q) then #[] else
        failingAtoms worldCount thingCount tables env p ++ failingAtoms worldCount thingCount tables env q
  | .forallThing name body =>
      Id.run do
        let mut out := #[]
        for x in [:thingCount] do
          out := out ++ failingAtoms worldCount thingCount tables (env.push (name, x)) body
        return out
  | .forallWorld name body =>
      Id.run do
        let mut out := #[]
        for w in [:worldCount] do
          out := out ++ failingAtoms worldCount thingCount tables (env.push (name, w)) body
        return out
  | .existsThing name body =>
      if evalDiagFormula worldCount thingCount tables env (.existsThing name body) then #[] else
        Id.run do
          let mut out := #[]
          for x in [:thingCount] do
            out := out ++ failingAtoms worldCount thingCount tables (env.push (name, x)) body
          return out
  | .existsWorld name body =>
      if evalDiagFormula worldCount thingCount tables env (.existsWorld name body) then #[] else
        Id.run do
          let mut out := #[]
          for w in [:worldCount] do
            out := out ++ failingAtoms worldCount thingCount tables (env.push (name, w)) body
          return out
  | .box _currentWorld witnessWorld body =>
      Id.run do
        let mut out := #[]
        for w in [:worldCount] do
          let env' := env.push (witnessWorld, w)
          if !evalDiagFormula worldCount thingCount tables env' body then
            out := out ++ failingAtoms worldCount thingCount tables env' body
        return out
  | .dia currentWorld witnessWorld body =>
      if evalDiagFormula worldCount thingCount tables env (.dia currentWorld witnessWorld body) then #[] else
        Id.run do
          let mut out := #[]
          for w in [:worldCount] do
            out := out ++ failingAtoms worldCount thingCount tables (env.push (witnessWorld, w)) body
          return out

private def appendEvidenceForFormula
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) :
    Array String :=
  Id.run do
    let mut out := out.push s!"Evidence for {renderDiagFormula worldNames thingNames env formula}:"
    let mut emitted := false
    for atom in collectAtoms formula do
      let evidence := atomEvidence worldNames thingNames namedFacts env atom
      if evidence.isEmpty then
        if evalDiagAtom worldCount thingCount tables env atom then
          out := out.push s!"  - {renderDiagAtom worldNames thingNames env atom} (present in generated finite model)"
          emitted := true
      else
        for item in evidence do
          out := out.push s!"  - {item}"
          emitted := true
    if !emitted then
      out := out.push s!"  - {renderDiagFormula worldNames thingNames env formula} (true in generated finite model)"
    return out

private def suggestionForAtom
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atom : DiagAtom) (wanted : Bool) : String :=
  let addOrRemove :=
    if wanted then
      "Add the missing DSL fact"
    else
      "Remove or reclassify the DSL fact"
  let tail :=
    if wanted then
      "or remove/relax the facts shown in this counterexample that make this obligation apply."
    else
      "or remove/relax the facts shown in this counterexample that make this combination forbidden."
  match atom with
  | .unary field thing world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{unaryFieldDslLabel field}({thingName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .binary .inst left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{leftName} :: {rightName}` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .binary .sub left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{leftName} ⊑ {rightName}` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .binary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{binaryFieldDslLabel field}({leftName}, {rightName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .ternary field first second third world =>
      let firstName := indexedName thingNames (lookupVar env first)
      let secondName := indexedName thingNames (lookupVar env second)
      let thirdName := indexedName thingNames (lookupVar env third)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{ternaryFieldDslLabel field}({firstName}, {secondName}, {thirdName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .derivedUnary field thing world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{field}({thingName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .derivedBinary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{field}({leftName}, {rightName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .quaternary field first second third fourth world =>
      let firstName := indexedName thingNames (lookupVar env first)
      let secondName := indexedName thingNames (lookupVar env second)
      let thirdName := indexedName thingNames (lookupVar env third)
      let fourthName := indexedName thingNames (lookupVar env fourth)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{field}({firstName}, {secondName}, {thirdName}, {fourthName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .typeSem thing _world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      if wanted then
        s!"Make `{thingName}` behave as a type by adding at least one compatible instantiation, or remove/relax the facts shown in this counterexample that require it to be a type."
      else
        s!"Remove the instantiations that make `{thingName}` behave as a type, or remove/relax the facts shown in this counterexample that require it to be an individual."
  | .individualSem thing _world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      if wanted then
        s!"Make `{thingName}` behave as an individual by removing its compatible instantiations as a type, or remove/relax the facts shown in this counterexample that require it to be an individual."
      else
        s!"Add a compatible instantiation for `{thingName}` if it should be a type, or remove/relax the facts shown in this counterexample that forbid it from being an individual."

private def suggestionForFailure
    (worldNames thingNames : Array Name) (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ =>
      "Add at least one of the alternatives listed here, or remove/relax the evidence for this counterexample that makes this alternative obligation apply."
  | .and _ _ =>
      if (flattenDiagAnd formula).any formulaHasDistinctnessRequirement then
        "Add a witness satisfying all listed requirements, including the distinctness condition, or remove/relax the evidence for this counterexample that makes this witness obligation apply."
      else
        let atoms := failingAtoms worldCount thingCount tables env formula
        match atoms[0]? with
        | some atom =>
            if atoms.size == 1 then
              suggestionForAtom worldNames thingNames env atom true
            else
              "Add all missing facts listed here, or remove/relax the evidence for this counterexample that makes these requirements apply."
        | none =>
            "Use the listed requirements and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."
  | .not (.atom atom) =>
      if evalDiagAtom worldCount thingCount tables env atom then
        suggestionForAtom worldNames thingNames env atom false
      else
        "Inspect the evidence for this counterexample: this forbidden condition holds, but the diagnostic could not reduce it to a single asserted DSL fact."
  | .atom atom =>
      suggestionForAtom worldNames thingNames env atom true
  | _ =>
      let atoms := failingAtoms worldCount thingCount tables env formula
      match atoms[0]? with
      | some atom =>
          if atoms.size == 1 then
            suggestionForAtom worldNames thingNames env atom true
          else
            "Several obligations fail together here. Add the missing facts named in the condition, or remove/relax the evidence for this counterexample that makes all of them required."
      | none =>
          "Use the condition and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."

private def dType (x w : String) : DiagFormula :=
  .atom (.typeSem x w)

private def dIndividual (x w : String) : DiagFormula :=
  .atom (.individualSem x w)

private def dUnary (field : UnaryField) (x w : String) : DiagFormula :=
  .atom (.unary field x w)

private def dBinary (field : BinaryField) (x y w : String) : DiagFormula :=
  .atom (.binary field x y w)

private def dTernary (field : TernaryField) (x y z w : String) : DiagFormula :=
  .atom (.ternary field x y z w)

private def dInst (x t w : String) : DiagFormula :=
  dBinary .inst x t w

private def dSub (x y w : String) : DiagFormula :=
  dBinary .sub x y w

private def dPart (x y w : String) : DiagFormula :=
  dBinary .part x y w

private def dOverlap (x y w : String) : DiagFormula :=
  dBinary .overlap x y w

private def dProperPart (x y w : String) : DiagFormula :=
  dBinary .properPart x y w

private def dGenericFunctionalDependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "GenericFunctionalDependence" x y w)

private def dIndividualFunctionalDependence
    (x x' y y' w : String) : DiagFormula :=
  .atom (.quaternary "IndividualFunctionalDependence" x x' y y' w)

private def dComponentOf
    (x x' y y' w : String) : DiagFormula :=
  .atom (.quaternary "ComponentOf" x x' y y' w)

private def dGenericConstitutionalDependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "GenericConstitutionalDependence" x y w)

private def dConstitution
    (x x' y y' w : String) : DiagFormula :=
  .atom (.quaternary "Constitution" x x' y y' w)

private def dExistentialDependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "ExistentialDependence" x y w)

private def dExistentialIndependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "ExistentialIndependence" x y w)

private def dExternallyDependent (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "ExternallyDependent" x y w)

private def dExternallyDependentMode (x w : String) : DiagFormula :=
  .atom (.derivedUnary "ExternallyDependentMode" x w)

private def dQuaIndividual (x w : String) : DiagFormula :=
  .atom (.derivedUnary "QuaIndividual" x w)

private def dQuaIndividualOf (x y w : String) : DiagFormula :=
  .atom (.binary .quaIndividualOf x y w)

private def dFoundedBy (x y w : String) : DiagFormula :=
  .atom (.binary .foundedBy x y w)

private def dMediates (x y w : String) : DiagFormula :=
  .atom (.binary .mediates x y w)

private def dCharacterization (x y w : String) : DiagFormula :=
  .atom (.binary .characterization x y w)

private def dDistance (x y r w : String) : DiagFormula :=
  dTernary .distance x y r w

private def dDistanceSum (x y z w : String) : DiagFormula :=
  dTernary .distanceSum x y z w

private def dDistanceZero (x w : String) : DiagFormula :=
  dUnary .distanceZero x w

private def dDistanceGreaterEq (x y w : String) : DiagFormula :=
  dBinary .distanceGreaterEq x y w

private def dNeThing (x y : String) : DiagFormula :=
  .not (.eqThing x y)

private def dAndList (xs : List DiagFormula) : DiagFormula :=
  match xs with
  | List.nil => .atom (.typeSem "__invalid" "__invalid")
  | List.cons p ps => ps.foldl (fun acc q => .and acc q) p

private def dOrList (xs : List DiagFormula) : DiagFormula :=
  match xs with
  | List.nil => .not (.atom (.typeSem "__invalid" "__invalid"))
  | List.cons p ps => ps.foldl (fun acc q => .or acc q) p

private def dQuality (x w : String) : DiagFormula :=
  .existsThing "__qualityKind" <| dAndList [
    dUnary .qualityKind "__qualityKind" w,
    dInst x "__qualityKind" w,
    .forallThing "__otherQualityKind" <|
      .imp
        (dAndList [
          dUnary .qualityKind "__otherQualityKind" w,
          dInst x "__otherQualityKind" w
        ])
        (.eqThing "__otherQualityKind" "__qualityKind")
  ]

private def dDerivedUnary (field x w : String) : DiagFormula :=
  .atom (.derivedUnary field x w)

private def dDerivedBinary (field x y w : String) : DiagFormula :=
  .atom (.derivedBinary field x y w)

private def dQualityStructure (x w : String) : DiagFormula :=
  dDerivedUnary "QualityStructure" x w

private def dNonEmptySet (x w : String) : DiagFormula :=
  dDerivedUnary "NonEmptySet" x w

private def dSimpleQuality (x w : String) : DiagFormula :=
  dDerivedUnary "SimpleQuality" x w

private def dComplexQuality (x w : String) : DiagFormula :=
  dDerivedUnary "ComplexQuality" x w

private def dSimpleQualityType (x w : String) : DiagFormula :=
  dDerivedUnary "SimpleQualityType" x w

private def dComplexQualityType (x w : String) : DiagFormula :=
  dDerivedUnary "ComplexQualityType" x w

private def dMemberOf (x y w : String) : DiagFormula :=
  dBinary .memberOf x y w

private def dProperSub (x y w : String) : DiagFormula :=
  dDerivedBinary "ProperSub" x y w

private def dProperSubsetOf (x y w : String) : DiagFormula :=
  dDerivedBinary "ProperSubsetOf" x y w

private def dSpecificEndurantKind (k w : String) : DiagFormula :=
  dOrList [
    dUnary .objectKind k w,
    dUnary .collectiveKind k w,
    dUnary .quantityKind k w,
    dUnary .relatorKind k w,
    dUnary .modeKind k w,
    dUnary .qualityKind k w
  ]

private def renderThingPath (thingNames : Array Name) (path : Array Nat) : String :=
  String.intercalate " InheresIn " <| path.toList.map (indexedName thingNames ·)

private structure UltimateBearerCandidate where
  bearer : Nat
  path : Array Nat
  deriving Inhabited

private def ultimateBearerCandidates
    (thingCount : Nat) (tables : FactTables) (w m : Nat) :
    Array UltimateBearerCandidate :=
  Id.run do
    let mut out := #[]
    for b in [:thingCount] do
      if !tables.unaryLookup "moment" b w then
        match tables.momentOfPath? thingCount w m b with
        | some path => out := out.push ⟨b, path⟩
        | none => pure ()
    return out

private def firstMomentWithoutUltimateBearer
    (worldCount thingCount : Nat) (tables : FactTables) :
    Option (Nat × Nat) :=
  Id.run do
    for w in [:worldCount] do
      for m in [:thingCount] do
        if tables.unaryLookup "moment" m w &&
            (ultimateBearerCandidates thingCount tables w m).isEmpty then
          return some (w, m)
    return none

private def firstMomentWithMultipleUltimateBearers
    (worldCount thingCount : Nat) (tables : FactTables) :
    Option (Nat × Nat × Array UltimateBearerCandidate) :=
  Id.run do
    for w in [:worldCount] do
      for m in [:thingCount] do
        if tables.unaryLookup "moment" m w then
          let candidates := ultimateBearerCandidates thingCount tables w m
          if candidates.size > 1 then
            return some (w, m, candidates)
    return none

def ax68ClosureAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  match firstMomentWithoutUltimateBearer worldNames.size thingNames.size tables with
  | some (w, m) =>
      #[
        s!"Closure check for ax68: `{indexedName thingNames m}` is a moment at `{indexedName worldNames w}`, but no non-moment ultimate bearer is reachable through `InheresIn`.",
        s!"Suggestion: add an inherence chain from `{indexedName thingNames m}` to a concrete non-moment bearer, or reclassify the endpoint so it is not a moment."
      ]
  | none =>
      match firstMomentWithMultipleUltimateBearers worldNames.size thingNames.size tables with
      | some (w, m, candidates) =>
          let rendered :=
            candidates.map (fun c =>
              s!"`{indexedName thingNames c.bearer}` via `{renderThingPath thingNames c.path}`")
          let renderedText := String.intercalate ", " rendered.toList
          #[
            s!"Closure check for ax68: `{indexedName thingNames m}` has multiple reachable non-moment bearers at `{indexedName worldNames w}`.",
            s!"Reachable bearers: {renderedText}.",
            "Suggestion: remove the competing inherence branch, or reclassify the unintended endpoint so it is not an ultimate bearer."
          ]
      | none =>
          #[
            "Closure check for ax68: every generated moment has exactly one reachable non-moment bearer in the finite `InheresIn` closure.",
            "The remaining failure is therefore in the Lean proof bridge from the computed closure to the inductive `MomentOf`, not in the DSL model data."
          ]

def hasAx68ClosureFailure (worldCount thingCount : Nat) (tables : FactTables) : Bool :=
  (firstMomentWithoutUltimateBearer worldCount thingCount tables).isSome ||
    (firstMomentWithMultipleUltimateBearers worldCount thingCount tables).isSome

private def partLookup (tables : FactTables) (x y w : Nat) : Bool :=
  x == y || tables.binaryLookup "part" x y w

private def overlapLookup (tables : FactTables) (x y w : Nat) : Bool :=
  x == y || tables.binaryLookup "overlap" x y w

private def foundationCandidates (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Array Nat :=
  Id.run do
    let mut out := #[]
    for y in [:thingCount] do
      if tables.binaryLookup "foundedBy" x y w then
        out := out.push y
    return out

private def uniqueFoundation? (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Option Nat :=
  let candidates := foundationCandidates thingCount tables x w
  if candidates.size == 1 then candidates[0]? else none

private def renderFoundationStatus
    (thingNames : Array Name) (tables : FactTables) (x w : Nat) : String :=
  let candidates := foundationCandidates thingNames.size tables x w
  if candidates.isEmpty then
    "no `FoundedBy` fact"
  else if candidates.size == 1 then
    s!"foundation `{indexedName thingNames (candidates[0]!)}`"
  else
    let rendered := String.intercalate "; " <| candidates.toList.map fun y =>
      s!"`{indexedName thingNames y}`"
    s!"ambiguous foundations {rendered}"

private def foundationEq?
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) : Option Bool :=
  match uniqueFoundation? thingCount tables x w, uniqueFoundation? thingCount tables y w with
  | some fx, some fy => some (fx == fy)
  | _, _ => none

/-
DSL-level reconstruction for ax99.

The axiom quantifies over an existential finite family `ys zs : Fin n → Thing`,
so it does not fit the simple `DiagFormula` language above.  The helpers here
perform the corresponding finite search directly over characterization,
association, membership, and tuple-projection tables.
-/
private def memberLookup (tables : FactTables) (x s w : Nat) : Bool :=
  tables.binaryLookup "memberOf" x s w

private def tupleProjectionValue (thingCount : Nat) (tables : FactTables)
    (p i w : Nat) : Nat :=
  Id.run do
    for candidate in [:thingCount] do
      if tables.tupleProjectionLookup p i candidate w then
        return candidate
    return p

private def characterizationTargets
    (thingCount : Nat) (tables : FactTables) (t w : Nat) : Array Nat :=
  Id.run do
    let mut out := #[]
    for z in [:thingCount] do
      if tables.binaryLookup "characterization" t z w then
        out := out.push z
    return out

private def productSubsetHolds
    (thingCount : Nat) (tables : FactTables) (x w : Nat) (ys : Array Nat) : Bool :=
  Id.run do
    for p in [:thingCount] do
      if memberLookup tables p x w then
        for i in [:ys.size] do
          let projection := tupleProjectionValue thingCount tables p i w
          if !memberLookup tables projection (ys[i]!) w then
            return false
    return true

private def productWitness?
    (thingCount : Nat) (tables : FactTables) (x t w : Nat) : Option (Array Nat × Array Nat) :=
  let zs := characterizationTargets thingCount tables t w
  if zs.isEmpty then
    some (#[], #[])
  else
    Id.run do
      let mut ys := #[]
      for i in [:zs.size] do
        let z := zs[i]!
        let mut found? : Option Nat := none
        for y in [:thingCount] do
          if tables.binaryLookup "associatedWith" y z w then
            let prefixOk := Id.run do
              for p in [:thingCount] do
                if memberLookup tables p x w then
                  let projection := tupleProjectionValue thingCount tables p i w
                  if !memberLookup tables projection y w then
                    return false
              return true
            if prefixOk then
              found? := some y
              break
        match found? with
        | some y => ys := ys.push y
        | none => return none
      if productSubsetHolds thingCount tables x w ys then
        return some (ys, zs)
      return none

private def ax99QualityDomainAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  Id.run do
    for w in [:worldNames.size] do
      for x in [:thingNames.size] do
        if tables.unaryLookup "qualityDomain" x w then
          for t in [:thingNames.size] do
            if tables.binaryLookup "associatedWith" x t w then
              let hasEntry :=
                tables.productFamilies.any fun pf =>
                  pf.domain == x && pf.qualityType == t
              match productWitness? thingNames.size tables x t w with
              | some _ => pure ()
              | none =>
                  let zs := characterizationTargets thingNames.size tables t w
                  let renderedZs :=
                    if zs.isEmpty then
                      "none"
                    else
                      String.intercalate ", " <| zs.toList.map (indexedName thingNames ·)
                  if hasEntry then
                    return #[
                      s!"Product-family witness data is present for x = {indexedName thingNames x}, t = {indexedName thingNames t}, w = {indexedName worldNames w}, but it does not satisfy ax99.",
                      s!"The witness must list one quality dimension for each characterization of `{indexedName thingNames t}` and prove that every member of `{indexedName thingNames x}` projects into the corresponding dimension.",
                      "Check the `dimensions` and `types` listed in the `product_family` block, the `Characterization(t, z)` facts, the `AssociatedWith(y, z)` facts for the listed dimensions, and the `TupleProjection(tuple, i, component)` plus `MemberOf(component, y)` facts for every domain member.",
                      s!"Characterization targets found for `{indexedName thingNames t}`: {renderedZs}."
                    ]
                  else
                    return #[
                      s!"Missing product-family witness data for x = {indexedName thingNames x}, t = {indexedName thingNames t}, w = {indexedName worldNames w}.",
                      s!"The model says `{indexedName thingNames x}` is a quality domain associated with `{indexedName thingNames t}`, so ax99 needs an explicit finite product-family witness for that pair.",
                      s!"Add a block of the form `product_family {indexedName thingNames x} for {indexedName thingNames t}:` with one `dimensions` entry and one `types` entry for each component quality type characterizing `{indexedName thingNames t}`.",
                      "For each listed dimension/type pair, also provide the ordinary facts that make the witness meaningful: `Characterization(t, z)`, `AssociatedWith(y, z)`, `MemberOf(tuple, x)` for domain members, `TupleProjection(tuple, i, component)`, and `MemberOf(component, y)`.",
                      s!"Characterization targets currently found for `{indexedName thingNames t}`: {renderedZs}."
                    ]
    return #[
      "Product check for ax99: every asserted quality-domain association has a finite product witness in the DSL tables.",
      "If ax99 is still reported, the remaining issue is likely missing or mismatched product-family witness data rather than an obvious table mismatch."
    ]

private def thingIndexByString? (thingNames : Array Name) (thing : String) : Option Nat :=
  thingNames.findIdx? (fun name => name.toString == thing)

private def resolvedScopeWorlds (worldNames : Array Name) : FactScope → Array Nat
  | .at w => #[w]
  | .everywhere => Array.range worldNames.size

/-
Derived assertions are checked before certification as generated theorems.
When one fails, these evaluators reconstruct the same definition-like relation
from finite tables so the widget can report the false assertion in DSL terms.
-/
private def typeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) : Bool :=
  hasPossibleInstance worldCount thingCount tables thing

private def subsetLookup (thingCount : Nat) (tables : FactTables) (s t w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if memberLookup tables x s w && !memberLookup tables x t w then
        return false
    return true

private def properSubsetLookup (thingCount : Nat) (tables : FactTables) (s t w : Nat) : Bool :=
  subsetLookup thingCount tables s t w &&
    Id.run do
      for x in [:thingCount] do
        if memberLookup tables x t w && !memberLookup tables x s w then
          return true
      return false

private def properSubLookup (tables : FactTables) (x y w : Nat) : Bool :=
  tables.binaryLookup "sub" x y w && !tables.binaryLookup "sub" y x w

private def isDisjointWithLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t t' w : Nat) : Bool :=
  typeLookup worldCount thingCount tables t &&
    typeLookup worldCount thingCount tables t' &&
    Id.run do
      for x in [:thingCount] do
        if tables.binaryLookup "inst" x t w && tables.binaryLookup "inst" x t' w then
          return false
      return true

private def isCompletelyCoveredByLookup
    (thingCount : Nat) (tables : FactTables) (t t' t'' w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x t w &&
          !(tables.binaryLookup "inst" x t' w || tables.binaryLookup "inst" x t'' w) then
        return false
    return true

private def isPartitionedIntoLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t t' t'' w : Nat) : Bool :=
  isCompletelyCoveredByLookup thingCount tables t t' t'' w &&
    isDisjointWithLookup worldCount thingCount tables t' t'' w

private def categorizesLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t1 t2 w : Nat) : Bool :=
  typeLookup worldCount thingCount tables t1 &&
    Id.run do
      for t3 in [:thingCount] do
        if tables.binaryLookup "inst" t3 t1 w && !tables.binaryLookup "sub" t3 t2 w then
          return false
      return true

private def qualityLookup (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  Id.run do
    let mut found? : Option Nat := none
    for q in [:thingCount] do
      if tables.unaryLookup "qualityKind" q w && tables.binaryLookup "inst" x q w then
        match found? with
        | none => found? := some q
        | some _ => return false
    return found?.isSome

private def nonEmptySetLookup (thingCount : Nat) (tables : FactTables) (s w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if memberLookup tables x s w then
        return true
    return false

private def uniqueThing? (thingCount : Nat) (p : Nat → Bool) : Option Nat :=
  Id.run do
    let mut found? : Option Nat := none
    for x in [:thingCount] do
      if p x then
        match found? with
        | none => found? := some x
        | some _ => return none
    return found?

private def qualityStructureLookup
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (uniqueThing? thingCount fun t =>
    tables.unaryLookup "qualityType" t w &&
      tables.binaryLookup "associatedWith" x t w).isSome

private def simpleQualityLookup (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  qualityLookup thingCount tables x w &&
    Id.run do
      for y in [:thingCount] do
        if tables.binaryLookup "inheresIn" y x w then
          return false
      return true

private def complexQualityLookup (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  qualityLookup thingCount tables x w &&
    Id.run do
      for y in [:thingCount] do
        if tables.binaryLookup "inheresIn" y x w then
          return true
      return false

private def simpleQualityTypeLookup
    (thingCount : Nat) (tables : FactTables) (t w : Nat) : Bool :=
  tables.unaryLookup "qualityType" t w &&
    Id.run do
      for x in [:thingCount] do
        if tables.binaryLookup "inst" x t w &&
            !simpleQualityLookup thingCount tables x w then
          return false
      return true

private def complexQualityTypeLookup
    (thingCount : Nat) (tables : FactTables) (t w : Nat) : Bool :=
  tables.unaryLookup "qualityType" t w &&
    Id.run do
      for x in [:thingCount] do
        if tables.binaryLookup "inst" x t w &&
            !complexQualityLookup thingCount tables x w then
          return false
      return true

private def ultimateBearerOfLookup
    (thingCount : Nat) (tables : FactTables) (b m w : Nat) : Bool :=
  !tables.unaryLookup "moment" b w &&
    tables.momentOfClosure thingCount w m b

private def evalNamedDerivedFact?
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Option Bool := do
  match fact with
  | .unary "Quality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| qualityLookup thingNames.size tables x w
  | .unary "NonEmptySet" x =>
      let x ← thingIndexByString? thingNames x
      pure <| nonEmptySetLookup thingNames.size tables x w
  | .unary "QualityStructure" x =>
      let x ← thingIndexByString? thingNames x
      pure <| qualityStructureLookup thingNames.size tables x w
  | .unary "SimpleQuality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| simpleQualityLookup thingNames.size tables x w
  | .unary "ComplexQuality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| complexQualityLookup thingNames.size tables x w
  | .unary "SimpleQualityType" x =>
      let x ← thingIndexByString? thingNames x
      pure <| simpleQualityTypeLookup thingNames.size tables x w
  | .unary "ComplexQualityType" x =>
      let x ← thingIndexByString? thingNames x
      pure <| complexQualityTypeLookup thingNames.size tables x w
  | .unary field x =>
      let x ← thingIndexByString? thingNames x
      pure <| derivedUnaryLookup worldNames.size thingNames.size tables field x w
  | .binary "UltimateBearerOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| ultimateBearerOfLookup thingNames.size tables x y w
  | .binary "ProperSub" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| properSubLookup tables x y w
  | .binary "SubsetOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| subsetLookup thingNames.size tables x y w
  | .binary "ProperSubsetOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| properSubsetLookup thingNames.size tables x y w
  | .binary "IsDisjointWith" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| isDisjointWithLookup worldNames.size thingNames.size tables x y w
  | .binary "Categorizes" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| categorizesLookup worldNames.size thingNames.size tables x y w
  | .binary field x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| derivedBinaryLookup worldNames.size thingNames.size tables field x y w
  | .ternary "IsCompletelyCoveredBy" x y z =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      let z ← thingIndexByString? thingNames z
      pure <| isCompletelyCoveredByLookup thingNames.size tables x y z w
  | .ternary "IsPartitionedInto" x y z =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      let z ← thingIndexByString? thingNames z
      pure <| isPartitionedIntoLookup worldNames.size thingNames.size tables x y z w
  | .ternary _ _ _ _ =>
      none
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| individualFunctionalDependenceLookup thingNames.size tables x x' y y' w
  | .quaternary "ComponentOf" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| componentOfLookup thingNames.size tables x x' y y' w
  | .quaternary "Constitution" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| constitutionLookup thingNames.size tables x x' y y' w
  | .quaternary _ _ _ _ _ =>
      none

private def derivedAssertionSuggestion (fact : NamedDerivedFact) : String :=
  match fact with
  | .unary "Quality" _ =>
      "Computed from `QualityKind(k)` plus `x :: k`, with exactly one such quality kind. Add exactly one quality-kind instantiation for the individual, and avoid competing quality-kind instantiations."
  | .unary "ExternallyDependentMode" _ =>
      "Computed from `Mode(x)` plus some computed `ExternallyDependent(x, y)`. `ExternallyDependent` itself is computed from modal existential dependence and independence from each bearer reached by `InheresIn`. Add `Mode`, `InheresIn`, and modal `Ex` facts that make a witness true, or remove the unsupported assertion."
  | .unary "QuaIndividual" _ =>
      "Computed from `QuaIndividualOf(x, y)`. Add a matching `QuaIndividualOf` fact and satisfy the §3.10 foundation requirements checked by the relator axioms, or remove the unsupported assertion."
  | .unary "NonEmptySet" _ =>
      "Computed from membership at the current world. Add at least one `MemberOf(member, set)` fact at this world, or remove the unsupported assertion."
  | .unary "QualityStructure" _ =>
      "Computed from exactly one association with a `QualityType`. Add exactly one `AssociatedWith(structure, qualityType)` fact whose target is a `QualityType`, or remove the unsupported assertion."
  | .unary "SimpleQuality" _ =>
      "Computed from `Quality(x)` plus absence of `InheresIn(_, x)`. Make the thing a computed `Quality` and ensure no other thing inheres in it at this world."
  | .unary "ComplexQuality" _ =>
      "Computed from `Quality(x)` plus at least one `InheresIn(_, x)`. Make the thing a computed `Quality` and add at least one `InheresIn(part, quality)` fact."
  | .unary "SimpleQualityType" _ =>
      "Computed from `QualityType(t)` plus every current instance of `t` being a computed `SimpleQuality`. Assert `QualityType(type)` and repair any non-simple-quality instance."
  | .unary "ComplexQualityType" _ =>
      "Computed from `QualityType(t)` plus every current instance of `t` being a computed `ComplexQuality`. Assert `QualityType(type)` and repair any non-complex-quality instance."
  | .binary "ProperSub" _ _ =>
      "Computed from `Sub(left, right)` and absence of reverse `Sub(right, left)`. Add the forward `Sub` fact and ensure the reverse `Sub` fact is not present."
  | .binary "GenericFunctionalDependence" _ _ =>
      "Computed from `Inst` and `FunctionsAs`: every instance functioning as the source type needs a distinct instance functioning as the target type."
  | .quaternary "IndividualFunctionalDependence" _ _ _ _ =>
      "Computed from generic functional dependence, the two instantiations, and the source-to-target `FunctionsAs` implication. Make the type-level dependence true, add the required instantiations, and ensure the target functions whenever the source functions."
  | .quaternary "ComponentOf" _ _ _ _ =>
      "Computed from `ProperPart(component, whole)` plus the corresponding computed `IndividualFunctionalDependence`. Add the proper-part fact and repair the functional-dependence side."
  | .binary "GenericConstitutionalDependence" _ _ =>
      "Computed from `Inst` and `ConstitutedBy`: every source-type instance needs a target-type instance that constitutionally bears it."
  | .quaternary "Constitution" _ _ _ _ =>
      "Computed from the two instantiations, computed generic constitutional dependence, and `ConstitutedBy(instance, constituter)`. Add the required instantiations, repair generic constitutional dependence, and add the concrete `ConstitutedBy` fact."
  | .binary "ExternallyDependent" _ _ =>
      "Computed from modal existential dependence plus existential independence from every bearer reached by `InheresIn`. Add modal `Ex` variation and `InheresIn` facts that satisfy external dependence, or remove the unsupported assertion."
  | .binary "ExistentialDependence" _ _ =>
      "Computed from `Ex` facts across worlds: every world where the dependent exists must also have the target existing. Add the missing `Ex` facts, or remove the unsupported assertion."
  | .binary "ExistentialIndependence" _ _ =>
      "Computed from `Ex` facts across worlds: each side must have a witness world where it exists without the other. Add those modal `Ex` variations, or remove the unsupported assertion."
  | .binary "UltimateBearerOf" _ _ =>
      "Computed from the `InheresIn` transitive closure and `Moment`: the bearer must be non-moment and reachable from the moment. Add an `InheresIn` path from the moment to the bearer and ensure the bearer is not a moment."
  | .binary "SubsetOf" _ _ =>
      "Computed from `MemberOf`: every member of the left set must also be a member of the right set at this world."
  | .binary "ProperSubsetOf" _ _ =>
      "Computed from `SubsetOf(left, right)` plus a strictness witness: some right-set member must not be in the left set."
  | .binary "IsDisjointWith" _ _ =>
      "Computed from typehood and `Inst`: the two types must have no shared instance. Remove the assertion, or remove the common instance facts that make the two types overlap."
  | .ternary "IsCompletelyCoveredBy" _ _ _ =>
      "Computed from `Inst`: every instance of the covered type must instantiate at least one covering type. Add missing instantiation facts, or remove the assertion."
  | .ternary "IsPartitionedInto" _ _ _ =>
      "Computed from complete coverage plus disjointness of the two covering types. Make the cover complete and the covering types disjoint, or remove the assertion."
  | .binary "Categorizes" _ _ =>
      "Computed from typehood, `Inst`, and `Sub`: every type instantiating the category must specialize the categorized type. Add missing specialization facts, or remove the assertion."
  | _ =>
      "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."

private def firstBoxExImpFailure?
    (worldNames : Array Name) (tables : FactTables) (x y : Nat) : Option Nat :=
  Id.run do
    for w in [:worldNames.size] do
      if tables.unaryLookup "ex" x w && !tables.unaryLookup "ex" y w then
        return some w
    return none

private def firstExternalIndependenceFailure?
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    Option String :=
  let yWithoutZ := Id.run do
    for w in [:worldNames.size] do
      if tables.unaryLookup "ex" y w && !tables.unaryLookup "ex" z w then
        return some w
    return none
  let zWithoutY := Id.run do
    for w in [:worldNames.size] do
      if tables.unaryLookup "ex" z w && !tables.unaryLookup "ex" y w then
        return some w
    return none
  match yWithoutZ, zWithoutY with
  | none, none =>
      some s!"the assertion needs one witness world where Ex({indexedName thingNames y}) holds without Ex({indexedName thingNames z}), and one witness world where Ex({indexedName thingNames z}) holds without Ex({indexedName thingNames y}); neither witness exists in the current `Ex` facts"
  | none, some _ =>
      some s!"the assertion needs a witness world where Ex({indexedName thingNames y}) holds without Ex({indexedName thingNames z}), but no such world exists in the current `Ex` facts"
  | some _, none =>
      some s!"the assertion needs a witness world where Ex({indexedName thingNames z}) holds without Ex({indexedName thingNames y}), but no such world exists in the current `Ex` facts"
  | some _, some _ => none

private def firstExternallyDependentFailureReason
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : String :=
  match firstBoxExImpFailure? worldNames tables x y with
  | some witnessWorld =>
      s!"`{indexedName thingNames x}` exists at `{indexedName worldNames witnessWorld}`, but `{indexedName thingNames y}` does not; this breaks existential dependence."
  | none =>
      Id.run do
        for z in [:thingNames.size] do
          if tables.binaryLookup "inheresIn" x z w then
            match firstExternalIndependenceFailure? worldNames thingNames tables y z with
            | some reason =>
                return s!"`{indexedName thingNames x}` inheres in `{indexedName thingNames z}` at `{indexedName worldNames w}`, but `{indexedName thingNames y}` is not existentially independent from that bearer: {reason}."
            | none => pure ()
        return "no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence."

private def externallyDependentWitnesses
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array Nat :=
  Id.run do
    let mut out := #[]
    for y in [:thingNames.size] do
      if externallyDependentLookup worldNames.size thingNames.size tables x y w then
        out := out.push y
    return out

private def renderExternallyDependentModeStatus
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array String :=
  if !tables.unaryLookup "mode" x w then
    #[s!"  - Computed ExternallyDependentMode: false, because `{indexedName thingNames x}` is not a `Mode` at `{indexedName worldNames w}`."]
  else
    let witnesses := externallyDependentWitnesses worldNames thingNames tables x w
    if witnesses.isEmpty then
      Id.run do
        let declaredCandidates := Id.run do
          let mut out := #[]
          for y in [:thingNames.size] do
            if tables.binaryLookup "externallyDependent" x y w ||
                assertedDerivedBinaryLookup tables "ExternallyDependent" x y w then
              out := out.push y
          return out
        let candidate? :=
          declaredCandidates[0]? <|>
            Id.run do
              for z in [:thingNames.size] do
                if tables.binaryLookup "inheresIn" x z w then
                  return some z
              return if thingNames.isEmpty then none else some 0
        let firstReason :=
          match candidate? with
          | none =>
            "there are no candidate things to witness external dependence."
          | some candidate =>
            firstExternallyDependentFailureReason worldNames thingNames tables x candidate w
        let mut out := #[
          s!"  - Computed ExternallyDependentMode: false. `{indexedName thingNames x}` is a `Mode`, but no thing witnesses computed `ExternallyDependent({indexedName thingNames x}, y)`.",
          s!"  - First candidate check: {firstReason}"
        ]
        if !declaredCandidates.isEmpty then
          let declared := String.intercalate ", " <| declaredCandidates.toList.map (indexedName thingNames ·)
          out := out.push s!"  - Note: asserted `ExternallyDependent` facts name candidate(s) {declared}, but certification uses the computed external-dependence semantics."
        return out
    else
      let rendered := String.intercalate ", " <| witnesses.toList.map (indexedName thingNames ·)
      #[s!"  - Computed ExternallyDependentMode: true, witnessed by {rendered}."]

private def qualityKindCandidates
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Array Nat :=
  Id.run do
    let mut out := #[]
    for q in [:thingCount] do
      if tables.unaryLookup "qualityKind" q w && tables.binaryLookup "inst" x q w then
        out := out.push q
    return out

private def qualityStatusEvidence
    (thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array String :=
  let candidates := qualityKindCandidates thingNames.size tables x w
  if candidates.isEmpty then
    #[s!"  - Computed Quality: false, because `{indexedName thingNames x}` instantiates no `QualityKind` at this world."]
  else if candidates.size == 1 then
    let q := candidates[0]!
    #[s!"  - Computed Quality: true, uniquely witnessed by `QualityKind({indexedName thingNames q})` and `{indexedName thingNames x} :: {indexedName thingNames q}`."]
  else
    let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
    #[s!"  - Computed Quality: false, because `{indexedName thingNames x}` instantiates multiple quality kinds at this world: {rendered}."]

private def qualityTypeAssociations
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Array Nat :=
  Id.run do
    let mut out := #[]
    for t in [:thingCount] do
      if tables.unaryLookup "qualityType" t w && tables.binaryLookup "associatedWith" x t w then
        out := out.push t
    return out

private def firstInheringThing?
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Option Nat :=
  Id.run do
    for y in [:thingCount] do
      if tables.binaryLookup "inheresIn" y x w then
        return some y
    return none

private def firstMember?
    (thingCount : Nat) (tables : FactTables) (s w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if memberLookup tables x s w then
        return some x
    return none

private def firstCoveredInstanceFailure?
    (thingCount : Nat) (tables : FactTables) (t t' t'' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x t w &&
          !(tables.binaryLookup "inst" x t' w || tables.binaryLookup "inst" x t'' w) then
        return some x
    return none

private def firstSharedInstance?
    (thingCount : Nat) (tables : FactTables) (t t' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x t w && tables.binaryLookup "inst" x t' w then
        return some x
    return none

private def firstCategorizationFailure?
    (thingCount : Nat) (tables : FactTables) (category target w : Nat) :
    Option Nat :=
  Id.run do
    for instType in [:thingCount] do
      if tables.binaryLookup "inst" instType category w &&
          !tables.binaryLookup "sub" instType target w then
        return some instType
    return none

private def firstGfdFailure?
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x x' w && tables.binaryLookup "functionsAs" x x' w then
        let found := Id.run do
          for y in [:thingCount] do
            if y != x && tables.binaryLookup "inst" y y' w &&
                tables.binaryLookup "functionsAs" y y' w then
              return true
          return false
        if !found then
          return some x
    return none

private def firstGcdFailure?
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x x' w then
        let found := Id.run do
          for y in [:thingCount] do
            if tables.binaryLookup "inst" y y' w &&
                tables.binaryLookup "constitutedBy" x y w then
              return true
          return false
        if !found then
          return some x
    return none

private def derivedAssertionRequiredMissing
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : String :=
  let fallback :=
    s!"asserted derived relation `{namedDerivedFactSummary fact}` must be true under the computed semantics at `{indexedName worldNames w}`, but its definition evaluates to false."
  match fact with
  | .unary "Quality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let candidates := qualityKindCandidates thingNames.size tables xIdx w
          if candidates.isEmpty then
            s!"`Quality({indexedName thingNames xIdx})` requires exactly one `QualityKind` instantiation; missing any `QualityKind(k)` with `{indexedName thingNames xIdx} :: k` at `{indexedName worldNames w}`."
          else
            let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
            s!"`Quality({indexedName thingNames xIdx})` requires exactly one `QualityKind` instantiation; found competing quality kinds {rendered} at `{indexedName worldNames w}`."
      | none => fallback
  | .unary "ExternallyDependentMode" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "mode" xIdx w then
            s!"`ExternallyDependentMode({indexedName thingNames xIdx})` requires `Mode({indexedName thingNames xIdx})` and some computed `ExternallyDependent({indexedName thingNames xIdx}, y)`; missing `Mode({indexedName thingNames xIdx})` at `{indexedName worldNames w}`."
          else
            let declaredCandidates := Id.run do
              let mut out := #[]
              for y in [:thingNames.size] do
                if tables.binaryLookup "externallyDependent" xIdx y w ||
                    assertedDerivedBinaryLookup tables "ExternallyDependent" xIdx y w then
                  out := out.push y
              return out
            let candidate? :=
              declaredCandidates[0]? <|>
                Id.run do
                  for z in [:thingNames.size] do
                    if tables.binaryLookup "inheresIn" xIdx z w then
                      return some z
                  return none
            match candidate? with
            | some yIdx =>
                s!"`ExternallyDependentMode({indexedName thingNames xIdx})` requires `Mode({indexedName thingNames xIdx})` and at least one computed `ExternallyDependent({indexedName thingNames xIdx}, y)`; missing such a witness. Candidate `{indexedName thingNames yIdx}` fails because {firstExternallyDependentFailureReason worldNames thingNames tables xIdx yIdx w}"
            | none =>
                s!"`ExternallyDependentMode({indexedName thingNames xIdx})` requires `Mode({indexedName thingNames xIdx})` and at least one computed `ExternallyDependent({indexedName thingNames xIdx}, y)`; missing any candidate witness and any relevant `InheresIn` bearer evidence."
      | none => fallback
  | .binary "ExternallyDependent" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          s!"`ExternallyDependent({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires existential dependence plus independence from every bearer of `{indexedName thingNames xIdx}`; missing condition: {firstExternallyDependentFailureReason worldNames thingNames tables xIdx yIdx w}"
      | _, _ => fallback
  | .binary "ExistentialDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstBoxExImpFailure? worldNames tables xIdx yIdx with
          | some witnessWorld =>
              s!"`ExistentialDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires `Ex({indexedName thingNames yIdx})` in every world where `Ex({indexedName thingNames xIdx})` holds; missing `Ex({indexedName thingNames yIdx})` at `{indexedName worldNames witnessWorld}`."
          | none => fallback
      | _, _ => fallback
  | .binary "ExistentialIndependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstExternalIndependenceFailure? worldNames thingNames tables xIdx yIdx with
          | some reason =>
              s!"`ExistentialIndependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires two modal `Ex` separation witnesses; missing condition: {reason}."
          | none => fallback
      | _, _ => fallback
  | .unary "NonEmptySet" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          s!"`NonEmptySet({indexedName thingNames xIdx})` requires some `MemberOf(member, {indexedName thingNames xIdx})`; missing any member at `{indexedName worldNames w}`."
      | none => fallback
  | .unary "QualityStructure" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let candidates := qualityTypeAssociations thingNames.size tables xIdx w
          if candidates.isEmpty then
            s!"`QualityStructure({indexedName thingNames xIdx})` requires exactly one associated `QualityType`; missing any `AssociatedWith({indexedName thingNames xIdx}, t)` where `QualityType(t)` holds."
          else
            let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
            s!"`QualityStructure({indexedName thingNames xIdx})` requires exactly one associated `QualityType`; found competing associated quality types {rendered}."
      | none => fallback
  | .unary "SimpleQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            s!"`SimpleQuality({indexedName thingNames xIdx})` requires computed `Quality({indexedName thingNames xIdx})`; missing the quality condition."
          else
            match firstInheringThing? thingNames.size tables xIdx w with
            | some yIdx =>
                s!"`SimpleQuality({indexedName thingNames xIdx})` requires no thing to inhere in it; conflicting `InheresIn({indexedName thingNames yIdx}, {indexedName thingNames xIdx})` is present."
            | none => fallback
      | none => fallback
  | .unary "ComplexQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            s!"`ComplexQuality({indexedName thingNames xIdx})` requires computed `Quality({indexedName thingNames xIdx})`; missing the quality condition."
          else
            s!"`ComplexQuality({indexedName thingNames xIdx})` requires at least one `InheresIn(part, {indexedName thingNames xIdx})`; missing any inhering part."
      | none => fallback
  | .unary "SimpleQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            s!"`SimpleQualityType({indexedName thingNames xIdx})` requires `QualityType({indexedName thingNames xIdx})`; missing that primitive classification."
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !simpleQualityLookup thingNames.size tables y w then
                  return s!"`SimpleQualityType({indexedName thingNames xIdx})` requires every instance to be a computed `SimpleQuality`; instance `{indexedName thingNames y}` is not simple."
              return fallback
      | none => fallback
  | .unary "ComplexQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            s!"`ComplexQualityType({indexedName thingNames xIdx})` requires `QualityType({indexedName thingNames xIdx})`; missing that primitive classification."
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !complexQualityLookup thingNames.size tables y w then
                  return s!"`ComplexQualityType({indexedName thingNames xIdx})` requires every instance to be a computed `ComplexQuality`; instance `{indexedName thingNames y}` is not complex."
              return fallback
      | none => fallback
  | .unary "QuaIndividual" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          s!"`QuaIndividual({indexedName thingNames xIdx})` requires some `QuaIndividualOf({indexedName thingNames xIdx}, y)`; missing any such fact at `{indexedName worldNames w}`."
      | none => fallback
  | .binary "UltimateBearerOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if tables.unaryLookup "moment" xIdx w then
            s!"`UltimateBearerOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires bearer `{indexedName thingNames xIdx}` not to be a `Moment`; conflicting `Moment({indexedName thingNames xIdx})` holds."
          else
            s!"`UltimateBearerOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires an `InheresIn` path from `{indexedName thingNames yIdx}` to bearer `{indexedName thingNames xIdx}`; missing that path at `{indexedName worldNames w}`."
      | _, _ => fallback
  | .binary "SubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          Id.run do
            for z in [:thingNames.size] do
              if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                return s!"`SubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires every left member to be a right member; `{indexedName thingNames z}` is in `{indexedName thingNames xIdx}` but missing from `{indexedName thingNames yIdx}`."
            return fallback
      | _, _ => fallback
  | .binary "ProperSubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !subsetLookup thingNames.size tables xIdx yIdx w then
            Id.run do
              for z in [:thingNames.size] do
                if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                  return s!"`ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` first requires `SubsetOf`; `{indexedName thingNames z}` is in the left set but missing from the right set."
              return s!"`ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` first requires `SubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; that subset condition is false."
          else
            s!"`ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires strictness; missing a member of `{indexedName thingNames yIdx}` that is not also a member of `{indexedName thingNames xIdx}`."
      | _, _ => fallback
  | .binary "ProperSub" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !tables.binaryLookup "sub" xIdx yIdx w then
            s!"`ProperSub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires `Sub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; missing the forward `Sub` fact."
          else
            s!"`ProperSub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires absence of reverse `Sub`; conflicting `Sub({indexedName thingNames yIdx}, {indexedName thingNames xIdx})` is present."
      | _, _ => fallback
  | .binary "GenericFunctionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGfdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              s!"`GenericFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires a distinct target-functioning witness for source-functioning `{indexedName thingNames witness}`; missing such a `{indexedName thingNames yIdx}` instance."
          | none => fallback
      | _, _ => fallback
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !genericFunctionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `GenericFunctionalDependence({indexedName thingNames xTypeIdx}, {indexedName thingNames yTypeIdx})`; that computed type-level dependence is false."
          else if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}`; missing that instantiation."
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}`; missing that instantiation."
          else
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames yIdx}` to function as `{indexedName thingNames yTypeIdx}` whenever `{indexedName thingNames xIdx}` functions as `{indexedName thingNames xTypeIdx}`; missing the target `FunctionsAs` fact."
      | _, _, _, _ => fallback
  | .quaternary "ComponentOf" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "properPart" xIdx yIdx w then
            s!"`ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `ProperPart({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; missing that proper-part fact."
          else
            s!"`ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` also requires computed `IndividualFunctionalDependence`; that dependence is false."
      | _, _, _, _ => fallback
  | .binary "GenericConstitutionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGcdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              s!"`GenericConstitutionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires a `{indexedName thingNames yIdx}` instance that constitutionally bears source instance `{indexedName thingNames witness}`; missing such a `ConstitutedBy({indexedName thingNames witness}, _)` witness."
          | none => fallback
      | _, _ => fallback
  | .quaternary "Constitution" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}`; missing that instantiation."
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}`; missing that instantiation."
          else if !genericConstitutionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires computed `GenericConstitutionalDependence({indexedName thingNames xTypeIdx}, {indexedName thingNames yTypeIdx})`; that dependence is false."
          else
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `ConstitutedBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; missing that fact."
      | _, _, _, _ => fallback
  | .binary "Categorizes" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !typeLookup worldNames.size thingNames.size tables xIdx then
            s!"`Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires `{indexedName thingNames xIdx}` to be a computed `Type`; missing any possible instance."
          else
            match firstCategorizationFailure? thingNames.size tables xIdx yIdx w with
            | some instType =>
                s!"`Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires each category-instance type to specialize `{indexedName thingNames yIdx}`; missing `Sub({indexedName thingNames instType}, {indexedName thingNames yIdx})`."
            | none => fallback
      | _, _ => fallback
  | .binary "IsDisjointWith" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstSharedInstance? thingNames.size tables xIdx yIdx w with
          | some z =>
              s!"`IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires no shared instance; `{indexedName thingNames z}` instantiates both types."
          | none =>
              s!"`IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires both arguments to be computed types and have no shared instance; missing typehood for one argument."
      | _, _ => fallback
  | .ternary "IsCompletelyCoveredBy" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              s!"`IsCompletelyCoveredBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})` requires every `{indexedName thingNames xIdx}` instance to instantiate at least one covering type; `{indexedName thingNames instIdx}` instantiates neither `{indexedName thingNames yIdx}` nor `{indexedName thingNames zIdx}`."
          | none => fallback
      | _, _, _ => fallback
  | .ternary "IsPartitionedInto" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              s!"`IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})` first requires complete coverage; `{indexedName thingNames instIdx}` instantiates the partitioned type but neither part type."
          | none =>
              match firstSharedInstance? thingNames.size tables yIdx zIdx w with
              | some instIdx =>
                  s!"`IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})` also requires disjoint parts; `{indexedName thingNames instIdx}` instantiates both part types."
              | none => fallback
      | _, _, _ => fallback
  | _ => fallback

private def derivedAssertionEvidence
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Array String :=
  match fact with
  | .unary "Quality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          #[s!"  - User assertion: `Quality({indexedName thingNames xIdx})`."] ++
            qualityStatusEvidence thingNames tables xIdx w
      | none => #[]
  | .unary "ExternallyDependentMode" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          #[
            s!"  - User assertion: `ExternallyDependentMode({indexedName thingNames xIdx})`.",
            "  - Certification treats this as a computed predicate, not as a primitive classification."
          ] ++ renderExternallyDependentModeStatus worldNames thingNames tables xIdx w
      | none => #[]
  | .binary "ExternallyDependent" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          #[
            s!"  - User assertion: `ExternallyDependent({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
            "  - Certification computes this from existential dependence plus existential independence from every bearer.",
            s!"  - Computed ExternallyDependent: false. {firstExternallyDependentFailureReason worldNames thingNames tables xIdx yIdx w}"
          ]
      | _, _ => #[]
  | .binary "ExistentialDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstBoxExImpFailure? worldNames tables xIdx yIdx with
          | some witnessWorld =>
              #[
                s!"  - User assertion: `ExistentialDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed ExistentialDependence: false, because `{indexedName thingNames xIdx}` exists at `{indexedName worldNames witnessWorld}` but `{indexedName thingNames yIdx}` does not."
              ]
          | none =>
              #[
                s!"  - User assertion: `ExistentialDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              "  - No concrete `Ex` counter-witness was isolated; inspect world-scoped `Ex` facts."
              ]
      | _, _ => #[]
  | .binary "UltimateBearerOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          let bearerIsMoment := tables.unaryLookup "moment" xIdx w
          let path? := tables.momentOfPath? thingNames.size w yIdx xIdx
          let pathEvidence :=
            match path? with
            | some path =>
                s!"`InheresIn` path exists: {renderThingPath thingNames path}."
            | none =>
                s!"no `InheresIn` path reaches `{indexedName thingNames xIdx}` from `{indexedName thingNames yIdx}` at `{indexedName worldNames w}`."
          #[
            s!"  - User assertion: `UltimateBearerOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
            s!"  - Bearer `{indexedName thingNames xIdx}` is a Moment: {if bearerIsMoment then "true" else "false"}.",
            s!"  - {pathEvidence}"
          ]
      | _, _ => #[]
  | .binary "ExistentialIndependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstExternalIndependenceFailure? worldNames thingNames tables xIdx yIdx with
          | some reason =>
              #[
                s!"  - User assertion: `ExistentialIndependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed ExistentialIndependence: false: {reason}."
              ]
          | none =>
              #[
                s!"  - User assertion: `ExistentialIndependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              "  - No concrete missing independence witness was isolated; inspect world-scoped `Ex` facts."
              ]
      | _, _ => #[]
  | .unary "NonEmptySet" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          match firstMember? thingNames.size tables xIdx w with
          | some member =>
              #[
                s!"  - User assertion: `NonEmptySet({indexedName thingNames xIdx})`.",
                s!"  - Computed NonEmptySet: true, witnessed by `MemberOf({indexedName thingNames member}, {indexedName thingNames xIdx})` at `{indexedName worldNames w}`."
              ]
          | none =>
              #[
                s!"  - User assertion: `NonEmptySet({indexedName thingNames xIdx})`.",
                s!"  - Computed NonEmptySet: false, because no `MemberOf(_, {indexedName thingNames xIdx})` fact holds at `{indexedName worldNames w}`."
              ]
      | none => #[]
  | .unary "QualityStructure" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let candidates := qualityTypeAssociations thingNames.size tables xIdx w
          if candidates.isEmpty then
            #[
              s!"  - User assertion: `QualityStructure({indexedName thingNames xIdx})`.",
              s!"  - Computed QualityStructure: false, because `{indexedName thingNames xIdx}` is not associated with any `QualityType` at `{indexedName worldNames w}`."
            ]
          else if candidates.size == 1 then
            #[
              s!"  - User assertion: `QualityStructure({indexedName thingNames xIdx})`.",
              s!"  - Computed QualityStructure: true, uniquely associated with `{indexedName thingNames candidates[0]!}`."
            ]
          else
            let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
            #[
              s!"  - User assertion: `QualityStructure({indexedName thingNames xIdx})`.",
              s!"  - Computed QualityStructure: false, because multiple associated quality types are present: {rendered}."
            ]
      | none => #[]
  | .unary "SimpleQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            #[s!"  - User assertion: `SimpleQuality({indexedName thingNames xIdx})`."] ++
              qualityStatusEvidence thingNames tables xIdx w
          else
            match firstInheringThing? thingNames.size tables xIdx w with
            | some yIdx =>
                #[
                  s!"  - User assertion: `SimpleQuality({indexedName thingNames xIdx})`.",
                  s!"  - Computed SimpleQuality: false, because `{indexedName thingNames yIdx}` inheres in `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `SimpleQuality({indexedName thingNames xIdx})`.",
                  "  - Computed SimpleQuality: true, because it is a computed `Quality` and no thing inheres in it."
                ]
      | none => #[]
  | .unary "ComplexQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            #[s!"  - User assertion: `ComplexQuality({indexedName thingNames xIdx})`."] ++
              qualityStatusEvidence thingNames tables xIdx w
          else
            match firstInheringThing? thingNames.size tables xIdx w with
            | some yIdx =>
                #[
                  s!"  - User assertion: `ComplexQuality({indexedName thingNames xIdx})`.",
                  s!"  - Computed ComplexQuality: true, witnessed by `InheresIn({indexedName thingNames yIdx}, {indexedName thingNames xIdx})` at `{indexedName worldNames w}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `ComplexQuality({indexedName thingNames xIdx})`.",
                  "  - Computed ComplexQuality: false, because it is a computed `Quality` but no thing inheres in it."
                ]
      | none => #[]
  | .unary "SimpleQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            #[
              s!"  - User assertion: `SimpleQualityType({indexedName thingNames xIdx})`.",
              s!"  - Computed SimpleQualityType: false, because `QualityType({indexedName thingNames xIdx})` is not true at `{indexedName worldNames w}`."
            ]
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !simpleQualityLookup thingNames.size tables y w then
                  return #[
                    s!"  - User assertion: `SimpleQualityType({indexedName thingNames xIdx})`.",
                    s!"  - Computed SimpleQualityType: false, because instance `{indexedName thingNames y}` is not a computed `SimpleQuality` at `{indexedName worldNames w}`."
                  ] ++ qualityStatusEvidence thingNames tables y w
              return #[
                s!"  - User assertion: `SimpleQualityType({indexedName thingNames xIdx})`.",
                "  - Computed SimpleQualityType: true; every current instance is a computed `SimpleQuality`."
              ]
      | none => #[]
  | .unary "ComplexQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            #[
              s!"  - User assertion: `ComplexQualityType({indexedName thingNames xIdx})`.",
              s!"  - Computed ComplexQualityType: false, because `QualityType({indexedName thingNames xIdx})` is not true at `{indexedName worldNames w}`."
            ]
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !complexQualityLookup thingNames.size tables y w then
                  return #[
                    s!"  - User assertion: `ComplexQualityType({indexedName thingNames xIdx})`.",
                    s!"  - Computed ComplexQualityType: false, because instance `{indexedName thingNames y}` is not a computed `ComplexQuality` at `{indexedName worldNames w}`."
                  ] ++ qualityStatusEvidence thingNames tables y w
              return #[
                s!"  - User assertion: `ComplexQualityType({indexedName thingNames xIdx})`.",
                "  - Computed ComplexQualityType: true; every current instance is a computed `ComplexQuality`."
              ]
      | none => #[]
  | .unary "QuaIndividual" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let qs := Id.run do
            let mut out := #[]
            for y in [:thingNames.size] do
              if tables.binaryLookup "quaIndividualOf" xIdx y w then
                out := out.push y
            return out
          if qs.isEmpty then
            #[
              s!"  - User assertion: `QuaIndividual({indexedName thingNames xIdx})`.",
              "  - Computed QuaIndividual: false, because no `QuaIndividualOf` fact has this thing on the left."
            ]
          else
            let rendered := String.intercalate ", " <| qs.toList.map (indexedName thingNames ·)
            #[
              s!"  - User assertion: `QuaIndividual({indexedName thingNames xIdx})`.",
              s!"  - `QuaIndividualOf` candidate(s) exist: {rendered}; inspect the corresponding §3.10 foundation diagnostics if certification still fails."
            ]
      | none => #[]
  | .binary "IsDisjointWith" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          Id.run do
            for z in [:thingNames.size] do
              if tables.binaryLookup "inst" z xIdx w && tables.binaryLookup "inst" z yIdx w then
                return #[
                  s!"  - User assertion: `IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed IsDisjointWith: false, because `{indexedName thingNames z}` instantiates both types at `{indexedName worldNames w}`."
                ]
            return #[
              s!"  - User assertion: `IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              "  - No shared instance was isolated; inspect typehood and instantiation facts."
            ]
      | _, _ => #[]
  | .binary "SubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          Id.run do
            for z in [:thingNames.size] do
              if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                return #[
                  s!"  - User assertion: `SubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed SubsetOf: false, because `{indexedName thingNames z}` is a member of `{indexedName thingNames xIdx}` but not of `{indexedName thingNames yIdx}` at `{indexedName worldNames w}`."
                ]
            return #[]
      | _, _ => #[]
  | .binary "ProperSubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          let subsetOk := subsetLookup thingNames.size tables xIdx yIdx w
          if !subsetOk then
            Id.run do
              for z in [:thingNames.size] do
                if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                  return #[
                    s!"  - User assertion: `ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                    s!"  - Computed ProperSubsetOf: false, because the subset condition already fails: `{indexedName thingNames z}` is a member of `{indexedName thingNames xIdx}` but not of `{indexedName thingNames yIdx}` at `{indexedName worldNames w}`."
                  ]
              return #[
                s!"  - User assertion: `ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                "  - Computed ProperSubsetOf: false, because the subset condition fails."
              ]
          else
            #[
              s!"  - User assertion: `ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              s!"  - Computed ProperSubsetOf: false, because no member of `{indexedName thingNames yIdx}` is outside `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`."
            ]
      | _, _ => #[]
  | .binary "ProperSub" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          let sub := tables.binaryLookup "sub" xIdx yIdx w
          let reverse := tables.binaryLookup "sub" yIdx xIdx w
          #[
            s!"  - User assertion: `ProperSub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
            s!"  - Sub({indexedName thingNames xIdx}, {indexedName thingNames yIdx}): {if sub then "true" else "false"}.",
            s!"  - Reverse Sub({indexedName thingNames yIdx}, {indexedName thingNames xIdx}): {if reverse then "true" else "false"}."
          ]
      | _, _ => #[]
  | .binary "GenericFunctionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGfdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              #[
                s!"  - User assertion: `GenericFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed GenericFunctionalDependence: false, because `{indexedName thingNames witness}` instantiates and functions as `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`, but there is no distinct thing that instantiates and functions as `{indexedName thingNames yIdx}`."
              ]
          | none =>
              #[
                s!"  - User assertion: `GenericFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."
              ]
      | _, _ => #[]
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !genericFunctionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            match firstGfdFailure? thingNames.size tables xTypeIdx yTypeIdx w with
            | some witness =>
                #[
                  s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  s!"  - Computed IndividualFunctionalDependence: false, because type-level functional dependence fails for source witness `{indexedName thingNames witness}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  "  - Computed IndividualFunctionalDependence: false, because type-level functional dependence is false."
                ]
          else if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames xIdx}` functions as `{indexedName thingNames xTypeIdx}` but `{indexedName thingNames yIdx}` does not function as `{indexedName thingNames yTypeIdx}` at `{indexedName worldNames w}`."
            ]
      | _, _, _, _ => #[]
  | .quaternary "ComponentOf" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "properPart" xIdx yIdx w then
            #[
              s!"  - User assertion: `ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed ComponentOf: false, because `ProperPart({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` is missing at `{indexedName worldNames w}`."
            ]
          else
            let ifdReason :=
              if !genericFunctionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
                match firstGfdFailure? thingNames.size tables xTypeIdx yTypeIdx w with
                | some witness =>
                    s!"type-level functional dependence fails for source witness `{indexedName thingNames witness}`"
                | none => "type-level functional dependence is false"
              else if !tables.binaryLookup "inst" xIdx xTypeIdx w then
                s!"`{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}` is missing"
              else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
                s!"`{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}` is missing"
              else
                s!"`{indexedName thingNames xIdx}` functions as `{indexedName thingNames xTypeIdx}` but `{indexedName thingNames yIdx}` does not function as `{indexedName thingNames yTypeIdx}`"
            #[
              s!"  - User assertion: `ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed ComponentOf: false, because the required individual functional dependence is false: {ifdReason}."
            ]
      | _, _, _, _ => #[]
  | .binary "GenericConstitutionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGcdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              #[
                s!"  - User assertion: `GenericConstitutionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed GenericConstitutionalDependence: false, because `{indexedName thingNames witness}` instantiates `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`, but no `{indexedName thingNames yIdx}` instance is related by `ConstitutedBy({indexedName thingNames witness}, _)`."
              ]
          | none =>
              #[
                s!"  - User assertion: `GenericConstitutionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."
              ]
      | _, _ => #[]
  | .quaternary "Constitution" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed Constitution: false, because `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed Constitution: false, because `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else if !genericConstitutionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            match firstGcdFailure? thingNames.size tables xTypeIdx yTypeIdx w with
            | some witness =>
                #[
                  s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  s!"  - Computed Constitution: false, because generic constitutional dependence fails for source witness `{indexedName thingNames witness}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  "  - Computed Constitution: false, because generic constitutional dependence is false."
                ]
          else
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed Constitution: false, because `ConstitutedBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` is missing at `{indexedName worldNames w}`."
            ]
      | _, _, _, _ => #[]
  | .binary "Categorizes" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !typeLookup worldNames.size thingNames.size tables xIdx then
            #[
              s!"  - User assertion: `Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              s!"  - Computed Categorizes: false, because `{indexedName thingNames xIdx}` is not a computed `Type`."
            ]
          else
            match firstCategorizationFailure? thingNames.size tables xIdx yIdx w with
            | some instType =>
                #[
                  s!"  - User assertion: `Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed Categorizes: false, because `{indexedName thingNames instType}` instantiates `{indexedName thingNames xIdx}` at `{indexedName worldNames w}` but `Sub({indexedName thingNames instType}, {indexedName thingNames yIdx})` is missing."
                ]
            | none =>
                #[
                  s!"  - User assertion: `Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed Categorizes: true; every instance type of `{indexedName thingNames xIdx}` specializes `{indexedName thingNames yIdx}`."
                ]
      | _, _ => #[]
  | .ternary "IsCompletelyCoveredBy" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              #[
                s!"  - User assertion: `IsCompletelyCoveredBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                s!"  - Computed IsCompletelyCoveredBy: false, because `{indexedName thingNames instIdx}` instantiates `{indexedName thingNames xIdx}` but instantiates neither covering type at `{indexedName worldNames w}`."
              ]
          | none =>
              #[
                s!"  - User assertion: `IsCompletelyCoveredBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                "  - Computed IsCompletelyCoveredBy: true; every current covered instance is assigned to at least one covering type."
              ]
      | _, _, _ => #[]
  | .ternary "IsPartitionedInto" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              #[
                s!"  - User assertion: `IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                s!"  - Computed IsPartitionedInto: false, because coverage fails: `{indexedName thingNames instIdx}` instantiates `{indexedName thingNames xIdx}` but instantiates neither covering type at `{indexedName worldNames w}`."
              ]
          | none =>
              match firstSharedInstance? thingNames.size tables yIdx zIdx w with
              | some instIdx =>
                  #[
                    s!"  - User assertion: `IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                    s!"  - Computed IsPartitionedInto: false, because disjointness fails: `{indexedName thingNames instIdx}` instantiates both covering types at `{indexedName worldNames w}`."
                  ]
              | none =>
                  #[
                    s!"  - User assertion: `IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                    "  - Coverage and disjointness counterexamples were not isolated; inspect typehood and instantiation facts."
                  ]
      | _, _, _ => #[]
  | _ => #[]

def derivedAssertionFailure?
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Option (Array String) :=
  Id.run do
    for i in [:namedFacts.size] do
      match namedFacts[i]?, scopedFacts[i]? with
      | some (.derived fact scope), some (.derived _ resolvedScope) =>
          for w in resolvedScopeWorlds worldNames resolvedScope do
            match evalNamedDerivedFact? worldNames thingNames tables fact w with
            | some true => pure ()
            | some false =>
                return some <| #[
                  s!"Counterexample assignment: w = {indexedName worldNames w}.",
                  s!"Required but missing: {derivedAssertionRequiredMissing worldNames thingNames tables fact w}",
                  s!"Suggestion: {derivedAssertionSuggestion fact}",
                  s!"Evidence: the assertion was written at `{namedScopeSummary scope}` and expands to world `{indexedName worldNames w}`."
                ] ++ derivedAssertionEvidence worldNames thingNames tables fact w
            | none =>
                return some #[
                  s!"Could not reconstruct the asserted derived relation `{namedDerivedFactSummary fact}` at the DSL level.",
                  "Suggestion: check that all mentioned things are declared and that the relation has a registered diagnostic evaluator."
                ]
      | _, _ => pure ()
    return none

def derivedAssertionAnalysis
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Array String :=
  (derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables).getD
    #["A user-written derived relation assertion failed, but the structured checker could not isolate a false asserted derived fact."]

private def ax71FoundationAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  Id.run do
    for w in [:worldNames.size] do
      for x in [:thingNames.size] do
        for y in [:thingNames.size] do
          if tables.binaryLookup "foundedBy" x y w then
            let classified :=
              externallyDependentModeLookup worldNames.size thingNames.size tables x w ||
                tables.unaryLookup "relator" x w
            let foundationOk := tables.unaryLookup "perdurant" y w
            if !(classified && foundationOk) then
              let mut out := #[
                s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}.",
                s!"Triggered by: `FoundedBy({indexedName thingNames x}, {indexedName thingNames y})`.",
                "Required together: the founded thing must be a computed `ExternallyDependentMode` or a `Relator`, and the foundation must be a `Perdurant`.",
                s!"  - Relator({indexedName thingNames x}): {if tables.unaryLookup "relator" x w then "true" else "false"}.",
                s!"  - Perdurant({indexedName thingNames y}): {if foundationOk then "true" else "false"}."
              ]
              out := out ++ renderExternallyDependentModeStatus worldNames thingNames tables x w
              if !classified then
                out := out.push "Suggestion: add the modal `Ex` variation and `InheresIn` facts needed for computed external dependence, or remove/relax the `FoundedBy` fact if this thing is not a relator or externally dependent mode."
              else if !foundationOk then
                out := out.push s!"Suggestion: classify `{indexedName thingNames y}` as `Perdurant`, or change the `FoundedBy` target to a perdurant foundation."
              return out
    return #[
      "Foundation check for ax71: every `FoundedBy` fact has a computed externally dependent mode or relator on the left and a perdurant on the right."
    ]

private def ax73FoundationAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  Id.run do
    let mut out := #[]
    for w in [:worldNames.size] do
      for x in [:thingNames.size] do
        for y in [:thingNames.size] do
          let qio := tables.binaryLookup "quaIndividualOf" x y w
          for z in [:thingNames.size] do
            let overlaps := overlapLookup tables z x w
            let rightWithoutFoundation :=
              derivedUnaryLookup worldNames.size thingNames.size tables "ExternallyDependentMode" z w &&
              tables.binaryLookup "inheresIn" z y w
            if qio && overlaps && rightWithoutFoundation then
              match foundationEq? thingNames.size tables z x w with
              | some true => pure ()
              | some false =>
                  out := out.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}."
                  out := out.push s!"Required but missing: QuaIndividualOf({indexedName thingNames x}, {indexedName thingNames y}) requires overlapping externally dependent mode `{indexedName thingNames z}` to share `FoundationOf` with `{indexedName thingNames x}`."
                  out := out.push "Suggestion: align the `FoundedBy` facts for the qua individual and its overlapping externally dependent modes, or remove/relax the `QuaIndividualOf` assertion."
                  out := out.push s!"Evidence for FoundationOf({indexedName thingNames z}) = FoundationOf({indexedName thingNames x}):"
                  out := out.push s!"  - {indexedName thingNames z}: {renderFoundationStatus thingNames tables z w}"
                  out := out.push s!"  - {indexedName thingNames x}: {renderFoundationStatus thingNames tables x w}"
                  return out
              | none =>
                  out := out.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}."
                  out := out.push s!"Missing witness requirements: QuaIndividualOf({indexedName thingNames x}, {indexedName thingNames y}) uses `FoundationOf`, but the DSL facts do not determine unique foundations for the compared terms."
                  out := out.push "Suggestion: add exactly one `FoundedBy` fact for each compared externally dependent mode/qua individual, or remove/relax the `QuaIndividualOf` assertion."
                  out := out.push s!"Evidence for FoundationOf({indexedName thingNames z}) = FoundationOf({indexedName thingNames x}):"
                  out := out.push s!"  - {indexedName thingNames z}: {renderFoundationStatus thingNames tables z w}"
                  out := out.push s!"  - {indexedName thingNames x}: {renderFoundationStatus thingNames tables x w}"
                  return out
            else
              pure ()
    if out.isEmpty then
      return #[
        "Foundation check for ax73: no DSL-level foundation mismatch was found among asserted `QuaIndividualOf` facts.",
        "If Lean still reports ax73, the remaining issue is likely the proof bridge around `FoundationOf` rather than an obvious finite-table mismatch."
      ]
    return out

private def ax78FoundationAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  Id.run do
    let mut out := #[]
    for w in [:worldNames.size] do
      for x in [:thingNames.size] do
        if tables.unaryLookup "relator" x w then
          for y in [:thingNames.size] do
            if partLookup tables y x w then
              match foundationEq? thingNames.size tables x y w with
              | some true => pure ()
              | some false =>
                  out := out.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
                  out := out.push s!"Required but missing: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` must share the same `FoundationOf`."
                  out := out.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
                  out := out.push s!"  - {indexedName thingNames x}: {renderFoundationStatus thingNames tables x w}"
                  out := out.push s!"  - {indexedName thingNames y}: {renderFoundationStatus thingNames tables y w}"
              | none =>
                  out := out.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
                  out := out.push s!"Missing witness requirements: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations."
                  out := out.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
                  out := out.push s!"  - {indexedName thingNames x}: {renderFoundationStatus thingNames tables x w}"
                  out := out.push s!"  - {indexedName thingNames y}: {renderFoundationStatus thingNames tables y w}"
    if !out.isEmpty then
      return out.push "Suggestion: align the `FoundedBy` facts for the relator and every relevant part, or remove/relax the `Relator`/`Part` assertions."
    return #[
      "Foundation check for ax78: every relator/part pair with unique DSL foundations has matching foundations.",
      "If Lean still reports ax78, inspect relator parts whose foundations are not explicitly determined by `FoundedBy` facts."
    ]

private def ax79FoundationAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  Id.run do
    for w in [:worldNames.size] do
      for x in [:thingNames.size] do
        if tables.unaryLookup "relator" x w then
          let parts := Id.run do
            let mut ps := #[]
            for y in [:thingNames.size] do
              if tables.binaryLookup "properPart" y x w then
                ps := ps.push y
            return ps
          if parts.isEmpty then
            return #[
              s!"Counterexample assignment: x = {indexedName thingNames x}, w = {indexedName worldNames w}.",
              s!"Missing witness requirements: Relator `{indexedName thingNames x}` must have at least one proper part in the finite DSL model.",
              "Suggestion: add `ProperPart(part, relator)` facts and the corresponding qua-individual/dependence/foundation facts, or remove/relax the `Relator` assertion."
            ]
          for y in parts do
            for z in parts do
              if !(derivedUnaryLookup worldNames.size thingNames.size tables "QuaIndividual" y w) ||
                  !(derivedUnaryLookup worldNames.size thingNames.size tables "QuaIndividual" z w) then
                return #[
                  s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                  s!"Required together: proper parts of relator `{indexedName thingNames x}` must be qua individuals.",
                  "Suggestion: add the missing `QuaIndividual(...)` derived assertions or remove/relax the `Relator`/`ProperPart` assertions."
                ]
              match foundationEq? thingNames.size tables y z w with
              | some true => pure ()
              | some false =>
                  return #[
                    s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                    s!"Required but missing: proper parts of relator `{indexedName thingNames x}` must share a foundation.",
                    "Suggestion: align the `FoundedBy` facts for the relator's qua-individual parts.",
                    s!"Evidence for FoundationOf({indexedName thingNames y}) = FoundationOf({indexedName thingNames z}):",
                    s!"  - {indexedName thingNames y}: {renderFoundationStatus thingNames tables y w}",
                    s!"  - {indexedName thingNames z}: {renderFoundationStatus thingNames tables z w}"
                  ]
              | none =>
                  return #[
                    s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                    s!"Missing witness requirements: ax79 compares `FoundationOf` for relator parts, but the DSL facts do not determine unique foundations.",
                    "Suggestion: add exactly one `FoundedBy` fact for each qua-individual part of the relator.",
                    s!"Evidence for FoundationOf({indexedName thingNames y}) = FoundationOf({indexedName thingNames z}):",
                    s!"  - {indexedName thingNames y}: {renderFoundationStatus thingNames tables y w}",
                    s!"  - {indexedName thingNames z}: {renderFoundationStatus thingNames tables z w}"
                  ]
              if !(derivedBinaryLookup worldNames.size thingNames.size tables "ExistentialDependence" y z w) ||
                  !(derivedBinaryLookup worldNames.size thingNames.size tables "ExistentialDependence" z y w) then
                return #[
                  s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                  s!"Required together: proper parts of relator `{indexedName thingNames x}` must be mutually existentially dependent.",
                  "Suggestion: add the missing `ExistentialDependence(...)` derived assertions or remove/relax the `Relator`/`ProperPart` assertions."
                ]
    return #[
      "Foundation check for ax79: no obvious DSL-level relator/foundation mismatch was found.",
      "If Lean still reports ax79, the remaining issue may involve the full closure direction of the relator definition."
    ]

/--
Structured diagnostic mirrors for selected certificate fields.

These formulas are not the authoritative axiom statements; they are finite-table
explainers used after Lean has already reported that a generated certificate
field failed. Keep them close to source-level vocabulary so the widget can point
modelers to facts they can add, remove, or re-scope.
-/
private def diagnosticFormula? : String → Option DiagFormula
  | "ax1" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dType "x" "w")
          (.dia "w" "w'" <| .existsThing "y" <| dInst "y" "x" "w'")
  | "ax2" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dIndividual "x" "w")
          (.box "w" "w'" <| .not <| .existsThing "y" <| dInst "y" "x" "w'")
  | "ax3" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dInst "x" "y" "w")
          (.or (dType "x" "w") (dIndividual "x" "w"))
  | "ax4" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| .existsThing "y" <| .existsThing "z" <|
          dAndList [
            dType "x" "w",
            dInst "x" "y" "w",
            dInst "y" "z" "w"
          ]
  | "ax5" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dSub "x" "y" "w")
          (dAndList [
            dType "x" "w",
            dType "y" "w",
            .box "w" "w'" <| .forallThing "z" <|
              .imp (dInst "z" "x" "w'") (dInst "z" "y" "w'")
          ])
  | "ax6" =>
      some <| .forallThing "t1" <| .forallThing "t2" <| .forallThing "x" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dInst "x" "t1" "w",
              dInst "x" "t2" "w",
              .not (dSub "t1" "t2" "w"),
              .not (dSub "t2" "t1" "w")
            ])
            (.or
              (.existsThing "t3" <| dAndList [
                dSub "t1" "t3" "w",
                dSub "t2" "t3" "w",
                dInst "x" "t3" "w"
              ])
              (.existsThing "t3" <| dAndList [
                dSub "t3" "t1" "w",
                dSub "t3" "t2" "w",
                dInst "x" "t3" "w"
              ]))
  | "ax7" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .concreteIndividual "x" "w") (dIndividual "x" "w")
  | "ax8" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .abstractIndividual "x" "w") (dIndividual "x" "w")
  | "ax9" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .concreteIndividual "x" "w")
          (.not (dUnary .abstractIndividual "x" "w"))
  | "ax10" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dIndividual "x" "w")
          (.or
            (dUnary .concreteIndividual "x" "w")
            (dUnary .abstractIndividual "x" "w"))
  | "ax11" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .endurant "x" "w") (dUnary .concreteIndividual "x" "w")
  | "ax12" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .perdurant "x" "w") (dUnary .concreteIndividual "x" "w")
  | "ax13" =>
      some <|
        .forallThing "x" <| .forallWorld "w" <|
          .imp
            (dUnary .endurant "x" "w")
            (.not (dUnary .perdurant "x" "w"))
  | "ax14" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dUnary .concreteIndividual "x" "w")
          (.or
            (dUnary .endurant "x" "w")
            (dUnary .perdurant "x" "w"))
  | "ax15" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .endurantType "x" "w") (dType "x" "w")
  | "ax16" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .perdurantType "x" "w") (dType "x" "w")
  | "ax17" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurantType "x" "w")
          (.not (dUnary .perdurantType "x" "w"))
  | "ax18" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .rigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .forallThing "x" <|
              .imp
                (.dia "w" "w'" <| dInst "x" "t" "w'")
                (.box "w" "w'" <| dInst "x" "t" "w'")
          ])
  | "ax19" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .antiRigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .forallThing "x" <|
              .imp
                (.dia "w" "w'" <| dInst "x" "t" "w'")
                (.dia "w" "w'" <| .not (dInst "x" "t" "w'"))
          ])
  | "ax20" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .semiRigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .not (dUnary .rigid "t" "w"),
            .not (dUnary .antiRigid "t" "w")
          ])
  | "ax21" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurant "x" "w")
          (.existsThing "k" <| dAndList [
            dUnary .kind "k" "w",
            .box "w" "w'" <| dInst "x" "k" "w'"
          ])
  | "ax22" =>
      some <| .forallThing "k" <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .kind "k" "w",
            dInst "x" "k" "w"
          ])
          (.not <| .dia "w" "w'" <| .existsThing "z" <| dAndList [
            dUnary .kind "z" "w'",
            dInst "x" "z" "w'",
            dNeThing "z" "k"
          ])
  | "ax23" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .sortal "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .existsThing "k" <| dAndList [
              dUnary .kind "k" "w",
              .box "w" "w'" <| .forallThing "x" <|
                .imp (dInst "x" "t" "w'") (dInst "x" "k" "w'")
            ]
          ])
  | "ax24" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .nonSortal "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .not (dUnary .sortal "t" "w")
          ])
  | "ax25" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .kind "t" "w",
          dUnary .subKind "t" "w"
        ]
  | "ax26" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .kind "t" "w",
            dUnary .subKind "t" "w"
          ])
          (dAndList [
            dUnary .rigid "t" "w",
            dUnary .sortal "t" "w"
          ])
  | "ax_kindStable" =>
      some <| .forallThing "k" <| .forallWorld "w" <| .forallWorld "v" <|
        .imp
          (dUnary .kind "k" "w")
          (dUnary .kind "k" "v")
  | "ax_instEndurant" =>
      some <| .forallThing "t" <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .endurantType "t" "w",
            dInst "x" "t" "w"
          ])
          (dUnary .endurant "x" "w")
  | "ax_sub_kind_sortal" =>
      some <| .forallThing "a" <| .forallThing "k" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dSub "a" "k" "w",
            dUnary .kind "k" "w"
          ])
          (dUnary .sortal "a" "w")
  | "ax_nonSortal_up" =>
      some <| .forallThing "a" <| .forallThing "b" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .nonSortal "a" "w",
            dSub "a" "b" "w"
          ])
          (dUnary .nonSortal "b" "w")
  | "ax27" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .phase "t" "w",
          dUnary .role "t" "w"
        ]
  | "ax28" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .phase "t" "w",
            dUnary .role "t" "w"
          ])
          (dAndList [
            dUnary .antiRigid "t" "w",
            dUnary .sortal "t" "w"
          ])
  | "ax29" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .semiRigidSortal "t" "w")
          (dAndList [
            dUnary .semiRigid "t" "w",
            dUnary .sortal "t" "w"
          ])
  | "ax30" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .category "t" "w")
          (dAndList [
            dUnary .rigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])
  | "ax31" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .mixin "t" "w")
          (dAndList [
            dUnary .semiRigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])
  | "ax32" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .phaseMixin "t" "w",
          dUnary .roleMixin "t" "w"
        ]
  | "ax33" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .phaseMixin "t" "w",
            dUnary .roleMixin "t" "w"
          ])
          (dAndList [
            dUnary .antiRigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])
  | "ax34" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .substantial "x" "w",
            dUnary .moment "x" "w"
          ])
          (dUnary .endurant "x" "w")
  | "ax35" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .substantial "x" "w",
          dUnary .moment "x" "w"
        ]
  | "ax36" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .object "x" "w",
            dUnary .collective "x" "w",
            dUnary .quantity "x" "w"
          ])
          (dUnary .substantial "x" "w")
  | "ax37" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .object "x" "w",
          dUnary .collective "x" "w"
        ]
  | "ax38" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .object "x" "w",
          dUnary .quantity "x" "w"
        ]
  | "ax39" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .collective "x" "w",
          dUnary .quantity "x" "w"
        ]
  | "ax40" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .relator "x" "w",
            dUnary .intrinsicMoment "x" "w"
          ])
          (dUnary .moment "x" "w")
  | "ax41" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .relator "x" "w",
          dUnary .intrinsicMoment "x" "w"
        ]
  | "ax42" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .mode "x" "w",
            dQuality "x" "w"
          ])
          (dUnary .intrinsicMoment "x" "w")
  | "ax43" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .mode "x" "w",
          dQuality "x" "w"
        ]
  | "ax44" =>
      some <| .forallThing "t" <| .forallWorld "w" <| dAndList [
        .iff
          (dUnary .endurantType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .endurant "x" "w'")
          ]),
        .iff
          (dUnary .perdurantType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .perdurant "x" "w'")
          ]),
        .iff
          (dUnary .substantialType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .substantial "x" "w'")
          ]),
        .iff
          (dUnary .momentType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .moment "x" "w'")
          ]),
        .iff
          (dUnary .objectType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .object "x" "w'")
          ]),
        .iff
          (dUnary .collectiveType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .collective "x" "w'")
          ]),
        .iff
          (dUnary .quantityType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .quantity "x" "w'")
          ]),
        .iff
          (dUnary .relatorType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .relator "x" "w'")
          ]),
        .iff
          (dUnary .modeType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .mode "x" "w'")
          ]),
        .iff
          (dUnary .qualityType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dQuality "x" "w'")
          ])
      ]
  | "ax45" =>
      some <| .forallThing "t" <| .forallWorld "w" <| dAndList [
        .iff
          (dUnary .objectKind "t" "w")
          (dAndList [dUnary .objectType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .collectiveKind "t" "w")
          (dAndList [dUnary .collectiveType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .quantityKind "t" "w")
          (dAndList [dUnary .quantityType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .relatorKind "t" "w")
          (dAndList [dUnary .relatorType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .modeKind "t" "w")
          (dAndList [dUnary .modeType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .qualityKind "t" "w")
          (dAndList [dUnary .qualityType "t" "w", dUnary .kind "t" "w"])
      ]
  | "ax46" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurant "x" "w")
          (.dia "w" "w'" <| .existsThing "k" <| dAndList [
            dSpecificEndurantKind "k" "w'",
            dInst "x" "k" "w'"
          ])
  | "ax47" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        dPart "x" "x" "w"
  | "ax48" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dPart "x" "y" "w",
            dPart "y" "x" "w"
          ])
          (.eqThing "x" "y")
  | "ax49" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dPart "x" "y" "w",
              dPart "y" "z" "w"
            ])
            (dPart "x" "z" "w")
  | "ax50" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dOverlap "x" "y" "w")
          (.existsThing "z" <| dAndList [
            dPart "z" "x" "w",
            dPart "z" "y" "w"
          ])
  | "ax51" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (.not (dPart "y" "x" "w"))
          (.existsThing "z" <| dAndList [
            dPart "z" "y" "w",
            .not (dOverlap "z" "x" "w")
          ])
  | "ax52" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dProperPart "x" "y" "w")
          (dAndList [
            dPart "x" "y" "w",
            .not (dPart "y" "x" "w")
          ])
  | "ax53" =>
      some <| .forallThing "x'" <| .forallThing "y'" <| .forallWorld "w" <|
        .iff
          (dGenericFunctionalDependence "x'" "y'" "w")
          (.forallThing "x" <|
            .imp
              (dAndList [
                dInst "x" "x'" "w",
                dBinary .functionsAs "x" "x'" "w"
              ])
              (.existsThing "y" <| dAndList [
                dNeThing "y" "x",
                dInst "y" "y'" "w",
                dBinary .functionsAs "y" "y'" "w"
              ]))
  | "ax54" =>
      some <| .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dIndividualFunctionalDependence "x" "x'" "y" "y'" "w")
            (dAndList [
              dGenericFunctionalDependence "x'" "y'" "w",
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              .imp
                (dBinary .functionsAs "x" "x'" "w")
                (dBinary .functionsAs "y" "y'" "w")
            ])
  | "ax55" =>
      some <| .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dComponentOf "x" "x'" "y" "y'" "w")
            (dAndList [
              dProperPart "x" "y" "w",
              dIndividualFunctionalDependence "x" "x'" "y" "y'" "w"
            ])
  | "ax56" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .constitutedBy "x" "y" "w")
          (dAndList [
            .iff (dUnary .endurant "x" "w") (dUnary .endurant "y" "w"),
            .iff (dUnary .perdurant "x" "w") (dUnary .perdurant "y" "w")
          ])
  | "ax57" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "x'" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .constitutedBy "x" "y" "w",
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              dUnary .kind "x'" "w",
              dUnary .kind "y'" "w"
            ])
            (dNeThing "x'" "y'")
  | "ax58" =>
      some <| .forallThing "x'" <| .forallThing "y'" <| .forallWorld "w" <|
        .iff
          (dGenericConstitutionalDependence "x'" "y'" "w")
          (.forallThing "x" <|
            .imp
              (dInst "x" "x'" "w")
              (.existsThing "y" <| dAndList [
                dInst "y" "y'" "w",
                dBinary .constitutedBy "x" "y" "w"
              ]))
  | "ax59" =>
      some <| .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dConstitution "x" "x'" "y" "y'" "w")
            (dAndList [
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              dGenericConstitutionalDependence "x'" "y'" "w",
              dBinary .constitutedBy "x" "y" "w"
            ])
  | "ax60" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .perdurant "x" "w",
            dBinary .constitutedBy "x" "y" "w"
          ])
          (.box "w" "w'" <|
            .imp
              (dUnary .ex "x" "w'")
              (dBinary .constitutedBy "x" "y" "w'"))
  | "ax61" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .constitutedBy "x" "y" "w")
          (.not (dBinary .constitutedBy "y" "x" "w"))
  | "ax62" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .ex "x" "w") (.eqThing "x" "x")
  | "ax63" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExistentialDependence "x" "y" "w")
          (.box "w" "w'" <|
            .imp
              (dUnary .ex "x" "w'")
              (dUnary .ex "y" "w'"))
  | "ax64" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExistentialIndependence "x" "y" "w")
          (dAndList [
            .not (dExistentialDependence "x" "y" "w"),
            .not (dExistentialDependence "y" "x" "w")
          ])
  | "ax65" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .inheresIn "x" "y" "w")
          (dExistentialDependence "x" "y" "w")
  | "ax66" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .inheresIn "x" "y" "w")
          (dAndList [
            dUnary .moment "x" "w",
            .or (dType "y" "w") (dUnary .concreteIndividual "y" "w")
          ])
  | "ax67" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .inheresIn "x" "y" "w",
              dBinary .inheresIn "x" "z" "w"
            ])
            (.eqThing "y" "z")
  | "ax69" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExternallyDependent "x" "y" "w")
          (dAndList [
            dExistentialDependence "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dBinary .inheresIn "x" "z" "w")
                (dExistentialIndependence "y" "z" "w")
          ])
  | "ax70" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dExternallyDependentMode "x" "w")
          (dAndList [
            dUnary .mode "x" "w",
            .existsThing "y" <| dExternallyDependent "x" "y" "w"
          ])
  | "ax71" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dFoundedBy "x" "y" "w")
          (dAndList [
            .or (dExternallyDependentMode "x" "w") (dUnary .relator "x" "w"),
            dUnary .perdurant "y" "w"
          ])
  | "ax72" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dExternallyDependentMode "x" "w")
          (.existsThing "y" <| dAndList [
            dFoundedBy "x" "y" "w",
            .forallThing "z" <|
              .imp (dFoundedBy "x" "z" "w") (.eqThing "z" "y")
          ])
  | "ax74" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dQuaIndividual "x" "w")
          (.existsThing "y" <| dQuaIndividualOf "x" "y" "w")
  | "ax75" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQuaIndividual "x" "w")
          (dExternallyDependentMode "x" "w")
  | "ax76" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "y'" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dQuaIndividualOf "x" "y" "w",
              dQuaIndividualOf "x" "y'" "w"
            ])
            (.eqThing "y" "y'")
  | "ax77" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .relator "x" "w")
          (.existsThing "y" <| dAndList [
            dFoundedBy "x" "y" "w",
            .forallThing "z" <|
              .imp (dFoundedBy "x" "z" "w") (.eqThing "z" "y")
          ])
  | "ax80" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dMediates "x" "y" "w")
          (dAndList [
            dUnary .relator "x" "w",
            dUnary .endurant "y" "w",
            .existsThing "z" <| dAndList [
              dQuaIndividualOf "z" "y" "w",
              dPart "z" "x" "w"
            ]
          ])
  | "axQuaIndividualOfEndurant" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dQuaIndividualOf "x" "y" "w")
          (dUnary .endurant "y" "w")
  | "ax81" =>
      some <| .forallThing "t" <| .forallThing "m" <| .forallWorld "w" <|
        .imp
          (dCharacterization "t" "m" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            dUnary .momentType "m" "w",
            .forallThing "x" <|
              .imp
                (dInst "x" "t" "w")
                (.existsThing "y" <| dAndList [
                  dInst "y" "m" "w",
                  dBinary .inheresIn "y" "x" "w"
                ]),
            .forallThing "z" <|
              .imp
                (dInst "z" "m" "w")
                (.existsThing "bearer" <| dAndList [
                  dInst "bearer" "t" "w",
                  dBinary .inheresIn "z" "bearer" "w",
                  .forallThing "otherBearer" <|
                    .imp
                      (dAndList [
                        dInst "otherBearer" "t" "w",
                        dBinary .inheresIn "z" "otherBearer" "w"
                      ])
                      (.eqThing "otherBearer" "bearer")
                ])
          ])
  | "ax82" =>
      some <| .forallThing "t" <| .forallThing "q" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dCharacterization "t" "q" "w",
            dUnary .qualityType "q" "w"
          ])
          (.forallThing "x" <|
            .imp
              (dInst "x" "q" "w")
              (.existsThing "y" <| dAndList [
                dInst "y" "t" "w",
                dBinary .inheresIn "x" "y" "w",
                .forallThing "otherBearer" <|
                  .imp
                    (dAndList [
                      dInst "otherBearer" "t" "w",
                      dBinary .inheresIn "x" "otherBearer" "w"
                    ])
                    (.eqThing "otherBearer" "y")
              ]))
  | "ax83" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .quale "x" "w")
          (dUnary .abstractIndividual "x" "w")
  | "ax84" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .set_ "x" "w")
          (dUnary .abstractIndividual "x" "w")
  | "ax85" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .quale "x" "w",
          dUnary .set_ "x" "w"
        ]
  | "ax86" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQualityStructure "x" "w")
          (dAndList [
            dUnary .set_ "x" "w",
            dNonEmptySet "x" "w"
          ])
  | "ax87" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dUnary .quale "x" "w")
          (.existsThing "y" <| dAndList [
            dQualityStructure "y" "w",
            dMemberOf "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dAndList [
                  dQualityStructure "z" "w",
                  dMemberOf "x" "z" "w"
                ])
                (.eqThing "z" "y")
          ])
  | "ax88" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dQualityStructure "x" "w")
          (.or
            (dUnary .qualityDomain "x" "w")
            (dUnary .qualityDimension "x" "w"))
  | "ax89" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .qualityDomain "x" "w")
          (.not (dUnary .qualityDimension "x" "w"))
  | "ax90" =>
      some <| .forallThing "s" <| .forallThing "t" <| .forallThing "s'" <|
        .forallThing "t'" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .associatedWith "s" "t" "w",
              dBinary .associatedWith "s'" "t'" "w",
              dProperSub "t'" "t" "w"
            ])
            (dProperSubsetOf "s'" "s" "w")
  | "ax91" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .qualityType "t" "w")
          (dAndList [
            dUnary .intrinsicMomentType "t" "w",
            .existsThing "x" <| dAndList [
              dQualityStructure "x" "w",
              dBinary .associatedWith "x" "t" "w",
              .forallThing "y" <|
                .imp
                  (dAndList [
                    dQualityStructure "y" "w",
                    dBinary .associatedWith "y" "t" "w"
                  ])
                  (.eqThing "y" "x")
            ]
          ])
  | "ax92" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .hasValue "x" "y" "w")
          (dAndList [
            dQuality "x" "w",
            dUnary .quale "y" "w"
          ])
  | "ax93" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQuality "x" "w")
          (.existsThing "y" <| dAndList [
            dBinary .hasValue "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dBinary .hasValue "x" "z" "w")
                (.eqThing "z" "y")
          ])
  | "ax94" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .hasValue "x" "y" "w")
          (.existsThing "t" <| .existsThing "s" <| dAndList [
            dInst "x" "t" "w",
            dBinary .associatedWith "s" "t" "w",
            dMemberOf "y" "s" "w"
          ])
  | "ax95" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .associatedWith "x" "y" "w")
          (.iff
            (dUnary .qualityDimension "x" "w")
            (dSimpleQualityType "y" "w"))
  | "ax96" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .associatedWith "x" "y" "w")
          (.iff
            (dUnary .qualityDomain "x" "w")
            (dComplexQualityType "y" "w"))
  | "ax97" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallThing "Y" <| .forallThing "Z" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dComplexQuality "x" "w",
              dInst "y" "Y" "w",
              dInst "z" "Z" "w",
              dBinary .inheresIn "y" "x" "w",
              dBinary .inheresIn "z" "x" "w",
              .eqThing "Y" "Z"
            ])
            (.eqThing "y" "z")
  | "ax98" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dComplexQuality "x" "w")
          (.forallThing "y" <|
            .imp
              (dBinary .inheresIn "y" "x" "w")
              (dSimpleQuality "y" "w"))
  | "ax100" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dDistance "x" "y" "r" "w")
            (dAndList [
              dUnary .quale "x" "w",
              dUnary .quale "y" "w",
              .existsThing "z" <| dAndList [
                dMemberOf "x" "z" "w",
                dMemberOf "y" "z" "w"
              ]
            ])
  | "ax101" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .quale "x" "w",
            dUnary .quale "y" "w"
          ])
          (.existsThing "r" <| dAndList [
            dDistance "x" "y" "r" "w",
            .forallThing "s" <|
              .imp
                (dDistance "x" "y" "s" "w")
                (.eqThing "s" "r")
          ])
  | "axDistanceIdentity" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              .eqThing "x" "y",
              dDistance "x" "y" "r" "w"
            ])
            (dDistanceZero "r" "w")
  | "axDistanceSymmetry" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dDistance "x" "y" "r" "w")
            (dDistance "y" "x" "r" "w")
  | "axDistanceTriangle" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallThing "r0" <| .forallThing "r1" <| .forallThing "r2" <|
        .forallThing "s" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dDistance "x" "y" "r0" "w",
              dDistance "y" "z" "r1" "w",
              dDistance "x" "z" "r2" "w",
              dDistanceSum "r0" "r1" "s" "w"
            ])
            (dDistanceGreaterEq "s" "r2" "w")
  | "ax102" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .manifests "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .endurant "y" "w"
          ])
  | "ax103" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dBinary .lifeOf "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .endurant "y" "w",
            .forallThing "z" <|
              .iff
                (dOverlap "z" "x" "w")
                (dAndList [
                  dUnary .perdurant "z" "w",
                  dBinary .manifests "z" "y" "w"
                ])
          ])
  | "ax104" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .meet "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .perdurant "y" "w"
          ])
  | _ => none

/--
Produce source-level witness text for a failed certificate field.

Specialized analyzers handle fields where the generic formula minimizer loses
important domain structure. All other registered formulas go through the same
evaluate-minimize-render pipeline.
-/
def diagnosticWitnesses
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) : Array String :=
  if field == "ax68" then
    ax68ClosureAnalysis worldNames thingNames tables
  else if field == "ax71" then
    ax71FoundationAnalysis worldNames thingNames tables
  else if field == "ax73" then
    ax73FoundationAnalysis worldNames thingNames tables
  else if field == "ax78" then
    ax78FoundationAnalysis worldNames thingNames tables
  else if field == "ax79" then
    ax79FoundationAnalysis worldNames thingNames tables
  else if field == "ax99" then
    ax99QualityDomainAnalysis worldNames thingNames tables
  else match diagnosticFormula? field with
  | none =>
      #[s!"No structured DSL-level witness extractor is registered for {field} yet."]
  | some formula =>
      let vars := formula.forallVars
      let body := formula.stripForalls
      let envs := enumerateDiagEnvs worldNames.size thingNames.size vars
      Id.run do
        let mut out := #[]
        for env in envs do
          if !evalDiagFormula worldNames.size thingNames.size tables env body then
            let minimized := minimizeFailure worldNames.size thingNames.size tables env body
            let failedFormula := minimized.formula
            let failedEnv := minimized.env
            let failedVars := diagnosticEnvVars vars failedFormula failedEnv
            let renderedCondition := renderDiagnosticCondition worldNames thingNames failedEnv failedFormula
            let conditionLine :=
              if renderedCondition.contains '\n' then
                s!"{diagnosticConditionLabel failedFormula}:\n{renderedCondition}"
              else
                s!"{diagnosticConditionLabel failedFormula}: {renderedCondition}."
            out := out.push s!"Counterexample assignment: {envSummary worldNames thingNames failedVars failedEnv}."
            out := out.push conditionLine
            out := out.push s!"Suggestion: {suggestionForFailure worldNames thingNames worldNames.size thingNames.size tables failedEnv failedFormula}"
            for trace in minimized.context do
              out := appendEvidenceForFormula worldNames thingNames namedFacts worldNames.size
                thingNames.size tables out trace.env trace.formula
            for atom in failingAtoms worldNames.size thingNames.size tables failedEnv failedFormula do
              let evidence := atomEvidence worldNames thingNames namedFacts failedEnv atom
              if !evidence.isEmpty then
                out := out.push s!"Evidence for {renderDiagAtom worldNames thingNames failedEnv atom}:"
                for item in evidence do
                  out := out.push s!"  - {item}"
        if out.isEmpty then
          return #[s!"The structured checker did not find a DSL-level witness for {field}."]
        return out


end LeanUfo.UFO.DSL
