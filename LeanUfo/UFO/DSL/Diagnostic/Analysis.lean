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
      tables.derivedProps.any fun prop =>
        prop == s!"sig.{field} {diagFinThingTerm thingIdx} {diagFinWorldTerm worldIdx}"
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
      tables.derivedProps.any fun prop =>
        prop == s!"sig.{field} {diagFinThingTerm leftIdx} {diagFinThingTerm rightIdx} {diagFinWorldTerm worldIdx}"
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

private def envContains (env : Array (String × Nat)) (name : String) : Bool :=
  env.any (fun entry => entry.1 == name)

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

private def derivedUnaryLookup (tables : FactTables) (field : String) (x w : Nat) : Bool :=
  tables.derivedProps.any fun prop =>
    prop == s!"sig.{field} {diagFinThingTerm x} {diagFinWorldTerm w}"

private def derivedBinaryLookup (tables : FactTables) (field : String) (x y w : Nat) : Bool :=
  tables.derivedProps.any fun prop =>
    prop == s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}"

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
      pure <| derivedUnaryLookup tables field x w
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
      pure <| derivedBinaryLookup tables field x y w
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
  | .quaternary _ _ _ _ _ =>
      none

private def derivedAssertionSuggestion (fact : NamedDerivedFact) : String :=
  match fact with
  | .binary "IsDisjointWith" _ _ =>
      "Remove the assertion, or remove the common instance facts that make the two types overlap."
  | .ternary "IsCompletelyCoveredBy" _ _ _ =>
      "Remove the assertion, or add missing instantiation facts so every instance of the covered type instantiates at least one covering type."
  | .ternary "IsPartitionedInto" _ _ _ =>
      "Remove the assertion, or make the cover complete and the two covering types disjoint."
  | .binary "Categorizes" _ _ =>
      "Remove the assertion, or add the missing specialization facts from each category-instance type to the categorized type."
  | _ =>
      "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."

def derivedAssertionAnalysis
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Array String :=
  Id.run do
    for i in [:namedFacts.size] do
      match namedFacts[i]?, scopedFacts[i]? with
      | some (.derived fact scope), some (.derived _ resolvedScope) =>
          for w in resolvedScopeWorlds worldNames resolvedScope do
            match evalNamedDerivedFact? worldNames thingNames tables fact w with
            | some true => pure ()
            | some false =>
                return #[
                  s!"Counterexample assignment: w = {indexedName worldNames w}.",
                  s!"Required but missing: asserted derived relation `{namedDerivedFactSummary fact}` is false in the generated finite model.",
                  s!"Suggestion: {derivedAssertionSuggestion fact}",
                  s!"Evidence: the assertion was written at `{namedScopeSummary scope}` and expands to world `{indexedName worldNames w}`."
                ]
            | none =>
                return #[
                  s!"Could not reconstruct the asserted derived relation `{namedDerivedFactSummary fact}` at the DSL level.",
                  "Suggestion: check that all mentioned things are declared and that the relation has a registered diagnostic evaluator."
                ]
      | _, _ => pure ()
    return #["A user-written derived relation assertion failed, but the structured checker could not isolate a false asserted derived fact."]

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
              derivedUnaryLookup tables "ExternallyDependentMode" z w &&
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
    for w in [:worldNames.size] do
      for x in [:thingNames.size] do
        if tables.unaryLookup "relator" x w then
          for y in [:thingNames.size] do
            if partLookup tables y x w then
              match foundationEq? thingNames.size tables x y w with
              | some true => pure ()
              | some false =>
                  return #[
                    s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}.",
                    s!"Required but missing: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` must share the same `FoundationOf`.",
                    "Suggestion: align the `FoundedBy` facts for the relator and its parts, or remove/relax the `Relator`/`Part` assertions.",
                    s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):",
                    s!"  - {indexedName thingNames x}: {renderFoundationStatus thingNames tables x w}",
                    s!"  - {indexedName thingNames y}: {renderFoundationStatus thingNames tables y w}"
                  ]
              | none =>
                  return #[
                    s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}.",
                    s!"Missing witness requirements: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations.",
                    "Suggestion: add exactly one `FoundedBy` fact for the relator and for each relevant part, or remove/relax the `Relator`/`Part` assertions.",
                    s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):",
                    s!"  - {indexedName thingNames x}: {renderFoundationStatus thingNames tables x w}",
                    s!"  - {indexedName thingNames y}: {renderFoundationStatus thingNames tables y w}"
                  ]
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
              if !(derivedUnaryLookup tables "QuaIndividual" y w) ||
                  !(derivedUnaryLookup tables "QuaIndividual" z w) then
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
              if !(derivedBinaryLookup tables "ExistentialDependence" y z w) ||
                  !(derivedBinaryLookup tables "ExistentialDependence" z y w) then
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
