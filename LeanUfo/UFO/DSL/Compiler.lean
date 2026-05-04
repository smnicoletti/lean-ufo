import Lean
import LeanUfo.UFO.DSL.FiniteModel

/-!
# Pure compiler core for the finite UFO DSL

This module separates the semantic DSL compiler from Lean command elaboration.
The parser in `Syntax.lean` is still metaprogramming, but it only constructs
named facts and emits the final Lean declarations. The pipeline in this file is
ordinary Lean code:

```text
NamedScopedFact
  → resolveNamedFacts
  → ScopedCompiledFact
  → expandScopedFacts
  → CompiledFact
  → addTaxonomyFacts
  → addReflexiveSpecializationFacts
  → ModelAST
  → compileExplicitModelAST
  → FactTables
  → compileExplicitModel
  → FiniteModel4
```

The resulting trust boundary is now:

* `Syntax.lean` is responsible for parsing concrete syntax and emitting Lean
  declarations;
* this file is responsible for name resolution, scoped fact expansion,
  taxonomy expansion, reflexive-specialization expansion, table compilation,
  and finite-model construction;
* `FiniteModel.lean` is responsible for interpreting the tables as
  `UFOSignature4`;
* generated `certify` declarations are still checked by Lean as ordinary
  theorems.
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
  | _ => none

/-- Primitive binary finite-table fields accepted by the resolved DSL AST. -/
inductive BinaryField where
  | inst | sub | part | overlap | properPart | functionsAs | constitutedBy
  | inheresIn | foundedBy | quaIndividualOf | mediates | characterization
  | associatedWith | hasValue | manifests | lifeOf | meet
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
  | .manifests => "manifests"
  | .lifeOf => "lifeOf"
  | .meet => "meet"

/-- Resolved DSL facts. Names have already been mapped to finite indices. -/
inductive CompiledFact where
  | unary (field : UnaryField) (thing world : Nat)
  | binary (field : BinaryField) (left right world : Nat)
  | derived (prop : String)
  deriving Repr, Inhabited

/-- Scope attached to a resolved fact before world expansion. -/
inductive FactScope where
  | at (world : Nat)
  | everywhere
  deriving Repr, Inhabited, DecidableEq

/--
Resolved facts before scope expansion.

Derived assertions carry a world-indexed proposition builder because their
generated Lean proposition mentions the concrete `Fin` world term.
-/
inductive ScopedCompiledFact where
  | unary (field : UnaryField) (thing : Nat) (scope : FactScope)
  | binary (field : BinaryField) (left right : Nat) (scope : FactScope)
  | derived (propAtWorld : Nat → String) (scope : FactScope)

/-- Scope attached to a named fact before world-name resolution. -/
inductive NamedFactScope where
  | at (world : String)
  | everywhere
  deriving Repr, Inhabited, DecidableEq

/-- Derived relation arities supported by the surface DSL. -/
inductive NamedDerivedFact where
  | unary (field thing : String)
  | binary (field left right : String)
  | ternary (field first second third : String)
  | quaternary (field first second third fourth : String)
  deriving Repr, Inhabited

/-- Named facts produced by the parser before pure name resolution. -/
inductive NamedScopedFact where
  | unary (field : UnaryField) (thing : String) (scope : NamedFactScope)
  | binary (field : BinaryField) (left right : String) (scope : NamedFactScope)
  | derived (fact : NamedDerivedFact) (scope : NamedFactScope)
  deriving Repr, Inhabited

/-- Errors that can arise during pure name resolution. -/
inductive ResolveError where
  | duplicateWorld (name : String)
  | duplicateThing (name : String)
  | unknownWorld (name : String)
  | unknownThing (name : String)
  deriving Repr, Inhabited, DecidableEq

/-- Locate a name in a declaration list. -/
def nameIndex? (xs : Array String) (x : String) : Option Nat :=
  xs.findIdx? (· == x)

private def hasDuplicate? (xs : Array String) : Option String :=
  Id.run do
    let mut seen : Std.HashSet String := {}
    for x in xs do
      if seen.contains x then
        return some x
      seen := seen.insert x
    return none

/-- Check world names for duplicates. -/
def checkWorldNames (worlds : Array String) : Except ResolveError Unit :=
  match hasDuplicate? worlds with
  | some world => throw (.duplicateWorld world)
  | none => pure ()

/-- Check thing names for duplicates. -/
def checkThingNames (things : Array String) : Except ResolveError Unit :=
  match hasDuplicate? things with
  | some thing => throw (.duplicateThing thing)
  | none => pure ()

/-- Resolve a thing name to its finite index. -/
def resolveThing (things : Array String) (thing : String) : Except ResolveError Nat :=
  match nameIndex? things thing with
  | some idx => pure idx
  | none => throw (.unknownThing thing)

/-- Resolve a world name to its finite index. -/
def resolveWorld (worlds : Array String) (world : String) : Except ResolveError Nat :=
  match nameIndex? worlds world with
  | some idx => pure idx
  | none => throw (.unknownWorld world)

/-- Resolve a named scope to an indexed scope. -/
def resolveScope (worlds : Array String) : NamedFactScope → Except ResolveError FactScope
  | .everywhere => pure .everywhere
  | .at world => return .at (← resolveWorld worlds world)

private def finThingSource (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)"

private def finWorldSource (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.worldCount)"

private def resolveDerivedFact
    (things : Array String) (fact : NamedDerivedFact) :
    Except ResolveError (Nat → String) := do
  match fact with
  | .unary field thing =>
      let idx ← resolveThing things thing
      pure fun w => s!"sig.{field} {finThingSource idx} {finWorldSource w}"
  | .binary field left right =>
      let leftIdx ← resolveThing things left
      let rightIdx ← resolveThing things right
      pure fun w =>
        s!"sig.{field} {finThingSource leftIdx} {finThingSource rightIdx} {finWorldSource w}"
  | .ternary field first second third =>
      let firstIdx ← resolveThing things first
      let secondIdx ← resolveThing things second
      let thirdIdx ← resolveThing things third
      pure fun w =>
        s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finWorldSource w}"
  | .quaternary field first second third fourth =>
      let firstIdx ← resolveThing things first
      let secondIdx ← resolveThing things second
      let thirdIdx ← resolveThing things third
      let fourthIdx ← resolveThing things fourth
      pure fun w =>
        s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finThingSource fourthIdx} {finWorldSource w}"

/-- Resolve one named scoped fact to an indexed scoped fact. -/
def resolveNamedFact
    (worlds things : Array String) : NamedScopedFact → Except ResolveError ScopedCompiledFact
  | .unary field thing scope => do
      let thingIdx ← resolveThing things thing
      let scope ← resolveScope worlds scope
      pure (.unary field thingIdx scope)
  | .binary field left right scope => do
      let leftIdx ← resolveThing things left
      let rightIdx ← resolveThing things right
      let scope ← resolveScope worlds scope
      pure (.binary field leftIdx rightIdx scope)
  | .derived fact scope => do
      let propAtWorld ← resolveDerivedFact things fact
      let scope ← resolveScope worlds scope
      pure (.derived propAtWorld scope)

/-- Resolve all named facts after checking uniqueness of world and thing names. -/
def resolveNamedFacts
    (worlds things : Array String) (facts : Array NamedScopedFact) :
    Except ResolveError (Array ScopedCompiledFact) := do
  checkWorldNames worlds
  checkThingNames things
  facts.mapM (resolveNamedFact worlds things)

/--
Resolved model AST used by the syntax frontend.

The AST deliberately stores `Nat` indices rather than names. Name lookup and
duplicate-name checks happen in the pure resolver above, before scoped facts are
expanded into ordinary `CompiledFact`s.
-/
structure ModelAST where
  worldCount : Nat
  thingCount : Nat
  facts : Array CompiledFact := #[]
  deriving Repr, Inhabited

/--
Accumulated finite table data before construction of a `FiniteModel4`.

The hash-map fields are retained for inspection and for closure steps that need
to enumerate facts. The lookup functions are the executable representation used
by `toFiniteModel4`; they normalize more predictably in generated certificates
than repeated `HashMap`/`Array.any` searches.
-/
structure FactTables where
  unary : Std.HashMap String (Array (Nat × Nat)) := {}
  binary : Std.HashMap String (Array (Nat × Nat × Nat)) := {}
  unaryLookup : String → Nat → Nat → Bool := fun _ _ _ => false
  binaryLookup : String → Nat → Nat → Nat → Bool := fun _ _ _ _ => false
  derivedProps : Array String := #[]
  deriving Inhabited

def addUnary (tables : FactTables) (field : String) (x w : Nat) : FactTables :=
  { tables with
    unary := tables.unary.insert field ((tables.unary.getD field #[]).push (x, w))
    unaryLookup := fun field' x' w' =>
      tables.unaryLookup field' x' w' || (field' == field && x' == x && w' == w) }

/--
Immediate unary taxonomy implications used to make the surface DSL lighter.

The map follows only the encoded classification hierarchy where a child
predicate has a unique positive parent path. It deliberately avoids inferences
that require choosing between disjoint alternatives.
-/
def unaryTaxonomyParents (field : String) : Array String :=
  match field with
  | "object" => #["substantial"]
  | "collective" => #["substantial"]
  | "quantity" => #["substantial"]
  | "relator" => #["moment"]
  | "intrinsicMoment" => #["moment"]
  | "mode" => #["intrinsicMoment"]
  | "substantial" => #["endurant"]
  | "moment" => #["endurant"]
  | "endurant" => #["concreteIndividual"]
  | "perdurant" => #["concreteIndividual"]
  | "quale" => #["abstractIndividual"]
  | "set_" => #["abstractIndividual"]
  | "externallyDependentMode" => #["mode"]
  | "quaIndividual" => #["externallyDependentMode"]

  | "subKind" => #["rigid", "sortal"]
  | "phase" => #["antiRigid", "sortal"]
  | "role" => #["antiRigid", "sortal"]
  | "semiRigidSortal" => #["semiRigid", "sortal"]
  | "category" => #["rigid", "nonSortal"]
  | "mixin" => #["semiRigid", "nonSortal"]
  | "phaseMixin" => #["antiRigid", "nonSortal"]
  | "roleMixin" => #["antiRigid", "nonSortal"]
  | "kind" => #["rigid", "sortal"]
  | "sortal" => #["endurantType"]
  | "nonSortal" => #["endurantType"]

  | "objectKind" => #["objectType", "kind"]
  | "collectiveKind" => #["collectiveType", "kind"]
  | "quantityKind" => #["quantityType", "kind"]
  | "relatorKind" => #["relatorType", "kind"]
  | "modeKind" => #["modeType", "kind"]
  | "qualityKind" => #["qualityType", "kind"]
  | "objectType" => #["substantialType"]
  | "collectiveType" => #["substantialType"]
  | "quantityType" => #["substantialType"]
  | "relatorType" => #["momentType"]
  | "modeType" => #["intrinsicMomentType", "momentType"]
  | "qualityType" => #["intrinsicMomentType", "momentType"]
  | "intrinsicMomentType" => #["momentType"]
  | "substantialType" => #["endurantType"]
  | "momentType" => #["endurantType"]
  | _ => #[]

/--
Insert a unary fact together with its deterministic taxonomy ancestors.

Duplicate insertions are harmless semantically, but the local `seen` set keeps
generated Boolean tables smaller and avoids cycles if the taxonomy map is
extended later.
-/
partial def addUnaryWithTaxonomyAux
    (tables : FactTables) (field : String) (x w : Nat)
    (seen : Std.HashSet String) : FactTables × Std.HashSet String :=
  if seen.contains field then
    (tables, seen)
  else
    let tables := addUnary tables field x w
    let seen := seen.insert field
    unaryTaxonomyParents field |>.foldl
      (fun (acc : FactTables × Std.HashSet String) parent =>
        addUnaryWithTaxonomyAux acc.1 parent x w acc.2)
      (tables, seen)

/-- Add a user-written unary fact and all deterministic taxonomy consequences. -/
def addUnaryWithTaxonomy (tables : FactTables) (field : String) (x w : Nat) : FactTables :=
  (addUnaryWithTaxonomyAux tables field x w {}).1

/-- Insert one binary table fact into both the inspectable store and executable lookup. -/
def addBinary (tables : FactTables) (field : String) (x y w : Nat) : FactTables :=
  { tables with
    binary := tables.binary.insert field ((tables.binary.getD field #[]).push (x, y, w))
    binaryLookup := fun field' x' y' w' =>
      tables.binaryLookup field' x' y' w' ||
        (field' == field && x' == x && y' == y && w' == w) }

/-- Record an asserted derived-relation proposition for generated checking. -/
def addDerivedProp (tables : FactTables) (prop : String) : FactTables :=
  { tables with derivedProps := tables.derivedProps.push prop }

/--
Close the specialization table under the basic reflexivity required by (a5).

In the current semantic compiler, `Type` is defined by possible instantiation:
a thing is a type iff it appears as the target of some `x :: T` fact in some
world. Since (a5) makes every type specialize itself at every world, the DSL
inserts those reflexive `T ⊑ T` facts automatically.
-/
def closeReflexiveSpecialization
    (worldCount : Nat) (tables : FactTables) : FactTables :=
  let instFacts := tables.binary.getD "inst" #[]
  let typeTargets :=
    instFacts.foldl
      (fun (seen : Std.HashSet Nat) (_x, t, _w) => seen.insert t)
      {}
  typeTargets.toArray.foldl
    (fun tables t =>
      Id.run do
        let mut tables := tables
        for w in [:worldCount] do
          tables := addBinary tables "sub" t t w
        pure tables)
    tables

/-- Compile one resolved DSL fact into finite-table data. -/
def compileFact (tables : FactTables) : CompiledFact → FactTables
  | .unary field x w => addUnaryWithTaxonomy tables field.toTableField x w
  | .binary field x y w => addBinary tables field.toTableField x y w
  | .derived prop => addDerivedProp tables prop

/-- Compile one resolved fact whose unary taxonomy closure is already explicit. -/
def compileExplicitFact (tables : FactTables) : CompiledFact → FactTables
  | .unary field x w => addUnary tables field.toTableField x w
  | .binary field x y w => addBinary tables field.toTableField x y w
  | .derived prop => addDerivedProp tables prop

/-- Compile resolved facts before global closure steps. -/
def compileFacts (facts : Array CompiledFact) : FactTables :=
  facts.foldl compileFact {}

/-- Compile a resolved model AST into finite tables, including global closures. -/
def compileModelAST (ast : ModelAST) : FactTables :=
  closeReflexiveSpecialization ast.worldCount (compileFacts ast.facts)

private def expandAtWorld (world : Nat) : ScopedCompiledFact → CompiledFact
  | .unary field x _ => .unary field x world
  | .binary field x y _ => .binary field x y world
  | .derived propAtWorld _ => .derived (propAtWorld world)

/-- Expand one scoped resolved fact into ordinary world-indexed facts. -/
def expandScopedFact (worldCount : Nat) : ScopedCompiledFact → Array CompiledFact
  | fact@(.unary _ _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.binary _ _ _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.derived _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.unary _ _ .everywhere) =>
      Id.run do
        let mut out := #[]
        for w in [:worldCount] do
          out := out.push (expandAtWorld w fact)
        pure out
  | fact@(.binary _ _ _ .everywhere) =>
      Id.run do
        let mut out := #[]
        for w in [:worldCount] do
          out := out.push (expandAtWorld w fact)
        pure out
  | fact@(.derived _ .everywhere) =>
      Id.run do
        let mut out := #[]
        for w in [:worldCount] do
          out := out.push (expandAtWorld w fact)
        pure out

/-- Expand all scoped resolved facts into ordinary world-indexed facts. -/
def expandScopedFacts (worldCount : Nat) (facts : Array ScopedCompiledFact) : Array CompiledFact :=
  facts.foldl (fun out fact => out ++ expandScopedFact worldCount fact) #[]

/-- Compile a resolved model AST whose global closure facts are already explicit. -/
def compileExplicitModelAST (ast : ModelAST) : FactTables :=
  ast.facts.foldl compileExplicitFact {}

namespace FactTables

/-- Pure Boolean table lookup for unary fields. -/
def unaryTable (tables : FactTables) (field : String)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.unaryLookup field x.val w.val

/-- Pure Boolean table lookup for binary fields. -/
def binaryTable (tables : FactTables) (field : String)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.binaryLookup field x.val y.val w.val

/--
Pure Boolean table lookup for reflexive binary fields.

`Part` and `Overlap` get identity by default, matching the original DSL emitter.
-/
def identityBinaryTable (tables : FactTables) (field : String)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  x == y || binaryTable tables field x y w

/--
Compile finite tables into a `FiniteModel4`.

This pure constructor defines the finite-model record fields used by generated
DSL models. Higher-arity primitive tables that are not yet surface syntax remain
explicit empty/default interpretations here.
-/
def toFiniteModel4
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount)
    (thingPositive : 0 < thingCount)
    (tables : FactTables) : FiniteModel4 :=
{ worldCount := worldCount
  thingCount := thingCount
  worldPositive := worldPositive
  thingPositive := thingPositive

  inst := tables.binaryTable "inst"
  sub := tables.binaryTable "sub"

  concreteIndividual := tables.unaryTable "concreteIndividual"
  abstractIndividual := tables.unaryTable "abstractIndividual"
  endurant := tables.unaryTable "endurant"
  perdurant := tables.unaryTable "perdurant"
  endurantType := tables.unaryTable "endurantType"
  perdurantType := tables.unaryTable "perdurantType"
  rigid := tables.unaryTable "rigid"
  antiRigid := tables.unaryTable "antiRigid"
  semiRigid := tables.unaryTable "semiRigid"
  kind := tables.unaryTable "kind"
  sortal := tables.unaryTable "sortal"
  nonSortal := tables.unaryTable "nonSortal"
  subKind := tables.unaryTable "subKind"
  phase := tables.unaryTable "phase"
  role := tables.unaryTable "role"
  semiRigidSortal := tables.unaryTable "semiRigidSortal"
  category := tables.unaryTable "category"
  mixin := tables.unaryTable "mixin"
  phaseMixin := tables.unaryTable "phaseMixin"
  roleMixin := tables.unaryTable "roleMixin"

  substantial := tables.unaryTable "substantial"
  moment := tables.unaryTable "moment"
  object := tables.unaryTable "object"
  collective := tables.unaryTable "collective"
  quantity := tables.unaryTable "quantity"
  relator := tables.unaryTable "relator"
  intrinsicMoment := tables.unaryTable "intrinsicMoment"
  mode := tables.unaryTable "mode"
  qualityKind := tables.unaryTable "qualityKind"

  substantialType := tables.unaryTable "substantialType"
  momentType := tables.unaryTable "momentType"
  objectType := tables.unaryTable "objectType"
  collectiveType := tables.unaryTable "collectiveType"
  quantityType := tables.unaryTable "quantityType"
  relatorType := tables.unaryTable "relatorType"
  modeType := tables.unaryTable "modeType"
  qualityType := tables.unaryTable "qualityType"
  objectKind := tables.unaryTable "objectKind"
  collectiveKind := tables.unaryTable "collectiveKind"
  quantityKind := tables.unaryTable "quantityKind"
  relatorKind := tables.unaryTable "relatorKind"
  modeKind := tables.unaryTable "modeKind"

  part := tables.identityBinaryTable "part"
  overlap := tables.identityBinaryTable "overlap"
  properPart := tables.binaryTable "properPart"

  functionsAs := tables.binaryTable "functionsAs"
  genericFunctionalDependence := tables.binaryTable "genericFunctionalDependence"
  individualFunctionalDependence := fun _ _ _ _ _ => false
  componentOf := fun _ _ _ _ _ => false

  ex := tables.unaryTable "ex"
  constitutedBy := tables.binaryTable "constitutedBy"
  genericConstitutionalDependence := tables.binaryTable "genericConstitutionalDependence"
  constitution := fun _ _ _ _ _ => false

  existentialDependence := tables.binaryTable "existentialDependence"
  existentialIndependence := tables.binaryTable "existentialIndependence"
  inheresIn := tables.binaryTable "inheresIn"

  externallyDependent := tables.binaryTable "externallyDependent"
  externallyDependentMode := tables.unaryTable "externallyDependentMode"
  foundedBy := tables.binaryTable "foundedBy"
  quaIndividualOf := tables.binaryTable "quaIndividualOf"
  quaIndividual := tables.unaryTable "quaIndividual"
  mediates := tables.binaryTable "mediates"

  characterization := tables.binaryTable "characterization"

  quale := tables.unaryTable "quale"
  set_ := tables.unaryTable "set_"
  setExtension := fun _ _ => ∅
  qualityDomain := tables.unaryTable "qualityDomain"
  qualityDimension := tables.unaryTable "qualityDimension"
  associatedWith := tables.binaryTable "associatedWith"
  intrinsicMomentType := tables.unaryTable "intrinsicMomentType"
  hasValue := tables.binaryTable "hasValue"
  tupleProjection := fun {_n} p _i _w => p
  distance := fun _ _ _ _ => false
  distanceZero := fun _ _ => false
  distanceSum := fun _ _ _ _ => false
  distanceGreaterEq := fun _ _ _ => false

  manifests := tables.binaryTable "manifests"
  lifeOf := tables.binaryTable "lifeOf"
  meet := tables.binaryTable "meet" }

end FactTables

/-- Compile a resolved AST all the way to a finite UFO model. -/
def compileModel
    (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount)
    (thingPositive : 0 < ast.thingCount) : FiniteModel4 :=
  (compileModelAST ast).toFiniteModel4
    ast.worldCount ast.thingCount worldPositive thingPositive

/-- Compile an already-expanded resolved AST all the way to a finite UFO model. -/
def compileExplicitModel
    (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount)
    (thingPositive : 0 < ast.thingCount) : FiniteModel4 :=
  (compileExplicitModelAST ast).toFiniteModel4
    ast.worldCount ast.thingCount worldPositive thingPositive

/--
Make the current reflexive-specialization closure explicit at the AST level.

This function is useful for generated declarations: certificates reduce much
better when all facts are syntactically present in the AST and table lookup does
not have to evaluate `HashSet.toArray` during proof search.
-/
def addReflexiveSpecializationFacts
    (worldCount : Nat) (facts : Array CompiledFact) : Array CompiledFact :=
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
    facts

private partial def expandUnaryTaxonomyFactAux
    (field : UnaryField) (x w : Nat) (seen : Std.HashSet String) :
    Array CompiledFact × Std.HashSet String :=
  let tableField := field.toTableField
  if seen.contains tableField then
    (#[], seen)
  else
    let seen := seen.insert tableField
    let init := (#[CompiledFact.unary field x w], seen)
    unaryTaxonomyParents tableField |>.foldl
      (fun (acc : Array CompiledFact × Std.HashSet String) parent =>
        match UnaryField.fromTableField? parent with
        | some parentField =>
            let expanded := expandUnaryTaxonomyFactAux parentField x w acc.2
            (acc.1 ++ expanded.1, expanded.2)
        | none => acc)
      init

/-- Expand one unary fact into itself plus deterministic taxonomy ancestors. -/
def expandUnaryTaxonomyFact (field : UnaryField) (x w : Nat) : Array CompiledFact :=
  (expandUnaryTaxonomyFactAux field x w {}).1

/-- Make all deterministic unary taxonomy consequences explicit in an AST fact list. -/
def addTaxonomyFacts (facts : Array CompiledFact) : Array CompiledFact :=
  facts.foldl
    (fun acc fact =>
      match fact with
      | .unary field x w => acc ++ expandUnaryTaxonomyFact field x w
      | _ => acc.push fact)
    #[]

/-- Clause theorem for unary fact compilation. -/
theorem compileFact_unary_eq
    (tables : FactTables) (field : UnaryField) (x w : Nat) :
    compileFact tables (.unary field x w) =
      addUnaryWithTaxonomy tables field.toTableField x w :=
  rfl

/-- Clause theorem for binary fact compilation. -/
theorem compileFact_binary_eq
    (tables : FactTables) (field : BinaryField) (x y w : Nat) :
    compileFact tables (.binary field x y w) = addBinary tables field.toTableField x y w :=
  rfl

/-- Clause theorem for asserted derived-relation facts. -/
theorem compileFact_derived_eq
    (tables : FactTables) (prop : String) :
    compileFact tables (.derived prop) = addDerivedProp tables prop :=
  rfl

/-- The resolved compiler is exactly fact folding followed by reflexive specialization closure. -/
theorem compileModelAST_eq (ast : ModelAST) :
    compileModelAST ast = closeReflexiveSpecialization ast.worldCount (compileFacts ast.facts) :=
  rfl

end LeanUfo.UFO.DSL
