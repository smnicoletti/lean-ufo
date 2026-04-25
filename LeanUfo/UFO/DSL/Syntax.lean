import Lean
import LeanUfo.UFO.DSL.FiniteModel

/-!
# Lean command syntax for finite UFO models

This module is the Phase 1 front end.  It deliberately stays thin:

* the **surface DSL** lets users write named worlds, named things, and named
  facts using UFO-friendly notation;
* the **command elaborator** compiles those names into finite Boolean tables
  over `Fin n`;
* the **semantic target** remains the trusted `UFOSignature4` kernel;
* the **certificate** is an ordinary theorem
  `Name.certified : UFOAxioms4 Name.sig`.

The command does not add new semantics.  It emits Lean declarations with the
same shape as a hand-written finite model, then lets Lean check the generated
proof.  If the generated finite model violates one of the currently encoded
axioms, the `certify` step fails during elaboration.

The canonical Phase 1 fact syntax is:

```lean
x : P       -- unary UFO classification predicate
x :: T      -- UFO instantiation
T₁ ⊑ T₂     -- specialization
```

For immediate extensibility, the parser also accepts binary relation facts of
the form `x Relation y`, including the mereological predicates `Part`,
`Overlap`, and `ProperPart`.  Missing facts default to `false`, except that
`Part` and `Overlap` include identity by default so that the common tiny-model
case satisfies extensional mereology without boilerplate.

The elaborator also closes unary taxonomy facts conservatively.  For example,
`x : QuantityKind` inserts the facts required by the encoded taxonomy, such as
`x : Kind`, `x : Sortal`, `x : Rigid`, `x : QuantityType`,
`x : SubstantialType`, and `x : EndurantType`.  This is DSL sugar over finite
data, not a change to the semantic kernel: certification still checks the
expanded tables against the original Prop-level axioms.

Definition-like relations may also be written explicitly.  They are not taken
as primitive semantic tables; `derive_relations` still computes their meaning
from the compiled model.  Explicit derived facts are instead
turned into a generated theorem `Name.assertedDerivedFacts`, so a misspecified
derived fact fails elaboration rather than being silently ignored.
Higher-arity derived facts use function-style syntax, for example
`IsPartitionedInto(Person, Employee, NonEmployee)`, because plain whitespace is
not a reliable arity separator in Lean command syntax.

A fact block may target the reserved pseudo-world `everywhere`.  The elaborator
expands `given everywhere:` into one copy of the block for every declared world.
This is only syntactic sugar; the compiled finite tables still contain ordinary
world-indexed facts.
-/

open Lean Elab Command Parser

namespace LeanUfo.UFO.DSL

declare_syntax_cat ufoFact
syntax (name := ufoUnaryFact) ident ":" ident : ufoFact
syntax (name := ufoInstFact) ident "::" ident : ufoFact
syntax (name := ufoSubFact) ident "⊑" ident : ufoFact
syntax (name := ufoBinaryFact) ident ident ident : ufoFact
syntax (name := ufoTernaryFact) ident "(" ident "," ident "," ident ")" : ufoFact
syntax (name := ufoQuaternaryFact) ident "(" ident "," ident "," ident "," ident ")" : ufoFact

declare_syntax_cat ufoFactBlock
syntax (name := ufoGivenAt) "given" ident ":" ppLine ufoFact* : ufoFactBlock

declare_syntax_cat ufoDeriveDirective
syntax (name := ufoDeriveRelations) "derive_relations" : ufoDeriveDirective

declare_syntax_cat ufoCertDirective
syntax (name := ufoCertify) "certify" : ufoCertDirective

syntax (name := ufoModelCmd)
  "ufo_model" ident ":" "UFO" "where"
  ppLine "worlds" ident+
  ppLine "things" ident+
  ppLine ufoFactBlock+
  ppLine ufoDeriveDirective
  ppLine ufoCertDirective : command

/-!
## Generated certificate tactic

The current proof backend is intentionally simple and transparent.  Generated
models have literal finite cardinalities and Boolean tables.  Unfolding the
compiled signature and the existing axiom definitions reduces each valid axiom
field to a finite proposition; the generated proof then uses finite-quantifier
reflection, simplification, arithmetic cleanup, and a final decidability pass.

This is checker completeness for the generated finite representation, not a
logical completeness theorem for UFO.
-/

private def certificateSimp : String :=
  "simp [sig, data, FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame,
    FiniteModel4.typeSem, FiniteModel4.individualSem, Frame.Dia, Frame.Box,
    forallFinSucc, existsFinSucc,
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
    ax_a102, ax_a103, ax_a104, ax_a105, ax_a106, ax_a107, ax_a108, Quality, QualityStructure]"

private structure FactTables where
  unary : Std.HashMap String (Array (Nat × Nat)) := {}
  binary : Std.HashMap String (Array (Nat × Nat × Nat)) := {}
  derivedProps : Array String := #[]

private def addUnary (tables : FactTables) (field : String) (x w : Nat) : FactTables :=
  { tables with unary := tables.unary.insert field ((tables.unary.getD field #[]).push (x, w)) }

/--
Immediate unary taxonomy implications used to make the surface DSL lighter.

The map follows only the encoded classification hierarchy where a child
predicate has a unique positive parent path.  It deliberately avoids inferences
that require choosing between disjoint alternatives.  For instance,
`ConcreteIndividual` does not imply `Endurant` or `Perdurant`, because the UFO
axioms say it is one of those but do not determine which one.
-/
private def unaryTaxonomyParents (field : String) : Array String :=
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

User-facing names disappear before this point: the closure is over internal
finite-table field names.  Duplicate insertions are harmless semantically, but
the local `seen` set keeps generated Boolean tables smaller and avoids cycles if
the taxonomy map is extended later.
-/
private partial def addUnaryWithTaxonomyAux
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
private def addUnaryWithTaxonomy (tables : FactTables) (field : String) (x w : Nat) : FactTables :=
  (addUnaryWithTaxonomyAux tables field x w {}).1

private def addBinary (tables : FactTables) (field : String) (x y w : Nat) : FactTables :=
  { tables with binary := tables.binary.insert field ((tables.binary.getD field #[]).push (x, y, w)) }

private def addDerivedProp (tables : FactTables) (prop : String) : FactTables :=
  { tables with derivedProps := tables.derivedProps.push prop }

/--
Close the specialization table under the basic reflexivity required by (a5).

In the current semantic compiler, `Type` is defined by possible instantiation:
a thing is a type iff it appears as the target of some `x :: T` fact in some
world.  Since (a5) makes every type specialize itself at every world, the DSL
inserts those reflexive `T ⊑ T` facts automatically.  User-written
specializations such as `Employee ⊑ Person` remain explicit.
-/
private def closeReflexiveSpecialization
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

private def indexOf? (xs : Array Name) (x : Name) : Option Nat :=
  xs.findIdx? (· == x)

private def requireIndex (kind : String) (xs : Array Name) (x : Syntax) : CommandElabM Nat := do
  match indexOf? xs x.getId with
  | some i => pure i
  | none => throwErrorAt x "unknown {kind} name `{x.getId}` in UFO model"

private def checkNoDuplicates (kind : String) (xs : Array Name) : CommandElabM Unit := do
  let mut seen : Std.HashSet Name := {}
  for x in xs do
    if seen.contains x then
      throwError "duplicate {kind} name `{x}` in UFO model"
    seen := seen.insert x

private def checkNoReservedWorldNames (xs : Array Name) : CommandElabM Unit := do
  for x in xs do
    if x == `everywhere then
      throwError "`everywhere` is reserved for facts that hold at every declared world"

private def finThing (i : Nat) : String :=
  s!"(⟨{i}, by decide⟩ : Fin data.thingCount)"

private def finWorld (i : Nat) : String :=
  s!"(⟨{i}, by decide⟩ : Fin data.worldCount)"

private def derivedUnaryField? (p : Name) : Option String :=
  match p.toString with
  | "ExternallyDependentMode" => some "ExternallyDependentMode"
  | "QuaIndividual" => some "QuaIndividual"
  | _ => none

private def derivedBinaryField? (p : Name) : Option String :=
  match p.toString with
  | "GenericFunctionalDependence" => some "GenericFunctionalDependence"
  | "GenericConstitutionalDependence" => some "GenericConstitutionalDependence"
  | "ExistentialDependence" => some "ExistentialDependence"
  | "ExistentialIndependence" => some "ExistentialIndependence"
  | "ExternallyDependent" => some "ExternallyDependent"
  | "IsDisjointWith" => some "IsDisjointWith"
  | "Categorizes" => some "Categorizes"
  | _ => none

private def derivedTernaryField? (p : Name) : Option String :=
  match p.toString with
  | "IsCompletelyCoveredBy" => some "IsCompletelyCoveredBy"
  | "IsPartitionedInto" => some "IsPartitionedInto"
  | _ => none

private def derivedQuaternaryField? (p : Name) : Option String :=
  match p.toString with
  | "IndividualFunctionalDependence" => some "IndividualFunctionalDependence"
  | "ComponentOf" => some "ComponentOf"
  | "Constitution" => some "Constitution"
  | _ => none

private def unaryField? (p : Name) : Option String :=
  match p.toString with
  | "ConcreteIndividual" => some "concreteIndividual"
  | "AbstractIndividual" => some "abstractIndividual"
  | "Endurant" => some "endurant"
  | "Perdurant" => some "perdurant"
  | "EndurantType" => some "endurantType"
  | "PerdurantType" => some "perdurantType"
  | "Rigid" => some "rigid"
  | "AntiRigid" => some "antiRigid"
  | "SemiRigid" => some "semiRigid"
  | "Kind" => some "kind"
  | "Sortal" => some "sortal"
  | "NonSortal" => some "nonSortal"
  | "SubKind" => some "subKind"
  | "Phase" => some "phase"
  | "Role" => some "role"
  | "SemiRigidSortal" => some "semiRigidSortal"
  | "Category" => some "category"
  | "Mixin" => some "mixin"
  | "PhaseMixin" => some "phaseMixin"
  | "RoleMixin" => some "roleMixin"
  | "Substantial" => some "substantial"
  | "Moment" => some "moment"
  | "Object" => some "object"
  | "Collective" => some "collective"
  | "Quantity" => some "quantity"
  | "Relator" => some "relator"
  | "IntrinsicMoment" => some "intrinsicMoment"
  | "Mode" => some "mode"
  | "QualityKind" => some "qualityKind"
  | "SubstantialType" => some "substantialType"
  | "MomentType" => some "momentType"
  | "ObjectType" => some "objectType"
  | "CollectiveType" => some "collectiveType"
  | "QuantityType" => some "quantityType"
  | "RelatorType" => some "relatorType"
  | "ModeType" => some "modeType"
  | "QualityType" => some "qualityType"
  | "ObjectKind" => some "objectKind"
  | "CollectiveKind" => some "collectiveKind"
  | "QuantityKind" => some "quantityKind"
  | "RelatorKind" => some "relatorKind"
  | "ModeKind" => some "modeKind"
  | "Ex" => some "ex"
  | "Quale" => some "quale"
  | "Set" => some "set_"
  | "Set_" => some "set_"
  | "QualityDomain" => some "qualityDomain"
  | "QualityDimension" => some "qualityDimension"
  | "IntrinsicMomentType" => some "intrinsicMomentType"
  | _ => none

private def binaryField? (p : Name) : Option String :=
  match p.toString with
  | "Part" => some "part"
  | "Overlap" => some "overlap"
  | "ProperPart" => some "properPart"
  | "FunctionsAs" => some "functionsAs"
  | "ConstitutedBy" => some "constitutedBy"
  | "InheresIn" => some "inheresIn"
  | "FoundedBy" => some "foundedBy"
  | "QuaIndividualOf" => some "quaIndividualOf"
  | "Mediates" => some "mediates"
  | "Characterization" => some "characterization"
  | "AssociatedWith" => some "associatedWith"
  | "HasValue" => some "hasValue"
  | "Manifests" => some "manifests"
  | "LifeOf" => some "lifeOf"
  | "Meet" => some "meet"
  | _ => none

private def unaryFields : Array String :=
  #["concreteIndividual", "abstractIndividual", "endurant", "perdurant",
    "endurantType", "perdurantType", "rigid", "antiRigid", "semiRigid",
    "kind", "sortal", "nonSortal", "subKind", "phase", "role",
    "semiRigidSortal", "category", "mixin", "phaseMixin", "roleMixin",
    "substantial", "moment", "object", "collective", "quantity", "relator",
    "intrinsicMoment", "mode", "qualityKind", "substantialType", "momentType",
    "objectType", "collectiveType", "quantityType", "relatorType", "modeType",
    "qualityType", "objectKind", "collectiveKind", "quantityKind",
    "relatorKind", "modeKind", "ex", "externallyDependentMode",
    "quaIndividual", "quale", "set_", "qualityDomain", "qualityDimension",
    "intrinsicMomentType"]

private def binaryFields : Array String :=
  #["inst", "sub", "part", "overlap", "properPart", "functionsAs",
    "genericFunctionalDependence", "constitutedBy", "genericConstitutionalDependence",
    "existentialDependence", "existentialIndependence", "inheresIn",
    "externallyDependent", "foundedBy", "quaIndividualOf", "mediates",
    "characterization", "associatedWith", "hasValue", "manifests", "lifeOf", "meet"]

private def boolDisj (terms : Array String) : String :=
  if terms.isEmpty then
    "false"
  else
    String.intercalate " || " terms.toList

private def unaryTable (fs : Array (Nat × Nat)) : String :=
  let terms := fs.map fun (x, w) => s!"(x.val == {x} && w.val == {w})"
  s!"fun x w => {boolDisj terms}"

private def binaryTable (fs : Array (Nat × Nat × Nat)) : String :=
  let terms := fs.map fun (x, y, w) => s!"(x.val == {x} && y.val == {y} && w.val == {w})"
  s!"fun x y w => {boolDisj terms}"

private def identityBinaryTable (fs : Array (Nat × Nat × Nat)) : String :=
  let explicit := fs.map fun (x, y, w) => s!"(x.val == {x} && y.val == {y} && w.val == {w})"
  s!"fun x y w => x == y || {boolDisj explicit}"

private def dataField (name value : String) : String :=
  s!"  {name} := {value}\n"

private def parseFact
    (_worldNames thingNames : Array Name) (currentWorld : Nat)
    (tables : FactTables) (fact : TSyntax `ufoFact) : CommandElabM FactTables := do
  match fact with
  | `(ufoFact| $x:ident : $p:ident) =>
      let xIdx ← requireIndex "thing" thingNames x
      match unaryField? p.getId with
      | some field => pure <| addUnaryWithTaxonomy tables field xIdx currentWorld
      | none =>
          match derivedUnaryField? p.getId with
          | some field =>
              pure <| addDerivedProp tables
                s!"sig.{field} {finThing xIdx} {finWorld currentWorld}"
          | none => throwErrorAt p "unsupported unary UFO predicate `{p.getId}`"
  | `(ufoFact| $x:ident :: $t:ident) =>
      let xIdx ← requireIndex "thing" thingNames x
      let tIdx ← requireIndex "thing" thingNames t
      pure <| addBinary tables "inst" xIdx tIdx currentWorld
  | `(ufoFact| $x:ident ⊑ $t:ident) =>
      let xIdx ← requireIndex "thing" thingNames x
      let tIdx ← requireIndex "thing" thingNames t
      pure <| addBinary tables "sub" xIdx tIdx currentWorld
  | `(ufoFact| $x:ident $r:ident $y:ident) =>
      let xIdx ← requireIndex "thing" thingNames x
      let yIdx ← requireIndex "thing" thingNames y
      match binaryField? r.getId with
      | some field => pure <| addBinary tables field xIdx yIdx currentWorld
      | none =>
          match derivedBinaryField? r.getId with
          | some field =>
              pure <| addDerivedProp tables
                s!"sig.{field} {finThing xIdx} {finThing yIdx} {finWorld currentWorld}"
          | none => throwErrorAt r "unsupported binary UFO relation `{r.getId}`"
  | `(ufoFact| $r:ident($x:ident, $y:ident, $z:ident)) =>
      let xIdx ← requireIndex "thing" thingNames x
      let yIdx ← requireIndex "thing" thingNames y
      let zIdx ← requireIndex "thing" thingNames z
      match derivedTernaryField? r.getId with
      | some field =>
          pure <| addDerivedProp tables
            s!"sig.{field} {finThing xIdx} {finThing yIdx} {finThing zIdx} {finWorld currentWorld}"
      | none => throwErrorAt r "unsupported ternary UFO relation `{r.getId}`"
  | `(ufoFact| $r:ident($x:ident, $y:ident, $z:ident, $q:ident)) =>
      let xIdx ← requireIndex "thing" thingNames x
      let yIdx ← requireIndex "thing" thingNames y
      let zIdx ← requireIndex "thing" thingNames z
      let qIdx ← requireIndex "thing" thingNames q
      match derivedQuaternaryField? r.getId with
      | some field =>
          pure <| addDerivedProp tables
            s!"sig.{field} {finThing xIdx} {finThing yIdx} {finThing zIdx} {finThing qIdx} {finWorld currentWorld}"
      | none => throwErrorAt r "unsupported quaternary UFO relation `{r.getId}`"
  | _ =>
      throwErrorAt fact "unsupported UFO fact syntax"

private def parseFactBlock
    (worldNames thingNames : Array Name)
    (tables : FactTables) (factBlock : TSyntax `ufoFactBlock) : CommandElabM FactTables := do
  match factBlock with
  | `(ufoFactBlock| given $factWorld:ident:
        $fs:ufoFact*) =>
      parseFactBlockContents worldNames thingNames tables factWorld fs
  | _ =>
      throwErrorAt factBlock "unsupported UFO `given` block"
where
  parseFactBlockContents
      (worldNames thingNames : Array Name) (tables : FactTables)
      (factWorld : TSyntax `ident) (fs : Array (TSyntax `ufoFact)) :
      CommandElabM FactTables := do
      let mut tables := tables
      if factWorld.getId == `everywhere then
        for wIdx in [:worldNames.size] do
          for fact in fs do
            tables ← parseFact worldNames thingNames wIdx tables fact
      else
        let wIdx ← requireIndex "world" worldNames factWorld
        for fact in fs do
          tables ← parseFact worldNames thingNames wIdx tables fact
      pure tables

private structure CertField where
  field : String
  prop : String

private def certFields : Array CertField :=
  #[
    ⟨"ax1", "ax_a1 sig.toUFOSignature3_1"⟩,
    ⟨"ax2", "ax_a2 sig.toUFOSignature3_1"⟩,
    ⟨"ax3", "ax_a3 sig.toUFOSignature3_1"⟩,
    ⟨"ax4", "ax_a4 sig.toUFOSignature3_1"⟩,
    ⟨"ax5", "ax_a5 sig.toUFOSignature3_1"⟩,
    ⟨"ax6", "ax_a6 sig.toUFOSignature3_1"⟩,
    ⟨"ax7", "ax_a7 sig.toUFOSignature3_1"⟩,
    ⟨"ax8", "ax_a8 sig.toUFOSignature3_1"⟩,
    ⟨"ax9", "ax_a9 sig.toUFOSignature3_1"⟩,
    ⟨"ax10", "ax_a10 sig.toUFOSignature3_1"⟩,
    ⟨"ax11", "ax_a11 sig.toUFOSignature3_1"⟩,
    ⟨"ax12", "ax_a12 sig.toUFOSignature3_1"⟩,
    ⟨"ax13", "ax_a13 sig.toUFOSignature3_1"⟩,
    ⟨"ax14", "ax_a14 sig.toUFOSignature3_1"⟩,
    ⟨"ax15", "ax_a15 sig.toUFOSignature3_1"⟩,
    ⟨"ax16", "ax_a16 sig.toUFOSignature3_1"⟩,
    ⟨"ax17", "ax_a17 sig.toUFOSignature3_1"⟩,
    ⟨"ax18", "ax_a18 sig.toUFOSignature3_2"⟩,
    ⟨"ax19", "ax_a19 sig.toUFOSignature3_2"⟩,
    ⟨"ax20", "ax_a20 sig.toUFOSignature3_2"⟩,
    ⟨"ax21", "ax_a21 sig.toUFOSignature3_2"⟩,
    ⟨"ax22", "ax_a22 sig.toUFOSignature3_2"⟩,
    ⟨"ax23", "ax_a23 sig.toUFOSignature3_2"⟩,
    ⟨"ax24", "ax_a24 sig.toUFOSignature3_2"⟩,
    ⟨"ax25", "ax_a25 sig.toUFOSignature3_2"⟩,
    ⟨"ax26", "ax_a26 sig.toUFOSignature3_2"⟩,
    ⟨"ax27", "ax_a27 sig.toUFOSignature3_2"⟩,
    ⟨"ax28", "ax_a28 sig.toUFOSignature3_2"⟩,
    ⟨"ax29", "ax_a29 sig.toUFOSignature3_2"⟩,
    ⟨"ax30", "ax_a30 sig.toUFOSignature3_2"⟩,
    ⟨"ax31", "ax_a31 sig.toUFOSignature3_2"⟩,
    ⟨"ax32", "ax_a32 sig.toUFOSignature3_2"⟩,
    ⟨"ax33", "ax_a33 sig.toUFOSignature3_2"⟩,
    ⟨"ax_instEndurant", "ax_instEndurant_of_EndurantType (Sig := sig.toUFOSignature3_2)"⟩,
    ⟨"ax_sub_kind_sortal", "ax_sub_of_kind_is_sortal (Sig := sig.toUFOSignature3_2)"⟩,
    ⟨"ax_nonSortal_up", "ax_nonSortal_upward (Sig := sig.toUFOSignature3_2)"⟩,
    ⟨"ax_kindStable", "ax_kindStable sig.toUFOSignature3_2"⟩,
    ⟨"ax34", "ax_a34 sig.toUFOSignature3_3"⟩,
    ⟨"ax35", "ax_a35 sig.toUFOSignature3_3"⟩,
    ⟨"ax36", "ax_a36 sig.toUFOSignature3_3"⟩,
    ⟨"ax37", "ax_a37 sig.toUFOSignature3_3"⟩,
    ⟨"ax38", "ax_a38 sig.toUFOSignature3_3"⟩,
    ⟨"ax39", "ax_a39 sig.toUFOSignature3_3"⟩,
    ⟨"ax40", "ax_a40 sig.toUFOSignature3_3"⟩,
    ⟨"ax41", "ax_a41 sig.toUFOSignature3_3"⟩,
    ⟨"ax42", "ax_a42 sig.toUFOSignature3_3"⟩,
    ⟨"ax43", "ax_a43 sig.toUFOSignature3_3"⟩,
    ⟨"ax44", "ax_a44 sig.toUFOSignature3_4"⟩,
    ⟨"ax45", "ax_a45 sig.toUFOSignature3_4"⟩,
    ⟨"ax46", "ax_a46 sig.toUFOSignature3_4"⟩,
    ⟨"ax47", "ax_a47 sig.toUFOSignature3_5"⟩,
    ⟨"ax48", "ax_a48 sig.toUFOSignature3_5"⟩,
    ⟨"ax49", "ax_a49 sig.toUFOSignature3_5"⟩,
    ⟨"ax50", "ax_a50 sig.toUFOSignature3_5"⟩,
    ⟨"ax51", "ax_a51 sig.toUFOSignature3_5"⟩,
    ⟨"ax52", "ax_a52 sig.toUFOSignature3_5"⟩,
    ⟨"ax53", "ax_a53 sig.toUFOSignature3_6"⟩,
    ⟨"ax54", "ax_a54 sig.toUFOSignature3_6"⟩,
    ⟨"ax55", "ax_a55 sig.toUFOSignature3_6"⟩,
    ⟨"ax56", "ax_a56 sig.toUFOSignature3_7"⟩,
    ⟨"ax57", "ax_a57 sig.toUFOSignature3_7"⟩,
    ⟨"ax58", "ax_a58 sig.toUFOSignature3_7"⟩,
    ⟨"ax59", "ax_a59 sig.toUFOSignature3_7"⟩,
    ⟨"ax60", "ax_a60 sig.toUFOSignature3_7"⟩,
    ⟨"ax61", "ax_a61 sig.toUFOSignature3_7"⟩,
    ⟨"ax62", "ax_a62 sig.toUFOSignature3_8"⟩,
    ⟨"ax63", "ax_a63 sig.toUFOSignature3_8"⟩,
    ⟨"ax64", "ax_a64 sig.toUFOSignature3_8"⟩,
    ⟨"ax65", "ax_a65 sig.toUFOSignature3_9"⟩,
    ⟨"ax66", "ax_a66 sig.toUFOSignature3_9"⟩,
    ⟨"ax67", "ax_a67 sig.toUFOSignature3_9"⟩,
    ⟨"ax68", "ax_a68 sig.toUFOSignature3_9"⟩,
    ⟨"ax69", "ax_a69 sig.toUFOSignature3_10"⟩,
    ⟨"ax70", "ax_a70 sig.toUFOSignature3_10"⟩,
    ⟨"ax71", "ax_a71 sig.toUFOSignature3_10"⟩,
    ⟨"ax72", "ax_a72 sig.toUFOSignature3_10"⟩,
    ⟨"ax73", "ax_a73 sig.toUFOSignature3_10"⟩,
    ⟨"ax74", "ax_a74 sig.toUFOSignature3_10"⟩,
    ⟨"ax75", "ax_a75 sig.toUFOSignature3_10"⟩,
    ⟨"ax76", "ax_a76 sig.toUFOSignature3_10"⟩,
    ⟨"ax77", "ax_a77 sig.toUFOSignature3_10"⟩,
    ⟨"ax78", "ax_a78 sig.toUFOSignature3_10"⟩,
    ⟨"ax79", "ax_a79 sig.toUFOSignature3_10"⟩,
    ⟨"ax80", "ax_a80 sig.toUFOSignature3_10"⟩,
    ⟨"axQuaIndividualOfEndurant", "ax_quaIndividualOf_endurant sig.toUFOSignature3_10"⟩,
    ⟨"ax81", "ax_a81 sig.toUFOSignature3_11"⟩,
    ⟨"ax82", "ax_a82 sig.toUFOSignature3_11"⟩,
    ⟨"ax83", "ax_a83 sig.toUFOSignature3_12"⟩,
    ⟨"ax84", "ax_a84 sig.toUFOSignature3_12"⟩,
    ⟨"ax85", "ax_a85 sig.toUFOSignature3_12"⟩,
    ⟨"ax86", "ax_a86 sig.toUFOSignature3_12"⟩,
    ⟨"ax87", "ax_a87 sig.toUFOSignature3_12"⟩,
    ⟨"ax88", "ax_a88 sig.toUFOSignature3_12"⟩,
    ⟨"ax89", "ax_a89 sig.toUFOSignature3_12"⟩,
    ⟨"ax90", "ax_a90 sig.toUFOSignature3_12"⟩,
    ⟨"ax91", "ax_a91 sig.toUFOSignature3_12"⟩,
    ⟨"ax92", "ax_a92 sig.toUFOSignature3_12"⟩,
    ⟨"ax93", "ax_a93 sig.toUFOSignature3_12"⟩,
    ⟨"ax94", "ax_a94 sig.toUFOSignature3_12"⟩,
    ⟨"ax95", "ax_a95 sig.toUFOSignature3_12"⟩,
    ⟨"ax96", "ax_a96 sig.toUFOSignature3_12"⟩,
    ⟨"ax97", "ax_a97 sig.toUFOSignature3_12"⟩,
    ⟨"ax98", "ax_a98 sig.toUFOSignature3_12"⟩,
    ⟨"ax99", "ax_a99 sig.toUFOSignature3_12"⟩,
    ⟨"ax100", "ax_a100 sig.toUFOSignature3_12"⟩,
    ⟨"ax101", "ax_a101 sig.toUFOSignature3_12"⟩,
    ⟨"axDistanceIdentity", "ax_distance_identity sig.toUFOSignature3_12"⟩,
    ⟨"axDistanceSymmetry", "ax_distance_symmetry sig.toUFOSignature3_12"⟩,
    ⟨"axDistanceTriangle", "ax_distance_triangle sig.toUFOSignature3_12"⟩,
    ⟨"ax102", "ax_a102 sig.toUFOSignature3_13"⟩,
    ⟨"ax103", "ax_a103 sig.toUFOSignature3_13"⟩,
    ⟨"ax104", "ax_a104 sig.toUFOSignature3_13"⟩,
    ⟨"ax105", "ax_a105 sig"⟩,
    ⟨"ax106", "ax_a106 sig"⟩,
    ⟨"ax107", "ax_a107 sig"⟩,
    ⟨"ax108", "ax_a108 sig"⟩
  ]

private def certTheoremName (field : String) : String :=
  s!"certified_{field}"

private def certTactic (_field : CertField) : String :=
  s!"{certificateSimp} <;> (try omega) <;> (try grind) <;> (decide +revert)"

private def certAxiomTheorem (field : CertField) : String :=
  s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem {certTheoremName field.field} : {field.prop} := by {certTactic field}"

private def certificateBody : String :=
  let fieldSource := certFields.map fun field =>
    s!"    {field.field} := {certTheoremName field.field}"
  "by\n  refine\n  {\n" ++ String.intercalate "\n" fieldSource.toList ++ "\n  }"

private def derivedFactsType (props : Array String) : String :=
  if props.isEmpty then
    "True"
  else
    String.intercalate " ∧\n  " props.toList

private def derivedFactsBody (props : Array String) : String :=
  if props.isEmpty then
    "by trivial"
  else
    s!"by\n  {certificateSimp} <;> (try omega) <;> (try grind) <;> (decide +revert)"

private def elabCommandString (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error err => throwError "failed to parse generated UFO command:\n{err}\n\nGenerated source:\n{source}"

/--
Emit the ordinary Lean declarations generated by a `ufo_model` command.

The generated namespace contains the finite data table, the compiled UFO
signature, optional checks for user-written derived-relation facts, one theorem
per axiom field, the final bundled `UFOAxioms4` certificate, and a
`FiniteModel4.Certified` packaging theorem for the generated finite data.  These
declarations are elaborated normally, so failed certification produces ordinary
Lean diagnostics.  As a consequence, the editor may also show intermediate
generated proof goals when the cursor is inside the expanded command.
-/
private def emitModel
    (model : Name) (worldNames thingNames : Array Name) (tables : FactTables) : CommandElabM Unit := do
  if worldNames.isEmpty then
    throwError "a UFO model must declare at least one world"
  if thingNames.isEmpty then
    throwError "a UFO model must declare at least one thing"

  let mut src := "def data : FiniteModel4 :=\n{\n"
  src := src ++ dataField "worldCount" (toString worldNames.size)
  src := src ++ dataField "thingCount" (toString thingNames.size)
  src := src ++ dataField "worldPositive" "by decide"
  src := src ++ dataField "thingPositive" "by decide"

  src := src ++ dataField "inst" (binaryTable (tables.binary.getD "inst" #[]))
  src := src ++ dataField "sub" (binaryTable (tables.binary.getD "sub" #[]))

  for field in unaryFields do
    src := src ++ dataField field (unaryTable (tables.unary.getD field #[]))

  for field in binaryFields do
    if field == "inst" || field == "sub" then
      pure ()
    else if field == "part" || field == "overlap" then
      src := src ++ dataField field (identityBinaryTable (tables.binary.getD field #[]))
    else
      src := src ++ dataField field (binaryTable (tables.binary.getD field #[]))

  /-
  Higher-arity primitive tables are not part of the first surface syntax.  They
  are still present in `FiniteModel4`, so the command emits explicit empty
  defaults rather than hiding them in the semantic compiler.
  -/
  src := src ++ dataField "individualFunctionalDependence" "fun _ _ _ _ _ => false"
  src := src ++ dataField "componentOf" "fun _ _ _ _ _ => false"
  src := src ++ dataField "constitution" "fun _ _ _ _ _ => false"
  src := src ++ dataField "setExtension" "fun _ _ => ∅"
  src := src ++ dataField "tupleProjection" "fun {_n} p _i _w => p"
  src := src ++ dataField "distance" "fun _ _ _ _ => false"
  src := src ++ dataField "distanceZero" "fun _ _ => false"
  src := src ++ dataField "distanceSum" "fun _ _ _ _ => false"
  src := src ++ dataField "distanceGreaterEq" "fun _ _ _ => false"
  src := src ++ "}\n"

  let modelIdent := mkIdent model
  elabCommand (← `(command| namespace $modelIdent))
  elabCommandString src
  elabCommandString "abbrev sig : UFOSignature4 := FiniteModel4.toUFOSignature4 data"
  elabCommandString
    s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem assertedDerivedFacts : {derivedFactsType tables.derivedProps} := {derivedFactsBody tables.derivedProps}"
  for field in certFields do
    elabCommandString (certAxiomTheorem field)
  elabCommandString s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem certified : UFOAxioms4 sig := {certificateBody}"
  elabCommandString "theorem certifiedModel : FiniteModel4.Certified data := certified"
  elabCommand (← `(command| end $modelIdent))

elab_rules : command
  | `(ufo_model $model:ident : UFO where
      worlds $ws:ident*
      things $ts:ident*
      $blocks:ufoFactBlock*
      $derive:ufoDeriveDirective
      $cert:ufoCertDirective) => do
    let _ := derive
    let _ := cert
    let worldNames := ws.map (·.getId)
    let thingNames := ts.map (·.getId)
    checkNoDuplicates "world" worldNames
    checkNoReservedWorldNames worldNames
    checkNoDuplicates "thing" thingNames
    let mut tables : FactTables := {}
    for factBlock in blocks do
      tables ← parseFactBlock worldNames thingNames tables factBlock
    let closedTables := closeReflexiveSpecialization worldNames.size tables
    emitModel model.getId worldNames thingNames closedTables

end LeanUfo.UFO.DSL
