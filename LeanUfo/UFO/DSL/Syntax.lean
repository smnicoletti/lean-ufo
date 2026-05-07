import Lean
import Lean.Widget
import LeanUfo.UFO.DSL.Compiler

/-!
# Lean command syntax for finite UFO models

This module is the Phase 1 front end.  It deliberately stays thin:

* the **surface DSL** lets users write named worlds, named things, and named
  facts using UFO-friendly notation;
* the **command elaborator** parses those facts into a named AST and delegates
  name resolution, scope expansion, taxonomy expansion, table compilation, and
  finite-model construction to the pure compiler in `Compiler.lean`;
* the **semantic target** remains the trusted `UFOSignature4` kernel;
* the **certificate** is an ordinary theorem
  `Name.certified : UFOAxioms4 Name.sig`.

The command does not add new semantics.  It emits ordinary Lean declarations
for the resolved/expanded AST, the compiled finite model, and the generated
certificate, then lets Lean check them.  If the generated finite model violates
one of the currently encoded axioms, the `certify` step fails during
elaboration.

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

The pure compiler also closes unary taxonomy facts conservatively.  For example,
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
records this as a scoped fact, and the pure compiler expands it into one copy
for every declared world. This is only syntactic sugar; the compiled finite
tables still contain ordinary world-indexed facts.
-/

open Lean Elab Command Parser

namespace LeanUfo.UFO.DSL

@[widget_module]
def ufoDiagnosticsWidget : Widget.Module where
  javascript := "
import * as React from 'react';

const e = React.createElement;

function item(text, key) {
  return e('li', { key }, text);
}

function Section({ title, children }) {
  return e('section', { style: { marginTop: '0.75rem' } },
    e('h4', { style: { margin: '0 0 0.35rem', fontSize: '0.95rem' } }, title),
    children);
}

function MappingTable({ rows }) {
  return e('table', { style: { width: '100%', borderCollapse: 'collapse', fontSize: '0.85rem' } },
    e('thead', null,
      e('tr', null,
        e('th', { style: { textAlign: 'left', borderBottom: '1px solid var(--vscode-panel-border)' } }, 'Name'),
        e('th', { style: { textAlign: 'right', borderBottom: '1px solid var(--vscode-panel-border)' } }, 'Fin index'))),
    e('tbody', null, rows.map((row, i) =>
      e('tr', { key: row.name + i },
        e('td', { style: { padding: '2px 0' } }, row.name),
        e('td', { style: { padding: '2px 0', textAlign: 'right', opacity: 0.75 } }, String(row.index))))));
}

function StatusBadge({ status }) {
  const colors = {
    success: '#2ea043',
    failed: '#f85149',
    pending: '#d29922',
    unchecked: '#8b949e',
    skipped: '#8b949e'
  };
  const color = colors[status] || colors.pending;
  return e('span', {
    style: {
      display: 'inline-block',
      minWidth: '4.4rem',
      color,
      fontWeight: 600,
      textTransform: 'capitalize'
    }
  }, status);
}

function CertificationRow({ row }) {
  return e('div', {
    title: row.formula || row.prop || '',
    style: {
      display: 'grid',
      gridTemplateColumns: '4.8rem max-content max-content 1fr',
      alignItems: 'baseline',
      columnGap: '0.5rem',
      fontSize: '0.85rem',
      marginBottom: '0.2rem',
      minWidth: 'max-content'
    }
  },
    e(StatusBadge, { status: row.status }),
    e('code', null, row.field),
    e('code', {
      style: {
        opacity: 0.75,
        whiteSpace: 'nowrap'
      }
    }, row.prop || ''),
    row.formula
      ? e('span', {
          style: {
            opacity: 0.9,
            whiteSpace: 'nowrap'
          }
        }, row.formula)
      : null);
}

export default function(props) {
  const facts = props.facts || [];
  const expandedFacts = props.expandedFacts || [];
  const statuses = props.certification || [];
  const failed = statuses.find(s => s.status === 'failed');

  return e('div', {
    style: {
      padding: '0.75rem',
      lineHeight: 1.35,
      maxWidth: 'none',
      overflowX: 'auto'
    }
  },
    e('h3', { style: { margin: '0 0 0.25rem' } }, 'UFO diagnostics'),
    e('div', { style: { opacity: 0.8, marginBottom: '0.5rem' } },
      props.model ? 'Model: ' + props.model : 'DSL model'),
    failed
      ? e('div', { style: { color: '#f85149', fontWeight: 600, marginBottom: '0.5rem' } },
          'Certification stopped at ', failed.field, '.')
      : props.failure
      ? e('div', { style: { color: '#f85149', fontWeight: 600, marginBottom: '0.5rem' } },
          props.failure)
      : e('div', { style: { color: '#2ea043', fontWeight: 600, marginBottom: '0.5rem' } },
          props.stage === 'certified' ? 'All generated certificate checks completed.' : 'Parsed model diagnostics are available.'),

    e(Section, { title: 'Worlds' }, e(MappingTable, { rows: props.worlds || [] })),
    e(Section, { title: 'Things' }, e(MappingTable, { rows: props.things || [] })),

    e(Section, { title: 'Input facts' },
      facts.length
        ? e('ul', { style: { margin: 0, paddingLeft: '1.2rem' } }, facts.map(item))
        : e('div', { style: { opacity: 0.75 } }, 'No input facts recorded.')),

    e(Section, { title: 'Expanded finite facts' },
      expandedFacts.length
        ? e('details', null,
            e('summary', null, expandedFacts.length + ' compiled facts'),
            e('ul', { style: { margin: '0.35rem 0 0', paddingLeft: '1.2rem' } }, expandedFacts.map(item)))
        : e('div', { style: { opacity: 0.75 } }, 'No expanded facts recorded.')),

    e(Section, { title: 'Certification' },
      statuses.length
        ? e('details', { open: !!failed },
            e('summary', null,
              failed ? 'Stopped at ' + failed.field : statuses.filter(s => s.status === 'success').length + ' certificate checks'),
            e('div', { style: { marginTop: '0.35rem', overflowX: 'auto' } }, statuses.map((s, i) =>
              e(CertificationRow, { key: s.field + i, row: s }))))
        : e('div', { style: { opacity: 0.75 } }, 'Certification has not started.')))
}
"

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
  "simp [sig, data, tables, ast, compileModel, compileModelAST, compileFacts, compileFact,
    compileExplicitModel, compileExplicitModelAST, compileExplicitFact,
    FactTables.toFiniteModel4, FactTables.unaryTable, FactTables.binaryTable,
    FactTables.identityBinaryTable, addUnary, addUnaryWithTaxonomy, addUnaryWithTaxonomyAux,
    addBinary, addDerivedProp, closeReflexiveSpecialization, unaryTaxonomyParents,
    UnaryField.toTableField, BinaryField.toTableField,
    FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame,
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

syntax (name := ufoCertTactic) "ufo_cert_tac" : tactic

@[tactic ufoCertTactic] def evalUFOCertTactic : Lean.Elab.Tactic.Tactic := fun _ => do
  let source := s!"{certificateSimp} <;> (try omega) <;> (try grind) <;> (decide +revert)"
  match Parser.runParserCategory (← getEnv) `tactic source with
  | .ok stx =>
      Lean.Elab.Term.withoutErrToSorry <|
        Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic stx
  | .error err => throwError "failed to parse generated UFO certificate tactic:\n{err}"

private def checkNoReservedWorldNames (xs : Array Name) : CommandElabM Unit := do
  for x in xs do
    if x == `everywhere then
      throwError "`everywhere` is reserved for facts that hold at every declared world"

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

private def unaryField? (p : Name) : Option UnaryField :=
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
  | _ => none

private def binaryField? (p : Name) : Option BinaryField :=
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
  | "Manifests" => some .manifests
  | "LifeOf" => some .lifeOf
  | "Meet" => some .meet
  | _ => none

private def dataField (name value : String) : String :=
  s!"  {name} := {value}\n"

private def unaryFieldTerm : UnaryField → String
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

private def binaryFieldTerm : BinaryField → String
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
  | .manifests => ".manifests"
  | .lifeOf => ".lifeOf"
  | .meet => ".meet"

private def leanStringLit (s : String) : String :=
  reprStr s

private def compiledFactTerm : CompiledFact → String
  | .unary field x w => s!"CompiledFact.unary {unaryFieldTerm field} {x} {w}"
  | .binary field x y w => s!"CompiledFact.binary {binaryFieldTerm field} {x} {y} {w}"
  | .derived prop => s!"CompiledFact.derived {leanStringLit prop}"

private def indexedNamesJson (names : Array Name) : Json :=
  Json.arr <| names.mapIdx fun idx name =>
    Json.mkObj [
      ("name", name.toString),
      ("index", idx)
    ]

private def indexedName (names : Array Name) (idx : Nat) : String :=
  match names[idx]? with
  | some name => name.toString
  | none => s!"#{idx}"

private def namedScopeSummary : NamedFactScope → String
  | .at world => world
  | .everywhere => "everywhere"

private def namedDerivedFactSummary : NamedDerivedFact → String
  | .unary field thing => s!"{thing} : {field}"
  | .binary field left right => s!"{left} {field} {right}"
  | .ternary field first second third => s!"{field}({first}, {second}, {third})"
  | .quaternary field first second third fourth =>
      s!"{field}({first}, {second}, {third}, {fourth})"

private def scopedWorldNames (worldNames : Array Name) : NamedFactScope → Array String
  | .at world => #[world]
  | .everywhere => worldNames.map (·.toString)

private def namedFactSummary : NamedScopedFact → String
  | .unary field thing scope =>
      s!"[{namedScopeSummary scope}] {thing} : {field.toTableField}"
  | .binary .inst left right scope =>
      s!"[{namedScopeSummary scope}] {left} :: {right}"
  | .binary .sub left right scope =>
      s!"[{namedScopeSummary scope}] {left} ⊑ {right}"
  | .binary field left right scope =>
      s!"[{namedScopeSummary scope}] {left} {field.toTableField} {right}"
  | .derived fact scope =>
      s!"[{namedScopeSummary scope}] {namedDerivedFactSummary fact}"

private def derivedPropSummaryPairs
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

private def derivedPropSummary (pairs : Array (String × String)) (prop : String) : Option String :=
  pairs.findSome? fun pair =>
    if pair.1 == prop then some pair.2 else none

private def compiledFactSummary
    (worldNames thingNames : Array Name) (derivedPairs : Array (String × String)) :
    CompiledFact → String
  | .unary field thing world =>
      s!"[{indexedName worldNames world}] {indexedName thingNames thing} : {field.toTableField}"
  | .binary .inst left right world =>
      s!"[{indexedName worldNames world}] {indexedName thingNames left} :: {indexedName thingNames right}"
  | .binary .sub left right world =>
      s!"[{indexedName worldNames world}] {indexedName thingNames left} ⊑ {indexedName thingNames right}"
  | .binary field left right world =>
      s!"[{indexedName worldNames world}] {indexedName thingNames left} {field.toTableField} {indexedName thingNames right}"
  | .derived prop => (derivedPropSummary derivedPairs prop).getD prop

private def stringsJson (xs : Array String) : Json :=
  Json.arr <| xs.map Json.str

private def modelASTSource (worldCount thingCount : Nat) (facts : Array CompiledFact) : String :=
  let factTerms := facts.map compiledFactTerm
  let factArray :=
    if factTerms.isEmpty then
      "#[]"
    else
      "#[" ++ String.intercalate ", " factTerms.toList ++ "]"
  "def ast : ModelAST :=\n" ++
    "{\n" ++
    dataField "worldCount" (toString worldCount) ++
    dataField "thingCount" (toString thingCount) ++
    dataField "facts" factArray ++
    "}\n"

private def parseFact
    (_worldNames _thingNames : Array Name) (scope : NamedFactScope)
    (facts : Array NamedScopedFact) (fact : TSyntax `ufoFact) :
    CommandElabM (Array NamedScopedFact) := do
  match fact with
  | `(ufoFact| $x:ident : $p:ident) =>
      let xName := x.getId.toString
      match unaryField? p.getId with
      | some field => pure <| facts.push (.unary field xName scope)
      | none =>
          match derivedUnaryField? p.getId with
          | some field =>
              pure <| facts.push (.derived (.unary field xName) scope)
          | none => throwErrorAt p "unsupported unary UFO predicate `{p.getId}`"
  | `(ufoFact| $x:ident :: $t:ident) =>
      pure <| facts.push (.binary .inst x.getId.toString t.getId.toString scope)
  | `(ufoFact| $x:ident ⊑ $t:ident) =>
      pure <| facts.push (.binary .sub x.getId.toString t.getId.toString scope)
  | `(ufoFact| $x:ident $r:ident $y:ident) =>
      let xName := x.getId.toString
      let yName := y.getId.toString
      match binaryField? r.getId with
      | some field => pure <| facts.push (.binary field xName yName scope)
      | none =>
          match derivedBinaryField? r.getId with
          | some field =>
              pure <| facts.push (.derived (.binary field xName yName) scope)
          | none => throwErrorAt r "unsupported binary UFO relation `{r.getId}`"
  | `(ufoFact| $r:ident($x:ident, $y:ident, $z:ident)) =>
      let xName := x.getId.toString
      let yName := y.getId.toString
      let zName := z.getId.toString
      match derivedTernaryField? r.getId with
      | some field =>
          pure <| facts.push (.derived (.ternary field xName yName zName) scope)
      | none => throwErrorAt r "unsupported ternary UFO relation `{r.getId}`"
  | `(ufoFact| $r:ident($x:ident, $y:ident, $z:ident, $q:ident)) =>
      let xName := x.getId.toString
      let yName := y.getId.toString
      let zName := z.getId.toString
      let qName := q.getId.toString
      match derivedQuaternaryField? r.getId with
      | some field =>
          pure <| facts.push (.derived (.quaternary field xName yName zName qName) scope)
      | none => throwErrorAt r "unsupported quaternary UFO relation `{r.getId}`"
  | _ =>
      throwErrorAt fact "unsupported UFO fact syntax"

private def parseFactBlock
    (worldNames thingNames : Array Name)
    (facts : Array NamedScopedFact) (factBlock : TSyntax `ufoFactBlock) :
    CommandElabM (Array NamedScopedFact) := do
  match factBlock with
  | `(ufoFactBlock| given $factWorld:ident:
        $fs:ufoFact*) =>
      parseFactBlockContents worldNames thingNames facts factWorld fs
  | _ =>
      throwErrorAt factBlock "unsupported UFO `given` block"
where
  parseFactBlockContents
      (worldNames thingNames : Array Name) (facts : Array NamedScopedFact)
      (factWorld : TSyntax `ident) (fs : Array (TSyntax `ufoFact)) :
      CommandElabM (Array NamedScopedFact) := do
      let mut facts := facts
      let scope :=
        if factWorld.getId == `everywhere then
          NamedFactScope.everywhere
        else
          NamedFactScope.at factWorld.getId.toString
      for fact in fs do
        facts ← parseFact worldNames thingNames scope facts fact
      pure facts

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

private def certFormula : String → String
  | "ax1" => "Type(x) ↔ ◇(∃ y, y :: x)"
  | "ax2" => "Individual(x) ↔ □(¬∃ y, y :: x)"
  | "ax3" => "x :: y → (Type(x) ∨ Individual(x))"
  | "ax4" => "¬∃ x y z, Type(x) ∧ x :: y ∧ y :: z"
  | "ax5" => "Type(x) → x ⊑ x"
  | "ax6" => "x ⊏ y ↔ x ⊑ y ∧ ¬ y ⊑ x"
  | "ax7" => "AbstractIndividual(x) → Individual(x)"
  | "ax8" => "ConcreteIndividual(x) → Individual(x)"
  | "ax9" => "Type(x) → ¬ Individual(x)"
  | "ax10" => "Thing(x) → Individual(x) ∨ Type(x)"
  | "ax11" => "Endurant(x) → ConcreteIndividual(x)"
  | "ax12" => "Perdurant(x) → ConcreteIndividual(x)"
  | "ax13" => "AbstractIndividual(x) → ¬ ConcreteIndividual(x)"
  | "ax14" => "ConcreteIndividual(x) ↔ Endurant(x) ∨ Perdurant(x)"
  | "ax15" => "Endurant(x) → ¬ Perdurant(x)"
  | "ax16" => "EndurantType(x) → Type(x)"
  | "ax17" => "PerdurantType(x) → Type(x)"
  | "ax18" => "Rigid(x) → EndurantType(x)"
  | "ax19" => "AntiRigid(x) → EndurantType(x)"
  | "ax20" => "SemiRigid(x) → EndurantType(x)"
  | "ax21" => "EndurantType(x) → (Rigid(x) ∨ AntiRigid(x) ∨ SemiRigid(x))"
  | "ax22" => "Kind(k) ∧ x :: k → ¬◇(∃ z, Kind(z) ∧ x :: z ∧ z ≠ k)"
  | "ax23" => "Sortal(x) → EndurantType(x)"
  | "ax24" => "NonSortal(x) → EndurantType(x)"
  | "ax25" => "EndurantType(x) → Sortal(x) ∨ NonSortal(x)"
  | "ax26" => "Kind(x) ∨ SubKind(x) ↔ Rigid(x) ∧ Sortal(x)"
  | "ax27" => "SubKind(x) → ∃ k, Kind(k) ∧ x ⊑ k"
  | "ax28" => "Phase(x) ∨ Role(x) ↔ AntiRigid(x) ∧ Sortal(x)"
  | "ax29" => "SemiRigidSortal(x) ↔ SemiRigid(x) ∧ Sortal(x)"
  | "ax30" => "Category(x) ↔ Rigid(x) ∧ NonSortal(x)"
  | "ax31" => "Mixin(x) ↔ SemiRigid(x) ∧ NonSortal(x)"
  | "ax32" => "PhaseMixin(x) ∨ RoleMixin(x) ↔ AntiRigid(x) ∧ NonSortal(x)"
  | "ax33" => "EndurantType(x) → exactly one rigidity class and exactly one sortality class"
  | "ax_instEndurant" => "EndurantType(t) ∧ x :: t → Endurant(x)"
  | "ax_sub_kind_sortal" => "x ⊑ k ∧ Kind(k) → Sortal(x)"
  | "ax_nonSortal_up" => "NonSortal(x) ∧ x ⊑ y → NonSortal(y)"
  | "ax_kindStable" => "Kind(k) → □ Kind(k)"
  | "ax34" => "Endurant(x) ↔ Substantial(x) ∨ Moment(x)"
  | "ax35" => "Substantial(x) → ¬ Moment(x)"
  | "ax36" => "Substantial(x) ↔ Object(x) ∨ Collective(x) ∨ Quantity(x)"
  | "ax37" => "Object(x) → ¬ Collective(x)"
  | "ax38" => "Object(x) → ¬ Quantity(x)"
  | "ax39" => "Collective(x) → ¬ Quantity(x)"
  | "ax40" => "Moment(x) ↔ Relator(x) ∨ IntrinsicMoment(x)"
  | "ax41" => "Relator(x) → ¬ IntrinsicMoment(x)"
  | "ax42" => "IntrinsicMoment(x) ↔ Mode(x) ∨ Quality(x)"
  | "ax43" => "Mode(x) → ¬ Quality(x)"
  | "ax44" => "EndurantType taxonomy mirrors Endurant taxonomy"
  | "ax45" => "Specific kind predicates imply matching type predicate and Kind"
  | "ax46" => "EndurantType(x) → ∃ k, Kind(k) ∧ x ⊑ k"
  | "ax47" => "Part(x, x)"
  | "ax48" => "Part(x, y) ∧ Part(y, z) → Part(x, z)"
  | "ax49" => "ProperPart(x, y) ↔ Part(x, y) ∧ ¬ Part(y, x)"
  | "ax50" => "Overlap(x, y) ↔ ∃ z, Part(z, x) ∧ Part(z, y)"
  | "ax51" => "Overlap(x, y) → Overlap(y, x)"
  | "ax52" => "(∀ z, ProperPart(z, x) ↔ ProperPart(z, y)) → x = y"
  | "ax53" => "IndividualFunctionalDependence(x, y, x', y') → y ≠ x"
  | "ax54" => "GenericFunctionalDependence(x', y') ↔ ∀ x, x :: x' → ∃ y, y :: y' ∧ IndividualFunctionalDependence(x, y, x', y')"
  | "ax55" => "IndividualFunctionalDependence(x, y, x', y') → x :: x' ∧ y :: y'"
  | "ax56" => "constitutedBy(x, y) → ((Endurant(x) ↔ Endurant(y)) ∧ (Perdurant(x) ↔ Perdurant(y)))"
  | "ax57" => "constitutedBy(x, y) ∧ x :: x' ∧ y :: y' ∧ Kind(x') ∧ Kind(y') → x' ≠ y'"
  | "ax58" => "GCD(x', y') ↔ ∀ x, x :: x' → ∃ y, y :: y' ∧ constitutedBy(x, y)"
  | "ax59" => "Constitution(x, x', y, y') ↔ x :: x' ∧ y :: y' ∧ GCD(x', y') ∧ constitutedBy(x, y)"
  | "ax60" => "Perdurant(x) ∧ constitutedBy(x, y) → □(ex(x) → constitutedBy(x, y))"
  | "ax61" => "constitutedBy(x, y) → ¬ constitutedBy(y, x)"
  | "ax62" => "ExistentialDependence(x, y) → x ≠ y"
  | "ax63" => "ExistentialDependence(x, y) → □(ex(x) → ex(y))"
  | "ax64" => "ExistentialIndependence(x, y) ↔ ¬ ExistentialDependence(x, y)"
  | "ax65" => "IntrinsicMoment(x) → ∃ y, inheresIn(x, y)"
  | "ax66" => "inheresIn(x, y) → ExistentialDependence(x, y)"
  | "ax67" => "inheresIn(x, y) ∧ inheresIn(x, z) → y = z"
  | "ax68" => "Ultimate bearer is reached by following inherence"
  | "ax69" => "Mediates(r, x) → Relator(r) ∧ Endurant(x)"
  | "ax70" => "Mediates(r, x) → ExistentialDependence(r, x)"
  | "ax71" => "Relator(r) → ∃ x y, x ≠ y ∧ Mediates(r, x) ∧ Mediates(r, y)"
  | "ax72" => "ExternallyDependentMode(x) → Mode(x) ∧ ∃ y, externallyDependent(x, y)"
  | "ax73" => "foundedBy(x, y) → Relator(x) ∧ Moment(y)"
  | "ax74" => "QuaIndividual(x) → ExternallyDependentMode(x)"
  | "ax75" => "QuaIndividual(x) → ∃ y, QuaIndividualOf(x, y)"
  | "ax76" => "QuaIndividualOf(x, y) → inheresIn(x, y)"
  | "ax77" => "QuaIndividualOf(x, y) ∧ QuaIndividualOf(x, z) → y = z"
  | "ax78" => "Qua individuals are mediated through their grounding relator"
  | "ax79" => "Characterization(x, y) → IntrinsicMoment(x) ∧ Endurant(y)"
  | "ax80" => "Characterization is mediated by inherence and ultimate bearers"
  | "axQuaIndividualOfEndurant" => "QuaIndividualOf(x, y) → Endurant(y)"
  | "ax81" => "Quality(x) → IntrinsicMoment(x) ∧ ∃ q, HasValue(x, q)"
  | "ax82" => "HasValue(x, q) → Quality(x) ∧ Quale(q)"
  | "ax83" => "Quale(x) → AbstractIndividual(x)"
  | "ax84" => "Set(x) → AbstractIndividual(x)"
  | "ax85" => "QualityDomain(x) → Set(x)"
  | "ax86" => "QualityDimension(x) → Set(x)"
  | "ax87" => "AssociatedWith(x, y) → QualityStructure(x) ∧ QualityStructure(y)"
  | "ax88" => "IntrinsicMomentType(x) → EndurantType(x)"
  | "ax89" => "HasValue(x, y) → Quality(x) ∧ Quale(y)"
  | "ax90" => "Quality(x) → ∃ y, HasValue(x, y)"
  | "ax91" => "HasValue(x, y) ∧ HasValue(x, z) → y = z"
  | "ax92" => "QualityStructure(x) → Set(x) ∧ x ≠ ∅"
  | "ax93" => "QualityDimension(x) → QualityStructure(x)"
  | "ax94" => "QualityDomain(x) → QualityStructure(x)"
  | "ax95" => "QualityDomain and QualityDimension association constraints"
  | "ax96" => "Quality values belong to associated quality structures"
  | "ax97" => "Proper set inclusion is strict inclusion"
  | "ax98" => "Set equality is extensional"
  | "ax99" => "Quality structure constraints over dimensions and values"
  | "ax100" => "Quality value association respects quality structures"
  | "ax101" => "Quality spaces satisfy required structural constraints"
  | "axDistanceIdentity" => "distance(x, y) = 0 ↔ x = y"
  | "axDistanceSymmetry" => "distance(x, y) = distance(y, x)"
  | "axDistanceTriangle" => "distance(x, z) ≤ distance(x, y) + distance(y, z)"
  | "ax102" => "manifests(x, y) → Perdurant(x) ∧ Endurant(y)"
  | "ax103" => "lifeOf(x, y) ↔ Perdurant(x) ∧ Endurant(y) ∧ ∀ z, Overlap(z, x) ↔ Perdurant(z) ∧ manifests(z, y)"
  | "ax104" => "meet(x, y) → Perdurant(x) ∧ Perdurant(y)"
  | "ax105" => "isDisjointWith(t, t') ↔ Type(t) ∧ Type(t') ∧ ¬∃ x, x :: t ∧ x :: t'"
  | "ax106" => "isCompletelyCoveredBy(t, t', t'') ↔ ∀ x, x :: t → x :: t' ∨ x :: t''"
  | "ax107" => "isPartitionedInto(t, t', t'') ↔ isCompletelyCoveredBy(t, t', t'') ∧ isDisjointWith(t', t'')"
  | "ax108" => "categorizes(t₁, t₂) ↔ Type(t₁) ∧ ∀ t₃, t₃ :: t₁ → t₃ ⊑ t₂"
  | _ => ""

/--
Status classifier used by the diagnostics widget.

`completed` contains exactly the certificate fields whose generated proof-term
probe succeeded and whose theorem was emitted. `failed?` records the first
field whose generated proof-term probe failed, if certification stopped before
all fields completed.
-/
def diagnosticCertStatus (completed : Array String) (failed? : Option String)
    (field : String) : String :=
  if completed.contains field then
    "success"
  else if failed? == some field then
    "failed"
  else
    "unchecked"

private def certificationJson (completed : Array String) (failed? : Option String) : Json :=
  Json.arr <| certFields.map fun field =>
    let status := diagnosticCertStatus completed failed? field.field
    Json.mkObj [
      ("field", field.field),
      ("prop", field.prop),
      ("formula", certFormula field.field),
      ("status", status)
    ]

private def diagnosticsProps
    (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String := #[]) (failed? : Option String := none)
    (failure? : Option String := none) : Json :=
  let derivedPairs := derivedPropSummaryPairs worldNames namedFacts scopedFacts
  Json.mkObj [
    ("model", model.toString),
    ("stage", stage),
    ("failure", failure?.getD ""),
    ("worlds", indexedNamesJson worldNames),
    ("things", indexedNamesJson thingNames),
    ("facts", stringsJson <| namedFacts.map namedFactSummary),
    ("expandedFacts", stringsJson <| expandedFacts.map (compiledFactSummary worldNames thingNames derivedPairs)),
    ("derivedProps", stringsJson tables.derivedProps),
    ("certification", certificationJson completed failed?)
  ]

private def saveDiagnosticsWidget
    (cmdStx : Syntax) (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String := #[]) (failed? : Option String := none)
    (failure? : Option String := none) : CommandElabM Unit := do
  liftCoreM <| Widget.savePanelWidgetInfo ufoDiagnosticsWidget.javascriptHash
    (pure <| diagnosticsProps model worldNames thingNames namedFacts scopedFacts expandedFacts tables
      stage completed failed? failure?)
    cmdStx

private def saveFailedDiagnosticsWidget
    (cmdStx : Syntax) (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String) (failed? : Option String)
    (message : String) : CommandElabM Unit := do
  saveDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts expandedFacts tables
    stage completed failed? (some message)
  logErrorAt cmdStx message

private def certTactic (_field : CertField) : String :=
  "ufo_cert_tac"

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
    "by\n  ufo_cert_tac"

private def elabCommandString (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error err => throwError "failed to parse generated UFO command:\n{err}\n\nGenerated source:\n{source}"

private def messageErrorCount (messages : MessageLog) : Nat :=
  messages.reportedPlusUnreported.foldl
    (fun count msg => if msg.severity == MessageSeverity.error then count + 1 else count)
    0

private def coreMessageErrorCount : CommandElabM Nat := do
  pure <| messageErrorCount (← liftCoreM Core.getMessageLog)

private def elabCommandStringWithErrorCheck (source : String) : CommandElabM Bool := do
  let savedCommandMessages ← modifyGet fun st =>
    (st.messages, { st with messages := {} })
  let savedMessages ← liftCoreM <| modifyGetThe Core.State fun st =>
    (st.messages, { st with messages := {} })
  let mut threw := false
  try
    elabCommandString source
  catch _ =>
    threw := true
  let newMessages ← liftCoreM Core.getMessageLog
  let newCommandMessages := (← get).messages
  modify fun st =>
    { st with messages := savedCommandMessages }
  liftCoreM <| modifyThe Core.State fun st =>
    { st with messages := savedMessages }
  pure <| threw || messageErrorCount newMessages > 0 || messageErrorCount newCommandMessages > 0

private def elabTermStringWithErrorCheck (source : String) : CommandElabM Bool := do
  let savedCommandMessages ← modifyGet fun st =>
    (st.messages, { st with messages := {} })
  let savedMessages ← liftCoreM <| modifyGetThe Core.State fun st =>
    (st.messages, { st with messages := {} })
  let mut threw := false
  try
    match Parser.runParserCategory (← getEnv) `term source with
    | .ok stx =>
        liftTermElabM <| Lean.Elab.Term.withoutErrToSorry do
          let _ ← Lean.Elab.Term.elabTerm stx none
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    | .error err =>
        throwError "failed to parse generated UFO proof check:\n{err}\n\nGenerated source:\n{source}"
  catch _ =>
    threw := true
  let newMessages ← liftCoreM Core.getMessageLog
  let newCommandMessages := (← get).messages
  modify fun st =>
    { st with messages := savedCommandMessages }
  liftCoreM <| modifyThe Core.State fun st =>
    { st with messages := savedMessages }
  pure <| threw || messageErrorCount newMessages > 0 || messageErrorCount newCommandMessages > 0

private def certAxiomProofCheck (field : CertField) : String :=
  s!"show {field.prop} from by
  set_option maxHeartbeats 1000000 in
  set_option linter.unusedSimpArgs false in
  ufo_cert_tac"

private def throwResolveError : ResolveError → CommandElabM α
  | .duplicateWorld name => throwError "duplicate world name `{name}` in UFO model"
  | .duplicateThing name => throwError "duplicate thing name `{name}` in UFO model"
  | .unknownWorld name => throwError "unknown world name `{name}` in UFO model"
  | .unknownThing name => throwError "unknown thing name `{name}` in UFO model"

/--
Emit the ordinary Lean declarations generated by a `ufo_model` command.

The generated namespace contains the expanded AST, the compiled finite tables,
the finite model, the compiled UFO signature, optional checks for user-written
derived-relation facts, one theorem per axiom field, the final bundled
`UFOAxioms4` certificate, and a `FiniteModel4.Certified` packaging theorem for
the generated finite data. These declarations are elaborated normally, so
failed certification is detected by Lean itself. The diagnostics widget is saved
once, after derived assertions and certificate checks have either completed or
stopped at the first failed generated axiom field.
-/
private def emitModel
    (cmdStx : Syntax) (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (facts : Array CompiledFact) (tables : FactTables) : CommandElabM Unit := do
  if worldNames.isEmpty then
    throwError "a UFO model must declare at least one world"
  if thingNames.isEmpty then
    throwError "a UFO model must declare at least one thing"

  let modelIdent := mkIdent model
  let initialErrors ← coreMessageErrorCount
  elabCommand (← `(command| namespace $modelIdent))
  elabCommandString (modelASTSource worldNames.size thingNames.size facts)
  elabCommandString "def tables : FactTables := compileExplicitModelAST ast"
  elabCommandString "def data : FiniteModel4 := compileExplicitModel ast (by decide) (by decide)"
  elabCommandString "abbrev sig : UFOSignature4 := FiniteModel4.toUFOSignature4 data"
  let derivedFailed ← elabCommandStringWithErrorCheck
    s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem assertedDerivedFacts : {derivedFactsType tables.derivedProps} := {derivedFactsBody tables.derivedProps}"
  if derivedFailed then
    saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
      "derived-facts-failed" #[] none "A user-written derived relation assertion failed."
  else
    let mut completed : Array String := #[]
    let mut failedField? : Option String := none
    for field in certFields do
      if failedField?.isNone then
        let certFailed ← elabTermStringWithErrorCheck (certAxiomProofCheck field)
        if certFailed then
          failedField? := some field.field
        else
          elabCommandString (certAxiomTheorem field)
          completed := completed.push field.field
    match failedField? with
    | some failedField =>
        saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
          "certification-failed" completed (some failedField)
          s!"Generated certificate theorem `{certTheoremName failedField}` failed."
    | none =>
        let certifiedFailed ← elabCommandStringWithErrorCheck
          s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem certified : UFOAxioms4 sig := {certificateBody}"
        if certifiedFailed then
          saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
            "packaging-failed" completed none "The individual axiom checks completed, but final certificate packaging failed."
        else
          let certifiedModelFailed ← elabCommandStringWithErrorCheck
            "theorem certifiedModel : FiniteModel4.Certified data := certified"
          if certifiedModelFailed then
            saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
              "packaging-failed" completed none "The individual axiom checks completed, but final certified model packaging failed."
          else if (← coreMessageErrorCount) > initialErrors then
            saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
              "certification-failed" completed none "Generated certification logged Lean errors; the model is not certified."
          else
            saveDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
              "certified" completed none none
  elabCommand (← `(command| end $modelIdent))

elab_rules : command
  | `(ufo_model $model:ident : UFO where
      worlds $ws:ident*
      things $ts:ident*
      $blocks:ufoFactBlock*
      $derive:ufoDeriveDirective
      $cert:ufoCertDirective) => do
    let cmdStx ← getRef
    let _ := derive
    let _ := cert
    let worldNames := ws.map (·.getId)
    let thingNames := ts.map (·.getId)
    checkNoReservedWorldNames worldNames
    let worldNameStrings := worldNames.map (·.toString)
    let thingNameStrings := thingNames.map (·.toString)
    let mut namedFacts : Array NamedScopedFact := #[]
    for factBlock in blocks do
      namedFacts ← parseFactBlock worldNames thingNames namedFacts factBlock
    let scopedFacts ←
      match resolveNamedFacts worldNameStrings thingNameStrings namedFacts with
      | .ok facts => pure facts
      | .error err => throwResolveError err
    let facts := expandScopedFacts worldNames.size scopedFacts
    let expandedFacts := addReflexiveSpecializationFacts worldNames.size (addTaxonomyFacts facts)
    let ast : ModelAST :=
      { worldCount := worldNames.size
        thingCount := thingNames.size
        facts := expandedFacts }
    emitModel cmdStx model.getId worldNames thingNames namedFacts scopedFacts expandedFacts (compileExplicitModelAST ast)

end LeanUfo.UFO.DSL
