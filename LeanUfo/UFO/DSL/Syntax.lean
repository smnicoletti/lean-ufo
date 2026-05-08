import Lean
import Lean.Widget
import LeanUfo.UFO.DSL.Compiler

/-!
# Lean command syntax for finite UFO models

This module is the finite-model DSL front end.  It deliberately stays thin:

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
one of the encoded axioms, the `certify` step fails during
elaboration.

The core fact syntax is:

```lean
P(x)        -- unary UFO classification predicate
x :: T      -- UFO instantiation
T₁ ⊑ T₂     -- specialization
R(x, y)     -- binary relation fact
R(x, y, z)  -- selected ternary primitive or derived relation fact
```

Instantiation and specialization keep their UFO notation because they carry
central modeling intent.  Other predicate and relation facts use uniform
call-style syntax, including tuple-projection facts such as
`TupleProjection(tuple, 0, component)`. Missing facts default to `false`, except
that `Part` and `Overlap` include identity by default so that the common
tiny-model case satisfies extensional mereology without boilerplate.

The pure compiler also closes unary taxonomy facts conservatively.  For example,
`QuantityKind(x)` inserts the facts required by the encoded taxonomy, such as
`Kind(x)`, `Sortal(x)`, `Rigid(x)`, `QuantityType(x)`,
`SubstantialType(x)`, and `EndurantType(x)`.  This is DSL sugar over finite
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

function parseFailureAnalysis(lines) {
  const intro = [];
  const cards = [];
  let current = null;
  let currentEvidence = null;

  const conditionPrefixes = [
    'Need one of:',
    'Required together:',
    'Required but missing:',
    'Forbidden condition:',
    'Missing witness requirements:',
    'Failed condition:'
  ];

  for (const raw of lines || []) {
    const text = String(raw || '');
    if (text.startsWith('Counterexample assignment:')) {
      current = {
        assignment: text.replace('Counterexample assignment:', '').trim(),
        conditionLabel: 'Failed condition',
        condition: '',
        suggestion: '',
        evidence: []
      };
      cards.push(current);
      currentEvidence = null;
    } else if (current && conditionPrefixes.some((prefix) => text.startsWith(prefix))) {
      const prefix = conditionPrefixes.find((candidate) => text.startsWith(candidate));
      current.conditionLabel = prefix.replace(':', '');
      current.condition = text.slice(prefix.length).trim();
      currentEvidence = null;
    } else if (current && text.startsWith('Suggestion:')) {
      current.suggestion = text.replace('Suggestion:', '').trim();
      currentEvidence = null;
    } else if (current && text.startsWith('Evidence for ')) {
      currentEvidence = {
        title: text.replace(/^Evidence for /, '').replace(/:$/, ''),
        items: []
      };
      current.evidence.push(currentEvidence);
    } else if (current && currentEvidence && text.trim().startsWith('- ')) {
      currentEvidence.items.push(text.trim().replace(/^- /, ''));
    } else if (current) {
      current.evidence.push({ title: text, items: [] });
      currentEvidence = null;
    } else {
      intro.push(text);
    }
  }

  return { intro, cards };
}

function FailureAnalysis({ lines }) {
  const parsed = parseFailureAnalysis(lines);
  const cardStyle = {
    border: '1px solid var(--vscode-panel-border)',
    borderRadius: '6px',
    padding: '0.55rem 0.65rem',
    marginTop: '0.5rem',
    background: 'color-mix(in srgb, var(--vscode-editor-foreground) 4%, transparent)'
  };
  const labelStyle = {
    fontSize: '0.72rem',
    opacity: 0.72,
    textTransform: 'uppercase',
    letterSpacing: '0.02em',
    marginBottom: '0.15rem'
  };
  const codeStyle = {
    whiteSpace: 'pre-wrap',
    overflowWrap: 'anywhere'
  };

  return e('div', null,
    parsed.intro.length
      ? e('div', {
          style: {
            borderLeft: '3px solid #d29922',
            padding: '0.35rem 0 0.35rem 0.65rem',
            marginBottom: '0.55rem'
          }
        }, parsed.intro.map((line, i) =>
          e('div', { key: 'intro-' + i, style: { marginBottom: i + 1 === parsed.intro.length ? 0 : '0.2rem' } }, line)))
      : null,
    parsed.cards.map((card, i) =>
      e('div', { key: 'ce-' + i, style: cardStyle },
        e('div', { style: { display: 'flex', alignItems: 'baseline', gap: '0.45rem', marginBottom: '0.45rem' } },
          e('span', { style: { color: '#f85149', fontWeight: 700 } }, 'Counterexample ' + (i + 1)),
          e('code', { style: { opacity: 0.9 } }, card.assignment)),
        card.condition
          ? e('div', { style: { marginBottom: '0.45rem' } },
              e('div', { style: labelStyle }, card.conditionLabel || 'Failed condition'),
              e('code', { style: codeStyle }, card.condition))
          : null,
        card.suggestion
          ? e('div', {
              style: {
                borderLeft: '3px solid #3fb950',
                paddingLeft: '0.55rem',
                marginBottom: '0.45rem'
              }
            },
              e('div', { style: labelStyle }, 'Suggestion'),
              e('div', null, card.suggestion))
          : null,
        card.evidence.length
          ? e('div', null,
              e('div', { style: labelStyle }, 'Evidence'),
              card.evidence.map((group, j) =>
                e('div', { key: 'ev-' + i + '-' + j, style: { marginTop: j === 0 ? 0 : '0.35rem' } },
                  e('code', { style: codeStyle }, group.title),
                  group.items.length
                    ? e('ul', { style: { margin: '0.2rem 0 0', paddingLeft: '1.1rem' } },
                        group.items.map((item, k) =>
                          e('li', { key: 'ev-item-' + k },
                            e('code', { style: codeStyle }, item))))
                    : null)))
          : null)));
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

    (props.failureAnalysis || []).length
      ? e(Section, { title: 'Failure analysis' },
          e(FailureAnalysis, { lines: props.failureAnalysis }))
      : null,

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
syntax (name := ufoInstFact) ident "::" ident : ufoFact
syntax (name := ufoSubFact) ident "⊑" ident : ufoFact
syntax (name := ufoUnaryFact) ident "(" ident ")" : ufoFact
syntax (name := ufoBinaryFact) ident "(" ident "," ident ")" : ufoFact
syntax (name := ufoTernaryFact) ident "(" ident "," ident "," ident ")" : ufoFact
syntax (name := ufoQuaternaryFact) ident "(" ident "," ident "," ident "," ident ")" : ufoFact
syntax (name := ufoTupleProjectionFact) "TupleProjection" "(" ident "," num "," ident ")" : ufoFact

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

The proof backend is intentionally simple and transparent.  Generated
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
    FactTables.toFiniteModel4, FactTables.unaryTable, FactTables.binaryTable, FactTables.ternaryTable,
    FactTables.tupleProjectionTable, FactTables.identityBinaryTable, addUnary, addUnaryWithTaxonomy,
    addUnaryWithTaxonomyAux, addBinary, addTernary, addTupleProjection, addDerivedProp,
    closeReflexiveSpecialization, unaryTaxonomyParents,
    UnaryField.toTableField, BinaryField.toTableField, TernaryField.toTableField,
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
    ax_a102, ax_a103, ax_a104, ax_a105, ax_a106, ax_a107, ax_a108, ProperSub, Quality,
    MomentOf, UltimateBearerOf, not_momentOf_of_no_inheres, momentOf_eq_of_unique_direct_bearer,
    MemberOf, SubsetOf, ProperSubsetOf, NonEmptySet, QualityStructure,
    SimpleQuality, ComplexQuality, SimpleQualityType, ComplexQualityType, ExistsUnique]"

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

private def derivedBinaryField? (p : Name) : Option String :=
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
  | "DistanceZero" => some .distanceZero
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
  | "MemberOf" => some .memberOf
  | "Manifests" => some .manifests
  | "LifeOf" => some .lifeOf
  | "Meet" => some .meet
  | "DistanceGreaterEq" => some .distanceGreaterEq
  | _ => none

private def ternaryField? (p : Name) : Option TernaryField :=
  match p.toString with
  | "Distance" => some .distance
  | "DistanceSum" => some .distanceSum
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
  | .distanceZero => ".distanceZero"

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
  | .memberOf => ".memberOf"
  | .manifests => ".manifests"
  | .lifeOf => ".lifeOf"
  | .meet => ".meet"
  | .distanceGreaterEq => ".distanceGreaterEq"

private def ternaryFieldTerm : TernaryField → String
  | .distance => ".distance"
  | .distanceSum => ".distanceSum"

private def UnaryField.toSurfaceName (field : UnaryField) : String :=
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

private def BinaryField.toSurfaceName (field : BinaryField) : String :=
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

private def TernaryField.toSurfaceName (field : TernaryField) : String :=
  match field with
  | .distance => "Distance"
  | .distanceSum => "DistanceSum"

private def leanStringLit (s : String) : String :=
  reprStr s

private def compiledFactTerm : CompiledFact → String
  | .unary field x w => s!"CompiledFact.unary {unaryFieldTerm field} {x} {w}"
  | .binary field x y w => s!"CompiledFact.binary {binaryFieldTerm field} {x} {y} {w}"
  | .ternary field x y z w => s!"CompiledFact.ternary {ternaryFieldTerm field} {x} {y} {z} {w}"
  | .tupleProjection tuple index result w => s!"CompiledFact.tupleProjection {tuple} {index} {result} {w}"
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
  | .unary field thing => s!"{field}({thing})"
  | .binary field left right => s!"{field}({left}, {right})"
  | .ternary field first second third => s!"{field}({first}, {second}, {third})"
  | .quaternary field first second third fourth =>
      s!"{field}({first}, {second}, {third}, {fourth})"

private def scopedWorldNames (worldNames : Array Name) : NamedFactScope → Array String
  | .at world => #[world]
  | .everywhere => worldNames.map (·.toString)

private def namedFactSummary : NamedScopedFact → String
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
  | `(ufoFact| $p:ident($x:ident)) =>
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
  | `(ufoFact| $r:ident($x:ident, $y:ident)) =>
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
      match ternaryField? r.getId with
      | some field => pure <| facts.push (.ternary field xName yName zName scope)
      | none =>
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
  | `(ufoFact| TupleProjection($x:ident, $i:num, $y:ident)) =>
      pure <| facts.push (.tupleProjection x.getId.toString i.getNat y.getId.toString scope)
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
  | "ax5" => "x ⊑ y ↔ Type(x) ∧ Type(y) ∧ □∀z (z :: x → z :: y)"
  | "ax6" => "If x instantiates incomparable t1 and t2, then x also instantiates a common supertype or common subtype"
  | "ax7" => "ConcreteIndividual(x) → Individual(x)"
  | "ax8" => "AbstractIndividual(x) → Individual(x)"
  | "ax9" => "ConcreteIndividual(x) → ¬AbstractIndividual(x)"
  | "ax10" => "Individual(x) ↔ ConcreteIndividual(x) ∨ AbstractIndividual(x)"
  | "ax11" => "Endurant(x) → ConcreteIndividual(x)"
  | "ax12" => "Perdurant(x) → ConcreteIndividual(x)"
  | "ax13" => "Endurant(x) → ¬Perdurant(x)"
  | "ax14" => "ConcreteIndividual(x) ↔ Endurant(x) ∨ Perdurant(x)"
  | "ax15" => "EndurantType(x) → Type(x)"
  | "ax16" => "PerdurantType(x) → Type(x)"
  | "ax17" => "EndurantType(x) → ¬PerdurantType(x)"
  | "ax18" => "Rigid(t) ↔ EndurantType(t) ∧ ∀x (◇(x :: t) → □(x :: t))"
  | "ax19" => "AntiRigid(t) ↔ EndurantType(t) ∧ ∀x (◇(x :: t) → ◇¬(x :: t))"
  | "ax20" => "SemiRigid(t) ↔ EndurantType(t) ∧ ¬Rigid(t) ∧ ¬AntiRigid(t)"
  | "ax21" => "Endurant(x) → ∃ k, Kind(k) ∧ □(x :: k)"
  | "ax22" => "Kind(k) ∧ x :: k → ¬◇(∃ z, Kind(z) ∧ x :: z ∧ z ≠ k)"
  | "ax23" => "Sortal(t) ↔ EndurantType(t) ∧ ∃ k, Kind(k) ∧ □∀x (x :: t → x :: k)"
  | "ax24" => "NonSortal(t) ↔ EndurantType(t) ∧ ¬Sortal(t)"
  | "ax25" => "¬∃ t, Kind(t) ∧ SubKind(t)"
  | "ax26" => "Kind(t) ∨ SubKind(t) ↔ Rigid(t) ∧ Sortal(t)"
  | "ax27" => "¬∃ t, Phase(t) ∧ Role(t)"
  | "ax28" => "Phase(x) ∨ Role(x) ↔ AntiRigid(x) ∧ Sortal(x)"
  | "ax29" => "SemiRigidSortal(x) ↔ SemiRigid(x) ∧ Sortal(x)"
  | "ax30" => "Category(x) ↔ Rigid(x) ∧ NonSortal(x)"
  | "ax31" => "Mixin(x) ↔ SemiRigid(x) ∧ NonSortal(x)"
  | "ax32" => "¬∃ t, PhaseMixin(t) ∧ RoleMixin(t)"
  | "ax33" => "PhaseMixin(t) ∨ RoleMixin(t) ↔ AntiRigid(t) ∧ NonSortal(t)"
  | "ax_instEndurant" => "EndurantType(t) ∧ x :: t → Endurant(x)"
  | "ax_sub_kind_sortal" => "x ⊑ k ∧ Kind(k) → Sortal(x)"
  | "ax_nonSortal_up" => "NonSortal(x) ∧ x ⊑ y → NonSortal(y)"
  | "ax_kindStable" => "Kind(k) → □ Kind(k)"
  | "ax34" => "Substantial(x) ∨ Moment(x) ↔ Endurant(x)"
  | "ax35" => "¬∃ x, Substantial(x) ∧ Moment(x)"
  | "ax36" => "Object(x) ∨ Collective(x) ∨ Quantity(x) ↔ Substantial(x)"
  | "ax37" => "¬∃ x, Object(x) ∧ Collective(x)"
  | "ax38" => "¬∃ x, Object(x) ∧ Quantity(x)"
  | "ax39" => "¬∃ x, Collective(x) ∧ Quantity(x)"
  | "ax40" => "Relator(x) ∨ IntrinsicMoment(x) ↔ Moment(x)"
  | "ax41" => "¬∃ x, Relator(x) ∧ IntrinsicMoment(x)"
  | "ax42" => "Mode(x) ∨ Quality(x) ↔ IntrinsicMoment(x)"
  | "ax43" => "¬∃ x, Mode(x) ∧ Quality(x)"
  | "ax44" => "EndurantType taxonomy mirrors Endurant taxonomy"
  | "ax45" => "Specific kind predicates imply matching type predicate and Kind"
  | "ax46" => "Endurant(x) → ◇∃ k, specific endurant kind k ∧ x :: k"
  | "ax47" => "Part(x, x)"
  | "ax48" => "Part(x, y) ∧ Part(y, x) → x = y"
  | "ax49" => "Part(x, y) ∧ Part(y, z) → Part(x, z)"
  | "ax50" => "Overlap(x, y) ↔ ∃ z, Part(z, x) ∧ Part(z, y)"
  | "ax51" => "¬Part(y, x) → ∃ z, Part(z, y) ∧ ¬Overlap(z, x)"
  | "ax52" => "ProperPart(x, y) ↔ Part(x, y) ∧ ¬Part(y, x)"
  | "ax53" => "GenericFunctionalDependence(x', y') ↔ ∀x, x :: x' ∧ FunctionsAs(x,x') → ∃y, y ≠ x ∧ y :: y' ∧ FunctionsAs(y,y')"
  | "ax54" => "IndividualFunctionalDependence(x,x',y,y') ↔ GFD(x',y') ∧ x :: x' ∧ y :: y' ∧ (FunctionsAs(x,x') → FunctionsAs(y,y'))"
  | "ax55" => "ComponentOf(x,x',y,y') ↔ ProperPart(x,y) ∧ IndividualFunctionalDependence(x,x',y,y')"
  | "ax56" => "constitutedBy(x, y) → ((Endurant(x) ↔ Endurant(y)) ∧ (Perdurant(x) ↔ Perdurant(y)))"
  | "ax57" => "constitutedBy(x, y) ∧ x :: x' ∧ y :: y' ∧ Kind(x') ∧ Kind(y') → x' ≠ y'"
  | "ax58" => "GCD(x', y') ↔ ∀ x, x :: x' → ∃ y, y :: y' ∧ constitutedBy(x, y)"
  | "ax59" => "Constitution(x, x', y, y') ↔ x :: x' ∧ y :: y' ∧ GCD(x', y') ∧ constitutedBy(x, y)"
  | "ax60" => "Perdurant(x) ∧ constitutedBy(x, y) → □(ex(x) → constitutedBy(x, y))"
  | "ax61" => "constitutedBy(x, y) → ¬ constitutedBy(y, x)"
  | "ax62" => "ex(x) → Thing(x) (trivial in the typed Lean encoding)"
  | "ax63" => "ExistentialDependence(x, y) ↔ □(ex(x) → ex(y))"
  | "ax64" => "ExistentialIndependence(x, y) ↔ ¬ExistentialDependence(x, y) ∧ ¬ExistentialDependence(y, x)"
  | "ax65" => "inheresIn(x, y) → ExistentialDependence(x, y)"
  | "ax66" => "inheresIn(x, y) → Moment(x) ∧ (Type(y) ∨ ConcreteIndividual(y))"
  | "ax67" => "inheresIn(x, y) ∧ inheresIn(x, z) → y = z"
  | "ax68" => "Moment(x) → ∃! y, UltimateBearerOf(y, x)"
  | "ax69" => "ExternallyDependent(x, y) ↔ ExistentialDependence(x, y) ∧ ∀z (InheresIn(x,z) → ExistentialIndependence(y,z))"
  | "ax70" => "ExternallyDependentMode(x) ↔ Mode(x) ∧ ∃ y, ExternallyDependent(x, y)"
  | "ax71" => "FoundedBy(x, y) → (ExternallyDependentMode(x) ∨ Relator(x)) ∧ Perdurant(y)"
  | "ax72" => "ExternallyDependentMode(x) → ∃! y, FoundedBy(x, y)"
  | "ax73" => "QuaIndividualOf(x, y) ↔ overlap-defined externally dependent modes sharing x's foundation"
  | "ax74" => "QuaIndividual(x) ↔ ∃ y, QuaIndividualOf(x, y)"
  | "ax75" => "QuaIndividual(x) → ExternallyDependentMode(x)"
  | "ax76" => "QuaIndividualOf(x, y) ∧ QuaIndividualOf(x, y') → y = y'"
  | "ax77" => "Relator(x) → ∃! y, FoundedBy(x, y)"
  | "ax78" => "Relator(x) ∧ Part(y, x) → FoundationOf(x) = FoundationOf(y)"
  | "ax79" => "Relator(x) ↔ sum of mutually dependent qua individuals sharing a foundation"
  | "ax80" => "Mediates(x, y) ↔ Relator(x) ∧ Endurant(y) ∧ ∃z (QuaIndividualOf(z, y) ∧ Part(z, x))"
  | "axQuaIndividualOfEndurant" => "QuaIndividualOf(x, y) → Endurant(y)"
  | "ax81" => "Characterization(t, m) → EndurantType(t) ∧ MomentType(m) ∧ instances of t have inhering m-instances, and m-instances have unique t-bearers"
  | "ax82" => "Characterization(t, q) ∧ QualityType(q) → each q-instance has a unique t-bearer"
  | "ax83" => "Quale(x) → AbstractIndividual(x)"
  | "ax84" => "Set(x) → AbstractIndividual(x)"
  | "ax85" => "¬∃ x, Quale(x) ∧ Set(x)"
  | "ax86" => "QualityStructure(x) → Set(x) ∧ NonEmptySet(x)"
  | "ax87" => "Quale(x) ↔ ∃! y, QualityStructure(y) ∧ MemberOf(x, y)"
  | "ax88" => "QualityStructure(x) ↔ QualityDomain(x) ∨ QualityDimension(x)"
  | "ax89" => "QualityDomain(x) → ¬ QualityDimension(x)"
  | "ax90" => "AssociatedWith(s,t) ∧ AssociatedWith(s',t') ∧ ProperSub(t',t) → ProperSubsetOf(s',s)"
  | "ax91" => "QualityType(t) ↔ IntrinsicMomentType(t) ∧ ∃! x, QualityStructure(x) ∧ AssociatedWith(x,t)"
  | "ax92" => "HasValue(x, y) → Quality(x) ∧ Quale(y)"
  | "ax93" => "Quality(x) → ∃! y, HasValue(x, y)"
  | "ax94" => "HasValue(x, y) → ∃ t s, x :: t ∧ AssociatedWith(s,t) ∧ MemberOf(y,s)"
  | "ax95" => "AssociatedWith(x,y) → (QualityDimension(x) ↔ SimpleQualityType(y))"
  | "ax96" => "AssociatedWith(x,y) → (QualityDomain(x) ↔ ComplexQualityType(y))"
  | "ax97" => "ComplexQuality(x) ∧ y :: Y ∧ z :: Z ∧ InheresIn(y,x) ∧ InheresIn(z,x) ∧ Y = Z → y = z"
  | "ax98" => "ComplexQuality(x) → ∀ y, InheresIn(y,x) → SimpleQuality(y)"
  | "ax99" => "QualityDomain(x) ∧ AssociatedWith(x,t) → product-subset characterization over associated dimensions"
  | "ax100" => "Distance(x,y,r) → Quale(x) ∧ Quale(y) ∧ ∃ z, MemberOf(x,z) ∧ MemberOf(y,z)"
  | "ax101" => "Quale(x) ∧ Quale(y) → ∃! r, Distance(x,y,r)"
  | "axDistanceIdentity" => "x = y ∧ Distance(x,y,r) → DistanceZero(r)"
  | "axDistanceSymmetry" => "Distance(x,y,r) → Distance(y,x,r)"
  | "axDistanceTriangle" => "Distance(x,y,r₀) ∧ Distance(y,z,r₁) ∧ Distance(x,z,r₂) ∧ DistanceSum(r₀,r₁,s) → DistanceGreaterEq(s,r₂)"
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

private def ax68ClosureAnalysis
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

private def hasAx68ClosureFailure (worldCount thingCount : Nat) (tables : FactTables) : Bool :=
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
              match productWitness? thingNames.size tables x t w with
              | some _ => pure ()
              | none =>
                  let zs := characterizationTargets thingNames.size tables t w
                  let renderedZs :=
                    if zs.isEmpty then
                      "none"
                    else
                      String.intercalate ", " <| zs.toList.map (indexedName thingNames ·)
                  return #[
                    s!"Counterexample assignment: x = {indexedName thingNames x}, t = {indexedName thingNames t}, w = {indexedName worldNames w}.",
                    s!"Missing witness requirements: quality domain `{indexedName thingNames x}` associated with `{indexedName thingNames t}` must be covered by product dimensions for all characterizations of `{indexedName thingNames t}`.",
                    "Suggestion: add `Characterization(t, z)` facts for the component quality types, `AssociatedWith(y, z)` facts for their quality dimensions, `MemberOf(tuple, x)` facts for domain tuples, matching `TupleProjection(tuple, i, component)` facts, and `MemberOf(component, y)` facts for each coordinate.",
                    s!"Characterization targets found for `{indexedName thingNames t}`: {renderedZs}."
                  ]
    return #[
      "Product check for ax99: every asserted quality-domain association has a finite product witness in the DSL tables.",
      "If Lean still reports ax99, the remaining issue is likely proof search over the existential finite family rather than an obvious table mismatch."
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

private def derivedAssertionAnalysis
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

private def diagnosticWitnesses
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : CertField) : Array String :=
  if field.field == "ax68" then
    ax68ClosureAnalysis worldNames thingNames tables
  else if field.field == "ax73" then
    ax73FoundationAnalysis worldNames thingNames tables
  else if field.field == "ax78" then
    ax78FoundationAnalysis worldNames thingNames tables
  else if field.field == "ax79" then
    ax79FoundationAnalysis worldNames thingNames tables
  else if field.field == "ax99" then
    ax99QualityDomainAnalysis worldNames thingNames tables
  else match diagnosticFormula? field.field with
  | none =>
      #[s!"No structured DSL-level witness extractor is registered for {field.field} yet."]
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
          return #[s!"The structured checker did not find a DSL-level witness for {field.field}."]
        return out

private def diagnosticsProps
    (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String := #[]) (failed? : Option String := none)
    (failure? : Option String := none) (failureAnalysis : Array String := #[]) : Json :=
  let derivedPairs := derivedPropSummaryPairs worldNames namedFacts scopedFacts
  Json.mkObj [
    ("model", model.toString),
    ("stage", stage),
    ("failure", failure?.getD ""),
    ("failureAnalysis", stringsJson failureAnalysis),
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
    (failure? : Option String := none) (failureAnalysis : Array String := #[]) :
    CommandElabM Unit := do
  liftCoreM <| Widget.savePanelWidgetInfo ufoDiagnosticsWidget.javascriptHash
    (pure <| diagnosticsProps model worldNames thingNames namedFacts scopedFacts expandedFacts tables
      stage completed failed? failure? failureAnalysis)
    cmdStx

private def saveFailedDiagnosticsWidget
    (cmdStx : Syntax) (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String) (failed? : Option String)
    (message : String) (failureAnalysis : Array String := #[]) : CommandElabM Unit := do
  saveDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts expandedFacts tables
    stage completed failed? (some message) failureAnalysis
  let detail :=
    if failureAnalysis.isEmpty then
      message
    else
      message ++ "\n" ++ String.intercalate "\n" failureAnalysis.toList
  logErrorAt cmdStx detail

private def finThingTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)"

private def finWorldTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.worldCount)"

private def localFinThingTerm (idx : Nat) (proofName : String) : String :=
  s!"(⟨{idx}, {proofName}⟩ : Fin data.thingCount)"

private def localFinWorldTerm (idx : Nat) (proofName : String) : String :=
  s!"(⟨{idx}, {proofName}⟩ : Fin data.worldCount)"

private def indentLines (pref source : String) : String :=
  String.intercalate "\n" <| (source.splitOn "\n").map (fun line => pref ++ line)

/-
Special proof generator for ax68.

Most generated axiom fields are discharged by `ufo_cert_tac`.  Ultimate-bearer
uniqueness is more brittle because it goes through the inductive `MomentOf`
closure, so the certificate generator emits explicit finite case splits for
the direct-terminal bearer pattern detected in the compiled tables.
-/
private def natExhaustedContradiction
    (varName boundProofName hypPrefix : String) (count : Nat) : String :=
  let neqProofs := (List.range count).map fun idx =>
    s!"have hne_{idx} : {varName} ≠ {idx} := {hypPrefix}_{idx}"
  String.intercalate "\n" <|
    ["exfalso", s!"have hlt := {boundProofName}", s!"change {varName} < {count} at hlt"] ++
      neqProofs ++ ["omega"]

partial def natByCases (varName boundProofName hypPrefix : String) (count idx : Nat)
    (leaf : Nat → String) : String :=
  if idx < count then
    let yesBranch := indentLines "  " s!"subst {varName}
{leaf idx}"
    let noBranch := indentLines "  " (natByCases varName boundProofName hypPrefix count (idx + 1) leaf)
    s!"by_cases {hypPrefix}_{idx} : {varName} = {idx}
·
{yesBranch}
·
{noBranch}"
  else
    natExhaustedContradiction varName boundProofName hypPrefix count

private def ax68UniqueDirectProof (thingCount _m _w _b : Nat) : String :=
  let cases := natByCases "zVal" "zLt" "h_z" thingCount 0 fun _ =>
    s!"{certificateSimp} at hz ⊢ <;> (try contradiction) <;> (try omega) <;> (try rfl)"
  s!"by
  intro z hz
  rcases z with ⟨zVal, zLt⟩
{indentLines "  " cases}"

private def ax68TerminalProof (thingCount _b _w : Nat) : String :=
  let cases := natByCases "zVal" "zLt" "h_z" thingCount 0 fun _ =>
    s!"{certificateSimp} at hz <;> (try contradiction) <;> (try omega) <;> (try rfl)"
  s!"by
  intro z hz
  rcases z with ⟨zVal, zLt⟩
{indentLines "  " cases}"

private def directTerminalBearer?
    (thingCount : Nat) (tables : FactTables) (w m : Nat) : Option Nat :=
  Id.run do
    let mut found? : Option Nat := none
    for b in [:thingCount] do
      if tables.binaryLookup "inheresIn" m b w &&
          !tables.unaryLookup "moment" b w then
        let mut terminal := true
        for z in [:thingCount] do
          if tables.binaryLookup "inheresIn" b z w then
            terminal := false
        if terminal then
          match found? with
          | none => found? := some b
          | some _ => return none
    return found?

private def ax68DirectBearerLeafTactic (thingCount m w b : Nat) : String :=
  let mTerm := localFinThingTerm m "mLt"
  let wTerm := localFinWorldTerm w "wLt"
  s!"refine ⟨{finThingTerm b}, ?_, ?_⟩
·
  constructor
  ·
    {certificateSimp} <;> (try contradiction) <;> (try omega) <;> (try rfl)
  ·
    exact MomentOf.direct (by {certificateSimp} <;> (try contradiction) <;> (try omega) <;> (try rfl))
·
  intro y hy
  exact momentOf_eq_of_unique_direct_bearer
    (Sig := sig.toUFOSignature3_9)
    (m := {mTerm}) (b := {finThingTerm b}) (x := y) (w := {wTerm})
    ({ax68UniqueDirectProof thingCount m w b})
    ({ax68TerminalProof thingCount b w})
    hy.2"

private def ax68LeafTactic
    (thingCount : Nat) (tables : FactTables) (m w : Nat) : String :=
  if tables.unaryLookup "moment" m w then
    match directTerminalBearer? thingCount tables w m with
    | some b => ax68DirectBearerLeafTactic thingCount m w b
    | none =>
        s!"{certificateSimp} at hm ⊢ <;> (try contradiction) <;> (try omega) <;> (try grind)"
  else
    s!"{certificateSimp} at hm ⊢ <;> contradiction"

partial def ax68WorldCases
    (thingCount worldCount : Nat) (tables : FactTables) (m idx : Nat) : String :=
  natByCases "wVal" "wLt" "h_w" worldCount idx fun w =>
    ax68LeafTactic thingCount tables m w

partial def ax68ThingCases
    (thingCount worldCount : Nat) (tables : FactTables) (idx : Nat) : String :=
  natByCases "mVal" "mLt" "h_m" thingCount idx fun m =>
    ax68WorldCases thingCount worldCount tables m 0

private def certTactic
    (worldCount thingCount : Nat) (tables : FactTables) (field : CertField) : String :=
  if field.field == "ax68" then
    s!"intro m w hm
rcases m with ⟨mVal, mLt⟩
rcases w with ⟨wVal, wLt⟩
{ax68ThingCases thingCount worldCount tables 0}"
  else
    "ufo_cert_tac"

/--
Some axioms must be probed by elaborating the generated theorem command, not by
first elaborating a standalone proof term.

The ordinary term probe is cheaper and keeps successful probes out of the
environment, but it elaborates in a slightly different context from the final
command.  A small number of fields are sensitive to that difference:

* `ax1`-`ax6` reduce to finite definitions over all things/worlds; on larger
  models the standalone term probe can run out before the command theorem does.
* `ax68` uses a generated proof shape that needs command-level context.
* `ax44` reduces to a large finite type-taxonomy proposition; the term probe may
  fail decidability synthesis even when the generated theorem command succeeds.

Keeping this list explicit avoids mistaking probe incompleteness for a semantic
counterexample.
-/
private def useCommandCertificateProbe (field : CertField) : Bool :=
  field.field == "ax1" || field.field == "ax2" || field.field == "ax3" ||
    field.field == "ax4" || field.field == "ax5" || field.field == "ax6" ||
    field.field == "ax44" || field.field == "ax68"

private def certAxiomTheorem
    (worldCount thingCount : Nat) (tables : FactTables) (field : CertField) : String :=
  s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem {certTheoremName field.field} : {field.prop} := by
{indentLines "  " (certTactic worldCount thingCount tables field)}"

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

/--
Check a generated proof as a term while suppressing any messages it produces.

This is only a fast preflight check.  It is intentionally not the authoritative
certificate path, because term elaboration can be weaker than command
elaboration for large generated finite proofs.  See `useCommandCertificateProbe`
for fields that skip this preflight and test the generated theorem command
directly.
-/
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

private def certAxiomCounterexampleCheck (field : CertField) : String :=
  s!"show ¬ ({field.prop}) from by
  set_option maxHeartbeats 1000000 in
  set_option linter.unusedSimpArgs false in
  {certificateSimp} <;> (try omega) <;> (try grind) <;> native_decide"

private def certificationFailureAnalysis
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : CertField) : CommandElabM (Array String) := do
  let counterexampleProbeFailed ←
    elabTermStringWithErrorCheck (certAxiomCounterexampleCheck field)
  if counterexampleProbeFailed then
    let base := #[
      s!"No counterexample proof was found for {field.field}.",
      "The generated certificate proof failed, and the generic negation probe also failed. This usually means proof search exhausted or hit a reducibility/decidability limit; it is not evidence by itself that the finite model violates the axiom."
    ]
    if field.field == "ax68" then
      pure <| base ++ ax68ClosureAnalysis worldNames thingNames tables
    else
      pure base
  else
    pure <| #[
      s!"A finite counterexample was confirmed for {field.field}.",
      "Lean successfully proved the negation of this axiom for the generated finite model, so this is a semantic model failure rather than certificate proof search exhaustion."
    ] ++ diagnosticWitnesses worldNames thingNames namedFacts tables field

private def certAxiomProofCheck
    (worldCount thingCount : Nat) (tables : FactTables) (field : CertField) : String :=
  s!"show {field.prop} from by
  set_option maxHeartbeats 1000000 in
  set_option linter.unusedSimpArgs false in
{indentLines "  " (certTactic worldCount thingCount tables field)}"

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
    let failureAnalysis := derivedAssertionAnalysis worldNames thingNames namedFacts scopedFacts tables
    saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
      "derived-facts-failed" #[] none "A user-written derived relation assertion failed."
      failureAnalysis
  else
    let mut completed : Array String := #[]
    let mut failedField? : Option CertField := none
    for field in certFields do
      if failedField?.isNone then
        if field.field == "ax68" &&
            hasAx68ClosureFailure worldNames.size thingNames.size tables then
          failedField? := some field
        else if useCommandCertificateProbe field then
          let certFailed ← elabCommandStringWithErrorCheck
            (certAxiomTheorem worldNames.size thingNames.size tables field)
          if certFailed then
            failedField? := some field
          else
            completed := completed.push field.field
        else
          let certFailed ← elabTermStringWithErrorCheck
            (certAxiomProofCheck worldNames.size thingNames.size tables field)
          if certFailed then
            failedField? := some field
          else
            elabCommandString (certAxiomTheorem worldNames.size thingNames.size tables field)
            completed := completed.push field.field
    match failedField? with
    | some failedField =>
        let failureAnalysis ←
          certificationFailureAnalysis worldNames thingNames namedFacts tables failedField
        saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
          "certification-failed" completed (some failedField.field)
          s!"Generated certificate theorem `{certTheoremName failedField.field}` failed."
          failureAnalysis
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
