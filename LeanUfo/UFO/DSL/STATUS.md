# Certified DSL Pipeline Status

This document is the detailed status note for the finite UFO DSL backend. It is
intended to be more exhaustive than the top-level README and to make the current
trusted/verified boundary explicit.

## Contents

- [Pipeline Snapshot](#pipeline-snapshot)
- [Trust Boundary Diagram](#trust-boundary-diagram)
- [What Is Formally Guaranteed](#what-is-formally-guaranteed)
- [What Is Still Trusted](#what-is-still-trusted)
- [Generated Declarations](#generated-declarations)
- [Surface Syntax](#surface-syntax)
- [Semantic Derivations](#semantic-derivations)
- [Current Limitations](#current-limitations)
- [File Roles](#file-roles)
- [How To Check The DSL](#how-to-check-the-dsl)

## Pipeline Snapshot

The current `ufo_model ... certify` command follows this pipeline:

```text
trusted Lean command parser
  -> NamedScopedFact
  -> resolveNamedFacts
  -> ScopedCompiledFact
  -> expandScopedFacts
  -> CompiledFact
  -> addTaxonomyFacts
  -> addReflexiveSpecializationFacts
  -> ModelAST
  -> compileExplicitModelAST
  -> FactTables
  -> compileExplicitModel
  -> FiniteModel4
  -> FiniteModel4.toUFOSignature4
  -> UFOAxioms4 certificate
```

The main semantic pipeline after parsing lives in `Compiler.lean` as ordinary
Lean functions. The generic facts documenting that pipeline live in
`Guarantees.lean`. The current command frontend runs these pure functions while
elaborating the command, then emits an already-expanded `ModelAST` declaration.
Thus the function definitions and generic theorems are verified Lean artifacts,
while the concrete emitted AST value remains part of the metaprogramming
boundary.

Pipeline stages:

- `trusted Lean command parser`: the `ufo_model ... where ...` syntax is parsed
  by Lean metaprogramming in `Syntax.lean`. This is the concrete frontend
  boundary.
- `NamedScopedFact`: parser output that still uses user-facing names such as
  `actual`, `I`, and `K`, and records whether a fact is scoped to one world or
  `everywhere`.
- `resolveNamedFacts`: pure name-resolution pass. It checks duplicate world and
  thing names, rejects unknown names, and replaces user names with numeric
  indices.
- `ScopedCompiledFact`: resolved facts whose worlds/things are numeric, but
  whose scope may still be either one world or `everywhere`.
- `expandScopedFacts`: pure scope-expansion pass. Facts scoped to one world stay
  single facts; facts scoped to `everywhere` are copied to every declared world.
- `CompiledFact`: ordinary world-indexed facts. At this point there are no
  names and no `everywhere` scope left.
- `addTaxonomyFacts`: pure deterministic taxonomy expansion. For example,
  `ObjectKind` contributes the encoded ancestor classifications such as `Kind`,
  `Sortal`, and the relevant type-taxonomy facts.
- `addReflexiveSpecializationFacts`: pure closure pass that inserts `T ⊑ T` for
  each type target detected from instantiation facts, at each declared world.
- `ModelAST`: the expanded finite model syntax tree emitted as a Lean
  declaration. It records world count, thing count, and the final compiled fact
  list.
- `compileExplicitModelAST`: pure fold from the expanded `ModelAST` into
  collected primitive facts and derived-assertion propositions.
- `FactTables`: the finite compiled data used by the backend. This is the last
  compact compiler representation before constructing the semantic model.
- `compileExplicitModel`: pure construction of a `FiniteModel4` from the
  expanded AST, using positivity proofs for the declared world and thing counts.
- `FiniteModel4`: the finite backend representation of worlds, things, and
  primitive finite facts.
- `FiniteModel4.toUFOSignature4`: semantic bridge from the finite backend to the
  Prop-valued `UFOSignature4` used by the core UFO axioms. This is where selected
  derived predicates receive their computed semantics.
- `UFOAxioms4 certificate`: generated Lean theorem proving that the compiled
  signature satisfies the encoded UFO axiom package.

## Trust Boundary Diagram

```mermaid
flowchart TD
  A["Concrete DSL syntax<br/>ufo_model ..."] --> B["Syntax.lean parser<br/>trusted metaprogramming"]
  B --> C["NamedScopedFact"]

  subgraph Pure["Pure Lean compiler pipeline"]
    C --> D["resolveNamedFacts<br/>name resolution and duplicate checks"]
    D --> E["ScopedCompiledFact"]
    E --> F["expandScopedFacts<br/>given everywhere expansion"]
    F --> G["CompiledFact"]
    G --> H["addTaxonomyFacts<br/>deterministic unary taxonomy closure"]
    H --> I["addReflexiveSpecializationFacts<br/>T sub T for instantiated types"]
    I --> J["ModelAST"]
    J --> K["compileExplicitModelAST"]
    K --> L["FactTables"]
    L --> M["compileExplicitModel"]
    M --> N["FiniteModel4"]
    N --> O["FiniteModel4.toUFOSignature4"]
  end

  O --> P["generated theorem<br/>Model.certified : UFOAxioms4 Model.sig"]
  P --> Q["Lean kernel checks proof"]

  B -. "emits declarations" .-> J
  B -. "emits certificate theorem skeleton/tactics" .-> P

  classDef trusted fill:#fff1cc,stroke:#b7791f,color:#222;
  classDef verified fill:#e6ffed,stroke:#2f855a,color:#222;
  classDef checked fill:#e6f0ff,stroke:#2b6cb0,color:#222;

  class A,B,C trusted;
  class D,E,F,G,H,I,J,K,L,M,N,O verified;
  class P,Q checked;
```

Legend:

- Yellow: trusted parser/declaration-emission boundary, including the concrete
  parsed fact value produced by the command elaborator.
- Green: ordinary Lean functions with generic theorem-backed guarantees.
- Blue: generated Lean theorem checked by the Lean kernel.

## What Is Formally Guaranteed

The guarantees below are generic theorems.

### Name Resolution

`Guarantees.lean` proves:

- `resolveThing_of_nameIndex_eq_some`
- `resolveThing_of_nameIndex_eq_none`
- `resolveWorld_of_nameIndex_eq_some`
- `resolveWorld_of_nameIndex_eq_none`
- `resolveScope_everywhere`
- `resolveScope_at_of_resolveWorld_eq_ok`
- `resolveNamedFact_unary_of_resolved`
- `resolveNamedFact_binary_of_resolved`
- `resolveNamedFacts_of_checks_ok`

These show that named thing/world lookup is governed by the pure `nameIndex?`
function, that absent names produce explicit errors, and that batch resolution
delegates to the pure single-fact resolver after duplicate-name checks.

### Scope Expansion

`given everywhere` is not expanded by an ad-hoc loop in the syntax frontend.
The parser records it as `NamedFactScope.everywhere`; after name resolution it
is expanded by `expandScopedFacts`.

`Guarantees.lean` proves:

- `unary_at_expands_to_singleton`
- `binary_at_expands_to_singleton`
- `derived_at_expands_to_singleton`
- `scoped_expansion_pipeline`

These describe how scoped facts become ordinary world-indexed facts.

### Taxonomy Expansion

The compiler has two paths:

- `compileFact`, which inserts unary taxonomy ancestors directly.
- the generated-model path, which first makes taxonomy facts explicit with
  `addTaxonomyFacts`, then uses `compileExplicitFact`.

`Guarantees.lean` proves:

- `unary_compiles_with_taxonomy`
- `explicit_unary_compiles_to_table`
- `taxonomy_expansion_pipeline`

These are pipeline guarantees. They expose where taxonomy expansion happens.
They do not yet prove a full graph-reachability theorem saying that the added
facts are exactly all and only taxonomy ancestors reachable through
`unaryTaxonomyParents`.

The current taxonomy expansion is intended to be conservative with respect to
the encoded UFO hierarchy: it adds only positive consequences of the axioms and
derived theorems, and it avoids reverse or choice-producing inferences. For
example, `Endurant` expands to `ConcreteIndividual`, but `ConcreteIndividual`
does not expand back to either `Endurant` or `Perdurant`, because that would
require choosing one branch of `ConcreteIndividual ↔ Endurant ∨ Perdurant`.

Current taxonomy:

| Expansion group | Added parent facts | UFO source |
| --- | --- | --- |
| `Object`, `Collective`, `Quantity` | `Substantial` | Section 3.3, `a36`: `Object ∨ Collective ∨ Quantity ↔ Substantial` |
| `Relator`, `IntrinsicMoment` | `Moment` | Section 3.3, `a40`: `Relator ∨ IntrinsicMoment ↔ Moment` |
| `Mode` | `IntrinsicMoment` | Section 3.3, `a42`: `Mode ∨ Quality ↔ IntrinsicMoment` |
| `Substantial`, `Moment` | `Endurant` | Section 3.3, `a34`: `Substantial ∨ Moment ↔ Endurant` |
| `Endurant`, `Perdurant` | `ConcreteIndividual` | Section 3.1, `a11`, `a12`, and `a14` |
| `Quale`, `Set` | `AbstractIndividual` | Section 3.12, `a83` and `a84` |
| `Rigid`, `AntiRigid`, `SemiRigid` | `EndurantType` | Section 3.2, `a18`, `a19`, `a20` |
| `Kind`, `SubKind` | `Rigid`, `Sortal` | Section 3.2, `a26`: `Kind ∨ SubKind ↔ Rigid ∧ Sortal` |
| `Phase`, `Role` | `AntiRigid`, `Sortal` | Section 3.2, `a28`: `Phase ∨ Role ↔ AntiRigid ∧ Sortal` |
| `SemiRigidSortal` | `SemiRigid`, `Sortal` | Section 3.2, `a29` |
| `Category` | `Rigid`, `NonSortal` | Section 3.2, `a30` |
| `Mixin` | `SemiRigid`, `NonSortal` | Section 3.2, `a31` |
| `PhaseMixin`, `RoleMixin` | `AntiRigid`, `NonSortal` | Section 3.2, `a32` |
| `Sortal`, `NonSortal` | `EndurantType` | Section 3.2, `a23`, `a24` |
| `ObjectKind`, `CollectiveKind`, `QuantityKind`, `RelatorKind`, `ModeKind`, `QualityKind` | their corresponding specific type plus `Kind` | Section 3.4, `a45` |
| `ObjectType`, `CollectiveType`, `QuantityType` | `SubstantialType` | Section 3.4, `a44` plus the corresponding individual taxonomy |
| `RelatorType`, `IntrinsicMomentType` | `MomentType` | Section 3.4, `a44` plus the corresponding individual taxonomy |
| `ModeType`, `QualityType` | `IntrinsicMomentType`, then `MomentType` | Section 3.4, `a44` plus the corresponding individual taxonomy |
| `SubstantialType`, `MomentType` | `EndurantType` | Section 3.4, `a44` plus the corresponding individual taxonomy |

The strongest currently formalized fact is still the pipeline theorem above:
`addTaxonomyFacts` applies exactly this encoded parent map. We do not yet have a
separate theorem proving, edge by edge, that each parent implication follows
from the UFO axioms. The practical backstop is the generated certificate:
if the expanded model violates `UFOAxioms4`, `certify` fails.

### Reflexive Specialization Expansion

For each type target found in instantiation facts, the compiler inserts
reflexive specialization facts at each declared world. This supports the
encoded requirement that types specialize themselves.

`Guarantees.lean` proves:

- `reflexive_specialization_expansion_pipeline`

This exposes the expansion policy. It does not yet prove an extensional theorem
such as "for every `x :: T`, `T sub T` appears at every world, and only such
facts are introduced by this closure."

### Explicit Fact Compilation

Generated models compile from an already-expanded `ModelAST`.

`Guarantees.lean` proves:

- `explicit_unary_compiles_to_table`
- `explicit_binary_compiles_to_table`
- `explicit_derived_compiles_to_assertion`
- `explicit_compilation_pipeline`

Thus, in the generated path, expanded unary/binary facts become direct table
insertions, and derived facts become generated propositions checked by Lean.

### Finite Model Construction

`FactTables.toFiniteModel4` is a pure constructor for the finite semantic
model.

`Guarantees.lean` proves:

- `explicit_model_pipeline`
- `toFiniteModel4_inst_eq`
- `toFiniteModel4_sub_eq`
- `toFiniteModel4_part_eq`

These show that generated finite models are built by ordinary compilation from
explicit AST facts to finite tables and then to `FiniteModel4`, with key fields
connected to the intended table lookups.

### Semantic Bridge

`FiniteModel.lean` compiles `FiniteModel4` into the trusted Prop-valued
`UFOSignature4`.

`Guarantees.lean` proves:

- `compiled_frame_universal`
- `compiled_frame_refl`
- `compiled_frame_symm`
- `compiled_frame_trans`
- `compiled_signature_frame_universal`
- `compiled_type_iff`
- `compiled_individual_iff`
- `compiled_inst_iff`
- `compiled_sub_iff`
- `compiled_part_iff`
- `compiled_constitution_iff`

These connect the finite representation to the semantic signature used by the
UFO axioms.

### Certification Meaning

The DSL does not introduce a new, weaker notion of certification.

`Guarantees.lean` proves:

- `certified_iff_ufoAxioms4`
- `certified_sound`
- `certified_of_ufoAxioms4`

The key theorem is:

```lean
FiniteModel4.Certified M ↔ UFOAxioms4 M.toUFOSignature4
```

So every generated:

```lean
Model.certified : UFOAxioms4 Model.sig
```

is an ordinary Lean theorem about the original UFO axiom package.

## What Is Still Trusted

The following pieces are still part of the trusted frontend boundary:

- concrete Lean command parsing for `ufo_model ... where ...`;
- conversion of parsed Lean identifiers to string names;
- construction/emission of the generated `ast`, `tables`, `data`, `sig`, and
  certificate theorem declarations;
- the tactic script used to search for each generated proof.

The tactic script is trusted only as a proof-search program, not as proof
evidence. The Lean kernel still checks the resulting theorem. If the tactic
constructs an invalid proof, elaboration fails.

## Generated Declarations

A certified model command emits declarations of this shape:

```lean
Model.ast       : ModelAST
Model.tables    : FactTables
Model.data      : FiniteModel4
Model.sig       : UFOSignature4

Model.assertedDerivedFacts : ...

Model.certified_ax1 : ax_a1 Model.sig.toUFOSignature3_1
Model.certified_ax2 : ax_a2 Model.sig.toUFOSignature3_1
-- ...
Model.certified_ax108 : ax_a108 Model.sig

Model.certified : UFOAxioms4 Model.sig
Model.certifiedModel : FiniteModel4.Certified Model.data
```

The generated AST is already expanded: `given everywhere`, unary taxonomy
closure, and reflexive specialization closure have been materialized before
`compileExplicitModelAST` is used. The generated Lean file does not currently
emit the named pre-resolution AST and replay `resolveNamedFacts` inside the
object language; that remains a possible future tightening of the audit trail.

## Surface Syntax

The canonical facts are:

```lean
x : P       -- unary UFO classification predicate
x :: T      -- UFO instantiation
T1 ⊑ T2     -- specialization
x R y       -- binary relation fact
```

Examples:

```lean
given actual:
  Mark : Object
  Mark :: Person
  Person : ObjectKind
  Employee ⊑ Person
```

Facts that hold in every declared world use the reserved pseudo-world:

```lean
given everywhere:
  Person : ObjectKind
```

Selected derived relations can be asserted explicitly:

```lean
Person IsDisjointWith Organization
IsPartitionedInto(Person, Employee, NonEmployee)
```

Derived assertions are checked in `Model.assertedDerivedFacts`; they do not
override the semantic definitions computed by the compiler.

The accepted directives are currently:

```lean
derive_relations
certify
```

## Semantic Derivations

Some predicates are not arbitrary user-controlled tables in the compiled
signature. The compiler gives them their semantic definitions from lower-level
finite tables, then Lean checks the original axioms.

Current derived semantics include:

- `Type`: derived from possible instantiation;
- `Individual`: derived from absence of instantiation;
- Section 3.6:
  - `GenericFunctionalDependence`
  - `IndividualFunctionalDependence`
  - `ComponentOf`
- Section 3.7:
  - `GenericConstitutionalDependence`
  - `Constitution`
- Section 3.8:
  - `ExistentialDependence`
  - `ExistentialIndependence`
- Selected Section 3.10 predicates:
  - `ExternallyDependent`
  - `ExternallyDependentMode`
  - `QuaIndividual`
- Section 4:
  - `IsDisjointWith`
  - `IsCompletelyCoveredBy`
  - `IsPartitionedInto`
  - `Categorizes`

`Part`, `Overlap`, and `ProperPart` are finite user tables. `Part` and
`Overlap` include identity by default in generated models. Certification is
responsible for proving that the resulting mereological tables satisfy the
Section 3.5 axioms.

## Current Limitations

The Phase 1 DSL does not yet surface every field of `UFOSignature4`.

Missing or limited surface support includes:

- custom accessibility relations; generated models use the default universal
  S5 frame;
- finite set extensions, set membership/product structure, tuple projections,
  and product-subset constraints used by richer quality-structure axioms;
- metric/distance tables such as `Distance`, `DistanceZero`, `DistanceSum`, and
  `DistanceGreaterEq`;
- primitive higher-arity tables for `IndividualFunctionalDependence`,
  `ComponentOf`, and `Constitution`; users can assert these as derived facts,
  but the semantic compiler computes them from lower-level relations;
- level-aware higher-order type declarations needed for the full
  concept-evolution pattern in UFO Section 4.5;
- high-level diagnostics for failed finite checks in user-facing world/thing
  names.

The current DSL has a flat `things` namespace and a single flat `::`
instantiation table. This is enough for first-order finite witnesses and for
checking derived Section 4 relations such as disjointness, coverage,
partitioning, and simple categorization assertions. It is not enough for a
faithful certified version of the paper's concept-evolution case, where
first-order types instantiate higher-order types while also specializing stable
base types.

## File Roles

- `Certification.lean`: finite quantifier reflection and decidability bridges
  for UFO axiom packages.
- `Compiler.lean`: pure DSL pipeline after parsing, including name resolution,
  scope expansion, taxonomy expansion, reflexive specialization expansion,
  table compilation, and finite-model construction.
- `FiniteModel.lean`: finite semantic representation and compilation to
  `UFOSignature4`.
- `Syntax.lean`: thin command frontend for `ufo_model ... certify`; parses
  concrete Lean syntax, emits declarations, and invokes the pure compiler.
- `Guarantees.lean`: generic theorem-backed guarantees for the DSL pipeline and
  semantic bridge.
- `Examples.lean`: imports the concrete DSL examples.
- `ConcreteExamples/*.lean`: certified finite DSL models, except
  `ConceptEvolution.lean`, which documents the current higher-order limitation.

## How To Check The DSL

Build the whole project:

```bash
lake build
```

Build just the DSL example collection:

```bash
lake build LeanUfo.UFO.DSL.Examples
```

Build the guarantee module:

```bash
lake build LeanUfo.UFO.DSL.Guarantees
```
