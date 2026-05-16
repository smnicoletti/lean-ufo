# Theoretical Notes

[Docs home](README.md) · [Project README](../README.md)

This page records the theoretical and axiom-level information from the
axiomatization effort. It focuses on semantic choices, formal milestones, S5
consequences, and structural assumptions that the Lean mechanization makes
explicit.

## Semantic Framework

Lean UFO is a semantic formalization, not a proof calculus for UFO.

The core development uses:

- first-order modal semantics;
- constant-domain, possibilist Kripke models;
- S5 accessibility frames, represented by `S5Frame`;
- nonempty UFO domains, carried explicitly as `thing_nonempty`;
- Prop-valued semantic predicates and relations indexed by worlds.

The basic signature shape begins in
`LeanUfo/UFO/Core/Signature3_1.lean`:

```lean
structure UFOSignature3_1 where
  F              : S5Frame
  Thing          : Type v
  thing_nonempty : Nonempty Thing
  Type_          : Thing -> F.World -> Prop
  Individual     : Thing -> F.World -> Prop
  Inst           : Thing -> Thing -> F.World -> Prop
  Sub            : Thing -> Thing -> F.World -> Prop
  -- ...
```

The S5 frame itself is an equivalence relation:

```lean
structure S5Frame extends Frame where
  refl  : forall w, R w w
  symm  : forall {w v}, R w v -> R v w
  trans : forall {w v u}, R w v -> R v u -> R w u
```

Modal operators are interpreted directly over this frame. There is no syntactic
derivability relation, no proof-theoretic consistency theorem, and no
completeness theorem for a UFO proof system. Consistency checkpoints in this
repository are model-existence theorems: Lean constructs a semantic model
satisfying the packaged axioms.

## Axiom Packages

Each UFO fragment is represented by:

- a semantic signature, such as `UFOSignature3_7`;
- axiom propositions, such as `ax_a56` through `ax_a61`;
- an axiom package typeclass, such as `UFOAxioms3_7`.

A concrete model consists of a signature plus an instance of the relevant axiom
package:

```lean
def sig3_7 : UFOSignature3_7 := ...

instance : UFOAxioms3_7 sig3_7 := ...
```

This typeclass organization gives ordinary Lean proofs access to inherited
axiom fields and lets later sections extend earlier signatures.

## Consistency Checkpoints

The model-existence theorems live in `LeanUfo/UFO/Models/Consistency.lean`.
They have the following shape:

```lean
theorem consistent_3_7 :
  exists (Sig : UFOSignature3_7.{0,0}),
    UFOAxioms3_7 Sig
```

The intended reading is joint satisfiability relative to:

- Lean's metatheory;
- the encoded UFO axioms;
- the chosen constant-domain S5 semantics;
- the additional structural assumptions listed below.

It is deliberately not a proof-theoretic claim about derivability from a
syntactic UFO calculus.

## S5-Derived Semantic Facts

Several consequences are not stated as UFO axioms in the paper, but follow from
the chosen S5 semantics together with the modal form of the encoded definitions.
These results are collected in `LeanUfo/UFO/Core/S5_Derived.lean`.

### Modal Stability Principles

The core frame lemmas are:

```lean
S5Frame.dia_stable
S5Frame.box_stable
```

They say that, in S5, possibility and necessity are invariant across accessible
worlds. Because accessibility is symmetric and transitive, moving from one
accessible world to another does not change the truth of `Dia phi` or `Box phi`.

This has important ontological consequences: modal definitions tend to become
world-invariant classifications, modulo accessibility.

### Section 3.1: Type, Individual, And Specialization

From the modal definitions:

```lean
ax_a1 : Type x w <-> Dia (exists y, y :: x)
ax_a2 : Individual x w <-> Box (not exists y, y :: x)
ax_a5 : Sub x y w <-> ...
```

and the S5 stability lemmas, Lean proves:

- `type_stable`;
- `individual_stable`;
- `sub_stable`;
- `properSub_stable`.

The conceptual point is that under S5, `Type`, `Individual`, `Sub`, and
`ProperSub` are not merely local classifications. Once they are defined through
possibility or necessity over an S5 frame, they become invariant across
accessible worlds.

### Section 3.2: Kind Stability

Kind invariance does not follow from S5 alone. It depends on an additional
structural axiom made explicit in the mechanization:

```lean
def ax_kindStable : Prop :=
  forall k w v,
    Kind k w ->
    R w v ->
    Kind k v
```

Using `ax_kindStable` and S5 frame properties, Lean proves:

- `kind_stable`;
- kindhood transports rigid/sortal consequences across accessible worlds.

The conceptual point is that the Kind branch is modally persistent only because
the mechanization explicitly adds the stability principle that the informal
development relies on.

### Section 3.4: Endurant-Type Refinements

The endurant-type refinements introduced by (a44) are defined using:

- `Type`;
- a boxed condition on instances.

Since both `Type` and `Box` are stable in S5, Lean proves invariance for:

- `substantialType_stable`;
- `momentType_stable`;
- `objectType_stable`;
- `collectiveType_stable`;
- `quantityType_stable`;
- `relatorType_stable`;
- `modeType_stable`;
- `qualityType_stable`.

For the corresponding kinds introduced by (a45), stability additionally depends
on `ax_kindStable`, because each specific kind is the corresponding specific
type plus `Kind`. Lean proves:

- `objectKind_stable`;
- `collectiveKind_stable`;
- `quantityKind_stable`;
- `relatorKind_stable`;
- `modeKind_stable`;
- `qualityKind_stable`.

The conceptual point is that S5 turns modal type refinements into stable
classifications, and `ax_kindStable` lifts that persistence to the specific
kind predicates.

### Later S5 Consequences

`S5_Derived.lean` also records later modal consequences, including:

- the S5 stability of the necessity clause from constitution axiom (a60);
- stability results for existential dependence and existential independence
  from Section 3.8.

These are not new UFO axioms. They are semantic consequences of representing the
paper's modal constraints inside S5.

## Formalization Milestones

This section summarizes what is currently mechanized section by section.

### Section 3.1: Types, Individuals, Instantiation

Files:

- `LeanUfo/UFO/Core/Signature3_1.lean`
- `LeanUfo/UFO/Core/Section3_1.lean`
- `LeanUfo/UFO/Models/Model3_1.lean`

Mechanized axioms:

- (a1)-(a6): `Type`, `Individual`, instantiation, and specialization;
- (a7)-(a17): concrete/abstract, endurant/perdurant, and type-taxonomy
  constraints.

Checkpoint:

```lean
consistent_3_1 :
  exists (Sig : UFOSignature3_1.{0,0}),
    UFOAxioms3_1 Sig
```

Interpretation: the encoded Section 3.1 axioms are jointly satisfiable.

### Section 3.2: Rigidity Taxonomy

Files:

- `LeanUfo/UFO/Core/Signature3_2.lean`
- `LeanUfo/UFO/Core/Section3_2.lean`
- `LeanUfo/UFO/Models/Model3_2.lean`

Mechanized axioms:

- (a18)-(a33);
- additional structural assumptions listed below.

Selected proved theorems:

- `th_t5`: rigidity trichotomy;
- `th_t6`: pairwise disjointness of rigidity classes;
- `th_t7`, `th_t8`: specialization constraints involving anti-rigidity;
- `th_t9`-`th_t16`: structural taxonomy properties;
- `th_t17`: pairwise disjointness of leaf categories;
- `th_t18`: exhaustiveness of the leaf partition.

Checkpoint:

```lean
consistent_3_2 :
  exists (Sig : UFOSignature3_2.{0,0}),
    UFOAxioms3_2 Sig
```

The small witness has one kind and one instance of that kind; other
rigidity-based categories can remain empty.

### Section 3.3: Endurant Individual Taxonomy

Files:

- `LeanUfo/UFO/Core/Signature3_3.lean`
- `LeanUfo/UFO/Core/Section3_3.lean`
- `LeanUfo/UFO/Models/Model3_3.lean`

Mechanized axioms:

- (a34)-(a43).

Selected proved theorems:

- `th_t19`: pairwise disjointness of leaf endurant categories;
- `th_t20`: exhaustiveness of the endurant partition.

Checkpoint:

```lean
consistent_3_3 :
  exists (Sig : UFOSignature3_3.{0,0}),
    UFOAxioms3_3 Sig
```

The small witness interprets all endurants as substantial objects and keeps
moment categories empty.

### Section 3.4: Endurant Types

Files:

- `LeanUfo/UFO/Core/Signature3_4.lean`
- `LeanUfo/UFO/Core/Section3_4.lean`
- `LeanUfo/UFO/Models/Model3_4.lean`

Mechanized axioms:

- (a44)-(a46), with (a44) and (a45) split into named component propositions for
  maintainable proofs.

Selected proved theorems:

- `th_t21`: pairwise disjointness of specific endurant type categories;
- `th_t22`: possible instantiation of a specific endurant kind implies
  enduranthood;
- `th_t23`: every endurant sortal belongs to a leaf of the endurant-type
  taxonomy;
- `th_t24`: characterization of specific endurant sortals via specialization of
  a specific kind;
- `th_t25`: pairwise disjointness of endurant-type taxonomy leaves;
- `th_t26`: exhaustiveness of the endurant-type leaf partition.

Checkpoint:

```lean
consistent_3_4 :
  exists (Sig : UFOSignature3_4.{0,0}),
    UFOAxioms3_4 Sig
```

The witness uses one endurant type, classifies it as an object kind, and gives
it one endurant individual instance.

### Section 3.5: Mereology

Files:

- `LeanUfo/UFO/Core/Signature3_5.lean`
- `LeanUfo/UFO/Core/Section3_5.lean`
- `LeanUfo/UFO/Models/Model3_5.lean`

Mechanized axioms:

- (a47)-(a52).

Checkpoint:

```lean
consistent_3_5 :
  exists (Sig : UFOSignature3_5.{0,0}),
    UFOAxioms3_5 Sig
```

The small witness interprets `Part` and `Overlap` as identity and `ProperPart`
as empty. This is a minimal extensional mereology compatible with the previous
tiny model.

### Section 3.6: Composition

Files:

- `LeanUfo/UFO/Core/Signature3_6.lean`
- `LeanUfo/UFO/Core/Section3_6.lean`
- `LeanUfo/UFO/Models/Model3_6.lean`

Mechanized axioms:

- (a53)-(a55).

Checkpoint:

```lean
consistent_3_6 :
  exists (Sig : UFOSignature3_6.{0,0}),
    UFOAxioms3_6 Sig
```

The small witness keeps `FunctionsAs` and `ComponentOf` empty and interprets
the dependence relations so the definitional constraints hold over the inherited
tiny model.

### Section 3.7: Constitution

Files:

- `LeanUfo/UFO/Core/Signature3_7.lean`
- `LeanUfo/UFO/Core/Section3_7.lean`
- `LeanUfo/UFO/Models/Model3_7.lean`

Mechanized axioms:

- (a56)-(a61).

Selected proved theorem:

- `th_t27`: constitution is non-reflexive.

Checkpoint:

```lean
consistent_3_7 :
  exists (Sig : UFOSignature3_7.{0,0}),
    UFOAxioms3_7 Sig
```

The small witness interprets existence as total and keeps constitution empty.

### Section 3.8: Existence And Existential Dependence

Files:

- `LeanUfo/UFO/Core/Signature3_8.lean`
- `LeanUfo/UFO/Core/Section3_8.lean`
- `LeanUfo/UFO/Models/Model3_8.lean`

Mechanized axioms:

- (a62)-(a64).

Checkpoint:

```lean
consistent_3_8 :
  exists (Sig : UFOSignature3_8.{0,0}),
    UFOAxioms3_8 Sig
```

The small witness has one world and total existence, so existential dependence
collapses to a total relation in the inherited tiny model.

### Section 3.9: Moments And Inherence

Files:

- `LeanUfo/UFO/Core/Signature3_9.lean`
- `LeanUfo/UFO/Core/Section3_9.lean`
- `LeanUfo/UFO/Models/Model3_9.lean`

Mechanized axioms:

- (a65)-(a68).

Selected proved theorems and helpers:

- `not_momentOf_of_no_inheres`;
- `momentOf_eq_of_unique_direct_bearer`;
- `th_t28`: inherence is non-reflexive;
- `th_t29`: inherence is asymmetric;
- `th_t30`: inherence is anti-transitive.

Checkpoint:

```lean
consistent_3_9 :
  exists (Sig : UFOSignature3_9.{0,0}),
    UFOAxioms3_9 Sig
```

Formalization note: `MomentOf` is represented as an inductive transitive-closure
relation, and ultimate-bearer uniqueness is encoded using Lean's unique
existence form (`exists unique`, displayed in Lean as `exists!` or
`ExistsUnique` in supporting code).

### Section 3.10: Relators

Files:

- `LeanUfo/UFO/Core/Signature3_10.lean`
- `LeanUfo/UFO/Core/Section3_10.lean`
- `LeanUfo/UFO/Models/Model3_10.lean`

Mechanized axioms:

- (a69)-(a80);
- the bridge axiom `ax_quaIndividualOf_endurant`.

Selected proved theorems:

- `foundationOf_eq_iff`;
- `th_t31`: parts of a qua individual share its foundation;
- `th_t32`: every relator has qua individuals as parts;
- `th_t33`: every relator mediates at least two distinct endurants.

Checkpoint:

```lean
consistent_3_10 :
  exists (Sig : UFOSignature3_10.{0,0}),
    UFOAxioms3_10 Sig
```

Formalization note: `FoundationOf` is defined using `Classical.epsilon`, which
is why the signatures carry a nonempty domain witness. The proof of `th_t33`
requires the explicit bridge axiom that qua individuals are of endurants.

### Section 3.11: Characterization

Files:

- `LeanUfo/UFO/Core/Signature3_11.lean`
- `LeanUfo/UFO/Core/Section3_11.lean`
- `LeanUfo/UFO/Models/Model3_11.lean`

Mechanized axioms:

- (a81)-(a82).

Checkpoint:

```lean
consistent_3_11 :
  exists (Sig : UFOSignature3_11.{0,0}),
    UFOAxioms3_11 Sig
```

The small witness keeps `Characterization` empty.

### Section 3.12: Qualities And Quality Structures

Files:

- `LeanUfo/UFO/Core/Signature3_12.lean`
- `LeanUfo/UFO/Core/Section3_12.lean`
- `LeanUfo/UFO/Models/Model3_12.lean`

Mechanized axioms:

- (a83)-(a101);
- `ax_distance_identity`;
- `ax_distance_symmetry`;
- `ax_distance_triangle`.

Checkpoint:

```lean
consistent_3_12 :
  exists (Sig : UFOSignature3_12.{0,0}),
    UFOAxioms3_12 Sig
```

Formalization notes:

- set membership and inclusion use Lean `Set Thing` extensions;
- product membership in (a99) is represented by tuple projections over a shared
  finite index;
- quales, quality domains, tuple-like product members, and distance values
  remain UFO `Thing`s rather than being split into separate Lean carrier types;
- in the finite DSL checker, membership-backed set obligations are executable,
  and the product-family obligation in (a99) is discharged from explicit
  finite `product_family` witnesses; this gives a sound checker-backed path for
  the core axiom and a complete checker for the finite stored-witness
  proposition `ax99Finite`, but not a converse theorem for arbitrary core
  `ax_a99` witnesses unless the model also satisfies the explicit
  representation-completeness condition `ProductFamilyWitnessTableComplete`;
- metric constraints are expressed relationally at the UFO object-language
  level;
- no additional bridge axiom is introduced here beyond the encoded metric
  constraints.

The witness keeps quality structures, quales, distance values, and set
extensions empty.

### Section 3.13: Endurants And Perdurants

Files:

- `LeanUfo/UFO/Core/Signature3_13.lean`
- `LeanUfo/UFO/Core/Section3_13.lean`
- `LeanUfo/UFO/Models/Model3_13.lean`

Mechanized axioms:

- (a102)-(a104).

Checkpoint:

```lean
consistent_3_13 :
  exists (Sig : UFOSignature3_13.{0,0}),
    UFOAxioms3_13 Sig
```

Formalization note: the packaged version of (a102) uses the corrected argument
order:

```text
manifests(x, y) -> Perdurant(x) and Endurant(y)
```

The printed order is retained separately as `ax_a102_printed`.

### Section 4: Type Structures

Files:

- `LeanUfo/UFO/Core/Signature4.lean`
- `LeanUfo/UFO/Core/Section4.lean`
- `LeanUfo/UFO/Models/Model4.lean`

Mechanized axioms:

- (a105): disjointness of types;
- (a106): complete binary coverage;
- (a107): binary partitioning;
- (a108): categorization by specialization.

Checkpoint:

```lean
consistent_4 :
  exists (Sig : UFOSignature4.{0,0}),
    UFOAxioms4 Sig
```

The witness reuses the inherited tiny model and interprets the Section 4
relations extensionally by the right-hand side of their defining axioms.

## Structural Assumptions Made Explicit

During mechanization, several assumptions that are implicit in the paper's
informal exposition had to be added as explicit axioms. This section records
them so the difference between paper text, encoded axioms, and Lean semantics is
visible.

### Kind Stability

File:

- `LeanUfo/UFO/Core/Section3_2.lean`

Formal axiom:

```lean
def ax_kindStable : Prop :=
  forall k w v,
    Kind k w ->
    R w v ->
    Kind k v
```

Intended reading: kinds are stable across accessible worlds.

Used for:

- `th_t10`: necessary disjointness of distinct kinds;
- `th_t11`: non-specialization of distinct kinds;
- `th_t14`: no type specializes two distinct kinds;
- Section 3.4 theorems that transport specific kind information across worlds;
- the S5-derived kind and specific-kind stability theorems.

### Instances Of Endurant Types Are Endurants

File:

- `LeanUfo/UFO/Core/Section3_2.lean`

Formal axiom:

```lean
def ax_instEndurant_of_EndurantType : Prop :=
  forall t x w,
    EndurantType t w ->
    Inst x t w ->
    Endurant x w
```

Intended reading: an instance of an endurant type is an endurant.

This typing principle is used by results such as `th_t16` and by the Section
3.4 endurant-type taxonomy results.

### Subtypes Of Kinds Are Sortals

File:

- `LeanUfo/UFO/Core/Section3_2.lean`

Formal axiom:

```lean
def ax_sub_of_kind_is_sortal : Prop :=
  forall a k w,
    Sub a k w ->
    Kind k w ->
    Sortal a w
```

Intended reading: the subtypes below kinds stay in the sortal branch.

This is used in the subtype branch of `th_t16` and in the Section 3.4
characterization of specific endurant sortals.

### Upward Closure Of NonSortal

File:

- `LeanUfo/UFO/Core/Section3_2.lean`

Formal axiom:

```lean
def ax_nonSortal_upward : Prop :=
  forall a b w,
    NonSortal a w ->
    Sub a b w ->
    NonSortal b w
```

Intended reading: if a non-sortal specializes a supertype, the supertype is
also non-sortal.

This is used in the common-supertype branch of `th_t16`.

### Qua Individuals Are Of Endurants

File:

- `LeanUfo/UFO/Core/Section3_10.lean`

Formal axiom:

```lean
def ax_quaIndividualOf_endurant : Prop :=
  forall x y w,
    QuaIndividualOf x y w ->
    Endurant y w
```

Intended reading: the bearer associated with a qua individual is an endurant.

This is required for `th_t33`, because the informal proof that every relator
mediates at least two distinct endurants relies on a typing assumption not
forced by (a73)-(a80) alone.

## Methodological Notes

The development follows a repeated pattern:

1. Encode a UFO fragment as a semantic signature and axiom package.
2. Prove theorems against that semantic package.
3. Construct a small witness model.
4. Prove a model-existence checkpoint.
5. Record any extra bridge principle needed for the paper's theorem statements.

The small witness models are intentionally sparse. Empty interpretations are
often informative: they show that a fragment's axioms constrain structure
without forcing unnecessary ontological richness.

## Relation To The DSL

The finite DSL is downstream of the core theory. It compiles named finite models
into `UFOSignature4` and asks Lean to check generated theorem declarations:

```lean
ModelName.certified : UFOAxioms4 ModelName.sig
ModelName.certifiedModel : FiniteModel4.Certified ModelName.data
```

The DSL does not change the semantic target. It is an interface for building
finite signatures and producing certificates against the same core axiom
packages described above.

[Docs home](README.md) · [Project README](../README.md)
