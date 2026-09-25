# Theoretical notes

[Docs home](README.md) · [Project README](../README.md)

## Overview

> [!IMPORTANT]
> **Bottom line.** Lean UFO gives the selected UFO fragments a precise
> possible-world semantics and checks their consequences in Lean. Concrete
> models establish satisfiability checkpoints. The relator analysis explains
> why active axiom (a73) uses parthood instead of the printed overlap formula.

The starting materials are the UFO axioms and theorem statements discussed
section by section below, together with Kripke possible-world semantics.
Lean proofs and concrete models check their consequences. Any added assumptions
are stated separately.

| Result family | What it establishes |
| --- | --- |
| Semantic encoding | UFO predicates and modal axioms have explicit Lean meanings |
| Satisfiability checkpoints | A concrete interpretation satisfies each cumulative axiom package |
| Anti-vacuity models | Primitive and selected derived predicates have witnesses together |
| S5 consequences | Stability and modal consequences follow from the chosen frame semantics |
| Relator analysis | The printed (a73) empties the intended relator branch. The active part-based formula preserves (t31)–(t33) |

### Reading routes

| Question | Section |
| --- | --- |
| What modal semantics does the project use? | [Semantic framework](#semantic-framework) |
| Are the encoded fragments jointly satisfiable? | [Consistency checkpoints](#consistency-checkpoints) |
| Do the models avoid empty predicates? | [Anti-vacuity analysis](#anti-vacuity-analysis) |
| What does S5 add? | [S5-derived results](#s5-derived-results) |
| What happened to axiom (a73)? | [Relators, qua individuals, and axiom (a73)](#relators-qua-individuals-and-axiom-a73) |
| Which assumptions were added explicitly? | [Derived facts and added assumptions](#structural-assumptions-made-explicit) |

## Semantic framework

Lean UFO formalizes UFO semantics. It does not define a UFO proof calculus.

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

## Axiom packages

Each UFO fragment is represented by:

- a semantic signature, for example `UFOSignature3_7`;
- axiom propositions, for example `ax_a56` through `ax_a61`;
- an axiom package typeclass, for example `UFOAxioms3_7`.

A concrete model consists of a signature plus an instance of the relevant axiom
package:

```lean
def sig3_7 : UFOSignature3_7 := ...

instance : UFOAxioms3_7 sig3_7 := ...
```

This typeclass organization gives ordinary Lean proofs access to inherited
axiom fields and lets later sections extend earlier signatures.

## Consistency checkpoints

The model-existence theorems live in `LeanUfo/UFO/FormalAnalysis/Satisfiability/Consistency.lean`.
They have the following shape:

```lean
theorem consistent_3_7 :
  exists (Sig : UFOSignature3_7.{0}),
    UFOAxioms3_7 Sig
```

The intended reading is joint satisfiability relative to:

- Lean's metatheory;
- the encoded UFO axioms;
- the chosen constant-domain S5 semantics;
- the additional structural assumptions listed below.

It makes no proof-theoretic claim about derivability from a syntactic UFO
calculus.

These checkpoints establish ordinary joint satisfiability. They do not require
every primitive predicate to have a nonempty extension. The stronger and
separate analyses under `LeanUfo/UFO/FormalAnalysis/AntiVacuity/` provide one
cumulative model per section from §3.1 through §4. In each model, every
predicate introduced by that section is inhabited simultaneously. The analysis
also covers the named derived predicates defined in the section files:
`ProperSub`, `Quality`, `UltimateBearerOf`, and the membership, subset,
quality-structure, simple/complex-quality, and simple/complex-quality-type
predicates of §3.12.

The two model families remain separate. A sparse `ModelX` interpretation
witnesses joint satisfiability; an anti-vacuity model tests whether the
section's vocabulary can have nonempty extensions together.
For example, the §4 model has a metatype whose sole instance properly
specializes a broader type. A further instance of that broader type prevents
reverse specialization, as (a108) requires. `AntiVacuity.lean` is the aggregate entry
point, parallel to `Satisfiability/Consistency.lean`.

## S5-derived semantic facts

Several consequences are not stated as UFO axioms in the paper, but follow from
the chosen S5 semantics together with the modal form of the encoded definitions.
These results are collected in `LeanUfo/UFO/Core/S5_Derived.lean`.

### Modal stability principles

The core frame lemmas are:

```lean
S5Frame.dia_stable
S5Frame.box_stable
```

They say that, in S5, possibility and necessity are invariant across accessible
worlds. Because accessibility is symmetric and transitive, moving from one
accessible world to another does not change the truth of `Dia phi` or `Box phi`.

As a result, modal definitions tend to become world-invariant classifications
along accessibility.

### Section 3.1: type, individual, and specialization

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

Under S5, `Type`, `Individual`, `Sub`, and `ProperSub` are invariant across
accessible worlds because their definitions use possibility or necessity.

### Section 3.4: derived kind stability

Kind classification is invariant across accessible worlds. The theorem
`kind_stable` derives this result from (a1), (a18), (a21), (a22), (a26), and
the endurant-type clause of (a44).

A kind has a possible instance by (a1), (a18), (a26), and (a44). Rigidity
carries that instance to the target world. Axiom (a44) makes it an endurant
there, so (a21) supplies a kind for it. Axiom (a22) forces that kind to be
the original kind. S5 symmetry gives the reverse direction.

This proof uses the §3.4 signature and axioms. The §3.2 package alone does
not supply the (a44) premise. The accompanying theorems transport rigidity
and sortality to accessible worlds using (a26).

The exact `th_t10` statement needs only (a18), (a22), and (a26). If two kinds
possibly share an instance, rigidity brings that instance to the world where
both kind classifications hold. Axiom (a22) then excludes their overlap.

### Section 3.4: endurant-type refinements

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

The stability proofs for the kinds introduced by (a45) use the derived
`kind_stable` theorem. Each specific kind combines a specific type with `Kind`.
Lean proves:

- `objectKind_stable`;
- `collectiveKind_stable`;
- `quantityKind_stable`;
- `relatorKind_stable`;
- `modeKind_stable`;
- `qualityKind_stable`.

Together, type stability and derived kind stability prove invariance for
these specific kind predicates.

### Later S5 consequences

`S5_Derived.lean` also records later modal consequences, including:

- the S5 stability of the necessity clause from constitution axiom (a60);
- stability results for existential dependence and existential independence
  from Section 3.8.

These are not new UFO axioms. They are semantic consequences of representing the
paper's modal constraints inside S5.

## Formalization milestones

The inventory below records the mechanized content section by section.

### Section 3.1: types, individuals, instantiation

Files:

- `LeanUfo/UFO/Core/Signature3_1.lean`
- `LeanUfo/UFO/Core/Section3_1.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_1.lean`

Mechanized axioms:

- (a1)-(a6): `Type`, `Individual`, instantiation, and specialization;
- (a7)-(a17): concrete/abstract, endurant/perdurant, and type-taxonomy
  constraints.

Checkpoint:

```lean
consistent_3_1 :
  exists (Sig : UFOSignature3_1.{0}),
    UFOAxioms3_1 Sig
```

Interpretation: the encoded Section 3.1 axioms are jointly satisfiable.

### Section 3.2: rigidity taxonomy

Files:

- `LeanUfo/UFO/Core/Signature3_2.lean`
- `LeanUfo/UFO/Core/Section3_2.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_2.lean`

Mechanized axioms:

- (a18)-(a33);
- additional structural assumptions listed below.

Selected proved theorems:

- `th_t5`: rigidity trichotomy;
- `th_t6`: pairwise disjointness of rigidity classes;
- `th_t7`, `th_t8`: specialization constraints involving anti-rigidity;
- `th_t9`–`th_t15`: structural taxonomy properties;
- `th_t16`: non-sortal instance coverage, proved in `Section3_4.lean` using (a44);
- `th_t17`: pairwise disjointness of leaf categories;
- `th_t18`: exhaustiveness of the leaf partition.

Checkpoint:

```lean
consistent_3_2 :
  exists (Sig : UFOSignature3_2.{0}),
    UFOAxioms3_2 Sig
```

The small witness has one kind and one instance of that kind; other
rigidity-based categories can remain empty.

### Section 3.3: endurant individual taxonomy

Files:

- `LeanUfo/UFO/Core/Signature3_3.lean`
- `LeanUfo/UFO/Core/Section3_3.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_3.lean`

Mechanized axioms:

- (a34)-(a43).

Selected proved theorems:

- `th_t19`: pairwise disjointness of leaf endurant categories;
- `th_t20`: exhaustiveness of the endurant partition.

Checkpoint:

```lean
consistent_3_3 :
  exists (Sig : UFOSignature3_3.{0}),
    UFOAxioms3_3 Sig
```

The small witness interprets all endurants as substantial objects and keeps
moment categories empty.

### Section 3.4: endurant types

Files:

- `LeanUfo/UFO/Core/Signature3_4.lean`
- `LeanUfo/UFO/Core/Section3_4.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_4.lean`

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
  exists (Sig : UFOSignature3_4.{0}),
    UFOAxioms3_4 Sig
```

The witness uses one endurant type, classifies it as an object kind, and gives
it one endurant individual instance.

### Section 3.5: mereology

Files:

- `LeanUfo/UFO/Core/Signature3_5.lean`
- `LeanUfo/UFO/Core/Section3_5.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_5.lean`

Mechanized axioms:

- (a47)-(a52).

Checkpoint:

```lean
consistent_3_5 :
  exists (Sig : UFOSignature3_5.{0}),
    UFOAxioms3_5 Sig
```

The small witness interprets `Part` and `Overlap` as identity and `ProperPart`
as empty. This is a minimal extensional mereology compatible with the previous
tiny model.

### Section 3.6: composition

Files:

- `LeanUfo/UFO/Core/Signature3_6.lean`
- `LeanUfo/UFO/Core/Section3_6.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_6.lean`

Mechanized axioms:

- (a53)-(a55).

Checkpoint:

```lean
consistent_3_6 :
  exists (Sig : UFOSignature3_6.{0}),
    UFOAxioms3_6 Sig
```

The small witness keeps `FunctionsAs` and `ComponentOf` empty and interprets
the dependence relations so the definitional constraints hold over the inherited
tiny model.

### Section 3.7: constitution

Files:

- `LeanUfo/UFO/Core/Signature3_7.lean`
- `LeanUfo/UFO/Core/Section3_7.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_7.lean`

Mechanized axioms:

- (a56)-(a61).

Selected proved theorem:

- `th_t27`: constitution is non-reflexive.

Checkpoint:

```lean
consistent_3_7 :
  exists (Sig : UFOSignature3_7.{0}),
    UFOAxioms3_7 Sig
```

The small witness interprets existence as total and keeps constitution empty.

### Section 3.8: existence and existential dependence

Files:

- `LeanUfo/UFO/Core/Signature3_8.lean`
- `LeanUfo/UFO/Core/Section3_8.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_8.lean`

Mechanized axioms:

- (a62)-(a64).

Checkpoint:

```lean
consistent_3_8 :
  exists (Sig : UFOSignature3_8.{0}),
    UFOAxioms3_8 Sig
```

The small witness has one world and total existence, so existential dependence
collapses to a total relation in the inherited tiny model.

### Section 3.9: moments and inherence

Files:

- `LeanUfo/UFO/Core/Signature3_9.lean`
- `LeanUfo/UFO/Core/Section3_9.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_9.lean`

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
  exists (Sig : UFOSignature3_9.{0}),
    UFOAxioms3_9 Sig
```

Formalization note: `MomentOf` means a finite, nonempty inherence path.
The inductive definition selects the least relation closed under the two
clauses of (d2). The recursive equation alone can admit larger fixed points.
This finite-path interpretation supplies the induction principle used in
(t28)–(t30). Ultimate-bearer uniqueness uses Lean's unique existence form
(`∃!`, or `ExistsUnique` in supporting code).

### Section 3.10: relators

Files:

- `LeanUfo/UFO/Core/Signature3_10.lean`
- `LeanUfo/UFO/Core/Section3_10.lean`
- `LeanUfo/UFO/FormalAnalysis/AxiomaticAnalysis.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_10.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Relator/Model3_1.lean` through `Model3_10.lean`
- `LeanUfo/UFO/FormalAnalysis/Historical/GuardedOverlapCountermodel.lean`
- `LeanUfo/UFO/FormalAnalysis/AntiVacuity/AntiVacuity3_10.lean`

Mechanized axioms:

- (a69)-(a80);
- the additional assumption `ax_quaIndividualOf_endurant`.

Selected proved theorems:

- `foundationOf_eq_iff`;
- `th_t31`: parts of a qua individual share its foundation;
- `th_t32`: every relator has qua individuals as parts;
- `th_t33`: every relator mediates at least two distinct endurants.

Checkpoint:

```lean
consistent_3_10 :
  exists (Sig : UFOSignature3_10.{0}),
    UFOAxioms3_10 Sig
```

Formalization note: `FoundationOf` is defined using `Classical.epsilon`, which
is why the signatures carry a nonempty domain witness. The proof of `th_t33`
requires the additional assumption that qua individuals are of endurants.

#### Historical finding: printed (a73) forces relators empty

`LeanUfo/UFO/FormalAnalysis/AxiomaticAnalysis.lean` records a stronger consequence of
the printed §3.10 formula:

```lean
no_relators :
  [UFOAxioms3_10PrintedA73 Sig] ->
  forall x w, not (Sig.Relator x w)
```

The theorem is a derived result about the current axiom package. The proof
chain is:

1. `Relator x` and (a79) give a proper part `p` of `x`.
2. The same (a79) makes that proper part a `QuaIndividual`.
3. (a74) gives a bearer `b` with `QuaIndividualOf p b`.
4. (a52) turns `ProperPart p x` into `Part p x`; (a47) gives `Part p p`; and
   (a50) gives `Overlap x p`.
5. (a73) says every overlapper of qua individual `p` is an
   `ExternallyDependentMode`, so the relator `x` itself becomes an
   externally dependent mode.
6. (a70) gives `Mode x`, and (a42) gives `IntrinsicMoment x`.
7. (a41) forbids anything from being both a relator and an intrinsic moment.

The same file also proves immediate propagated consequences:

```lean
no_mediates      : forall x y w, not (Sig.Mediates x y w)
no_relatorTypes  : forall t w, not (Sig.RelatorType t w)
no_relatorKinds  : forall t w, not (Sig.RelatorKind t w)
```

The printed overlap-based (a73) therefore makes the relator branch empty when
combined with the retained §3.10 background. This is a theorem about the
historical package. The active corrected package is `UFOAxioms3_10`.

#### First repair attempt: distinct proper parts

The first analyzed repair follows a suggestion from Giancarlo Guizzardi: add a
distinctness guard to (a79)'s pairwise proper-part clause. The guarded clause
has the shape:

```text
ProperPart(y, r) and ProperPart(z, r) and y != z ->
  QuaIndividual(y) and QuaIndividual(z) and
  FoundationOf(y) = FoundationOf(z) and
  ed(y, z) and ed(z, y)
```

This blocks the original proof's direct instantiation with `(p, p)`. The
analysis-only proposition `ax_a79_distinct_guard` records this variant without
changing the packaged `ax_a79`, the DSL, or the reflective checker.

The repair is insufficient. General extensional mereology already
forces every proper part to have a distinct proper-part companion:

```lean
properPart_has_distinct_companion :
  ProperPart p x w -> exists q, ProperPart q x w and p != q
```

Given `ProperPart(p, r)`, strong supplementation (a51) supplies a part `q` of
`r` that does not overlap `p`. Transitivity and the overlap definition show
that `r` cannot be part of `q`, so (a52) makes `q` a proper part of `r`; the
non-overlap fact also gives `p != q`. The guarded pairwise clause then applies
to `(p, q)` and still yields `QuaIndividual(p)`.

The original contradiction therefore resumes through (a74), (a73), (a70),
(a42), and (a41). This is proved without assuming the original (a79):

```lean
no_relators_from_distinct_guard_attempt :
  ax_a79_distinct_guard Sig ->
  forall x w, not (Sig.Relator x w)
```

The distinctness guard alone cannot support a positive model with a nonempty
relator. Under the existing mereology and reflexive existential
dependence, `ax_a79_distinct_guard` and the original (a79) imply one another.
The guard is therefore retained as a failed experiment and possible
clarification of pairwise intent. It does not repair the semantics.

#### Selected repair: part-based (a73)

The general no-go result isolates the defect independently of every version of
(a79):

```lean
no_relator_with_quaIndividual_properPart :
  Relator r w -> ProperPart q r w -> QuaIndividual q w -> False

relator_composition_refutes_current_ax73 :
  Relator r w -> ProperPart q r w -> QuaIndividual q w ->
  not (ax_a73_printed Sig)
```

These theorems retain the relevant taxonomy and ordinary mereology assumptions
but do not assume (a79). If relators remain ordinary wholes with qua-individual
proper parts, the printed (a73) must change: its unrestricted
overlap characterization incorrectly classifies the containing relator as an
externally dependent mode.

The selected replacement characterizes a qua individual by its parts:

```text
QuaIndividualOf(x, y) <->
  forall z,
    Part(z, x) <->
      ExternallyDependentMode(z) and
      InheresIn(z, y) and
      FoundationOf(z) = FoundationOf(x)
```

`ax_a73` records this formula in `Section3_10.lean`, and
`UFOAxioms3_10.ax73` uses it. The analysis alias
`ax_a73_part_characterization` and package `UFOAxioms3_10PartRepair` are
retained so the earlier formula comparison remains reproducible. The following
results establish theorem preservation:

- `th_t31_part_characterization` proves the original (t31) conclusion directly
  from the part-based formula;
- `th_t32_without_current_ax73` shows that (t32) is independent of (a73);
- `th_t33_part_characterization` preserves (t33) unchanged.

#### Guarded-overlap comparison

The full guarded-overlap alternative does not imply unrestricted (t31), even
with the later axioms through §4. It supports a nonempty relator and preserves
(t32) and (t33). The active part-based repair also proves unrestricted (t31).

Under guarded overlap, these conditions suffice for (t31):

- `th_t31_guarded_overlap`: the selected part is an externally dependent mode,
  using (a47), (a50), and guarded (a73).
- `th_t31_guarded_overlap_of_founded`: the selected part has a foundation,
  using the full guarded-repair package through §3.10. Axiom (a71) makes that
  part an externally dependent mode or a relator. In the relator case, a
  qua-individual constituent connects the foundations through (a78) and
  guarded (a73).
- `th_t31_of_part_relator`: the qua individual is part of a relator. Axioms
  (a49) and (a78) alone give the conclusion for all its parts.

`Historical/GuardedOverlapCountermodel.lean` proves `full_counterexample`
with ten entities and three worlds. It satisfies (a1)–(a108) as currently
encoded, with guarded-overlap (a73) replacing the active part-based formula.
Both added assumptions and the source distance laws hold.

| Entities | Role in the countermodel |
| --- | --- |
| Types 0, 1, 2 | Classify objects, modes, and perdurants |
| Objects 3, 4 | Bearer and external dependence witness for the qua individual |
| Qua individual 5 | The only externally dependent mode, with proper parts 6 and 7 |
| Objects 6, 7 | Disjoint, unfounded parts of 5 |
| Perdurants 8, 9 | Two possible choices for the foundation of 5 |

Only the qua individual has proper parts. Its two disjoint parts satisfy
supplementation, and all other parthood facts are reflexive. Neither part is
a qua individual, so (a79) requires no relator. The qua individual and its
bearer exist at world 0. Two further worlds separate the existence of the
bearer and the external object, establishing their existential independence.

The unfounded parts escape the externally-dependent-mode condition in guarded
(a73). Any counterexample must use an unfounded part, as proved by
`t31_guarded_overlap_failure_unfounded`. For such a part, `FoundationOf` still
returns a value through classical choice. That value has no corresponding
`FoundedBy` fact. The model chooses perdurant 9 as the qua individual's
foundation if that unspecified value is 8, and chooses 8 otherwise.
The two values therefore differ, regardless of which value classical choice
returns. This refutes the exact total-function encoding of (t31).

Some additional restriction is thus necessary for the guarded alternative.
Requiring the selected part to have a foundation suffices. The countermodel
does not establish a weakest sufficient restriction and leaves that
restricted theorem intact.

The direct model chain under `LeanUfo/UFO/FormalAnalysis/Satisfiability/Relator/` mirrors the
section-by-section witness style of the main `ModelX` files. `Model3_10.lean`
constructs a model of `UFOAxioms3_10PartRepair` containing a relator with two
qua-individual proper parts, distinct mediated bearers, and a shared perdurant
foundation. The theorem `positive_relator_witness` exposes these facts.

The active core package and direct relator model use the part-based (a73).
The printed formula remains as `ax_a73_printed`, and the ordinary sparse
`Model3_10` proves both formulas only because its relator branch is empty. The
finite DSL, reflective checker, diagnostics, and certified fixtures are updated
in a separate propagation step so that this core change and its checker impact
remain independently reviewable.

### Section 3.11: characterization

Files:

- `LeanUfo/UFO/Core/Signature3_11.lean`
- `LeanUfo/UFO/Core/Section3_11.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_11.lean`

Mechanized axioms:

- (a81)-(a82).

Checkpoint:

```lean
consistent_3_11 :
  exists (Sig : UFOSignature3_11.{0}),
    UFOAxioms3_11 Sig
```

The small witness keeps `Characterization` empty.

### Section 3.12: qualities and quality structures

Files:

- `LeanUfo/UFO/Core/Signature3_12.lean`
- `LeanUfo/UFO/Core/Section3_12.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_12.lean`

Mechanized axioms:

- (a83)-(a101);
- `ax_distance_identity`;
- `ax_distance_symmetry`;
- `ax_distance_triangle`.

Checkpoint:

```lean
consistent_3_12 :
  exists (Sig : UFOSignature3_12.{0}),
    UFOAxioms3_12 Sig
```

Formalization notes:

- set membership and inclusion use Lean `Set Thing` extensions;
- (a99) represents product membership by finite coordinate projections.
  Coordinates must distinguish domain members: equal coordinate tuples imply
  equal members. `ProductSubsetOf.embedding` proves that these requirements
  embed the domain into the Lean Cartesian product of its component sets.
  The product may contain tuples outside the domain;
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
- no additional assumption is introduced here beyond the encoded metric
  constraints.

The witness keeps quality structures, quales, distance values, and set
extensions empty.

### Section 3.13: endurants and perdurants

Files:

- `LeanUfo/UFO/Core/Signature3_13.lean`
- `LeanUfo/UFO/Core/Section3_13.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model3_13.lean`

Mechanized axioms:

- (a102)-(a104).

Checkpoint:

```lean
consistent_3_13 :
  exists (Sig : UFOSignature3_13.{0}),
    UFOAxioms3_13 Sig
```

Formalization note: the packaged version of (a102) uses the corrected argument
order:

```text
manifests(x, y) -> Perdurant(x) and Endurant(y)
```

The printed order is retained separately as `ax_a102_printed`.

### Section 4: type structures

Files:

- `LeanUfo/UFO/Core/Signature4.lean`
- `LeanUfo/UFO/Core/Section4.lean`
- `LeanUfo/UFO/FormalAnalysis/Satisfiability/Model4.lean`

Mechanized axioms:

- (a105): disjointness of types;
- (a106): complete binary coverage;
- (a107): binary partitioning;
- (a108): categorization by proper specialization.

In the original formula (p. 202), `⊏` is proper specialization from (d1)
(p. 175): `Sub(x, y) ∧ ¬ Sub(y, x)`. Each instance of the categorizing type
must satisfy both conditions. Self-specialization and mutual specialization
between distinct types therefore fail the requirement. The Core uses
`ProperSub`, and the finite-model interpretation uses the same two conditions.

Checkpoint:

```lean
consistent_4 :
  exists (Sig : UFOSignature4.{0}),
    UFOAxioms4 Sig
```

The witness reuses the inherited tiny model and interprets the Section 4
relations extensionally by the right-hand side of their defining axioms.

## Structural assumptions made explicit

Instance typing, subtype-of-kind typing, and kind stability follow from
numbered axioms once §3.4 is available. They are ordinary theorems, with no
extra package fields or certificate checks. Two added assumptions remain:
non-sortal upward closure and qua-individual bearer typing.

| Principle | Status | Evidence |
| --- | --- | --- |
| Instances of endurant types are endurants | Derived | `inst_endurant_of_a44`: endurant-type clause of (a44) |
| Subtypes of kinds are sortals | Derived | `sub_kind_is_sortal`: (a5), (a23), (a26), endurant-type clause of (a44) |
| Kind classification is stable across accessible worlds | Derived | `kind_stable`: (a1), (a18), (a21), (a22), (a26), endurant-type clause of (a44) |
| Non-sortal upward closure | Additional assumption | Countermodel satisfying all remaining encoded axioms also refutes (t16) |
| Qua-individual bearer typing | Additional assumption | Countermodel satisfying all remaining encoded axioms also refutes (t33) |
| Distance identity, symmetry, and triangle constraints | Source axioms | The three unnumbered formulas following (a101) in §3.12 |

The distance constraints are present in the original formalization. The
selected S5 frame, nonempty constant domain, and interpretations of derived
predicates are semantic choices, described in the preceding sections.
`FormalAnalysis/StructuralAssumptions.lean` collects the derivability checks
and countermodels. Proofs used by the numbered theorems stay in `Core`.
The countermodels satisfy (a1)–(a108) as currently encoded, including the
documented corrections to (a73) and (a102), the source distance laws, and the
other added assumption. They also refute (t16) and (t33), respectively. Thus
both theorems need some additional restriction. These results do not establish
that the retained assumptions are the weakest sufficient ones.

### Instances of endurant types are endurants

In `Core/Section3_4.lean`, `inst_endurant_of_a44` applies the boxed instance
clause of (a44) at the current world. Reflexivity of S5 accessibility permits
that step. The proof needs only the endurant-type clause of (a44).
The taxonomy proofs (t23), (t24), and (t26) use this derived fact.

### Subtypes of kinds are sortals

In the same module, `sub_kind_is_sortal` first obtains endurant-type status for
the kind from (a26) and (a23). Axiom (a5) transfers instance membership from
the subtype to the kind at every accessible world. Axiom (a44) then classifies
the subtype as an endurant type, and (a23) classifies it as a sortal.

The source states (t16) in §3.2, but the mechanized proof uses (a44). Its
statement and number are preserved in `Core/Section3_4.lean`, after that axiom.
The §3.2 and §3.3 packages contain no instance-typing or subtype-of-kind field.
Their satisfiability checkpoints therefore concern the smaller packages.
From §3.4 onward, the derived facts recover both properties.

### Upward closure of NonSortal

Some additional restriction is necessary for (t16). The current proof uses
non-sortal upward closure. A countermodel below shows why the remaining
encoded axioms are insufficient.

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

The proof of `th_t16` uses this assumption in its common-supertype branch.
The lemma `nonSortal_supertype_of_endurantType` proves the conclusion from
(a5), (a23), and (a24) when the supertype is an endurant type. It uses (t15)
to rule out a sortal supertype. The unrestricted closure must also supply
the supertype's endurant-type status.

The nine-entity, one-world countermodel in
`FormalAnalysis/StructuralAssumptions.lean` refutes
both (t16) and non-sortal upward closure. It uses four objects `a`, `b`, `c`,
and `d`, one abstract individual `e`, and these four types:

| Type | Instances | Classification |
| --- | --- | --- |
| `K₁` | `a`, `b` | Kind, sortal |
| `K₂` | `c`, `d` | Kind, sortal |
| `C` | `a`, `c` | Category, non-sortal |
| `U` | `a`, `b`, `c`, `d`, `e` | Neither endurant type nor non-sortal |

For the instance `a` of `C`, both alternatives of (t16) fail:

- The only sortal containing `a` is `K₁`. It does not specialize `C`, because
  `b` belongs to `K₁` but not to `C`.
- Their only common supertype is `U`. Its abstract instance `e` excludes
  endurant-type status by (a44), and therefore non-sortal status by (a24).

Axiom (a6) still holds: it requires a common supertype without requiring
non-sortal status. Identity parthood and empty moments, relators, and quality
structures extend the model through §4. Lean verifies (a1)–(a108) as currently
encoded, the source distance laws, and qua-individual bearer typing.
`Results.t16_fails` verifies the failure of (t16) in that full model.

The current closure assumption suffices for the proof of (t16). This result
does not establish that it is the weakest sufficient assumption.

### Qua individuals are of endurants

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

The second countermodel in `FormalAnalysis/StructuralAssumptions.lean` modifies
the positive relator model. Its two qua individuals inhere in types rather
than endurants. The model satisfies all numbered axioms, the source distance
laws, and non-sortal upward closure. Its relator mediates no endurants, so
both the bearer-typing assumption and (t33) are false.

Some additional restriction is therefore necessary to recover (t33).
`th_t33_of_relator_bearer_typing` in `Core/Section3_10.lean` proves it under
the weaker condition that bearers of qua-individual proper parts of relators
are endurants. The package retains the global assumption above, which supplies
that condition. The proof uses (a47), (a49)–(a52), (a73), (a74), (a79), and
(a80); it does not use (a48).

## Methodological notes

The development follows a repeated pattern:

1. Encode a UFO fragment as a semantic signature and axiom package.
2. Prove theorems against that semantic package.
3. Construct a small witness model.
4. Prove a model-existence checkpoint.
5. Record any additional assumption needed for the paper's theorem statements.

The small witness models are sparse. Empty interpretations are
permitted in ordinary model-existence checkpoints and show joint satisfiability
without asserting ontological richness. The separate anti-vacuity modules add
section-by-section simultaneous-nonemptiness checks for the complete primitive
vocabulary and the named derived predicates listed above.

## Relation to the DSL

The finite DSL is downstream of the core theory. It compiles named finite models
into `UFOSignature4` and asks Lean to check generated theorem declarations:

```lean
ModelName.certified : UFOAxioms4 ModelName.sig
ModelName.certifiedModel : FiniteModel4.Certified ModelName.data
```

The DSL builds finite models for the same semantic target. It is an interface for building
finite signatures and producing certificates against the same core axiom
packages described above.

[Docs home](README.md) · [Project README](../README.md)
