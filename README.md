# Lean UFO Formalization

> A formal, machine-checked semantic mechanization of the  
> **Unified Foundational Ontology (UFO)** in Lean 4.

---

## ✦ Overview

This repository develops a rigorous semantic formalization of the **Unified Foundational Ontology (UFO)** using the Lean 4 theorem prover.

The development proceeds fragment-by-fragment, aligned with the structure of the original UFO axiomatization (see below).

The goal is to establish **explicit, machine-checked semantic consistency
checkpoints** for successive UFO fragments via concrete Kripke models. In this
repository, a consistency checkpoint means a joint-satisfiability result: we
construct a model satisfying the packaged axioms.

The repository also includes a first Lean-native DSL for finite UFO models.
The DSL lets users write compact named-world/named-thing models, expands them
to finite semantic data, and automatically emits ordinary Lean certificates of
`UFOAxioms4`.  Consequently, any DSL model that successfully passes `certify`
comes with a Lean theorem proving that its compiled finite signature is a model
of the encoded UFO axioms.

Each subsection:

- defines a semantic signature,
- packages its axioms as a Lean typeclass,
- proves the stated theorems semantically,
- constructs a small concrete witness model,
- establishes a formal joint-satisfiability theorem.

---

## ✦ Logical Framework

The mechanization is based on:

- First-order modal logic **S5**
- Constant-domain (possibilist) Kripke semantics
- Nonempty domains of quantification (`Nonempty Thing` is carried explicitly in
  the signatures, to support definite-description style constructions, e.g., used in
  §3.10)
- Equivalence accessibility relations

Modal operators are interpreted semantically. No proof calculus, derivability
relation, syntactic consistency theorem, or completeness theory is implemented
at this stage.

Lean 4:  
https://leanprover.github.io/

---

## ✦ Source Material

This formalization follows the axiomatization presented in:

**Guizzardi et al. (2022)**  
*UFO: Unified Foundational Ontology*  
Applied Ontology 17(2): 167–210  
https://doi.org/10.3233/AO-210256

```bibtex
@article{guizzardi2022ufo,
  author  = {Guizzardi, Giancarlo and Benevides, Alessander Botti and
             Fonseca, Claudenir M. and Porello, Daniele and
             Almeida, Jo{\~a}o Paulo A. and Sales, Tiago Prince},
  title   = {UFO: Unified Foundational Ontology},
  journal = {Applied Ontology},
  volume  = {17},
  number  = {2},
  pages   = {167--210},
  year    = {2022},
  doi     = {10.3233/AO-210256}
}
```
---

## ✦ S5-Derived Semantic Facts

Adopting S5 Kripke semantics has strong structural consequences for the interpretation of UFO predicates.

In particular, because accessibility is an equivalence relation, modal operators become **invariant across accessible worlds**. This yields additional semantic results beyond the axioms explicitly stated in the UFO paper.

### World Invariance of Modal Definitions (§3.1)

From the modal definitions of key predicates:

- `Type(x) ↔ ◇(∃ y, y :: x)` (a1)  
- `Individual(x) ↔ □(¬∃ y, y :: x)` (a2)  

and S5 modal properties, we obtain:

- `Type` is invariant across accessible worlds  
- `Individual` is invariant across accessible worlds  
- `Sub` (specialization) is invariant across accessible worlds  
- `ProperSub` is invariant across accessible worlds  

Intuitively:

> Under S5, modal definitions collapse into **world-independent classifications modulo accessibility**.

These results are formalized in:

`LeanUfo/UFO/Core/S5_Derived.lean`

### Accessibility Invariance for Kinds (§3.2)

In §3.2, the core additional S5-derived facts concern `Kind`.

These results do **not** follow from S5 alone. They require the explicit
structural axiom introduced in the mechanization (see below):

- `ax_kindStable`

From this axiom and S5 symmetry/transitivity, we obtain:

- `Kind` is invariant across accessible worlds  
- if something is a `Kind` at `w`, then at every accessible world `v` it is still:
  - `Rigid`
  - `Sortal`

Intuitively:

> Under S5 plus `ax_kindStable`, the Kind branch becomes modally persistent.

### Accessibility Invariance for Endurant-Type Refinements (§3.4)

In §3.4, the new type-level refinements introduced by (a44) are all defined as:

- `Type`
- together with a boxed condition on instances

Since `Type` is S5-stable and `Box` is S5-stable, the following predicates are
invariant across accessible worlds:

- `SubstantialType`
- `MomentType`
- `ObjectType`
- `CollectiveType`
- `QuantityType`
- `RelatorType`
- `ModeType`
- `QualityType`

For the specific endurant kinds introduced by (a45), stability additionally
depends on the introduced structural axiom `ax_kindStable`, because each such
predicate is defined as:

- the corresponding specific endurant type
- together with `Kind`

Hence we also obtain:

- `ObjectKind` is invariant across accessible worlds  
- `CollectiveKind` is invariant across accessible worlds  
- `QuantityKind` is invariant across accessible worlds  
- `RelatorKind` is invariant across accessible worlds  
- `ModeKind` is invariant across accessible worlds  
- `QualityKind` is invariant across accessible worlds  

Intuitively:

> In §3.4, S5 turns the new modal type refinements into world-invariant
> classifications, and with `ax_kindStable` the same becomes true for the
> corresponding specific kinds.

These results are formalized in:

`LeanUfo/UFO/Core/S5_Derived.lean`

---

## ✦ Architecture and Design

### Signatures and Axioms

Each subsection introduces:

- A semantic signature:
  - `UFOSignature3_X`
- A typeclass packaging its axioms:
  - `UFOAxioms3_X (Sig : UFOSignature3_X)`

A concrete model consists of:

```lean
def sig3_X : UFOSignature3_X := ...
instance : UFOAxioms3_X sig3_X := ...
```

Axioms are attached via **typeclass instances**. This allows:

- automatic axiom inference in proofs,
- clean extension between subsections,
- multiple alternative models for the same signature.

### Semantic Consistency Checkpoints

For each subsection:

```lean
theorem consistent_3_X :
  ∃ (Sig : UFOSignature3_X.{0,0}),
    UFOAxioms3_X Sig
```

This establishes joint satisfiability of the axioms. We also call these
theorems semantic consistency checkpoints: relative to Lean’s metatheory and
the chosen S5 semantics, the displayed model existence theorem rules out a
semantic contradiction in the packaged axiom set. It is not a proof-theoretic
consistency result, since no UFO proof calculus is formalized here.

---

## ✦ Milestones

---

### ✓ Subsection 3.1 — Types, Individuals, Instantiation

Mechanized axioms:

- (a1)–(a6): core constraints on Type, Individual, Instantiation, Specialization  
- (a7)–(a17): taxonomic classification constraints  

All axioms are encoded as semantic constraints on constant-domain S5 Kripke models.

Concrete witness:

`LeanUfo/UFO/Models/Model3_1.lean`

Consistency theorem:

```lean
consistent_3_1 :
  ∃ (Sig : UFOSignature3_1.{0,0}),
    UFOAxioms3_1 Sig
```

Interpretation:

> The subsection 3.1 axioms are jointly satisfiable.

---

### ✓ Subsection 3.2 — Rigidity Taxonomy

Mechanized axioms:

- (a18)–(a33)

Proved theorems:

- (t5) Rigidity trichotomy  
- (t6) Pairwise disjointness of rigidity classes  
- (t7)–(t8) Specialization constraints  
- (t9)–(t16) Structural taxonomy properties  
- (t17) Pairwise disjointness of leaf categories  
- (t18) Exhaustiveness of the leaf partition  

Concrete witness:

`LeanUfo/UFO/Models/Model3_2.lean`

Consistency theorem:

```lean
consistent_3_2 :
  ∃ (Sig : UFOSignature3_2.{0,0}),
    UFOAxioms3_2 Sig
```

Small model characteristics:

- One Kind
- One instance of that Kind
- All other rigidity-based categories empty

This shows that the rigidity taxonomy constrains classification structure
without forcing ontological richness.

---

### ✓ Subsection 3.3 — Endurant Individual Taxonomy

Mechanized axioms:

- (a34)–(a43)

Proved theorems:

- (t19) Pairwise disjointness of leaf endurant categories  
- (t20) Exhaustiveness of the endurant partition  

Concrete witness:

`LeanUfo/UFO/Models/Model3_3.lean`

Consistency theorem:

```lean
consistent_3_3 :
  ∃ (Sig : UFOSignature3_3.{0,0}),
    UFOAxioms3_3 Sig
```

The small witness interprets:

- All Endurants as Substantials (Objects)
- Moment categories empty

This leverages the fact that §3.3 model is a refinement of §3.2.

---

### ✓ Subsection 3.4 — Endurant Types

Mechanized axioms:

- (a44)–(a46)

Proved theorems:

- (t21) Pairwise disjointness of the six specific endurant type categories  
- (t22) Possible instantiation of a specific endurant kind implies enduranthood  
- (t23) Every endurant sortal belongs to a leaf of the endurant-type taxonomy  
- (t24) Characterization of specific endurant sortals via specialization of a specific kind  
- (t25) Pairwise disjointness of the leaves of the endurant-type taxonomy  
- (t26) Exhaustiveness of the endurant-type leaf partition  

Concrete witness:

`LeanUfo/UFO/Models/Model3_4.lean`

Consistency theorem:

```lean
consistent_3_4 :
  ∃ (Sig : UFOSignature3_4.{0,0}),
    UFOAxioms3_4 Sig
```

The small witness interprets:

- one unique endurant type, which is an `ObjectType`
- that same type as an `ObjectKind`
- one unique endurant individual instantiating it
- all other new §3.4 refinements as empty

This shows that the §3.4 refinements are jointly satisfiable together with
all inherited constraints from §§3.1–3.3.

---

### ✓ Subsection 3.5 — Mereology

Mechanized axioms:

- (a47)–(a52)

Concrete witness:

`LeanUfo/UFO/Models/Model3_5.lean`

Consistency theorem:

```lean
consistent_3_5 :
  ∃ (Sig : UFOSignature3_5.{0,0}),
    UFOAxioms3_5 Sig
```

The small witness interprets:

- `Part` as identity
- `Overlap` as identity
- `ProperPart` as empty

This yields a minimal extensional mereology compatible with the existing
tiny witness model from §§3.1–3.4.

---

### ✓ Subsection 3.6 — Composition

Mechanized axioms:

- (a53)–(a55)

Concrete witness:

`LeanUfo/UFO/Models/Model3_6.lean`

Consistency theorem:

```lean
consistent_3_6 :
  ∃ (Sig : UFOSignature3_6.{0,0}),
    UFOAxioms3_6 Sig
```

The small witness interprets:

- `FunctionsAs` as empty
- `GenericFunctionalDependence` as universally true
- `IndividualFunctionalDependence` by the right-hand side of (a54)
- `ComponentOf` as empty

This yields a minimal composition witness compatible with the tiny models
already used for §§3.1–3.5.

---

### ✓ Subsection 3.7 — Constitution

Mechanized axioms:

- (a56)–(a61)

Proved theorems:

- (t27) Constitution is non-reflexive

Concrete witness:

`LeanUfo/UFO/Models/Model3_7.lean`

Consistency theorem:

```lean
consistent_3_7 :
  ∃ (Sig : UFOSignature3_7.{0,0}),
    UFOAxioms3_7 Sig
```

The small witness interprets:

- `Ex` as total
- `ConstitutedBy` as empty
- `GenericConstitutionalDependence` as true only vacuously for instance-empty arguments
- `Constitution` as empty

This gives a minimal constitution layer compatible with the witness already
constructed for §§3.1–3.6.

---

### ✓ Subsection 3.8 — Existence and Existential Dependence

Mechanized axioms:

- (a62)–(a64)

Concrete witness:

`LeanUfo/UFO/Models/Model3_8.lean`

Consistency theorem:

```lean
consistent_3_8 :
  ∃ (Sig : UFOSignature3_8.{0,0}),
    UFOAxioms3_8 Sig
```

The small witness interprets:

- `Ex` as total
- `ExistentialDependence` exactly by the right-hand side of (a63)
- `ExistentialIndependence` as empty

Since the witness has one world and everything exists there, existential
dependence becomes total in the model.

---

### ✓ Subsection 3.9 — Moments and Inherence

Mechanized axioms:

- (a65)–(a68)

Proved theorems:

- (t28) Inherence is non-reflexive
- (t29) Inherence is asymmetric
- (t30) Inherence is anti-transitive

Concrete witness:

`LeanUfo/UFO/Models/Model3_9.lean`

Consistency theorem:

```lean
consistent_3_9 :
  ∃ (Sig : UFOSignature3_9.{0,0}),
    UFOAxioms3_9 Sig
```

Formalization notes:

- `momentOf` is represented as an inductive transitive-closure relation (`MomentOf`)
- `ultimateBearerOf` uniqueness is encoded using mathlib’s `∃!` / `ExistsUnique`

The small witness interprets:

- `InheresIn` as empty
- `MomentOf` and `UltimateBearerOf` therefore as empty as well

This yields a minimal consistency witness for the inherence layer.

---

### ✓ Subsection 3.10 — Relators

Mechanized axioms:

- (a69)–(a80)

Proved theorems:

- (t31) Parts of a qua individual share its foundation
- (t32) Every relator has qua individuals as parts
- (t33) Every relator mediates at least two distinct endurants

Concrete witness:

`LeanUfo/UFO/Models/Model3_10.lean`

Consistency theorem:

```lean
consistent_3_10 :
  ∃ (Sig : UFOSignature3_10.{0,0}),
    UFOAxioms3_10 Sig
```

Formalization notes:

- `foundationOf` is defined via `Classical.epsilon`, using the explicit
  nonemptiness witness carried by the signature
- the uniqueness axioms (a72) and (a77) use mathlib’s `∃!` / `ExistsUnique`
- `t33` requires one additional bridge axiom made explicit in the mechanization
  (see the structural assumptions section below)

The small witness interprets:

- `ExternallyDependent` as total
- `ExternallyDependentMode`, `FoundedBy`, `QuaIndividualOf`, `QuaIndividual`,
  `Relator`, and `Mediates` as empty

This keeps the §3.10 witness minimal.

---

### ✓ Subsection 3.11 — Characterization

Mechanized axioms:

- (a81)–(a82)

Concrete witness:

`LeanUfo/UFO/Models/Model3_11.lean`

Consistency theorem:

```lean
consistent_3_11 :
  ∃ (Sig : UFOSignature3_11.{0,0}),
    UFOAxioms3_11 Sig
```

Formalization notes:

- the uniqueness clauses in (a81) and (a82) use mathlib’s `∃!` /
  `ExistsUnique`

The small witness interprets:

- `Characterization` as empty

This keeps the §3.11 witness minimal, reusing the inherited model with no
moments, no quality types.

---

### ✓ Subsection 3.12 — Qualities and Quality Structures

Mechanized axioms:

- (a83)–(a101)
- distance identity, symmetry, and triangle constraints

Concrete witness:

`LeanUfo/UFO/Models/Model3_12.lean`

Consistency theorem:

```lean
consistent_3_12 :
  ∃ (Sig : UFOSignature3_12.{0,0}),
    UFOAxioms3_12 Sig
```

Formalization notes:

- set-theoretic membership, inclusion, proper inclusion, and non-emptiness are
  encoded via Lean `Set Thing` extensions
- the finite Cartesian product subset in (a99) is represented by tuple
  projections over a shared `Fin n` index
- metric arithmetic is kept relational and abstract, with distance values still
  represented as UFO `Thing`s
- these choices deliberately keep §3.12 at the paper's object-language level:
  quales, sets, quality domains, tuple-like product members, and distance
  values remain entities in one UFO domain and are classified by predicates and
  relations, rather than being separated into Lean-level carrier types
- this proof-oriented encoding is still extensible: later bridge layers can
  interpret selected UFO `Thing`s as Lean tuples, numeric distance values, or
  richer structures without changing the core §3.12 axioms
- no additional bridge axioms are introduced in §3.12; the extra distance
  constraints are direct encodings of the metric constraints stated in the
  paper, while tuple projections and relational arithmetic are signature-level
  interfaces
- definitions (d5)–(d10) are treated as derived predicates, following the
  treatment of earlier definitions such as `ProperSub`, `MomentOf`, and
  `FoundationOf`; `d6` is formalized earlier in §3.3 because the §3.3
  intrinsic-moment partition already refers to `Quality`

The small witness interprets:

- quales, quality domains, quality dimensions, quality values, and distances
  as empty
- the derived quality-structure and simple/complex quality predicates as empty
  by their definitions
- all Lean-set extensions as empty

This keeps the §3.12 witness minimal while validating the new set-theoretic
and metric-interface axioms.

---

### ✓ Subsection 3.13 — Endurants and Perdurants

Mechanized axioms:

- (a102)–(a104)

Concrete witness:

`LeanUfo/UFO/Models/Model3_13.lean`

Consistency theorem:

```lean
consistent_3_13 :
  ∃ (Sig : UFOSignature3_13.{0,0}),
    UFOAxioms3_13 Sig
```

Formalization notes:

- `Manifests`, `LifeOf`, and `Meet` extend the §3.12 signature
- the packaged version of (a102) uses the corrected argument order
  `manifests(x, y) → Perdurant(x) ∧ Endurant(y)`, matching (a103) and the
  surrounding natural-language explanation
- the printed version of (a102), with `Endurant(x) ∧ Perdurant(y)`, is encoded
  separately as the non-packaged proposition `ax_a102_printed`

The small witness interprets:

- `Manifests`, `LifeOf`, and `Meet` as empty

This keeps the §3.13 witness minimal.

---

### ✓ Section 4 — Type Structures

Mechanized axioms:

- (a105) disjointness of types
- (a106) complete binary coverage
- (a107) binary partitioning
- (a108) categorization by specialization

Concrete witness:

`LeanUfo/UFO/Models/Model4.lean`

Consistency theorem:

```lean
consistent_4 :
  ∃ (Sig : UFOSignature4.{0,0}),
    UFOAxioms4 Sig
```

Formalization notes:

- the new predicates are added in `UFOSignature4` as signature-level
  relations over the existing UFO domain
- the concrete witness interprets each new §4 primitive extensionally by the
  right-hand side of its corresponding axiom; after unfolding, the §4
  biconditionals reduce to the intended condition on the inherited tiny model

The small witness reuses:

- `K` as the only type
- `I` as the only individual
- `I :: K` as the only instantiation fact

This establishes the joint satisfiability of the axioms through section 4
without adding extra domain objects.

---

## ✦ Structural Assumptions Made Explicit by the Lean Mechanization

During mechanization, certain structural commitments that are implicit
in the textual exposition of the paper had to be encoded as explicit axioms.

These additional axioms make precise assumptions presupposed by the
informal argumentation but not stated as standalone formal constraints.

All such assumptions are tracked here to maintain transparency between:

- conceptual ontology (paper),
- logical axiomatization,
- mechanized semantics in Lean.

### §3.2 Additional Structural Axioms

#### 1. Kind Stability (Modal Persistence)

**Intended reading in the paper:**  
Kinds are rigid and stable across accessible worlds.

**Formal axiom introduced:**
```lean
def ax_kindStable : Prop :=
  ∀ k w v,
    Kind k w →
    R w v →
    Kind k v
```

**Required for:**
- (t10) Necessary disjointness of distinct kinds  
- (t11) Non-specialization of distinct kinds  
- (t14) No type specializes two distinct kinds
- (t22) All entities that possibly instantiate a specific endurant kind are endurants
- Helper theorem kind_implies_specific_kind, every kind in the endurant branch is one of the six specific endurant kinds
- (t23) every endurant sortal belongs to one of the leaves of the taxonomy of endurant sortals
- (t24) Characterization of specific endurant sortals via specialization of a specific kind
- (t26) every endurant type belongs to one of the leaves of the taxonomy of endurant types

This allows transporting `Kind` facts along S5 accessibility.

---

#### 2. Instances of Endurant Types Are Endurants

**Intended reading in the paper:**  
If a type is an EndurantType, then its instances are endurants.

**Formal axiom introduced:**
```lean
def ax_instEndurant_of_EndurantType : Prop :=
  ∀ t x w,
    EndurantType t w →
    Inst x t w →
    Endurant x w
```

**Required for:**
- (t16) Non-sortals do not have direct instances
- Helper theorem kind_implies_specific_kind, every kind in the endurant branch is one of the six specific endurant kinds
- (t23) every endurant sortal belongs to one of the leaves of the taxonomy of endurant sortals
- (t24) Characterization of specific endurant sortals via specialization of a specific kind 
- (t26) every endurant type belongs to one of the leaves of the taxonomy of endurant types

This typing principle is implicitly used in the paragraph introducing (a21).

---

#### 3. Subtypes of Kinds Are Sortals

**Intended reading in the paper:**  
Kinds and their subkinds form the rigid sortal branch.

**Formal axiom introduced:**
```lean
def ax_sub_of_kind_is_sortal : Prop :=
  ∀ a k w,
    Sub a k w →
    Kind k w →
    Sortal a w
```

**Required for:**
- (t16), subtype case
- (t24) Characterization of specific endurant sortals via specialization of a specific kind 

---

#### 4. Upward Closure of NonSortal

**Intended reading in the paper:**  
If a non-sortal specializes another type, that supertype cannot be a sortal.

**Formal axiom introduced:**
```lean
def ax_nonSortal_upward : Prop :=
  ∀ a b w,
    NonSortal a w →
    Sub a b w →
    NonSortal b w
```

**Required for:**
- (t16), common-supertype branch  

---

### §3.10 Additional Bridge Axiom

#### 5. Qua Individuals Are Of Endurants

**Intended reading in the paper:**  
The bearer associated with a qua individual is an endurant.

**Formal axiom introduced:**
```lean
def ax_quaIndividualOf_endurant : Prop :=
  ∀ x y w,
    QuaIndividualOf x y w →
    Endurant y w
```

**Required for:**
- (t33) Every relator mediates at least two distinct endurants

This bridge axiom was needed because the paper’s proof of (t33) relies on an
implicit typing assumption that is not forced by the formal statements of
(a73)–(a80) alone.

---

## ✦ Repository Structure

```
LeanUfo/
  UFO/
    Modal/
      Basics.lean
      FirstOrder.lean
      S5.lean
    Core/
      S5_Derived.lean
      Signature3_1.lean
      Signature3_2.lean
      Signature3_3.lean
      Signature3_4.lean
      Signature3_5.lean
      Signature3_6.lean
      Signature3_7.lean
      Signature3_8.lean
      Signature3_9.lean
      Signature3_10.lean
      Signature3_11.lean
      Signature3_12.lean
      Signature3_13.lean
      Signature4.lean
      Section3_1.lean
      Section3_2.lean
      Section3_3.lean
      Section3_4.lean
      Section3_5.lean
      Section3_6.lean
      Section3_7.lean
      Section3_8.lean
      Section3_9.lean
      Section3_10.lean
      Section3_11.lean
      Section3_12.lean
      Section3_13.lean
      Section4.lean
    Models/
      Model3_1.lean
      Model3_2.lean
      Model3_3.lean
      Model3_4.lean
      Model3_5.lean
      Model3_6.lean
      Model3_7.lean
      Model3_8.lean
      Model3_9.lean
      Model3_10.lean
      Model3_11.lean
      Model3_12.lean
      Model3_13.lean
      Model4.lean
      Consistency.lean
    DSL/
      Certification.lean
      FiniteModel.lean
      Syntax.lean
      Guarantees.lean
      Examples.lean
      ConcreteExamples/
        Minimal.lean
        Company.lean
        Role.lean
        WoodenTable.lean
        SchoolRoles.lean
        FlowerPropertyChange.lean
        RedirectedWalk.lean
        ConceptEvolution.lean
    UFO.lean
  LeanUfo.lean
```

The development is fully semantic: axioms constrain models rather than forming a proof calculus.
Accordingly, each consistency checkpoint is a model-existence/joint-satisfiability
theorem.

---

## ✦ Methodology

For each subsection:

1. Encode axioms as semantic constraints.
2. Prove derived theorems.
3. Construct a small concrete witness model.
4. Establish a new semantic consistency checkpoint, i.e. a joint-satisfiability
   theorem witnessed by a concrete model.

---

## ✦ Roadmap

- Strengthen witness models where needed.
- Integrate domain ontologies (e.g., COVER for risk and value).
- Extend the Phase 1 DSL with level-aware UFO type support, so examples such as
  Section 4.5 concept evolution can distinguish ordinary individuals,
  first-order types, and higher-order types while keeping `::`, `⊑`, and
  `Categorizes` well-typed.
- Complete DSL coverage for the remaining `UFOSignature4` fields.  The current
  surface syntax does not yet provide concrete user syntax for custom
  accessibility relations, set extensions, set membership/product structure,
  tuple projections, metric/distance tables, or primitive higher-arity
  functional-dependence/component/constitution tables.
- Improve failure diagnostics so rejected DSL models report failed checks in
  user-facing world/thing names instead of exposing only the generated Lean goal.
- Add query syntax and higher-level tactics on top of certified finite models.
- Later, connect querying and custom high-level tactics with quantitative/model checking
  integrations while keeping the qualitative UFO kernel separate.

---

## ✦ Phase 1 Certified DSL Backend

The repository now contains the first finite-model backend for a Lean-based UFO model DSL.
Its central guarantee is proof-producing validation:

> if a `ufo_model ... certify` DSL command elaborates successfully, Lean has proved
> that the generated finite model satisfies the encoded UFO axioms (`UFOAxioms4`).

Invalid DSL models do not silently pass as partial artifacts. They fail
elaboration either while checking explicit derived-relation assertions or while
building one of the generated axiom certificates.

```text
LeanUfo/UFO/DSL/
  Certification.lean   -- decidability bridge for axiom packages
  FiniteModel.lean     -- finite data compiled to UFOSignature4
  Syntax.lean          -- `ufo_model ... certify` command
  Guarantees.lean      -- formal DSL pipeline guarantees
  Examples.lean        -- index for concrete DSL examples
  ConcreteExamples/
    Minimal.lean       -- smallest certified DSL model
    Company.lean       -- small company/person/organization DSL model
    Role.lean          -- two-world anti-rigid role DSL model
    WoodenTable.lean   -- minimal paper-inspired constitution example
    SchoolRoles.lean   -- minimal Section 4.2 role-change example
    FlowerPropertyChange.lean -- minimal Section 4.3 property-change example
    RedirectedWalk.lean -- minimal Section 4.4 redirected-walk example
    ConceptEvolution.lean -- documented Section 4.5 higher-order limitation
```

The user-facing command syntax is:

```lean
import LeanUfo.UFO.DSL.Syntax

open LeanUfo.UFO.DSL

ufo_model MinimalCommand : UFO where
  worlds actual
  things K I
  given actual:
    I :: K
    I : Object
    K : ObjectKind
  derive_relations
  certify
```

Here `:` asserts a unary UFO classification predicate, `::` keeps its UFO-paper
meaning of instantiation, and `⊑` asserts specialization.  Multiple
`given <world>:` blocks are accepted for modal models.  Binary relation facts
can also be written as `x Relation y`, including `Part`, `Overlap`, and
`ProperPart`.

Reflexive specialization facts are inserted automatically for every type
detected from instantiation targets.  For example, after `I :: K`, the DSL
generates the required `K ⊑ K` facts internally, so users only write
informative specializations such as `Employee ⊑ Person`.

Unary taxonomy facts are closed automatically before certification.  Users
should normally write the most specific classification they mean:

```lean
WoodPortion : QuantityKind
WoodenTableComponent : ObjectKind
Object0 : Quantity
Object1 : Object
```

The DSL compiler expands these into deterministic ancestors from the encoded
UFO taxonomy.  For example, `QuantityKind` contributes `Kind`, `Sortal`,
`Rigid`, `QuantityType`, `SubstantialType`, and `EndurantType`; `Object`
contributes `Substantial`, `Endurant`, and `ConcreteIndividual`.  The compiler
does not infer facts that require choosing between alternatives, so
`ConcreteIndividual` alone does not imply either `Endurant` or `Perdurant`.
This is only finite-data sugar: Lean still checks the expanded generated model
against the original `UFOAxioms4` definitions.

For facts that hold in every declared world, use the reserved pseudo-world
`everywhere`:

```lean
given everywhere:
  Mark : Object
  Mark :: Person
  Person : ObjectKind
```

This is syntax sugar only: the elaborator expands the block into one copy for
each declared world before building the finite tables.

Definition-like derived facts are accepted too.  Binary derived facts use the
same relation syntax, for example `Person IsDisjointWith Organization`.
Higher-arity derived facts use function-style notation, for example
`IsPartitionedInto(Person, Employee, NonEmployee)`.  These facts are checked in
the generated theorem `ModelName.assertedDerivedFacts`; they do not override
the semantics computed by `derive_relations`.

The only accepted directives in the first public DSL surface are
`derive_relations` and `certify`.

The aggregate `LeanUfo.UFO.UFO` imports the DSL backend, command syntax, and
generic guarantee theorems.  Concrete example files are kept under
`LeanUfo/UFO/DSL/ConcreteExamples/` and can be imported explicitly, or all at
once via `LeanUfo.UFO.DSL.Examples`.

The command elaborates to ordinary Lean declarations:

```lean
MinimalCommand.data      : FiniteModel4
MinimalCommand.sig       : UFOSignature4
MinimalCommand.assertedDerivedFacts : True
MinimalCommand.certified_ax1 : ax_a1 MinimalCommand.sig.toUFOSignature3_1
-- ...
MinimalCommand.certified : UFOAxioms4 MinimalCommand.sig
MinimalCommand.certifiedModel : FiniteModel4.Certified MinimalCommand.data
```

The module `LeanUfo.UFO.DSL.Guarantees` proves the generic facts behind this
pipeline.  In particular, `FiniteModel4.Certified M` is definitionally the
original `UFOAxioms4 M.toUFOSignature4` proposition, the Phase 1 compiler uses
a universal S5 frame, and core compiled predicates such as instantiation,
specialization, parthood, `Type`, and `Individual` are tied directly to the
finite tables or semantic finite definitions.

The finite backend compiles user-level names to `Fin` indices, then builds an
ordinary `UFOSignature4`.  The semantic kernel remains unchanged: the target
certificate is still the existing proposition

```lean
UFOAxioms4 generatedSignature
```

Current implementation status:

- implemented: finite model data through `UFOSignature4`;
- implemented: semantic compilation into the existing Prop-valued signature;
- implemented: semantic derivation, rather than primitive user tables, for
  `Type`, `Individual`, the definition-like predicates in §3.6, §3.7, §3.8,
  selected §3.10 predicates, and the §4 type-structure relations;
- implemented: checked explicit assertions for derived relations through
  `assertedDerivedFacts`;
- implemented: conservative unary taxonomy closure for DSL classifications;
- implemented: finite tables for user-specified mereological facts;
- implemented: the `ufo_model ... certify` command;
- implemented: proof-producing finite certificates for the concrete DSL examples
  in `LeanUfo/UFO/DSL/ConcreteExamples/`, except for `ConceptEvolution.lean`,
  which documents the higher-order MLT-style pattern needed for the paper's
  Section 4.5 case.

In this status note, "semantic derivation" means that the DSL does not store
those predicates as arbitrary user-controlled Boolean tables.  Instead, the
compiler computes their Prop-valued interpretation from smaller primitive
tables and then asks Lean to certify the original axiom package.  For example:

- `Type` is derived from possible instantiation;
- `Individual` is derived from absence of instantiation;
- §3.6 `GenericFunctionalDependence`, `IndividualFunctionalDependence`, and
  `ComponentOf` are derived from instantiation, `FunctionsAs`, and mereology;
- §3.7 `GenericConstitutionalDependence` and `Constitution` are derived from
  instantiation and `ConstitutedBy`;
- §3.8 `ExistentialDependence` and `ExistentialIndependence` are derived from
  the `Ex` table across the finite S5 frame;
- selected §3.10 predicates currently derived by the compiler are
  `ExternallyDependent`, `ExternallyDependentMode`, and `QuaIndividual`;
- §4 `IsDisjointWith`, `IsCompletelyCoveredBy`, `IsPartitionedInto`, and
  `Categorizes` are derived from their axiom right-hand sides.

The Phase 1 DSL deliberately does not yet surface all fields of
`UFOSignature4`.  In particular, it does not provide user syntax for:

- custom accessibility relations; generated models use the default universal
  S5 frame;
- finite set extensions, set membership, tuple projections, or product-subset
  constraints used by the richer quality-structure axioms;
- metric/distance tables such as `Distance`, `DistanceZero`, `DistanceSum`,
  and `DistanceGreaterEq`;
- primitive higher-arity tables for `IndividualFunctionalDependence`,
  `ComponentOf`, and `Constitution`; users can assert these as derived facts,
  but the semantic compiler computes them from lower-level relations;
- level-aware higher-order type declarations needed for the full
  concept-evolution example in Section 4.5.

Known limitation: the Phase 1 DSL has a flat `things` namespace and a single
flat `::` instantiation table.  This is enough for first-order finite witnesses
and for checking derived §4 relations such as disjointness, coverage,
partitioning, and simple categorization assertions.  It is not yet enough for a
faithful certified version of the paper's concept-evolution case, where
first-order types instantiate higher-order types while also specializing stable
base types.  The axiomatisation already contains the relevant `Categorizes`
axiom (`a108`); what is missing is level-aware DSL syntax and finite-model
metadata, for example explicit `higher_types` declarations and checks that
separate individual-to-type instantiation from type-to-higher-type
instantiation.

The current certificate is intentionally generated as an ordinary Lean proof of
`UFOAxioms4 sig`: the command first emits one named theorem per axiom field
(`certified_ax1`, `certified_ax2`, ...), then assembles the final
`certified` record from those per-axiom lemmas.  Each lemma is discharged by
unfolding the compiled finite signature, reflecting finite `Fin` quantifiers,
and simplifying over the resulting finite cases.  This gives a push-button
certificate path for DSL-generated files while keeping the trusted semantic
kernel unchanged.

One remaining engineering task is: richer diagnostics for failed finite checks
in user-facing DSL terms.  At the moment, an invalid model fails at either
`assertedDerivedFacts` or the generated certificate proof, exposing the
remaining Prop-level Lean goal.

`Part`, `Overlap`, and `ProperPart` are finite user tables. Certification is responsible for proving that the supplied tables satisfy the §3.5 axioms.

---

## ✦ Build

Requires Lean 4, Lake, and [mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake build
```

To rebuild just the DSL example collection:

```bash
lake build LeanUfo.UFO.DSL.Examples
```

---

## ✦ Status

Active research development.  
Fragment-by-fragment formalization in progress.

---

## ✦ License

Licensed under the Apache License 2.0. See the LICENSE file for details.
