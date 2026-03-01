# Lean UFO Formalization

> A formal, machine-checked semantic mechanization of the  
> **Unified Foundational Ontology (UFO)** in Lean 4.

---

## ✦ Overview

This repository develops a rigorous semantic formalization of the **Unified Foundational Ontology (UFO)** using the Lean 4 theorem prover.

The development proceeds fragment-by-fragment, aligned with the structure of the original UFO axiomatization (see below).

The goal is to establish **explicit, machine-checked consistency checkpoints** for successive UFO fragments via concrete Kripke models.

Each subsection:

- defines a semantic signature,
- packages its axioms as a Lean typeclass,
- proves the stated theorems semantically,
- constructs a small concrete witness model,
- establishes a formal consistency theorem.

---

## ✦ Logical Framework

The mechanization is based on:

- First-order modal logic **S5**
- Constant-domain (possibilist) Kripke semantics
- Equivalence accessibility relations
- Barcan and Converse Barcan principles (derivable under constant domains)

Modal operators are interpreted semantically. No proof calculus or completeness theory is implemented at this stage.

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

### Consistency Checkpoints

For each subsection:

```lean
theorem consistent_3_X :
  ∃ (Sig : UFOSignature3_X.{0,0}),
    UFOAxioms3_X Sig
```

This establishes joint satisfiability of the axioms
(relative to Lean’s metatheory and the chosen S5 semantics).

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

## ✦ Repository Structure

```
LeanUfo/
  UFO/
    Modal/
      Basics.lean
      FirstOrder.lean
      Barcan.lean
    Core/
      Signature3_1.lean
      Signature3_2.lean
      Signature3_3.lean
      Section3_1.lean
      Section3_2.lean
      Section3_3.lean
    Models/
      Model3_1.lean
      Model3_2.lean
      Model3_3.lean
      Consistency.lean
    UFO.lean
  LeanUfo.lean
```

The development is fully semantic: axioms constrain models rather than forming a proof calculus.

---

## ✦ Methodology

For each subsection:

1. Encode axioms as semantic constraints.
2. Prove derived theorems.
3. Construct a small concrete witness model.
4. Establish a new consistency checkpoint.

---

## ✦ Roadmap

- Extend mechanization to subsequent UFO subsections.
- Strengthen witness models where needed.
- Integrate domain ontologies (e.g., COVER for risk and value).
- Develop Lean-based DSL layers for scenario modeling and risk reasoning.

---

## ✦ Build

Requires Lean 4 and Lake.

```bash
lake build
```

---

## ✦ Status

Active research development.  
Fragment-by-fragment formalization in progress.

---

## ✦ License

Licensed under the Apache License 2.0. See the LICENSE file for details.