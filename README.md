# Lean UFO Formalization

> A formal, machine-checked semantic mechanization of the  
> **Unified Foundational Ontology (UFO)** in Lean 4.

---

## ✦ Overview

This repository develops a rigorous semantic formalization of the **Unified Foundational Ontology (UFO)** using the Lean 4 theorem prover.

The development proceeds fragment-by-fragment, aligned with the structure of the original UFO axiomatization.

The goal is to establish **explicit, machine-checked consistency checkpoints** for successive UFO fragments via concrete Kripke models.

---

## ✦ Logical Framework

The mechanization is based on:

- First-order modal logic **S5**
- Constant-domain (possibilist) Kripke semantics
- Equivalence accessibility relations
- Barcan and Converse Barcan principles (derivable under constant domains)

Modal operators are interpreted semantically.  
No proof calculus or completeness theory is implemented at this stage.

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

## ✦ Current Milestone  
### Subsection 3.1 — Types, Individuals, Instantiation

Mechanized axioms:

- (a1)–(a6): core constraints on Type, Individual, Instantiation, Specialization
- (a7)–(a17): taxonomic classification constraints

All axioms are encoded as **semantic constraints on Kripke models**.

---

## ✦ Consistency Checkpoint

An explicit witness model is constructed in:

`LeanUfo/UFO/Models/Model3_1.lean`

This yields:

```lean
model3_1 : UFOModel
```

and the formal consistency theorem:

```lean
consistent_3_1 : Nonempty (UFOModel.{0,0})
```

Interpretation:

> The subsection 3.1 axioms are jointly satisfiable  
> (relative to Lean's metatheory and the chosen semantics).

---

## ✦ Architecture

```
LeanUfo/
  UFO/
    Modal/
      Basics.lean        S5 Kripke semantics
      FirstOrder.lean    Constant-domain FOL layer
      Barcan.lean        Barcan + Converse Barcan
    Core/
      Signature.lean     UFO vocabulary
      Axioms.lean        UFO axioms + UFOModel structure
    Models/
      Model3_1.lean      Concrete witness for §3.1
      Consistency.lean   Consistency theorem
  LeanUfo.lean           Library root
```

The development is fully semantic:  
axioms constrain models rather than forming a deductive proof calculus.

---

## ✦ Methodology

For each subsection of the reference paper:

1. Encode axioms as semantic constraints.
2. Prove derived theorems stated in the paper.
3. Construct an explicit witness model.
4. Establish a new consistency checkpoint.

---

## ✦ Roadmap

Planned progression:

- Extend mechanization to subsequent UFO subsections.
- Strengthen witness models where necessary.
- Mechanize domain ontologies (e.g., COVER, for Risk and Value).
- Develop Lean-based reasoning layers for domain modeling and risk analysis.

---

## ✦ Build

Requires Lean 4 and Lake.

```
lake build
```

---

## ✦ Status

Active research development.  
Fragment-by-fragment formalization in progress. Currently working on:

### ✦ Subsection 3.2 — Rigidity Taxonomy

This subsection formalizes the rigidity-based taxonomy of endurant types (a18–a33) and proves:

- (t5) Rigidity trichotomy  
- (t6) Pairwise disjointness of rigidity classes  
- (t7)–(t8) Specialization constraints  
- (t9)–(t16) Structural taxonomy properties  
- (t17) Pairwise disjointness of leaf categories  
- (t18) Exhaustiveness of the leaf partition  

All theorems are proved semantically over S5 Kripke models.

---

## ✦ Structural Assumptions Made Explicit by the Lean Mechanization

Following, we track additional axioms that we found needed to prove theorems as stated in the reference paper. These axioms make explicit structural commitments that are presupposed in the textual exposition but not stated as formal axioms.

All such assumptions are tracked here to maintain transparency between:

- conceptual ontology (paper),
- logical axiomatization,
- mechanized semantics in Lean.

### ✦ §3.2

While mechanizing §3.2, several structural commitments that are implicit in the paper had to be encoded as explicit axioms.

The prose assumes a well-formed ontological hierarchy; Lean requires these assumptions to be formalized.

Below we list the additional axioms introduced, together with the proofs that depend on them.

---

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


