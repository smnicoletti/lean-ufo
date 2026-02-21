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
Fragment-by-fragment formalization in progress.