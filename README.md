# Lean UFO Formalization

A mechanization of the Unified Foundational Ontology (UFO) in the Lean 4 theorem prover.

---

## Overview

This project develops a formal, machine-checked semantic foundation for the Unified Foundational Ontology (UFO) using Lean 4.

The development follows a model-theoretic approach based on first-order modal logic S5 with constant domains (possibilist semantics). UFO axioms are encoded as constraints on Kripke models.

The long-term objective is to:

- Establish relative consistency of core UFO axioms.
- Provide a formally verified foundation for domain ontologies (e.g., COVER).
- Enable formal reasoning about risk and domain structures within Lean.

---

## Logical Foundations

The formalization is based on:

- **First-order modal logic S5**
- **Constant-domain (possibilist) Kripke semantics**
- Equivalence accessibility relations
- Barcan and Converse Barcan principles (derivable under constant domains)

Modal operators are interpreted semantically; no proof calculus or completeness proofs are currently implemented.

Lean Theorem Prover:

- Lean 4  
  https://leanprover.github.io/

---

## UFO Source Material

This mechanization follows the axiomatization of UFO as presented in:

- Guizzardi et al. (2022), UFO: Unified Foundational Ontology, Applied Ontology 17(2): 167–210. https://doi.org/10.3233/AO-210256

@article{guizzardi2022ufo,
  author  = {Guizzardi, Giancarlo and Benevides, Alessander Botti and 
             Fonseca, Claudenir M. and Porello, Daniele and 
             Almeida, João Paulo A. and Sales, Tiago Prince},
  title   = {UFO: Unified Foundational Ontology},
  journal = {Applied Ontology},
  volume  = {17},
  number  = {2},
  pages   = {167--210},
  year    = {2022},
  doi     = {10.3233/AO-210256}
}

The current implementation encodes:

- Axioms (a1)–(a4)
- Taxonomy constraints (t1)–(t2)

as semantic constraints on models.

---

## Current Status

Implemented:

- S5 modal kernel
- Constant-domain first-order layer
- Barcan and Converse Barcan theorems
- UFO semantic signature
- Core UFO axioms:
  - (a1) Type characterization
  - (a2) Individual characterization
  - (a3) Instantiation typing constraint
  - (a4) Instantiation chain restriction
  - (t1) Completeness of Thing partition
  - (t2) Disjointness of Type and Individual
- Bundled `UFOModel` structure

The development is fully semantic: axioms are treated as constraints on Kripke models for now.

---

## Repository Structure

LeanUfo/
  UFO/
    Modal/          — S5 and first-order modal semantics
    Core/
      Signature     — UFO vocabulary (Thing, Type, Individual, Instantiation)
      Axioms        — Core UFO axioms and UFOModel structure

---

## Research Roadmap

Planned steps:

1. Prove elementary consequences of the core axioms.
2. Construct explicit models to demonstrate relative consistency.
3. Extend the formalization to additional UFO fragments.
4. Mechanize domain-specific ontologies (e.g., COVER).
5. Develop a Lean-based DSL for formal risk reasoning.

---

## Build Instructions

Requires Lean 4 and Lake.

Run:

lake build

---

## Status

This is an ongoing research project.
The formalization is under active development.