import LeanUfo.UFO.DSL.Syntax

/-
Minimal certified DSL model

This is the smallest concrete UFO DSL example: one individual I, one kind K,
and a single world.  It is meant as the first smoke test for the
ufo_model ... certify pipeline.

The model states only the most specific unary classifications.  The DSL
compiler expands Object to Substantial, Endurant, and ConcreteIndividual, and
expands ObjectKind to its deterministic type-taxonomy ancestors.

Reflexive specialization for K is inserted automatically because K is the
target of an instantiation fact.
-/

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
