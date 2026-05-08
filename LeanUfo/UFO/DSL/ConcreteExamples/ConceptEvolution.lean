import LeanUfo.UFO.DSL.Syntax

/-
Paper example: concept evolution

Section 4.5 uses marriage to illustrate anticipated concept evolution.  Unlike
the other Section 4 examples, the central pattern is higher-order:
a type such as ConjugalRelationshipType has first-order types as instances,
and those instances specialize a stable base type such as ConjugalRelationship.

This is a limitation of the finite DSL/backend, not a claim that the
axiomatisation cannot express the pattern.  The encoded UFO axiom package
already contains axiom a108
for `Categorizes`.  What is missing is a level-aware surface and finite model
layer that distinguishes ordinary individual-to-type instantiation from
type-to-higher-type instantiation.

The DSL still has one flat `things` namespace and one flat `::` table.
If we force `MonogamousHeterosexualMarriage :: ConjugalRelationshipType` into
that first-order layer while also treating `MonogamousHeterosexualMarriage` as
a normal kind/subkind, the generated model either conflicts with the existing
kind/subkind constraints or no longer represents the paper's higher-order
meaning.  A faithful certified version should therefore wait for explicit DSL
support for higher-order declarations, such as `higher_types`, and level-aware
checks around `::` and `Categorizes`.

The intended surface shape is:

  ufo_model ConceptEvolutionExample : UFO where
    worlds actual
    things
      ConjugalRelationshipType
      ConjugalRelationship
      MonogamousHeterosexualMarriage

    given actual:
      MonogamousHeterosexualMarriage :: ConjugalRelationshipType
      MonogamousHeterosexualMarriage ⊑ ConjugalRelationship
      Categorizes(ConjugalRelationshipType, ConjugalRelationship)
    derive_relations
    certify

Until level-aware declarations are added, this file documents the intended
surface shape rather than emitting a checked model.
-/

open LeanUfo.UFO.DSL
