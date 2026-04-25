import LeanUfo.UFO.DSL.Syntax

/-
Paper example: minimal redirected-walk witness

Section 4.4 argues that the redirected-walk case is not a genuine change of an
event.  What changes is the underlying endurant focus: the walk-related mode or
state of the person.  The full paper model uses externally dependent modes,
destinations, and a material relation arrivedAt.  This small certified witness
keeps the endurant-change pattern using phases of Person.

Paul is a Person in both worlds.  Before the turn, Paul is in the OngoingWalker
phase; after the turn, Paul is in the RedirectedWalker phase.
-/

open LeanUfo.UFO.DSL

ufo_model RedirectedWalkExample : UFO where
  worlds beforeTurn afterTurn
  things Person OngoingWalker RedirectedWalker Paul

  given everywhere:
    Person : ObjectKind

    OngoingWalker : Phase
    OngoingWalker : ObjectType
    OngoingWalker ⊑ Person

    RedirectedWalker : Phase
    RedirectedWalker : ObjectType
    RedirectedWalker ⊑ Person

    Paul : Object
    Paul :: Person

    IsPartitionedInto(Person, OngoingWalker, RedirectedWalker)

  given beforeTurn:
    Paul :: OngoingWalker

  given afterTurn:
    Paul :: RedirectedWalker

  derive_relations
  certify
