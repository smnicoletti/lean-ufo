import LeanUfo.UFO.DSL.Syntax

/-!
Paper example: a walk mode changes phase

Section 4.4 of Guizzardi et al. (2022) explains the redirected walk through a
mode inhering in the walker. Here PaulsWalk inheres in Paul in both worlds and
changes from OngoingWalk to RedirectedWalk. The partition assertion checks
that the two phases are disjoint and cover Walk at every world.

This finite example omits destinations, intentions, external dependence, and
the paper's arrival relation and full phase hierarchy.
-/

open LeanUfo.UFO.DSL

ufo_model RedirectedWalkExample : UFO where
  worlds beforeTurn afterTurn
  things Person Walk OngoingWalk RedirectedWalk Paul PaulsWalk

  given everywhere:
    ObjectKind(Person)
    Object(Paul)
    Paul :: Person
    ModeKind(Walk)
    Mode(PaulsWalk)
    PaulsWalk :: Walk
    InheresIn(PaulsWalk, Paul)
    Characterization(Person, Walk)
    Phase(OngoingWalk)
    ModeType(OngoingWalk)
    OngoingWalk ⊑ Walk
    Phase(RedirectedWalk)
    ModeType(RedirectedWalk)
    RedirectedWalk ⊑ Walk
    IsPartitionedInto(Walk, OngoingWalk, RedirectedWalk)
    Ex(Paul)
    Ex(PaulsWalk)

  given beforeTurn:
    PaulsWalk :: OngoingWalk

  given afterTurn:
    PaulsWalk :: RedirectedWalk

  derive_relations
  certify
