import LeanUfo.UFO.DSL.Syntax

/-!
Natural goal-as-mode example.

The goal of winning all grants is represented as a mode inhering in Stefano.
-/

open LeanUfo.UFO.DSL

ufo_model GrantGoalExample : UFO where
  worlds current
  things Goal WinAllGrants Person Stefano

  given current:
    ObjectKind(Person)
    Object(Stefano)
    Stefano :: Person
    ModeKind(Goal)
    Mode(WinAllGrants)
    WinAllGrants :: Goal
    InheresIn(WinAllGrants, Stefano)

  derive_relations
  certify
