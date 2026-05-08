import LeanUfo.UFO.DSL.Syntax

/-
Natural goal-as-mode example.

This records a modeler-facing sketch where the goal of winning all grants is a
mode inhering in Stefano.

The model is intentionally not imported by `LeanUfo.UFO.DSL.Examples` yet.  In
the current generated certificate, this natural surface shape stops at ax73
with an unclassified generated-proof/search failure rather than a confirmed
semantic counterexample.
-/

open LeanUfo.UFO.DSL

ufo_model FailedGrantGoalExample : UFO where
  worlds current
  things Goal WinAllGrants Person Stefano

  given everywhere:
    ObjectKind(Person)

    Object(Stefano)
    Stefano :: Person

    ModeKind(Goal)

    Mode(WinAllGrants)
    WinAllGrants :: Goal

    InheresIn(WinAllGrants, Stefano)

  derive_relations
  certify
