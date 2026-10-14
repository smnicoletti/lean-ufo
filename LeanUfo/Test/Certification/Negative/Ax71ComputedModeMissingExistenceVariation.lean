import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax71 fixture.

`M` is a mode founded by a perdurant, but the checker computes
`ExternallyDependentMode` from modal `Ex` variation and inherence. With only one
world and no existence variation, no thing can witness the computed
external-dependence predicate.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx71ComputedModeMissingExistenceVariation : UFO where
  worlds actual
  things ModeKind1 ObjectKind1 M B D F

  given actual:
    ModeKind(ModeKind1)
    ObjectKind(ObjectKind1)
    Mode(M)
    Object(B)
    Object(D)
    Perdurant(F)
    M :: ModeKind1
    B :: ObjectKind1
    D :: ObjectKind1
    InheresIn(M, B)
    FoundedBy(M, F)

  derive_relations
  certify
