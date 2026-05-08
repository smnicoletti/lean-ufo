import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax10 fixture.

`Bobs_Enrollment` is introduced only in the future world. Since nothing
instantiates it, the finite semantics treats it as an individual at every
world, but it is concrete/abstract-classified only in `future`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx10FutureOnlyIndividualClassification : UFO where
  worlds current future
  things Enrollment Bobs_Enrollment

  given everywhere:
    ObjectKind(Enrollment)
  given future:
    Object(Bobs_Enrollment)
    Bobs_Enrollment :: Enrollment

  derive_relations
  certify

