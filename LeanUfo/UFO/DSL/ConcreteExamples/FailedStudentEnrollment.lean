import LeanUfo.UFO.DSL.Syntax

/-
Negative diagnostic example: future-only classification of an individual.

This is the minimized failure extracted from an incomplete student-enrollment
scenario.  `Bobs_Enrollment` is introduced only in the future world, but the
compiled semantics derives `Individual(Bobs_Enrollment)` from the fact that
nothing instantiates it.  That individual/type status is modal, so ax10 requires
the enrollment object to be classified as concrete or abstract at every world.

The intended fix is to make the individual classification stable, e.g. declare
`Bobs_Enrollment : Object` everywhere and use existence facts such as `Ex` to
represent world-dependent existence.
-/

open LeanUfo.UFO.DSL

ufo_model StudentEnrollment : UFO where
  worlds current future
  things Enrollment Bobs_Enrollment

  given everywhere:
    Enrollment : ObjectKind

  given future:
    Bobs_Enrollment : Object
    Bobs_Enrollment :: Enrollment

  derive_relations
  certify
