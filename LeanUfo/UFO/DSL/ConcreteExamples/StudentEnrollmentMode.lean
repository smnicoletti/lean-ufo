import LeanUfo.UFO.DSL.Syntax

/-
Student-enrollment mode example.

This single-world example treats Bob's enrollment as a mode inhering in Bob.
-/

open LeanUfo.UFO.DSL

ufo_model StudentEnrollmentModeExample : UFO where
  worlds current
  things Person Bob Enrollment Bobs_Enrollment

  given everywhere:
    ObjectKind(Person)

    Object(Bob)
    Bob :: Person

    ModeKind(Enrollment)

    Mode(Bobs_Enrollment)
    Bobs_Enrollment :: Enrollment

    InheresIn(Bobs_Enrollment, Bob)

  derive_relations
  certify
