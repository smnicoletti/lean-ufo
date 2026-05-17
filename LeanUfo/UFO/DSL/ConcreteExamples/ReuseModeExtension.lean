import LeanUfo.UFO.DSL.Syntax

/-!
# Reuse mode extension example

This example starts with Bob as a person and then extends the model with a
student-enrollment mode inhering in Bob.  It is intentionally single-world:
the point is to show extension and certificate reuse around an inherence fact,
not modal role change.
-/

open LeanUfo.UFO.DSL

ufo_model PersonBearerBase : UFO where
  worlds current
  things Person Bob

  given everywhere:
    ObjectKind(Person)
    Object(Bob)
    Bob :: Person

  derive_relations
  certify

export_certificate PersonBearerBase

ufo_model PersonWithEnrollmentMode : UFO extends PersonBearerBase : UFO where
  things Enrollment Bobs_Enrollment

  given everywhere:
    ModeKind(Enrollment)
    Mode(Bobs_Enrollment)
    Bobs_Enrollment :: Enrollment
    InheresIn(Bobs_Enrollment, Bob)

  derive_relations
  certify

export_certificate PersonWithEnrollmentMode

ufo_model PersonWithEnrollmentModeFresh : UFO extends PersonBearerBase : UFO where
  things Enrollment Bobs_Enrollment

  given everywhere:
    ModeKind(Enrollment)
    Mode(Bobs_Enrollment)
    Bobs_Enrollment :: Enrollment
    InheresIn(Bobs_Enrollment, Bob)

  derive_relations
  certify_fresh
