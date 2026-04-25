import LeanUfo.UFO.DSL.Syntax

/-
Paper example: minimal school-role witness

This file captures a minimal core of Section 4.2, where people contingently
play school roles.  The full paper model also includes students, schools,
classes, courses, and relators such as Employment and SchoolEnrollment.  This
finite witness keeps only the teacher-replacement pattern that the current DSL
can certify quickly:

* Potter is a teacher before the break and not after it.
* Bumblebee is not a teacher before the break and is a teacher after it.
-/

open LeanUfo.UFO.DSL

ufo_model SchoolRolesExample : UFO where
  worlds beforeBreak afterBreak
  things Person Teacher Potter Bumblebee

  given everywhere:
    Person : ObjectKind

    Teacher : Role
    Teacher : ObjectType
    Teacher ⊑ Person

    Potter : Object
    Potter :: Person

    Bumblebee : Object
    Bumblebee :: Person

  given beforeBreak:
    Potter :: Teacher

  given afterBreak:
    Bumblebee :: Teacher

  derive_relations
  certify
