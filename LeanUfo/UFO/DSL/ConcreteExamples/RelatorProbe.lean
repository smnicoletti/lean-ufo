import LeanUfo.UFO.DSL.Syntax

open LeanUfo.UFO.DSL

/-!
This file records the minimal relator-boundary probe used during the §3.10
axiomatic analysis.

This is useful as source documentation for the computed
`ExternallyDependentMode` pattern and the modal `Ex` witnesses it requires:
`actual` witnesses dependence of `C1` on `UT`, while `markOnly` and `utOnly`
witness independence between `Mark` and `UT`.
-/

/-
ufo_model RelatorProbe : UFO where
worlds actual markOnly utOnly
things Person Commitment Mark UT SigningEvent C1

given everywhere:
   Object(Mark)
   Mark :: Person

   AbstractIndividual(UT)

   Perdurant(SigningEvent)

   Mode(C1)
   C1 :: Commitment

   ObjectKind(Person)
   ModeKind(Commitment)

   InheresIn(C1,Mark)
   FoundedBy(C1,SigningEvent)
   QuaIndividualOf(C1,Mark)

given actual:
-- Derived assertions: these are checked against computed semantics.
-- They need the modal Ex variation below so C1 can be externally dependent
-- on UT while inhering in Mark.
   ExternallyDependentMode(C1)
   ExternallyDependent(C1,UT)

-- Additional needed facts to pass ExternallyDependentMode checks.
-- `actual` witnesses existential dependence of C1 on UT.
-- `markOnly` and `utOnly` witness independence between Mark and UT.
   Ex(Mark)
   Ex(UT)
   Ex(C1)

given markOnly:
   Ex(Mark)

given utOnly:
   Ex(UT)

derive_relations
certify
-/
