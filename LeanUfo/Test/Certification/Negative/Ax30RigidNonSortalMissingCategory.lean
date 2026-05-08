import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax30 fixture.

`T` is a rigid non-sortal quality type, but it is not classified as a category.
This was found while trying to isolate a later quality-domain axiom.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx30RigidNonSortalMissingCategory : UFO where
  worlds actual
  things S T M
  given actual:
    QualityType(T)
    Rigid(T)
    NonSortal(T)
    AssociatedWith(S, T)
    QualityDomain(S)
    QualityDimension(S)
    Set(S)
    AbstractIndividual(S)
    Quale(M)
    AbstractIndividual(M)
    M :: T
    MemberOf(M, S)
  derive_relations
  certify
