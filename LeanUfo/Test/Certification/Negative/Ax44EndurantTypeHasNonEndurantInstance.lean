import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure (a44) fixture.

`T` is an endurant quality type, but its instance `Q` is only classified as an
abstract quale. The endurant-type clause of (a44) rejects that instance.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx44EndurantTypeHasNonEndurantInstance : UFO where
  worlds actual
  things S T Q
  given actual:
    QualityType(T)
    Rigid(T)
    NonSortal(T)
    Category(T)
    AssociatedWith(S, T)
    Set(S)
    AbstractIndividual(S)
    Quale(Q)
    AbstractIndividual(Q)
    Q :: T
    MemberOf(Q, S)
  derive_relations
  certify
