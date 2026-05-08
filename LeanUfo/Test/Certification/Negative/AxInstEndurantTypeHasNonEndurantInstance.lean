import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure `ax_instEndurant` fixture.

`T` is an endurant quality type, but its instance `Q` is only classified as an
abstract quale.  This was found while building a quality-structure scaffold.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAxInstEndurantTypeHasNonEndurantInstance : UFO where
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
