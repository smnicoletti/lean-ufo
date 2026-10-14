import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax101 fixture.

`V` is made a genuine quale by putting it in the unique quality structure `S`.
No distance value is supplied for `V` to itself, so the model reaches the
distance-totality obligation in `certified_ax101`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx101QualesWithoutDistance : UFO where
  worlds actual
  things T Q B S V
  given actual:
    QualityKind(T)
    QualityType(T)
    Rigid(T)
    Sortal(T)

    ConcreteIndividual(Q)
    Endurant(Q)
    Moment(Q)
    IntrinsicMoment(Q)
    Q :: T

    ConcreteIndividual(B)
    Perdurant(B)
    InheresIn(Q, B)

    QualityDimension(S)
    Set(S)
    AssociatedWith(S, T)
    MemberOf(V, S)
    Quale(V)
    AbstractIndividual(V)

    HasValue(Q, V)

  derive_relations
  certify
