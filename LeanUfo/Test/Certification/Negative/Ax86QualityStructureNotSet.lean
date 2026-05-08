import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax86 fixture candidate.

`S` is a quality structure because it is uniquely associated with quality kind
`QT`, but `S` is not asserted as a set.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx86QualityStructureNotSet : UFO where
  worlds actual
  things S QT Q
  given actual:
    QualityKind(QT)
    AbstractIndividual(S)
    ConcreteIndividual(Q)
    Endurant(Q)
    Moment(Q)
    IntrinsicMoment(Q)
    AssociatedWith(S, QT)
    Q :: QT
  derive_relations
  certify
