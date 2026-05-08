import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax86 fixture candidate.

`S` is a quality structure because it is uniquely associated with quality kind
`QT`, but `S` is not asserted as a set.

`Q` has an explicit perdurant bearer so the fixture reaches ax86 instead of
failing earlier at the ultimate-bearer axioms for moments.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx86QualityStructureNotSet : UFO where
  worlds actual
  things S QT Q B
  given actual:
    QualityKind(QT)
    AbstractIndividual(S)
    ConcreteIndividual(Q)
    ConcreteIndividual(B)
    Perdurant(B)
    Endurant(Q)
    Moment(Q)
    IntrinsicMoment(Q)
    InheresIn(Q, B)
    AssociatedWith(S, QT)
    Q :: QT
  derive_relations
  certify
