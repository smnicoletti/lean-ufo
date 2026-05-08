import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax91 fixture.

`QT` is a quality type but no quality structure is associated with it.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx91QualityTypeWithoutStructure : UFO where
  worlds actual
  things QT Q
  given actual:
    QualityKind(QT)
    ConcreteIndividual(Q)
    Endurant(Q)
    Moment(Q)
    IntrinsicMoment(Q)
    Q :: QT
  derive_relations
  certify
