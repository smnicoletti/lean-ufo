import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax91 fixture.

`QT` is a quality type but no quality structure is associated with it.

`Q` has an explicit perdurant bearer so the fixture reaches ax91 instead of
failing earlier at the ultimate-bearer axioms for moments.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx91QualityTypeWithoutStructure : UFO where
  worlds actual
  things QT Q B
  given actual:
    QualityKind(QT)
    ConcreteIndividual(Q)
    Endurant(Q)
    Moment(Q)
    IntrinsicMoment(Q)
    ConcreteIndividual(B)
    Perdurant(B)
    InheresIn(Q, B)
    Q :: QT
  derive_relations
  certify
