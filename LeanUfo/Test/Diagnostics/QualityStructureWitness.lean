import LeanUfo.UFO.DSL.Syntax

/-!
# An ax87 counterexample with one valid quale

`S` is a quality structure because it has exactly one associated quality type.
`V` belongs to `S`, while `Missing` belongs to no structure. Certification must
fail at ax87, and the diagnostic assignment must select `Missing`, never `V`.
-/

open LeanUfo.UFO.DSL

ufo_model QualityWitness : UFO where
  worlds actual
  things S QT Q B V Missing
  given actual:
    QualityKind(QT)
    Set(S)
    ConcreteIndividual(Q)
    ConcreteIndividual(B)
    Perdurant(B)
    Endurant(Q)
    Moment(Q)
    IntrinsicMoment(Q)
    InheresIn(Q, B)
    AssociatedWith(S, QT)
    Q :: QT
    Quale(V)
    Quale(Missing)
    MemberOf(V, S)
  derive_relations
  certify
