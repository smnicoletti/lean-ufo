import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure moment/relator fixture.

The relator is a moment with an explicit non-moment bearer, so it passes the
ultimate-bearer obligation before failing at the relator-specific founded-by
obligation in `certified_ax77`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx77RelatorFoundedBy : UFO where
  worlds actual
  things RelationKind ObjectKind1 Relator1 Bearer

  given actual:
    RelatorKind(RelationKind)
    ObjectKind(ObjectKind1)
    Object(Bearer)
    Relator(Relator1)
    Moment(Relator1)
    Bearer :: ObjectKind1
    Relator1 :: RelationKind
    InheresIn(Relator1, Bearer)

  derive_relations
  certify
