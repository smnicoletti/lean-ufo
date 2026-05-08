import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure moment/relator fixture.

The relator is a moment, but no inherence fact supplies an ultimate bearer.  The
current finite encoding can still satisfy ax68 for this tiny table and reaches
the first relator-specific founded-by obligation at `certified_ax77`.  This
fixture remains close to the ax68/ultimate-bearer area while the per-axiom pass
backfills a stricter ax68 counterexample.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx77RelatorFoundedBy : UFO where
  worlds actual
  things RelationKind Relator1

  given actual:
    RelatorKind(RelationKind)
    Relator(Relator1)
    Moment(Relator1)
    Relator1 :: RelationKind

  derive_relations
  certify
