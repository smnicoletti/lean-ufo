import LeanUfo.UFO.DSL.Syntax

/-! Conflicting tuple projections are rejected; identical duplicates are allowed. -/

open LeanUfo.UFO.DSL

ufo_model RejectedConflictingTupleProjection : UFO where
  worlds actual
  things Tuple First Second
  given actual:
    TupleProjection(Tuple, 0, First)
    TupleProjection(Tuple, 0, Second)
  derive_relations
  certify
