import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax85 fixture.

`X` is both a quale and a set-like abstract individual.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx85QualeAndSet : UFO where
  worlds actual
  things X
  given actual:
    Quale(X)
    Set(X)
    AbstractIndividual(X)
  derive_relations
  certify
