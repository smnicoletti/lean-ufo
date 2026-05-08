import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax60 fixture.

`X` is a perdurant constituted by `Y` at `actual`, and `X` exists at `future`,
but the constitution fact is not present at `future`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx60PerdurantConstitutionNecessity : UFO where
  worlds actual future
  things X Y
  given actual:
    Perdurant(X)
    Perdurant(Y)
    ConstitutedBy(X, Y)
  given future:
    Perdurant(X)
    Perdurant(Y)
    Ex(X)
  derive_relations
  certify
