import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax103 fixture.

`LifeOf(P,E)` is asserted with the right endpoint types, but no manifestation
overlap facts make the defining biconditional true.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx103LifeOfWithoutManifestationOverlap : UFO where
  worlds actual
  things K P E
  given actual:
    ObjectKind(K)
    Perdurant(P)
    Object(E)
    E :: K
    LifeOf(P, E)
  derive_relations
  certify
