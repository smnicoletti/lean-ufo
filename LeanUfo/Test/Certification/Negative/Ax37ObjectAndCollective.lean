import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax37 fixture.

`I` is classified as both object and collective, the first disjointness axiom
inside the substantial taxonomy.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx37ObjectAndCollective : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    Object(I)
    Collective(I)
    I :: K
  derive_relations
  certify
