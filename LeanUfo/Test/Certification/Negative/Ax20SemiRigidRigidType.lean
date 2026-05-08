import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax20 candidate.

`K` is a rigid object kind, but it is also asserted as semi-rigid.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx20SemiRigidRigidType : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    Object(I)
    I :: K
    SemiRigid(K)
  derive_relations
  certify
