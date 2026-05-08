import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax19 candidate.

`K` is a rigid object kind with a necessary instance, but it is also asserted as
anti-rigid.  The expected useful first failure is the anti-rigidity definition.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx19AntiRigidRigidType : UFO where
  worlds actual future
  things K I
  given everywhere:
    ObjectKind(K)
    Object(I)
    I :: K
    AntiRigid(K)
  derive_relations
  certify
