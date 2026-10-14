import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax23 fixture.

`M` is classified as phase-mixin and role-mixin.  The first useful failure is
earlier than their disjointness: the inherited sortal obligation cannot find a
kind covering `M`'s possible instance.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx23MixinSortalWithoutKind : UFO where
  worlds actual future
  things K M I
  given everywhere:
    ObjectKind(K)
    ObjectType(M)
    PhaseMixin(M)
    RoleMixin(M)
    M ⊑ K
    Object(I)
    I :: K
  given actual:
    I :: M
  derive_relations
  certify
