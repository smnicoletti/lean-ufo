import LeanUfo.UFO.Modal.Basics

universe u v

/--
A semantic signature for (a fragment of) UFO over S5 possible-world semantics.

This bundles:
- `F`      : an S5 Kripke frame (worlds + accessibility),
- `Entity` : the (constant) domain of quantification,
- `Type_`  : world-indexed predicate identifying types,
- `Inst`   : world-indexed instantiation relation.

Semantic reading (with `Sig : UFOSignature`):

  Sig.Type_ x w    ≈  "x is a Type at world w"
  Sig.Inst  a t w  ≈  "a instantiates t at world w"

We introduce notation `a :: t` for `Sig.Inst a t`, and since `Inst` is world-indexed,
the typical usage is:

  (a :: t) w
-/
structure UFOSignature where
  F       : S5Frame
  Entity  : Type v
  Type_   : Entity → F.World → Prop
  Inst    : Entity → Entity → F.World → Prop

namespace UFOSignature

/-- Infix notation for instantiation: `a :: t` means `Inst a t`. -/
infix:50 " :: " => UFOSignature.Inst

end UFOSignature
