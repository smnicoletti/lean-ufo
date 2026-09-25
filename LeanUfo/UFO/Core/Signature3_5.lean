import LeanUfo.UFO.Core.Signature3_4

universe u v

/--
Extension of `UFOSignature3_4` with the §3.5
mereological predicates.

We use representative names for the paper's symbols:
- `Part` for `P`
- `Overlap` for `O`
- `ProperPart` for `PP`
-/
structure UFOSignature3_5 extends UFOSignature3_4 where

  Part       : Thing → Thing → F.World → Prop
  Overlap    : Thing → Thing → F.World → Prop
  ProperPart : Thing → Thing → F.World → Prop
