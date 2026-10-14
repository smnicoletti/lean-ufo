import LeanUfo.UFO.Core.Signature3_8

universe u v

/--
Extension of `UFOSignature3_8` with the §3.9
inherence relation.

We use representative names for the paper's symbols:
- `InheresIn` for `inheresIn`
-/
structure UFOSignature3_9 extends UFOSignature3_8 where

  InheresIn :
    Thing → Thing → F.World → Prop
