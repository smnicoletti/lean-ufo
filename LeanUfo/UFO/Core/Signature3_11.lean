import LeanUfo.UFO.Core.Signature3_10

universe u v

/--
Extension of `UFOSignature3_10` with the §3.11
characterization predicate.
-/
structure UFOSignature3_11 extends UFOSignature3_10 where

  Characterization :
    Thing → Thing → F.World → Prop
