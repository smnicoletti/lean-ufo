import LeanUfo.UFO.Core.Signature3_12

universe u v

/--
Extension of `UFOSignature3_12` with the §3.13
endurant/perdurant connection predicates.

-/
structure UFOSignature3_13 extends UFOSignature3_12 where

  Manifests :
    Thing → Thing → F.World → Prop

  LifeOf :
    Thing → Thing → F.World → Prop

  Meet :
    Thing → Thing → F.World → Prop
