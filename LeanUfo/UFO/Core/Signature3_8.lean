import LeanUfo.UFO.Core.Signature3_7

universe u v

/--
Extension of `UFOSignature3_7` with the §3.8
existential-dependence predicates.

We use representative names for the paper's symbols:
- `ExistentialDependence` for `ed`
- `ExistentialIndependence` for `ind`
-/
structure UFOSignature3_8 extends UFOSignature3_7 where

  ExistentialDependence :
    Thing → Thing → F.World → Prop

  ExistentialIndependence :
    Thing → Thing → F.World → Prop
