import LeanUfo.UFO.Core.Signature3_5

universe u v

/--
Extension of `UFOSignature3_5` with the §3.6
composition predicates.

We use representative names for the paper's symbols:
- `FunctionsAs` for `F`
- `GenericFunctionalDependence` for `gfd`
- `IndividualFunctionalDependence` for `ifd`
- `ComponentOf` for `componentOf`
-/
structure UFOSignature3_6 extends UFOSignature3_5 where

  FunctionsAs : Thing → Thing → F.World → Prop

  GenericFunctionalDependence :
    Thing → Thing → F.World → Prop

  IndividualFunctionalDependence :
    Thing → Thing → Thing → Thing → F.World → Prop

  ComponentOf :
    Thing → Thing → Thing → Thing → F.World → Prop
