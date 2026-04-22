import LeanUfo.UFO.Core.Signature3_6

universe u v

/--
Extension of `UFOSignature3_6` with the §3.7
constitution predicates.

We use representative names for the paper's symbols:
- `Ex` for `ex`
- `ConstitutedBy` for `constitutedBy`
- `GenericConstitutionalDependence` for `GCD`
- `Constitution` for `Constitution`
-/
structure UFOSignature3_7 extends UFOSignature3_6 where

  Ex :
    Thing → F.World → Prop

  ConstitutedBy :
    Thing → Thing → F.World → Prop

  GenericConstitutionalDependence :
    Thing → Thing → F.World → Prop

  Constitution :
    Thing → Thing → Thing → Thing → F.World → Prop
