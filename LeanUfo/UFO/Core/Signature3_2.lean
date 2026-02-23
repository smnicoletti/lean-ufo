import LeanUfo.UFO.Core.Signature3_1

universe u

structure UFOSignature3_2 extends UFOSignature3_1 where
  Rigid          : Thing → F.World → Prop
  AntiRigid      : Thing → F.World → Prop
  SemiRigid      : Thing → F.World → Prop

  Kind           : Thing → F.World → Prop
  Sortal         : Thing → F.World → Prop
  NonSortal      : Thing → F.World → Prop

  SubKind        : Thing → F.World → Prop
  Phase          : Thing → F.World → Prop
  Role           : Thing → F.World → Prop
  SemiRigidSortal : Thing → F.World → Prop
  Category       : Thing → F.World → Prop
  Mixin          : Thing → F.World → Prop
  PhaseMixin     : Thing → F.World → Prop
  RoleMixin      : Thing → F.World → Prop
