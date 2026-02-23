import LeanUfo.UFO.Modal.Basics

universe u v

/--
Basic semantic signature for UFO over S5 possible-world semantics.

- `Thing` is the domain of quantification (the top category in the taxonomy).
- `Type_` and `Individual` are world-indexed predicates.
- `Inst` is world-indexed instantiation (written `::` in the paper).
-/
structure UFOSignature3_1 where
  F                  : S5Frame
  Thing              : Type v
  Type_              : Thing → F.World → Prop
  Individual         : Thing → F.World → Prop
  Inst               : Thing → Thing → F.World → Prop
  Sub                : Thing → Thing → F.World → Prop
  ConcreteIndividual : Thing → F.World → Prop
  AbstractIndividual : Thing → F.World → Prop
  Endurant           : Thing → F.World → Prop
  Perdurant          : Thing → F.World → Prop
  EndurantType       : Thing → F.World → Prop
  PerdurantType      : Thing → F.World → Prop
namespace UFOSignature3_1

infix:50 " :: " => UFOSignature3_1.Inst
infix:50 " ⊑ "  => UFOSignature3_1.Sub

end UFOSignature3_1
