import LeanUfo.UFO.Modal.Basics

universe u v

/-
We fix:
- an S5 frame `F`
- a type `D` of individuals

The key semantic assumption:
`D` does not depend on the world.

This implements constant-domain (possibilist) semantics,
matching the assumptions of the UFO axiomatization paper.
-/
variable {F : S5Frame}
variable (D : Type v)

/--
Universal quantification over a constant domain `D`.

Semantics:
  (ForallD φ) w  ≡  ∀ x : D, φ x w
-/
def ForallD (φ : D → F.World → Prop) : F.World → Prop :=
  fun w => ∀ x : D, φ x w

/--
Existential quantification over a constant domain `D`.

Semantics:
  (ExistsD φ) w  ≡  ∃ x : D, φ x w
-/
def ExistsD (φ : D → F.World → Prop) : F.World → Prop :=
  fun w => ∃ x : D, φ x w

notation "∀₀[" D "]" φ => ForallD D φ
notation "∃₀[" D "]" φ => ExistsD D φ
