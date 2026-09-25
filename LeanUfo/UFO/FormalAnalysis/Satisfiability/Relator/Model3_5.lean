import LeanUfo.UFO.Core.Section3_5
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_4

/-!
# Positive relator model: section 3.5

The mereology has two incomparable atoms, `quaA` and `quaB`, as proper parts of
`relator`. All remaining parthood facts are reflexive. The qua individuals do
not overlap each other, and each overlaps the relator.
-/

namespace Relator.Model3_5

open Model3_1

def part : Thing -> Thing -> Prop
  | x, y => x = y ∨
      (x = .quaA ∧ y = .relator) ∨
      (x = .quaB ∧ y = .relator)

def overlap : Thing -> Thing -> Prop
  | x, y => x = y ∨
      (x = .relator ∧ (y = .quaA ∨ y = .quaB)) ∨
      (y = .relator ∧ (x = .quaA ∨ x = .quaB))

def sig : UFOSignature3_5 where
  toUFOSignature3_4 := Model3_4.sig
  Part := fun x y _ => part x y
  Overlap := fun x y _ => overlap x y
  ProperPart := fun x y _ => part x y ∧ ¬ part y x

attribute [simp] part overlap sig

/-- Parthood is reflexive, antisymmetric, and transitive in the finite poset. -/
theorem ax47_sig : ax_a47 sig := by intro x w; exact Or.inl rfl

theorem ax48_sig : ax_a48 sig := by
  intro x y w h
  rcases h with ⟨hxy, hyx⟩
  rcases hxy with rfl | hxy | hxy
  · rfl
  · rcases hxy with ⟨rfl, rfl⟩
    simp [part] at hyx
  · rcases hxy with ⟨rfl, rfl⟩
    simp [part] at hyx

theorem ax49_sig : ax_a49 sig := by
  intro x y z w h
  rcases h with ⟨hxy, hyz⟩
  rcases hxy with rfl | hxy | hxy
  · exact hyz
  · rcases hxy with ⟨rfl, rfl⟩
    have hz : Thing.relator = z := by simpa [part] using hyz
    subst z
    simp [part]
  · rcases hxy with ⟨rfl, rfl⟩
    have hz : Thing.relator = z := by simpa [part] using hyz
    subst z
    simp [part]

private theorem overlap_of_part {x y : Thing} (h : part x y) : overlap x y := by
  rcases h with rfl | h | h
  · exact Or.inl rfl
  · rcases h with ⟨rfl, rfl⟩
    simp [overlap]
  · rcases h with ⟨rfl, rfl⟩
    simp [overlap]

/-- The explicit overlap table is exactly common-part overlap. -/
theorem ax50_sig : ax_a50 sig := by
  intro x y w
  constructor
  · intro h
    rcases h with rfl | h | h
    · exact ⟨x, Or.inl rfl, Or.inl rfl⟩
    · rcases h with ⟨rfl, rfl | rfl⟩
      · exact ⟨.quaA, by simp [part]⟩
      · exact ⟨.quaB, by simp [part]⟩
    · rcases h with ⟨rfl, rfl | rfl⟩
      · exact ⟨.quaA, by simp [part]⟩
      · exact ⟨.quaB, by simp [part]⟩
  · rintro ⟨z, hzx, hzy⟩
    rcases hzx with rfl | hzx | hzx
    · exact overlap_of_part hzy
    · rcases hzx with ⟨rfl, rfl⟩
      rcases hzy with h | h | h
      · subst y; simp [overlap]
      · rcases h with ⟨_hSelf, rfl⟩; simp [overlap]
      · rcases h with ⟨hFalse, _⟩; cases hFalse
    · rcases hzx with ⟨rfl, rfl⟩
      rcases hzy with h | h | h
      · subst y; simp [overlap]
      · rcases h with ⟨hFalse, _⟩; cases hFalse
      · rcases h with ⟨_hSelf, rfl⟩; simp [overlap]

/-- Strong supplementation chooses the opposite qua atom below the relator. -/
theorem ax51_sig : ax_a51 sig := by
  intro x y w hNotPart
  cases x <;> cases y <;> simp_all [part, overlap]

/-- Proper parthood is interpreted by its defining strict-parthood clause. -/
theorem ax52_sig : ax_a52 sig := by intro x y w; rfl

/-- Consistency witness for §3.5 of the positive relator model chain. -/
instance : UFOAxioms3_5 sig where
  toUFOAxioms3_4 := by
    change UFOAxioms3_4 Model3_4.sig
    infer_instance
  ax47 := ax47_sig
  ax48 := ax48_sig
  ax49 := ax49_sig
  ax50 := ax50_sig
  ax51 := ax51_sig
  ax52 := ax52_sig

end Relator.Model3_5
