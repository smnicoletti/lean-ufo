import LeanUfo.UFO.Core.Section3_13
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_12

/-!
# Endurant/perdurant anti-vacuity analysis through section 3.13

This file extends the cumulative section 3.12 model. The carrier already has
the perdurant `life` and the endurant `bearer`, so section 3.13 only needs to
interpret the three new relations.

`life` manifests `bearer` and is its life. The mereology inherited from
section 3.12 is identity mereology, hence `life` overlaps exactly itself. This
matches (a103): the only perdurant that manifests `bearer` is `life`. The meet
relation is also witnessed by `life` meeting itself. The resulting model
satisfies all axioms through section 3.13 while keeping all three newly
introduced relations inhabited together.
-/

namespace AntiVacuity.Section3_13

open AntiVacuity.Section3_12

def manifests : Thing -> Thing -> Prop
  | .life, .bearer => True
  | _, _ => False

def sig : UFOSignature3_13 where
  toUFOSignature3_12 := AntiVacuity.Section3_12.sig
  Manifests := fun x y _ => manifests x y
  LifeOf := fun x y _ => x = .life ∧ y = .bearer
  Meet := fun x y _ => x = .life ∧ y = .life

attribute [simp] manifests sig

instance axioms : UFOAxioms3_13 sig where
  toUFOAxioms3_12 := AntiVacuity.Section3_12.axioms
  ax102 := by
    intro x y w h
    cases x <;> cases y <;> simp_all [manifests, perdurant, endurant]
  ax103 := by
    intro x y w
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨trivial, trivial, ?_⟩
      intro z
      cases z <;> simp [manifests, perdurant]
    · rintro ⟨hx, hy, hz⟩
      have hx' : x = .life := by cases x <;> simp_all [perdurant]
      subst x
      have hself := (hz .life).1 rfl
      have hy' : y = .bearer := by
        cases y <;> simp_all [manifests]
      exact ⟨rfl, hy'⟩
  ax104 := by
    intro x y w h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨trivial, trivial⟩

/- One theorem combines the witnesses for manifestation, life-of, and meet,
so their non-emptiness is established in the same cumulative model. -/
theorem predicates_nonempty :
    (∃ x y w, sig.Manifests x y w) ∧
    (∃ x y w, sig.LifeOf x y w) ∧
    (∃ x y w, sig.Meet x y w) := by
  exact ⟨⟨.life, .bearer, (), trivial⟩,
    ⟨.life, .bearer, (), ⟨rfl, rfl⟩⟩,
    ⟨.life, .life, (), ⟨rfl, rfl⟩⟩⟩

end AntiVacuity.Section3_13
