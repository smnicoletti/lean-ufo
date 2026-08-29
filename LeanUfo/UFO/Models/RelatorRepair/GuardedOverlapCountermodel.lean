import LeanUfo.UFO.Models.RelatorRepair.Model3_10

/-!
# Countermodel for (t31) under guarded overlap

This finite interpretation extends the positive repair model with one
additional parthood fact: `foundation` is part of `quaA`. The added part is not
an externally dependent mode, so the guarded-overlap formula does not constrain
it. Giving that part a different foundation refutes the original (t31)
conclusion and records why this alternative was not selected.
-/

namespace RelatorRepair.GuardedOverlapCountermodel

open Model3_1

def part : Thing -> Thing -> Prop
  | x, y => Model3_5.part x y ∨ (x = .foundation ∧ y = .quaA)

def overlap (x y : Thing) : Prop :=
  ∃ z, part z x ∧ part z y

def foundedBy : Thing -> Thing -> Prop
  | .relator, .foundation | .quaA, .foundation | .quaB, .foundation => True
  | .foundation, .bearerA => True
  | _, _ => False

def sig : UFOSignature3_10 :=
{ Model3_10.sig with
  Part := fun x y _ => part x y
  Overlap := fun x y _ => overlap x y
  ProperPart := fun x y _ => part x y ∧ ¬ part y x
  FoundedBy := fun x y _ => foundedBy x y
}

attribute [simp] part overlap foundedBy

/-- The extended parthood relation remains reflexive. -/
theorem ax47_sig : ax_a47 sig.toUFOSignature3_5 := by
  intro x w
  exact Or.inl (Or.inl rfl)

/-- Overlap is defined as the existence of a common part. -/
theorem ax50_sig : ax_a50 sig.toUFOSignature3_5 := by intro x y w; rfl

private theorem unique_foundation_quaA (w : World) :
    ∃! y, sig.FoundedBy .quaA y w := by
  refine ⟨.foundation, by change foundedBy .quaA .foundation; trivial, ?_⟩
  intro y h
  change foundedBy .quaA y at h
  cases y <;> simp_all [foundedBy]
  rfl

private theorem unique_foundation_foundation (w : World) :
    ∃! y, sig.FoundedBy .foundation y w := by
  refine ⟨.bearerA, by change foundedBy .foundation .bearerA; trivial, ?_⟩
  intro y h
  change foundedBy .foundation y at h
  cases y <;> simp_all [foundedBy]
  rfl

@[simp] theorem foundationOf_quaA (w : World) :
    FoundationOf sig .quaA w = .foundation :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_quaA w)).2 (by
    change foundedBy .quaA .foundation
    trivial)

@[simp] theorem foundationOf_foundation (w : World) :
    FoundationOf sig .foundation w = .bearerA :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_foundation w)).2 (by
    change foundedBy .foundation .bearerA
    trivial)

/-- The guarded-overlap formula permits the additional non-EDM part. -/
theorem ax73_guarded_overlap_sig : ax_a73_guarded_overlap sig := by
  intro x y w
  constructor
  · intro h
    change Model3_10.quaIndividualOf x y at h
    cases x <;> cases y <;> simp [Model3_10.quaIndividualOf] at h
    · refine ⟨by change Model3_10.externallyDependentMode .quaA; trivial,
        by change Model3_9.inheresIn .quaA .bearerA; trivial, ?_⟩
      intro z hz
      change Model3_10.externallyDependentMode z at hz
      change overlap z .quaA ↔
        (Model3_9.inheresIn z .bearerA ∧
          FoundationOf sig z w = FoundationOf sig .quaA w)
      cases z <;> simp_all [Model3_10.externallyDependentMode, overlap, part,
        Model3_9.inheresIn, Model3_5.part]
    · refine ⟨by change Model3_10.externallyDependentMode .quaB; trivial,
        by change Model3_9.inheresIn .quaB .bearerB; trivial, ?_⟩
      intro z hz
      change Model3_10.externallyDependentMode z at hz
      change overlap z .quaB ↔
        (Model3_9.inheresIn z .bearerB ∧
          FoundationOf sig z w = FoundationOf sig .quaB w)
      cases z <;> simp_all [Model3_10.externallyDependentMode, overlap, part,
        Model3_9.inheresIn, Model3_5.part]
  · rintro ⟨hEDM, hInheres, _⟩
    change Model3_10.externallyDependentMode x at hEDM
    change Model3_9.inheresIn x y at hInheres
    change Model3_10.quaIndividualOf x y
    cases x <;> cases y <;> simp_all [Model3_10.externallyDependentMode,
      Model3_9.inheresIn, Model3_10.quaIndividualOf]

/--
Finite counterexample to the original (t31) conclusion for guarded overlap.
The qua individual and its added part have different selected foundations.
-/
theorem t31_counterexample :
    sig.QuaIndividualOf .quaA .bearerA .actual ∧
    sig.Part .foundation .quaA .actual ∧
    FoundationOf sig .quaA .actual ≠ FoundationOf sig .foundation .actual := by
  refine ⟨by change Model3_10.quaIndividualOf .quaA .bearerA; trivial,
    by change part .foundation .quaA; exact Or.inr ⟨rfl, rfl⟩, ?_⟩
  rw [foundationOf_quaA, foundationOf_foundation]
  intro h
  cases h

end RelatorRepair.GuardedOverlapCountermodel
