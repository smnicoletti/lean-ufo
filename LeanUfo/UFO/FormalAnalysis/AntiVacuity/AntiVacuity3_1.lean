import LeanUfo.UFO.Core.Section3_1

/-!
# Taxonomy anti-vacuity analysis through section 3.1

The finite domain below validates the section 3.1 axioms. Subsequent modules
extend the same interpretation. The selected taxonomy predicates have
inhabitants at one world.
-/

namespace AntiVacuity.Taxonomy

/-- Names of the six concrete endurant leaves introduced in sections 3.3 and
3.4. We include them in the domain from the start so later files can extend one
fixed interpretation instead of replacing earlier witnesses. -/
inductive Leaf
  | object | collective | quantity | relator | mode | quality
  | abstract | perdurant
  deriving DecidableEq, Repr

/-- Domain of the common taxonomy interpretation.

For every leaf `l` it contains:
- `individual l`, the intended inhabitant of the individual-level leaf;
- `kind l`, the unique type instantiated by that individual.

The abstract and perdurant representatives witness the upper section 3.1
taxonomy branches; the other six representatives support the later endurant
taxonomy. Keeping individuals and their types in distinct constructors makes
the section 3.1 `Type_`/`Individual` partition immediate. -/
inductive Thing
  | individual (leaf : Leaf)
  | kind (leaf : Leaf)
  deriving DecidableEq, Repr

/-- The common interpretation uses one S5 world. Accessibility is universal,
so `Box` and `Dia` reduce to truth at that world. This is sufficient for the
rigid taxonomy branch used by the endurant-leaf witness. -/
def frame : S5Frame where
  World := Unit
  R := fun _ _ => True
  refl := by simp
  symm := by simp
  trans := by simp

/-- Exactly the `kind` constructors are types. -/
def isType : Thing -> Prop
  | .kind _ => True
  | .individual _ => False

/-- Instantiation pairs each leaf individual with its corresponding leaf kind.
No individual instantiates two kinds, and no type is itself an instance. -/
def inst : Thing -> Thing -> Prop
  | .individual x, .kind y => x = y
  | _, _ => False

/-- Concrete individuals comprise the six endurant leaves and the perdurant. -/
def concrete : Thing -> Prop
  | .individual .abstract | .kind _ => False
  | .individual _ => True

/-- The dedicated abstract representative is the only abstract individual. -/
def abstract : Thing -> Prop
  | .individual .abstract => True
  | _ => False

/-- The six UFO endurant leaves are exactly the endurants in this domain. -/
def endurant : Thing -> Prop
  | .individual .object | .individual .collective | .individual .quantity
  | .individual .relator | .individual .mode | .individual .quality => True
  | _ => False

/-- The dedicated perdurant representative is the only perdurant. -/
def perdurant : Thing -> Prop
  | .individual .perdurant => True
  | _ => False

/-- Matching kinds of the six endurant leaves are endurant types. -/
def endurantType : Thing -> Prop
  | .kind .object | .kind .collective | .kind .quantity
  | .kind .relator | .kind .mode | .kind .quality => True
  | _ => False

/-- The matching kind of the perdurant representative is a perdurant type. -/
def perdurantType : Thing -> Prop
  | .kind .perdurant => True
  | _ => False

/-- The substantial/moment division used when section 3.3 is added. -/
def isSubstantial : Leaf -> Bool
  | .object | .collective | .quantity => true
  | .relator | .mode | .quality | .abstract | .perdurant => false

/-- Moment leaves are the Boolean complement of substantial leaves. -/
def isMoment : Leaf -> Bool
  | .relator | .mode | .quality => true
  | .object | .collective | .quantity | .abstract | .perdurant => false

/-- Interpretation of the section 3.1 signature.

All six individuals are concrete endurants and all six matching types are
endurant types. Specialization is interpreted by the semantic clause from
(a5): two things are types and every instance of the first is necessarily an
instance of the second. Because every type has one unique instance, this
reduces to identity between leaf kinds. -/
def sig1 : UFOSignature3_1 where
  F := frame
  Thing := Thing
  thing_nonempty := ⟨.individual .object⟩
  Type_ := fun x _ => isType x
  Individual := fun x _ => ¬ isType x
  Inst := fun x t _ => inst x t
  Sub := fun x y w =>
    isType x ∧ isType y ∧
      Frame.Box (F := frame) (fun _ => ∀ z, inst z x -> inst z y) w
  ConcreteIndividual := fun x _ => concrete x
  AbstractIndividual := fun x _ => abstract x
  Endurant := fun x _ => endurant x
  Perdurant := fun x _ => perdurant x
  EndurantType := fun x _ => endurantType x
  PerdurantType := fun x _ => perdurantType x

attribute [simp] frame isType inst concrete abstract endurant perdurant
  endurantType perdurantType isSubstantial isMoment sig1

/-- An individual has exactly one corresponding leaf type in this interpretation. -/
theorem inst_target_unique {x t₁ t₂ : Thing}
    (h₁ : inst x t₁) (h₂ : inst x t₂) : t₁ = t₂ := by
  cases x <;> cases t₁ <;> cases t₂ <;> simp_all

/-- Every interpreted type has its matching leaf individual as an instance. -/
theorem type_has_instance {t : Thing} (h : isType t) :
    ∃ x, inst x t := by
  cases t with
  | individual leaf => simp_all
  | kind leaf => exact ⟨.individual leaf, rfl⟩

/-- Axiom (a1): every type is possibly instantiated. The matching individual
is the witness at the unique world. -/
theorem ax1_sig : ax_a1 sig1 := by
  intro x w
  cases x with
  | individual leaf => cases leaf <;> cases w <;> simp [Frame.Dia]
  | kind leaf =>
      cases leaf <;> cases w <;> simp [Frame.Dia]
      all_goals exact ⟨.individual _, rfl⟩

/-- Axiom (a2): individuals cannot themselves have instances. -/
theorem ax2_sig : ax_a2 sig1 := by
  intro x w
  cases x with
  | individual leaf => cases leaf <;> cases w <;> simp [Frame.Box]
  | kind leaf =>
      cases leaf <;> cases w <;> simp [Frame.Box]
      all_goals exact ⟨.individual _, rfl⟩

/-- Axiom (a3): the source of every instantiation pair is an individual. -/
theorem ax3_sig : ax_a3 sig1 := by
  intro x y w h
  cases x <;> cases y <;> cases w <;> simp_all

/-- Axiom (a4): the unique-target interpretation rules out instantiating two
distinct incomparable types. -/
theorem ax4_sig : ax_a4 sig1 := by
  intro w h
  rcases h with ⟨x, y, z, hx⟩
  cases x <;> cases y <;> cases z <;> simp_all

/-- Axiom (a5) holds by construction because `Sub` is defined by its right-hand
semantic characterization. -/
theorem ax5_sig : ax_a5 sig1 := by intro x y w; rfl

/-- Axiom (a6): if one individual instantiates both candidate types, uniqueness
makes those types equal. Their reflexive specialization contradicts the
incomparability premise, so the antecedent cannot hold. -/
theorem ax6_sig : ax_a6 sig1 := by
  intro t₁ t₂ x w h
  have ht : t₁ = t₂ := inst_target_unique h.1 h.2.1
  subst t₂
  have htType : isType t₁ := by
    cases x <;> cases t₁ <;> simp_all [inst]
  have hSelf : sig1.Sub t₁ t₁ w :=
    (ax5_sig t₁ t₁ w).2 ⟨htType, htType,
      fun _ _ _ hInst => hInst⟩
  exact False.elim (h.2.2.1 hSelf)

/-- Axioms (a7)-(a17) validate the individual/type, concrete/abstract, and
endurant/perdurant classifications by exhaustive finite case splits. -/
theorem ax7_sig : ax_a7 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax8_sig : ax_a8 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax9_sig : ax_a9 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax10_sig : ax_a10 sig1 := by
  intro x w; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp
theorem ax11_sig : ax_a11 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax12_sig : ax_a12 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax13_sig : ax_a13 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax14_sig : ax_a14 sig1 := by
  intro x w; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp
theorem ax15_sig : ax_a15 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax16_sig : ax_a16 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all
theorem ax17_sig : ax_a17 sig1 := by
  intro x w h; cases x <;> rename_i leaf <;> cases leaf <;> cases w <;> simp_all

/-- The complete section 3.1 package for the common anti-vacuity domain. -/
instance axioms1 : UFOAxioms3_1 sig1 where
  ax1 := ax1_sig
  ax2 := ax2_sig
  ax3 := ax3_sig
  ax4 := ax4_sig
  ax5 := ax5_sig
  ax6 := ax6_sig
  ax7 := ax7_sig
  ax8 := ax8_sig
  ax9 := ax9_sig
  ax10 := ax10_sig
  ax11 := ax11_sig
  ax12 := ax12_sig
  ax13 := ax13_sig
  ax14 := ax14_sig
  ax15 := ax15_sig
  ax16 := ax16_sig
  ax17 := ax17_sig

/-- All upper section 3.1 taxonomy branches are inhabited simultaneously. -/
theorem section3_1_taxonomy_nonempty :
    sig1.Type_ (.kind .object) () ∧
    sig1.Individual (.individual .object) () ∧
    sig1.ConcreteIndividual (.individual .object) () ∧
    sig1.AbstractIndividual (.individual .abstract) () ∧
    sig1.Endurant (.individual .object) () ∧
    sig1.Perdurant (.individual .perdurant) () ∧
    sig1.EndurantType (.kind .object) () ∧
    sig1.PerdurantType (.kind .perdurant) () := by
  simp

/- Every primitive field of `UFOSignature3_1` is inhabited in the common
taxonomy model. Specialization is witnessed reflexively here; the proper
specialization derived predicate receives a nonreflexive witness in the richer
multi-world model of `AntiVacuity3_2`. -/
theorem section3_1_predicates_nonempty :
    (∃ x w, sig1.Type_ x w) ∧
    (∃ x w, sig1.Individual x w) ∧
    (∃ x t w, sig1.Inst x t w) ∧
    (∃ t u w, sig1.Sub t u w) ∧
    (∃ x w, sig1.ConcreteIndividual x w) ∧
    (∃ x w, sig1.AbstractIndividual x w) ∧
    (∃ x w, sig1.Endurant x w) ∧
    (∃ x w, sig1.Perdurant x w) ∧
    (∃ t w, sig1.EndurantType t w) ∧
    (∃ t w, sig1.PerdurantType t w) := by
  exact ⟨⟨.kind .object, (), by simp⟩,
    ⟨.individual .object, (), by simp⟩,
    ⟨.individual .object, .kind .object, (), by simp⟩,
    ⟨.kind .object, .kind .object, (), by
      refine ⟨by simp, by simp, ?_⟩
      intro _ _ _ h
      exact h⟩,
    ⟨.individual .object, (), by simp⟩,
    ⟨.individual .abstract, (), by simp⟩,
    ⟨.individual .object, (), by simp⟩,
    ⟨.individual .perdurant, (), by simp⟩,
    ⟨.kind .object, (), by simp⟩,
    ⟨.kind .perdurant, (), by simp⟩⟩

end AntiVacuity.Taxonomy
