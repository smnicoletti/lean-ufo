import LeanUfo.UFO.FormalAnalysis.StructuralAssumptions
import LeanUfo.UFO.FormalAnalysis.AxiomaticAnalysis

/-!
# Guarded overlap does not imply unrestricted (t31)

A ten-entity, three-world model satisfies the guarded-overlap alternative
through §4 but refutes (t31). It retains both added assumptions and all source
distance laws. The only changed numbered axiom is (a73), replaced by
`ax_a73_guarded_overlap`; (a102) has the current corrected argument order.

The qua individual has two unfounded object parts. Guarded overlap only
constrains externally dependent modes, so it permits these parts. The total
`FoundationOf` function returns an unspecified value for an unfounded entity.
We choose the qua individual's foundation from two perdurants so that it
differs from that value. The proof works for any value returned by classical choice.

Reading order:

- `base` and `sig`: taxonomy, parthood, and dependence.
- `full_package`: every guarded-repair assumption through §3.10.
- `chosenFoundation` and `counterexample`: the failure of (t31).
- `full_counterexample`: the same failure after extending through §4.

This refutes the repository's exact total-function statement of (t31).
It does not concern a statement restricted to parts with a foundation:
`th_t31_guarded_overlap_of_founded` proves that version. The active part-based
(a73) already proves unrestricted (t31).
-/

namespace Historical.GuardedOverlapCountermodel

/-! ## Domain and taxonomy

The domain has ten entities. Three types classify four objects (3, 4, 6, 7),
one mode (5), and two perdurants (8, 9). There are no relators or qualities.
Objects 6 and 7 will be proper parts of mode 5. The mereology axioms impose
no requirement that a mode's parts are themselves modes.
-/

def obj (x : Fin 10) : Prop := x = 3 ∨ x = 4 ∨ x = 6 ∨ x = 7
def inst (x t : Fin 10) : Prop :=
  (obj x ∧ t = 0) ∨ (x = 5 ∧ t = 1) ∨ (8 ≤ x ∧ t = 2)

def base : UFOSignature3_4 where
  F := {
    World := Fin 3
    R := fun _ _ => True
    refl := fun _ => True.intro
    symm := fun _ => True.intro
    trans := fun _ _ => True.intro }
  Thing := Fin 10
  thing_nonempty := ⟨0⟩
  Type_ := fun t _ => t < 3
  Individual := fun x _ => 3 ≤ x
  Inst := fun x t _ => inst x t
  Sub := fun a b _ => a < 3 ∧ b < 3 ∧ ∀ x, inst x a → inst x b
  ConcreteIndividual := fun x _ => 3 ≤ x
  AbstractIndividual := fun _ _ => False
  Endurant := fun x _ => 3 ≤ x ∧ x < 8
  Perdurant := fun x _ => 8 ≤ x
  EndurantType := fun t _ => t < 2
  PerdurantType := fun t _ => t = 2
  Rigid := fun t _ => t < 2
  AntiRigid := fun _ _ => False
  SemiRigid := fun _ _ => False
  Kind := fun t _ => t < 2
  Sortal := fun t _ => t < 2
  NonSortal := fun _ _ => False
  SubKind := fun _ _ => False
  Phase := fun _ _ => False
  Role := fun _ _ => False
  SemiRigidSortal := fun _ _ => False
  Category := fun _ _ => False
  Mixin := fun _ _ => False
  PhaseMixin := fun _ _ => False
  RoleMixin := fun _ _ => False
  Substantial := fun x _ => obj x
  Moment := fun x _ => x = 5
  Object := fun x _ => obj x
  Collective := fun _ _ => False
  Quantity := fun _ _ => False
  Relator := fun _ _ => False
  IntrinsicMoment := fun x _ => x = 5
  Mode := fun x _ => x = 5
  QualityKind := fun _ _ => False
  SubstantialType := fun t _ => t = 0
  MomentType := fun t _ => t = 1
  ObjectType := fun t _ => t = 0
  CollectiveType := fun _ _ => False
  QuantityType := fun _ _ => False
  RelatorType := fun _ _ => False
  ModeType := fun t _ => t = 1
  QualityType := fun _ _ => False
  ObjectKind := fun t _ => t = 0
  CollectiveKind := fun _ _ => False
  QuantityKind := fun _ _ => False
  RelatorKind := fun _ _ => False
  ModeKind := fun t _ => t = 1

-- Unfold the axioms and enumerate both finite domains. Lean's kernel checks
-- the resulting proofs, including the inherited non-sortal closure assumption.
local macro "check_base" : tactic =>
  `(tactic| (
    delta ax_a1 ax_a2 ax_a3 ax_a4 ax_a5 ax_a6 ax_a7 ax_a8 ax_a9 ax_a10 ax_a11 ax_a12 ax_a13
      ax_a14 ax_a15 ax_a16 ax_a17 ax_a18 ax_a19 ax_a20 ax_a21 ax_a22 ax_a23 ax_a24 ax_a25
      ax_a26 ax_a27 ax_a28 ax_a29 ax_a30 ax_a31 ax_a32 ax_a33 ax_a34 ax_a35 ax_a36 ax_a37
      ax_a38 ax_a39 ax_a40 ax_a41 ax_a42 ax_a43 ax_a44 ax_a45 ax_a46
      ax_nonSortal_upward Quality Frame.Box Frame.Dia base inst obj
      ax_a44_endurantType ax_a44_perdurantType ax_a44_substantialType
      ax_a44_momentType ax_a44_objectType ax_a44_collectiveType ax_a44_quantityType
      ax_a44_relatorType ax_a44_modeType ax_a44_qualityType ax_a45_objectKind
      ax_a45_collectiveKind ax_a45_quantityKind ax_a45_relatorKind ax_a45_modeKind
      ax_a45_qualityKind
    simp [Fin.forall_fin_succ, Fin.exists_fin_succ]))

instance : UFOAxioms3_1 base.toUFOSignature3_1 where
  ax1 := by check_base
  ax2 := by check_base
  ax3 := by check_base
  ax4 := by check_base
  ax5 := by check_base
  ax6 := by check_base
  ax7 := by check_base
  ax8 := by check_base
  ax9 := by check_base
  ax10 := by check_base
  ax11 := by check_base
  ax12 := by check_base
  ax13 := by check_base
  ax14 := by check_base
  ax15 := by check_base
  ax16 := by check_base
  ax17 := by check_base

instance : UFOAxioms3_2 base.toUFOSignature3_2 where
  toUFOAxioms3_1 := inferInstance
  ax18 := by check_base
  ax19 := by check_base
  ax20 := by check_base
  ax21 := by check_base
  ax22 := by check_base
  ax23 := by check_base
  ax24 := by check_base
  ax25 := by check_base
  ax26 := by check_base
  ax27 := by check_base
  ax28 := by check_base
  ax29 := by check_base
  ax30 := by check_base
  ax31 := by check_base
  ax32 := by check_base
  ax33 := by check_base
  ax_nonSortal_up := by check_base

instance : UFOAxioms3_3 base.toUFOSignature3_3 where
  toUFOAxioms3_2 := inferInstance
  ax34 := by check_base
  ax35 := by check_base
  ax36 := by check_base
  ax37 := by check_base
  ax38 := by check_base
  ax39 := by check_base
  ax40 := by check_base
  ax41 := by check_base
  ax42 := by check_base
  ax43 := by check_base

instance : UFOAxioms3_4 base where
  toUFOAxioms3_3 := inferInstance
  ax44 := by check_base
  ax45 := by check_base
  ax46 := by check_base

/-! ## Parthood and dependence

The qua individual (5) is the sum of two disjoint object parts (6 and 7).
All other parthood facts are reflexive. Either atom supplies supplementation
when the other atom fails to contain the whole.

At world 0 the qua individual and both dependence witnesses exist. World 1
contains bearer 3 without external object 4; world 2 contains 4 without 3.
Thus 5 depends on both objects, while 3 and 4 are existentially independent.
These worlds make 5 an externally dependent mode under (a69) and (a70).
-/

def part (x y : Fin 10) : Prop := x = y ∨ ((x = 6 ∨ x = 7) ∧ y = 5)
def overlap (x y : Fin 10) : Prop := ∃ z, part z x ∧ part z y
def ex (x : Fin 10) (w : Fin 3) : Prop :=
  if x = 5 then w = 0 else if x = 3 then w < 2 else if x = 4 then w = 0 ∨ w = 2 else True
def ed (x y : Fin 10) : Prop := ∀ w, ex x w → ex y w
def ind (x y : Fin 10) : Prop := ¬ ed x y ∧ ¬ ed y x
def inh (x y : Fin 10) : Prop := x = 5 ∧ y = 3
def ext (x y : Fin 10) : Prop := ed x y ∧ ∀ z, inh x z → ind y z

def sig (f : Fin 10) : UFOSignature3_10 where
  toUFOSignature3_4 := base
  Part := fun x y _ => part x y
  Overlap := fun x y _ => overlap x y
  ProperPart := fun x y _ => part x y ∧ ¬ part y x
  FunctionsAs := fun _ _ _ => False
  GenericFunctionalDependence := fun _ _ _ => True
  IndividualFunctionalDependence := fun x t y u _ => inst x t ∧ inst y u
  ComponentOf := fun x t y u _ => (part x y ∧ ¬ part y x) ∧ inst x t ∧ inst y u
  Ex := ex
  ConstitutedBy := fun _ _ _ => False
  GenericConstitutionalDependence := fun t _ _ => ∀ x, ¬ inst x t
  Constitution := fun _ _ _ _ _ => False
  ExistentialDependence := fun x y _ => ed x y
  ExistentialIndependence := fun x y _ => ind x y
  InheresIn := fun x y _ => inh x y
  ExternallyDependent := fun x y _ => ext x y
  ExternallyDependentMode := fun (x : Fin 10) _ => x = 5
  FoundedBy := fun (x y : Fin 10) _ => x = 5 ∧ y = f
  QuaIndividualOf := fun (x y : Fin 10) _ => x = 5 ∧ y = 3
  QuaIndividual := fun (x : Fin 10) _ => x = 5
  Mediates := fun _ _ _ => False

/-! ## Axiom proofs through §3.10

Finite enumeration handles the propositional axioms. The proofs for unique
ultimate bearers, foundations, guarded overlap, and the relator definition
explain the cases where a model-specific argument is needed.
-/

local macro "check_later" : tactic =>
  `(tactic| (
    delta ax_a47 ax_a48 ax_a49 ax_a50 ax_a51 ax_a52 ax_a53 ax_a54 ax_a55 ax_a56 ax_a57 ax_a58
      ax_a59 ax_a60 ax_a61 ax_a62 ax_a63 ax_a64 ax_a65 ax_a66 ax_a67 ax_a68 ax_a69 ax_a70
      ax_a71 ax_a72 ax_a74 ax_a75 ax_a76 ax_a77 ax_a78 ax_a79 ax_a80
      ax_a73_guarded_overlap sig base inst obj part overlap
      ex ed ind inh ext Frame.Box Frame.Dia
    simp [Fin.forall_fin_succ, Fin.exists_fin_succ]))

variable (f : Fin 10)

theorem a47 : ax_a47 (sig f).toUFOSignature3_5 := by check_later

theorem a48 : ax_a48 (sig f).toUFOSignature3_5 := by check_later

theorem a49 : ax_a49 (sig f).toUFOSignature3_5 := by check_later

theorem a50 : ax_a50 (sig f).toUFOSignature3_5 := by check_later

theorem a51 : ax_a51 (sig f).toUFOSignature3_5 := by check_later

theorem a52 : ax_a52 (sig f).toUFOSignature3_5 := by check_later

theorem a53 : ax_a53 (sig f).toUFOSignature3_6 := by check_later

theorem a54 : ax_a54 (sig f).toUFOSignature3_6 := by check_later

theorem a55 : ax_a55 (sig f).toUFOSignature3_6 := by check_later

theorem a56 : ax_a56 (sig f).toUFOSignature3_7 := by check_later

theorem a57 : ax_a57 (sig f).toUFOSignature3_7 := by check_later

theorem a58 : ax_a58 (sig f).toUFOSignature3_7 := by check_later

theorem a59 : ax_a59 (sig f).toUFOSignature3_7 := by check_later

theorem a60 : ax_a60 (sig f).toUFOSignature3_7 := by check_later

theorem a61 : ax_a61 (sig f).toUFOSignature3_7 := by check_later

theorem a62 : ax_a62 (sig f).toUFOSignature3_8 := by check_later

theorem a63 : ax_a63 (sig f).toUFOSignature3_8 := by check_later

theorem a64 : ax_a64 (sig f).toUFOSignature3_8 := by check_later

theorem a65 : ax_a65 (sig f).toUFOSignature3_9 := by check_later

theorem a66 : ax_a66 (sig f).toUFOSignature3_9 := by check_later

theorem a67 : ax_a67 (sig f).toUFOSignature3_9 := by check_later

/-- The only moment inheres directly in object 3, which inheres in nothing.
Every inherence path therefore ends at that same ultimate bearer. -/
theorem a68 : ax_a68 (sig f).toUFOSignature3_9 := by
  intro m w hm
  have hm5 : m = (5 : Fin 10) := hm
  subst m
  refine ⟨(3 : Fin 10), ⟨by change ¬ ((3 : Fin 10) = 5); decide,
    MomentOf.direct ⟨rfl, rfl⟩⟩, ?_⟩
  intro b hb
  exact momentOf_eq_of_unique_direct_bearer (Sig := (sig f).toUFOSignature3_9)
    (fun _ h => h.2) (by intro y h; have hbad : (3 : Fin 10) = 5 := h.1; contradiction) hb.2

theorem a69 : ax_a69 (sig f) := by check_later

theorem a70 : ax_a70 (sig f) := by check_later

theorem a71 (hf : 8 ≤ f) : ax_a71 (sig f) := by
  intro x y w h
  exact ⟨Or.inl h.1, h.2.symm ▸ hf⟩

theorem a72 : ax_a72 (sig f) := by
  intro x w hx
  refine ⟨f, ⟨hx, rfl⟩, ?_⟩
  intro y hy
  exact hy.2

/-- Only entity 5 is an externally dependent mode. The guarded formula tests
its overlap with itself and places no condition on its two object parts. -/
theorem guarded : ax_a73_guarded_overlap (sig f) := by
  intro x y w
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ⟨rfl, rfl⟩, ?_⟩
    intro z hz
    have hz5 : z = (5 : Fin 10) := hz
    subst z
    simp [sig, inh, overlap, part]
  · rintro ⟨hx, hi, _⟩
    exact ⟨hx, hi.2⟩

theorem a74 : ax_a74 (sig f) := by check_later

theorem a75 : ax_a75 (sig f) := by check_later

theorem a76 : ax_a76 (sig f) := by check_later

theorem a77 : ax_a77 (sig f) := by check_later

theorem a78 : ax_a78 (sig f) := by check_later

/-- No entity meets the relator definition. Only 5 has proper parts, and those
parts are objects, not qua individuals. This permits a qua individual outside
every relator, where (a78) cannot force its parts to share its foundation. -/
theorem a79 : ax_a79 (sig f) := by
  intro x w
  constructor
  · intro h; exact False.elim h
  · rintro ⟨⟨p, hp⟩, hpair, _⟩
    have hq := (hpair p p ⟨hp, hp⟩).1
    change p = (5 : Fin 10) at hq
    subst p
    have hbad := hp
    change part 5 x ∧ ¬ part x 5 at hbad
    simp [part] at hbad
    exact hbad.2.1 hbad.1.symm

theorem a80 : ax_a80 (sig f) := by check_later

theorem quaTyping : ax_quaIndividualOf_endurant (Sig := sig f) := by
  intro x y w h
  rcases h with ⟨_, rfl⟩
  change (3 : Fin 10) ≥ 3 ∧ (3 : Fin 10) < 8
  decide

instance : UFOAxioms3_5 (sig f).toUFOSignature3_5 where
  toUFOAxioms3_4 := by change UFOAxioms3_4 base; infer_instance
  ax47 := a47 f
  ax48 := a48 f
  ax49 := a49 f
  ax50 := a50 f
  ax51 := a51 f
  ax52 := a52 f

instance : UFOAxioms3_6 (sig f).toUFOSignature3_6 where
  toUFOAxioms3_5 := inferInstance
  ax53 := a53 f
  ax54 := a54 f
  ax55 := a55 f

instance : UFOAxioms3_7 (sig f).toUFOSignature3_7 where
  toUFOAxioms3_6 := inferInstance
  ax56 := a56 f
  ax57 := a57 f
  ax58 := a58 f
  ax59 := a59 f
  ax60 := a60 f
  ax61 := a61 f

instance : UFOAxioms3_8 (sig f).toUFOSignature3_8 where
  toUFOAxioms3_7 := inferInstance
  ax62 := a62 f
  ax63 := a63 f
  ax64 := a64 f

instance : UFOAxioms3_9 (sig f).toUFOSignature3_9 where
  toUFOAxioms3_8 := inferInstance
  ax65 := a65 f
  ax66 := a66 f
  ax67 := a67 f
  ax68 := a68 f

/-- Every §3.10 assumption holds for either perdurant foundation. The background
package excludes the active part-based (a73), preventing its accidental use. -/
theorem full_package (hf : 8 ≤ f) : UFOAxioms3_10GuardedOverlapRepair (sig f) where
  toUFOAxioms3_9 := inferInstance
  ax69 := a69 f
  ax70 := a70 f
  ax71 := a71 f hf
  ax72 := a72 f
  ax74 := a74 f
  ax75 := a75 f
  ax76 := a76 f
  ax77 := a77 f
  ax78 := a78 f
  ax79 := a79 f
  ax80 := a80 f
  axQuaIndividualOfEndurant := quaTyping f
  ax73GuardedOverlap := guarded f

/-! ## Foundation values and failure of (t31)

For an unfounded entity, the predicate supplied to `Classical.epsilon` is
everywhere false. Its returned value is therefore the same unspecified value
`unfoundedValue`. We do not assume that this value is any particular entity.

Perdurants 8 and 9 are distinct. Choosing 9 when the unspecified value is 8,
and choosing 8 otherwise, gives a genuine foundation different from that value.
This noncomputable choice defines a finite countermodel without adding an
axiom about how epsilon behaves on an empty predicate.
-/

noncomputable def unfoundedValue : Fin 10 :=
  @Classical.epsilon (Fin 10) ⟨0⟩ (fun _ => False)

noncomputable def chosenFoundation : Fin 10 :=
  if unfoundedValue = 8 then 9 else 8

theorem chosen_perdurant : 8 ≤ chosenFoundation := by
  classical
  unfold chosenFoundation
  split <;> decide

theorem chosen_ne_empty : chosenFoundation ≠ unfoundedValue := by
  classical
  unfold chosenFoundation
  split <;> rename_i h
  · rw [h]
    decide
  · exact Ne.symm h

theorem foundation_qua (w : Fin 3) :
    FoundationOf (sig f) (5 : Fin 10) w = f :=
  (foundationOf_eq_iff (Sig := sig f) (a72 f (5 : Fin 10) w rfl)).2 ⟨rfl, rfl⟩

/-- The selected part has no foundation at any world. The value of
`FoundationOf` on this entity therefore has no corresponding foundedness fact. -/
theorem part_unfounded (w : Fin 3) :
    ¬ ∃ y, (sig f).FoundedBy (6 : Fin 10) y w := by
  simp [sig]

theorem foundation_part (w : Fin 3) :
    FoundationOf (sig f) (6 : Fin 10) w = unfoundedValue := by
  simp [FoundationOf, sig, base, unfoundedValue]

/-- The foundation of the qua individual differs from the value returned for
its unfounded part. This works regardless of which value epsilon selects. -/
theorem counterexample :
    UFOAxioms3_10GuardedOverlapRepair (sig chosenFoundation) ∧
    (sig chosenFoundation).QuaIndividualOf (5 : Fin 10) (3 : Fin 10) (0 : Fin 3) ∧
    (sig chosenFoundation).Part (6 : Fin 10) (5 : Fin 10) (0 : Fin 3) ∧
    FoundationOf (sig chosenFoundation) (5 : Fin 10) (0 : Fin 3) ≠
      FoundationOf (sig chosenFoundation) (6 : Fin 10) (0 : Fin 3) := by
  refine ⟨full_package chosenFoundation chosen_perdurant, ⟨rfl, rfl⟩,
    Or.inr ⟨Or.inl rfl, rfl⟩, ?_⟩
  rw [foundation_qua, foundation_part]
  exact chosen_ne_empty

/-! ## Extension through §4

Empty quality structures and characterization satisfy §§3.11–3.12. The later
relations use their defining formulas, leaving parthood and foundations intact.
The shared extension from the added-assumption audit avoids duplicating these
proofs. `LaterNumbered` lists all remaining numbered obligations explicitly.
-/

open StructuralAssumptions

def extended (f : Fin 10) := EmptyLaterSections.extend (sig f)

def LaterNumbered (S : UFOSignature4) : Prop :=
  ax_a81 S.toUFOSignature3_11 ∧
  ax_a82 S.toUFOSignature3_11 ∧
  ax_a83 S.toUFOSignature3_12 ∧
  ax_a84 S.toUFOSignature3_12 ∧
  ax_a85 S.toUFOSignature3_12 ∧
  ax_a86 S.toUFOSignature3_12 ∧
  ax_a87 S.toUFOSignature3_12 ∧
  ax_a88 S.toUFOSignature3_12 ∧
  ax_a89 S.toUFOSignature3_12 ∧
  ax_a90 S.toUFOSignature3_12 ∧
  ax_a91 S.toUFOSignature3_12 ∧
  ax_a92 S.toUFOSignature3_12 ∧
  ax_a93 S.toUFOSignature3_12 ∧
  ax_a94 S.toUFOSignature3_12 ∧
  ax_a95 S.toUFOSignature3_12 ∧
  ax_a96 S.toUFOSignature3_12 ∧
  ax_a97 S.toUFOSignature3_12 ∧
  ax_a98 S.toUFOSignature3_12 ∧
  ax_a99 S.toUFOSignature3_12 ∧
  ax_a100 S.toUFOSignature3_12 ∧
  ax_a101 S.toUFOSignature3_12 ∧
  ax_a102 S.toUFOSignature3_13 ∧
  ax_a103 S.toUFOSignature3_13 ∧
  ax_a104 S.toUFOSignature3_13 ∧
  ax_a105 S ∧
  ax_a106 S ∧
  ax_a107 S ∧
  ax_a108 S

theorem later_numbered : LaterNumbered (extended f) :=
  ⟨EmptyLaterSections.a81 (sig f),
    EmptyLaterSections.a82 (sig f),
    EmptyLaterSections.a83 (sig f),
    EmptyLaterSections.a84 (sig f),
    EmptyLaterSections.a85 (sig f),
    EmptyLaterSections.a86 (sig f),
    EmptyLaterSections.a87 (sig f),
    EmptyLaterSections.a88 (sig f),
    EmptyLaterSections.a89 (sig f),
    EmptyLaterSections.a90 (sig f),
    EmptyLaterSections.a91 (sig f) (by intro t w h; exact h),
    EmptyLaterSections.a92 (sig f),
    EmptyLaterSections.a93 (sig f) (by intro t w h; exact h),
    EmptyLaterSections.a94 (sig f),
    EmptyLaterSections.a95 (sig f),
    EmptyLaterSections.a96 (sig f),
    EmptyLaterSections.a97 (sig f) (by intro t w h; exact h),
    EmptyLaterSections.a98 (sig f) (by intro t w h; exact h),
    EmptyLaterSections.a99 (sig f),
    EmptyLaterSections.a100 (sig f),
    EmptyLaterSections.a101 (sig f),
    EmptyLaterSections.a102 (sig f),
    EmptyLaterSections.a103 (sig f),
    EmptyLaterSections.a104 (sig f),
    EmptyLaterSections.a105 (sig f),
    EmptyLaterSections.a106 (sig f),
    EmptyLaterSections.a107 (sig f),
    EmptyLaterSections.a108 (sig f)⟩

theorem distance : StructuralAssumptions.Results.DistanceLaws (extended f) :=
  ⟨EmptyLaterSections.distance_identity _, EmptyLaterSections.distance_symmetry _,
    EmptyLaterSections.distance_triangle _⟩

/-- This model satisfies the full guarded alternative through section 4,
including both added assumptions and the source distance laws, but falsifies (t31). -/
theorem full_counterexample :
    UFOAxioms3_10GuardedOverlapRepair (extended chosenFoundation).toUFOSignature3_10 ∧
    LaterNumbered (extended chosenFoundation) ∧
    StructuralAssumptions.Results.DistanceLaws (extended chosenFoundation) ∧
    ¬ (∀ x p y w, (extended chosenFoundation).QuaIndividualOf x y w ∧
      (extended chosenFoundation).Part p x w →
      FoundationOf (extended chosenFoundation).toUFOSignature3_10 x w =
        FoundationOf (extended chosenFoundation).toUFOSignature3_10 p w) := by
  refine ⟨counterexample.1, later_numbered chosenFoundation, distance chosenFoundation, ?_⟩
  intro h
  exact counterexample.2.2.2
    (h (5 : Fin 10) (6 : Fin 10) (3 : Fin 10) (0 : Fin 3)
      ⟨counterexample.2.1, counterexample.2.2.1⟩)

end Historical.GuardedOverlapCountermodel
