import LeanUfo.UFO.Core.S5_Derived
import LeanUfo.UFO.Core.Section4
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_10
import Mathlib.Data.Fintype.Basic

/-!
# Added assumptions: derivations and countermodels

Three former assumptions follow from numbered axioms: instance typing,
subtype-of-kind typing, and kind stability. Their proofs stay in Section3_4
and S5_Derived, where other theorems use them. The applications below check
their premises and the conclusions of (t10), (t11), (t14), and (t16).

Two assumptions do not follow from the remaining encoded axioms:
non-sortal upward closure and qua-individual bearer typing. The countermodels
below satisfy (a1)–(a108), the source's distance laws, and the other added
assumption. The first also refutes (t16), and the second refutes (t33).

The two kinds of evidence answer different questions. A derivation shows that
an added assumption can be removed without losing its consequences. A model
that satisfies the remaining axioms but falsifies the assumption proves that
no derivation from those axioms is possible. Separate countermodels retain
the other added assumption, so each failure can be attributed to the assumption
being tested. For (t16) and (t33), we also check that the theorem itself is false.

Reading order:
- `KindChecks` and `TypingChecks`: derivable facts and theorem applications.
- `NonSortalClosure` and `NonSortalExtension`: the nine-entity countermodel.
- `QuaBearerCountermodel`: the relator with types as bearers.
- `Results`: all numbered axioms and the countermodel conclusions together.

The proof of (t33) under restricted bearer typing stays in Section3_10.
Some additional restriction is necessary for (t16). Its current proof uses
non-sortal upward closure, but we do not establish that this is the weakest
sufficient assumption.
-/

namespace StructuralAssumptions

/-- The conclusion of (t16), shared by the positive application and countermodel.
The application of `th_t16` below checks that this is the core theorem's conclusion. -/
def T16 (S : UFOSignature3_4) : Prop :=
  ∀ t x w, S.NonSortal t w ∧ S.Inst x t w →
    (∃ s, S.Sortal s w ∧ S.Sub s t w ∧ S.Inst x s w) ∨
    (∃ n s, S.NonSortal n w ∧ S.Sortal s w ∧
      S.Sub s n w ∧ S.Sub t n w ∧ S.Inst x s w)

section KindChecks

-- These applications keep the numbered conclusions and premises explicit.
-- If a proof starts requiring an extra assumption, the application fails to
-- compile instead of silently accepting a stronger theorem hypothesis.
variable (Sig : UFOSignature3_2)

example (h18 : ax_a18 Sig) (h22 : ax_a22 Sig) (h26 : ax_a26 Sig) :
    ∀ x y w, Sig.Kind x w ∧ Sig.Kind y w ∧ x ≠ y →
      Frame.Box (F := Sig.F) (fun v => ¬ ∃ z, Sig.Inst z x v ∧ Sig.Inst z y v) w :=
  th_t10 Sig h18 h22 h26

example (h1 : ax_a1 Sig.toUFOSignature3_1)
    (h5 : ax_a5 Sig.toUFOSignature3_1) (h15 : ax_a15 Sig.toUFOSignature3_1)
    (h18 : ax_a18 Sig) (h22 : ax_a22 Sig) (h23 : ax_a23 Sig) (h26 : ax_a26 Sig) :
    ∀ x y w, Sig.Kind x w ∧ Sig.Kind y w ∧ x ≠ y →
      (¬ Sig.Sub x y w ∧ ¬ Sig.Sub y x w) :=
  th_t11 Sig h1 h5 h15 h23 h26 h22 h18

example (h1 : ax_a1 Sig.toUFOSignature3_1) (h5 : ax_a5 Sig.toUFOSignature3_1)
    (h18 : ax_a18 Sig) (h22 : ax_a22 Sig) (h26 : ax_a26 Sig) :
    ∀ w, ¬ ∃ x y z, Sig.Kind y w ∧ Sig.Kind z w ∧ y ≠ z ∧
      Sig.Sub x y w ∧ Sig.Sub x z w :=
  th_t14 Sig h1 h5 h22 h18 h26

-- The package supplies every premise of kind stability through its numbered
-- axioms. In particular, the endurant-type clause of (a44) supplies typing.
example (Sig4 : UFOSignature3_4) [h : UFOAxioms3_4 Sig4] :
    ∀ k w v, Sig4.F.R w v → (Sig4.Kind k w ↔ Sig4.Kind k v) :=
  kind_stable Sig4 h.ax1 h.ax18 h.ax21 h.ax22 h.ax26 h.ax44.1

end KindChecks

section TypingChecks

-- The two former typing assumptions are consequences of numbered axioms.
-- Applying their proofs here checks the justification for removing their
-- separate axiom fields. The reusable derivations remain in Section3_4.
variable (Sig : UFOSignature3_4)

example (h44 : ax_a44_endurantType Sig) :
    ∀ t x w, Sig.EndurantType t w → Sig.Inst x t w → Sig.Endurant x w :=
  inst_endurant_of_a44 Sig h44

example (h5 : ax_a5 Sig.toUFOSignature3_1) (h23 : ax_a23 Sig.toUFOSignature3_2)
    (h26 : ax_a26 Sig.toUFOSignature3_2) (h44 : ax_a44_endurantType Sig) :
    ∀ a k w, Sig.Sub a k w → Sig.Kind k w → Sig.Sortal a w :=
  sub_kind_is_sortal Sig h5 h23 h26 h44

-- The §3.4 axioms suffice for this application of (t16). Its proof also uses
-- the retained assumption that supertypes of non-sortals are non-sortals.
example [h : UFOAxioms3_4 Sig] : T16 Sig :=
  th_t16 Sig h.ax5 h.ax6 h.ax21 h.ax23 h.ax24 h.ax26 h.ax44.1 h.ax_nonSortal_up

example (S : UFOSignature3_2) (h5 : ax_a5 S.toUFOSignature3_1)
    (h23 : ax_a23 S) (h24 : ax_a24 S) {a b : S.Thing} {w : S.F.World}
    (ha : S.NonSortal a w) (hab : S.Sub a b w) (hb : S.EndurantType b w) :
    S.NonSortal b w :=
  nonSortal_supertype_of_endurantType S h5 h23 h24 ha hab hb

end TypingChecks

end StructuralAssumptions

namespace StructuralAssumptions.NonSortalClosure

/- This model refutes (t16) as well as non-sortal upward closure. It has nine
entities at one world: kinds 0 and 1, category 2, mixed type 3, objects 4–7,
and abstract individual 8. Their instances are:

  kind 0: {4, 5}      kind 1: {6, 7}
  category 2: {4, 6}  mixed type 3: {4, 5, 6, 7, 8}

The category crosses the two kinds. For its instance 4, the only candidate
sortal in (t16) is kind 0. That kind has an instance outside the category, so
the first alternative fails. Their only common supertype is the mixed type.
Its abstract instance prevents endurant-type status by (a44), hence non-sortal
status by (a24). The second alternative therefore fails too. Axiom (a6) still
holds: it requires a common supertype without requiring non-sortal status. -/
private def inst (x t : Fin 9) : Prop :=
  ((x = 4 ∨ x = 5) ∧ (t = 0 ∨ t = 3)) ∨
  ((x = 6 ∨ x = 7) ∧ (t = 1 ∨ t = 3)) ∨
  ((x = 4 ∨ x = 6) ∧ t = 2) ∨ (x = 8 ∧ t = 3)

def sig : UFOSignature3_4 where
  F := {
    World := Unit
    R := fun _ _ => True
    refl := fun _ => True.intro
    symm := fun _ => True.intro
    trans := fun _ _ => True.intro }
  Thing := Fin 9
  thing_nonempty := ⟨0⟩
  Type_ := fun t _ => t < 4
  Individual := fun x _ => 4 ≤ x
  Inst := fun x t _ => inst x t
  Sub := fun a b _ => a < 4 ∧ b < 4 ∧ ∀ x, inst x a → inst x b
  ConcreteIndividual := fun x _ => 4 ≤ x ∧ x < 8
  AbstractIndividual := fun x _ => x = 8
  Endurant := fun x _ => 4 ≤ x ∧ x < 8
  Perdurant := fun _ _ => False
  EndurantType := fun t _ => t < 3
  PerdurantType := fun _ _ => False
  Rigid := fun t _ => t < 3
  AntiRigid := fun _ _ => False
  SemiRigid := fun _ _ => False
  Kind := fun t _ => t < 2
  Sortal := fun t _ => t < 2
  NonSortal := fun t _ => t = 2
  SubKind := fun _ _ => False
  Phase := fun _ _ => False
  Role := fun _ _ => False
  SemiRigidSortal := fun _ _ => False
  Category := fun t _ => t = 2
  Mixin := fun _ _ => False
  PhaseMixin := fun _ _ => False
  RoleMixin := fun _ _ => False
  Substantial := fun x _ => 4 ≤ x ∧ x < 8
  Moment := fun _ _ => False
  Object := fun x _ => 4 ≤ x ∧ x < 8
  Collective := fun _ _ => False
  Quantity := fun _ _ => False
  Relator := fun _ _ => False
  IntrinsicMoment := fun _ _ => False
  Mode := fun _ _ => False
  QualityKind := fun _ _ => False
  SubstantialType := fun t _ => t < 3
  MomentType := fun _ _ => False
  ObjectType := fun t _ => t < 3
  CollectiveType := fun _ _ => False
  QuantityType := fun _ _ => False
  RelatorType := fun _ _ => False
  ModeType := fun _ _ => False
  QualityType := fun _ _ => False
  ObjectKind := fun t _ => t < 2
  CollectiveKind := fun _ _ => False
  QuantityKind := fun _ _ => False
  RelatorKind := fun _ _ => False
  ModeKind := fun _ _ => False

-- Unfold the semantic definitions and enumerate the finite domain. All resulting
-- proof terms are checked by the kernel.
local macro "verify_nonSortalClosure" : tactic =>
  `(tactic| (
    delta ax_a1 ax_a2 ax_a3 ax_a4 ax_a5 ax_a6 ax_a7 ax_a8 ax_a9 ax_a10 ax_a11 ax_a12 ax_a13
      ax_a14 ax_a15 ax_a16 ax_a17 ax_a18 ax_a19 ax_a20 ax_a21 ax_a22 ax_a23 ax_a24 ax_a25 ax_a26
      ax_a27 ax_a28 ax_a29 ax_a30 ax_a31 ax_a32 ax_a33 ax_a34 ax_a35 ax_a36 ax_a37 ax_a38 ax_a39
      ax_a40 ax_a41 ax_a42 ax_a43 ax_a44 ax_a45 ax_a46 ax_nonSortal_upward Quality Frame.Box
      Frame.Dia sig inst ax_a44_endurantType ax_a44_perdurantType ax_a44_substantialType
      ax_a44_momentType ax_a44_objectType ax_a44_collectiveType ax_a44_quantityType
      ax_a44_relatorType ax_a44_modeType ax_a44_qualityType ax_a45_objectKind
      ax_a45_collectiveKind ax_a45_quantityKind ax_a45_relatorKind ax_a45_modeKind
      ax_a45_qualityKind
    simp [Fin.forall_fin_succ, Fin.exists_fin_succ]))

/-- The complete numbered §3.1 package holds. -/
theorem numbered_3_1 : UFOAxioms3_1 sig.toUFOSignature3_1 where
  ax1 := by verify_nonSortalClosure
  ax2 := by verify_nonSortalClosure
  ax3 := by verify_nonSortalClosure
  ax4 := by verify_nonSortalClosure
  ax5 := by verify_nonSortalClosure
  ax6 := by verify_nonSortalClosure
  ax7 := by verify_nonSortalClosure
  ax8 := by verify_nonSortalClosure
  ax9 := by verify_nonSortalClosure
  ax10 := by verify_nonSortalClosure
  ax11 := by verify_nonSortalClosure
  ax12 := by verify_nonSortalClosure
  ax13 := by verify_nonSortalClosure
  ax14 := by verify_nonSortalClosure
  ax15 := by verify_nonSortalClosure
  ax16 := by verify_nonSortalClosure
  ax17 := by verify_nonSortalClosure

/-- All numbered axioms of §3.2 hold, without the added closure field. -/
theorem numbered_3_2 :
    ax_a18 sig.toUFOSignature3_2 ∧ ax_a19 sig.toUFOSignature3_2 ∧
    ax_a20 sig.toUFOSignature3_2 ∧ ax_a21 sig.toUFOSignature3_2 ∧
    ax_a22 sig.toUFOSignature3_2 ∧ ax_a23 sig.toUFOSignature3_2 ∧
    ax_a24 sig.toUFOSignature3_2 ∧ ax_a25 sig.toUFOSignature3_2 ∧
    ax_a26 sig.toUFOSignature3_2 ∧ ax_a27 sig.toUFOSignature3_2 ∧
    ax_a28 sig.toUFOSignature3_2 ∧ ax_a29 sig.toUFOSignature3_2 ∧
    ax_a30 sig.toUFOSignature3_2 ∧ ax_a31 sig.toUFOSignature3_2 ∧
    ax_a32 sig.toUFOSignature3_2 ∧ ax_a33 sig.toUFOSignature3_2 := by verify_nonSortalClosure

/-- All numbered axioms of §3.3 hold. -/
theorem numbered_3_3 :
    ax_a34 sig.toUFOSignature3_3 ∧ ax_a35 sig.toUFOSignature3_3 ∧
    ax_a36 sig.toUFOSignature3_3 ∧ ax_a37 sig.toUFOSignature3_3 ∧
    ax_a38 sig.toUFOSignature3_3 ∧ ax_a39 sig.toUFOSignature3_3 ∧
    ax_a40 sig.toUFOSignature3_3 ∧ ax_a41 sig.toUFOSignature3_3 ∧
    ax_a42 sig.toUFOSignature3_3 ∧ ax_a43 sig.toUFOSignature3_3 := by verify_nonSortalClosure

/-- The (a44) and (a45) schemas and (a46) hold. -/
theorem numbered_3_4 : ax_a44 sig ∧ ax_a45 sig ∧ ax_a46 sig := by verify_nonSortalClosure

/-- The category specializes a mixed type, which is not a non-sortal.
Thus the added closure does not follow from (a1)–(a46). -/
theorem not_nonSortal_upward :
    ¬ ax_nonSortal_upward (Sig := sig.toUFOSignature3_2) := by verify_nonSortalClosure

/-- The category's instance 4 satisfies neither alternative of (t16).
Thus removing closure loses the theorem, not just this particular proof of it. -/
theorem not_t16 : ¬ T16 sig := by
  intro h
  have bad := h (2 : Fin 9) (4 : Fin 9) () ⟨rfl, by simp [sig, inst]⟩
  simp [sig, inst, Fin.exists_fin_succ, Fin.forall_fin_succ] at bad

end StructuralAssumptions.NonSortalClosure

namespace StructuralAssumptions

/-! ## Extending the countermodels through §4

Both models have no qualities. Empty quality structures and characterization
satisfy §§3.11–3.12. The remaining relations use the defining formulas from
§§3.13–4, so neither extension changes the earlier predicates.

An early-section countermodel alone cannot exclude a derivation from later
axioms. This extension closes that gap. Empty predicates are sufficient here
because these later axioms do not require a quality or characterization to
exist in either model. Where an axiom defines a relation by an equivalence,
we interpret that relation by its right-hand side rather than assume it empty.
This preserves equivalences that can hold even when some classes are empty.
-/

namespace EmptyLaterSections

def extend (S : UFOSignature3_10) : UFOSignature4 where
  toUFOSignature3_10 := S
  Characterization := fun _ _ _ => False
  Quale := fun _ _ => False
  Set_ := fun _ _ => False
  SetExtension := fun _ _ => ∅
  QualityDomain := fun _ _ => False
  QualityDimension := fun _ _ => False
  AssociatedWith := fun _ _ _ => False
  IntrinsicMomentType := fun _ _ => False
  HasValue := fun _ _ _ => False
  TupleProjection := fun p _ _ => p
  Distance := fun _ _ _ _ => False
  DistanceZero := fun _ _ => False
  DistanceSum := fun _ _ _ _ => False
  DistanceGreaterEq := fun _ _ _ => False
  Manifests := fun _ _ _ => False
  LifeOf := fun x y w => S.Perdurant x w ∧ S.Endurant y w ∧
    ∀ z, S.Overlap z x w ↔ S.Perdurant z w ∧ False
  Meet := fun _ _ _ => False
  IsDisjointWith := fun t u w => S.Type_ t w ∧ S.Type_ u w ∧
    ¬ ∃ x, S.Inst x t w ∧ S.Inst x u w
  IsCompletelyCoveredBy := fun t u v w => ∀ x, S.Inst x t w → S.Inst x u w ∨ S.Inst x v w
  IsPartitionedInto := fun t u v w =>
    (∀ x, S.Inst x t w → S.Inst x u w ∨ S.Inst x v w) ∧
    (S.Type_ u w ∧ S.Type_ v w ∧ ¬ ∃ x, S.Inst x u w ∧ S.Inst x v w)
  Categorizes := fun t u w => S.Type_ t w ∧ ∀ x, S.Inst x t w →
    ProperSub S.toUFOSignature3_1 x u w

variable (S : UFOSignature3_10)
variable (hQT : ∀ t w, ¬ S.QualityType t w) (hQK : ∀ t w, ¬ S.QualityKind t w)

theorem a81 : ax_a81 (extend S).toUFOSignature3_11 := by
  simp [ax_a81, extend]

theorem a82 : ax_a82 (extend S).toUFOSignature3_11 := by
  simp [ax_a82, extend]

theorem a83 : ax_a83 (extend S).toUFOSignature3_12 := by
  simp [ax_a83, extend]

theorem a84 : ax_a84 (extend S).toUFOSignature3_12 := by
  simp [ax_a84, extend]

theorem a85 : ax_a85 (extend S).toUFOSignature3_12 := by
  simp [ax_a85, extend]

theorem a86 : ax_a86 (extend S).toUFOSignature3_12 := by
  simp [ax_a86, extend, QualityStructure]

theorem a87 : ax_a87 (extend S).toUFOSignature3_12 := by
  simp [ax_a87, extend, QualityStructure]

theorem a88 : ax_a88 (extend S).toUFOSignature3_12 := by
  simp [ax_a88, extend, QualityStructure]

theorem a89 : ax_a89 (extend S).toUFOSignature3_12 := by
  simp [ax_a89, extend]

theorem a90 : ax_a90 (extend S).toUFOSignature3_12 := by
  simp [ax_a90, extend]

theorem a91 (hQT : ∀ t w, ¬ S.QualityType t w) : ax_a91 (extend S).toUFOSignature3_12 := by
  simp [ax_a91, extend, QualityStructure, hQT]

theorem a92 : ax_a92 (extend S).toUFOSignature3_12 := by
  simp [ax_a92, extend]

theorem a93 (hQK : ∀ t w, ¬ S.QualityKind t w) : ax_a93 (extend S).toUFOSignature3_12 := by
  simp [ax_a93, extend, Quality, hQK]

theorem a94 : ax_a94 (extend S).toUFOSignature3_12 := by
  simp [ax_a94, extend]

theorem a95 : ax_a95 (extend S).toUFOSignature3_12 := by
  simp [ax_a95, extend]

theorem a96 : ax_a96 (extend S).toUFOSignature3_12 := by
  simp [ax_a96, extend]

theorem a97 (hQK : ∀ t w, ¬ S.QualityKind t w) : ax_a97 (extend S).toUFOSignature3_12 := by
  simp [ax_a97, extend, ComplexQuality, Quality, hQK]

theorem a98 (hQK : ∀ t w, ¬ S.QualityKind t w) : ax_a98 (extend S).toUFOSignature3_12 := by
  simp [ax_a98, extend, ComplexQuality, Quality, hQK]

theorem a99 : ax_a99 (extend S).toUFOSignature3_12 := by
  simp [ax_a99, extend]

theorem a100 : ax_a100 (extend S).toUFOSignature3_12 := by
  simp [ax_a100, extend]

theorem a101 : ax_a101 (extend S).toUFOSignature3_12 := by
  simp [ax_a101, extend]

theorem a102 : ax_a102 (extend S).toUFOSignature3_13 := by
  simp [ax_a102, extend]

theorem a103 : ax_a103 (extend S).toUFOSignature3_13 := by
  intro x y w; rfl

theorem a104 : ax_a104 (extend S).toUFOSignature3_13 := by
  simp [ax_a104, extend]

theorem a105 : ax_a105 (extend S) := by
  intro x y w; rfl

theorem a106 : ax_a106 (extend S) := by
  intro x y z w; rfl

theorem a107 : ax_a107 (extend S) := by
  intro x y z w; rfl

theorem a108 : ax_a108 (extend S) := by
  intro x y w; rfl

theorem distance_identity : ax_distance_identity (extend S).toUFOSignature3_12 := by
  simp [ax_distance_identity, extend]

theorem distance_symmetry : ax_distance_symmetry (extend S).toUFOSignature3_12 := by
  simp [ax_distance_symmetry, extend]

theorem distance_triangle : ax_distance_triangle (extend S).toUFOSignature3_12 := by
  simp [ax_distance_triangle, extend]

end EmptyLaterSections

/-! ## Non-sortal closure: extension beyond §3.4

Identity parthood and empty moments, constitution, and relators extend the
nine-entity countermodel. The other added assumption holds vacuously.

These choices preserve the taxonomy responsible for the counterexample.
Identity parthood has no proper parts, so supplementation is satisfied and
the relator definition (a79) does not force a relator. The qua-individual
typing assumption is true because there are no qua individuals. Thus removing
that second assumption is not needed to make non-sortal closure fail.
-/

namespace NonSortalExtension
open StructuralAssumptions.NonSortalClosure
def extended : UFOSignature3_10 where
  toUFOSignature3_4 := sig
  Part := fun x y _ => x = y
  Overlap := fun x y _ => x = y
  ProperPart := fun _ _ _ => False
  FunctionsAs := fun _ _ _ => False
  GenericFunctionalDependence := fun _ _ _ => True
  IndividualFunctionalDependence := fun x t y u w => sig.Inst x t w ∧ sig.Inst y u w
  ComponentOf := fun _ _ _ _ _ => False
  Ex := fun _ _ => True
  ConstitutedBy := fun _ _ _ => False
  GenericConstitutionalDependence := fun t _ w => ∀ x, ¬ sig.Inst x t w
  Constitution := fun _ _ _ _ _ => False
  ExistentialDependence := fun _ _ _ => True
  ExistentialIndependence := fun _ _ _ => False
  InheresIn := fun _ _ _ => False
  ExternallyDependent := fun _ _ _ => True
  ExternallyDependentMode := fun _ _ => False
  FoundedBy := fun _ _ _ => False
  QuaIndividualOf := fun _ _ _ => False
  QuaIndividual := fun _ _ => False
  Mediates := fun _ _ _ => False

theorem a47 : ax_a47 extended.toUFOSignature3_5 := by
  simp [ax_a47, extended, sig]

theorem a48 : ax_a48 extended.toUFOSignature3_5 := by
  simp [ax_a48, extended, sig]

theorem a49 : ax_a49 extended.toUFOSignature3_5 := by
  simp [ax_a49, extended, sig]

theorem a50 : ax_a50 extended.toUFOSignature3_5 := by
  simp [ax_a50, extended, sig]

theorem a51 : ax_a51 extended.toUFOSignature3_5 := by
  simp [ax_a51, extended, sig]

theorem a52 : ax_a52 extended.toUFOSignature3_5 := by
  simp [ax_a52, extended, sig]

theorem a53 : ax_a53 extended.toUFOSignature3_6 := by
  simp [ax_a53, extended, sig]

theorem a54 : ax_a54 extended.toUFOSignature3_6 := by
  simp [ax_a54, extended, sig]

theorem a55 : ax_a55 extended.toUFOSignature3_6 := by
  simp [ax_a55, extended, sig]

theorem a56 : ax_a56 extended.toUFOSignature3_7 := by
  simp [ax_a56, extended, sig]

theorem a57 : ax_a57 extended.toUFOSignature3_7 := by
  simp [ax_a57, extended, sig]

theorem a58 : ax_a58 extended.toUFOSignature3_7 := by
  simp [ax_a58, extended, sig]

theorem a59 : ax_a59 extended.toUFOSignature3_7 := by
  simp [ax_a59, extended, sig]

theorem a60 : ax_a60 extended.toUFOSignature3_7 := by
  simp [ax_a60, extended, sig, Frame.Box]

theorem a61 : ax_a61 extended.toUFOSignature3_7 := by
  simp [ax_a61, extended, sig]

theorem a62 : ax_a62 extended.toUFOSignature3_8 := by
  simp [ax_a62, extended, sig]

theorem a63 : ax_a63 extended.toUFOSignature3_8 := by
  simp [ax_a63, extended, sig, Frame.Box]

theorem a64 : ax_a64 extended.toUFOSignature3_8 := by
  simp [ax_a64, extended, sig]

theorem a65 : ax_a65 extended.toUFOSignature3_9 := by
  simp [ax_a65, extended, sig]

theorem a66 : ax_a66 extended.toUFOSignature3_9 := by
  simp [ax_a66, extended, sig]

theorem a67 : ax_a67 extended.toUFOSignature3_9 := by
  simp [ax_a67, extended, sig]

theorem a68 : ax_a68 extended.toUFOSignature3_9 := by
  simp [ax_a68, extended, sig]

theorem a69 : ax_a69 extended := by
  simp [ax_a69, extended, sig]

theorem a70 : ax_a70 extended := by
  simp [ax_a70, extended, sig]

theorem a71 : ax_a71 extended := by
  simp [ax_a71, extended, sig]

theorem a72 : ax_a72 extended := by
  simp [ax_a72, extended, sig]

theorem a73 : ax_a73 extended := by
  simp [ax_a73, extended, sig]

theorem a74 : ax_a74 extended := by
  simp [ax_a74, extended, sig]

theorem a75 : ax_a75 extended := by
  simp [ax_a75, extended, sig]

theorem a76 : ax_a76 extended := by
  simp [ax_a76, extended, sig]

theorem a77 : ax_a77 extended := by
  simp [ax_a77, extended, sig]

theorem a78 : ax_a78 extended := by
  simp [ax_a78, extended, sig]

theorem a79 : ax_a79 extended := by
  simp [ax_a79, extended, sig]

theorem a80 : ax_a80 extended := by
  simp [ax_a80, extended, sig]

theorem qua_typing : ax_quaIndividualOf_endurant (Sig := extended) := by
  intro x y w h
  exact False.elim h
end NonSortalExtension

/-! ## Qua-individual bearer typing: countermodel

The domain and taxonomy come from the positive relator model. The qua
individuals now inhere in `objectKind` and `modeKind`, both types rather than
endurants. Their existence at worlds follows the former bearers' pattern,
preserving the required dependence and independence relations. The encoded
axioms do not identify existence (`Ex`) with type classification.

The relator has two qua-individual proper parts but mediates no endurants.
This refutes both the global bearer-typing assumption and (t33).
-/

namespace QuaBearerCountermodel.Model3_7

open Relator.Model3_1

/-- The new type bearers must sometimes exist without the external object,
and the external object must sometimes exist without them. Those worlds
witness the independence required by (a69). Keeping the types existent at
every world would destroy that independence. The earlier taxonomy is unchanged:
the axioms do not equate type classification with the predicate `Ex`. -/
def ex : Thing -> World -> Prop
  | .relator, .actual | .quaA, .actual | .quaB, .actual => True
  | .bearerA, .actual | .bearerA, .bearerA => True
  | .bearerB, .actual | .bearerB, .bearerB => True
  | .external, .actual | .external, .external => True
  | .foundation, .actual => True
  | .objectKind, .actual | .objectKind, .bearerA => True
  | .modeKind, .actual | .modeKind, .bearerB => True
  | .relatorKind, _ | .perdurantKind, _ => True
  | _, _ => False

def sig : UFOSignature3_7 where
  toUFOSignature3_6 := Relator.Model3_6.sig
  Ex := fun x w => ex x w
  ConstitutedBy := fun _ _ _ => False
  GenericConstitutionalDependence := fun x' y' w =>
    forall x, Relator.Model3_6.sig.Inst x x' w ->
      exists y, Relator.Model3_6.sig.Inst y y' w ∧ False
  Constitution := fun x x' y y' w =>
    Relator.Model3_6.sig.Inst x x' w ∧
      Relator.Model3_6.sig.Inst y y' w ∧
      (forall u, Relator.Model3_6.sig.Inst u x' w ->
        exists v, Relator.Model3_6.sig.Inst v y' w ∧ False) ∧
      False

attribute [simp] ex sig

theorem ax56_sig : ax_a56 sig := by
  intro x y w h
  simp [sig] at h

theorem ax57_sig : ax_a57 sig := by
  intro x y x' y' w h
  simp [sig] at h

theorem ax58_sig : ax_a58 sig := by intro x' y' w; rfl

theorem ax59_sig : ax_a59 sig := by intro x x' y y' w; rfl

theorem ax60_sig : ax_a60 sig := by
  intro x y w h
  simp [sig] at h

theorem ax61_sig : ax_a61 sig := by
  intro x y w h
  simp [sig] at h

instance : UFOAxioms3_7 sig where
  toUFOAxioms3_6 := by
    change UFOAxioms3_6 Relator.Model3_6.sig
    infer_instance
  ax56 := ax56_sig
  ax57 := ax57_sig
  ax58 := ax58_sig
  ax59 := ax59_sig
  ax60 := ax60_sig
  ax61 := ax61_sig

end QuaBearerCountermodel.Model3_7

namespace QuaBearerCountermodel.Model3_8

/-- Dependence must be recomputed after changing existence at worlds.
Using the formulas from (a63) and (a64) ensures that the countermodel cannot
obtain the desired dependence facts by assigning them arbitrarily. -/
def sig : UFOSignature3_8 where
  toUFOSignature3_7 := Model3_7.sig
  ExistentialDependence := fun x y w =>
    Frame.Box (F := Model3_7.sig.F)
      (fun w' => Model3_7.sig.Ex x w' -> Model3_7.sig.Ex y w') w
  ExistentialIndependence := fun x y w =>
    (¬ Frame.Box (F := Model3_7.sig.F)
      (fun w' => Model3_7.sig.Ex x w' -> Model3_7.sig.Ex y w') w) ∧
    (¬ Frame.Box (F := Model3_7.sig.F)
      (fun w' => Model3_7.sig.Ex y w' -> Model3_7.sig.Ex x w') w)

attribute [simp] sig

theorem ax62_sig : ax_a62 sig := by intro x w h; trivial

theorem ax63_sig : ax_a63 sig := by intro x y w; rfl

theorem ax64_sig : ax_a64 sig := by intro x y w; rfl

instance : UFOAxioms3_8 sig where
  toUFOAxioms3_7 := by
    change UFOAxioms3_7 Model3_7.sig
    infer_instance
  ax62 := ax62_sig
  ax63 := ax63_sig
  ax64 := ax64_sig

end QuaBearerCountermodel.Model3_8

namespace QuaBearerCountermodel.Model3_9

open Relator.Model3_1

/-- Axiom (a66) explicitly permits a type as an inherence target. Choosing
types tests whether other axioms nevertheless force endurant bearers.
Each target has no outgoing inherence edge and is not a moment, so it remains
a unique ultimate bearer as required by (a68). -/
def inheresIn : Thing -> Thing -> Prop
  | .relator, .objectKind | .quaA, .objectKind | .quaB, .modeKind => True
  | _, _ => False

def sig : UFOSignature3_9 where
  toUFOSignature3_8 := Model3_8.sig
  InheresIn := fun x y _ => inheresIn x y

attribute [simp] inheresIn sig

theorem ax65_sig : ax_a65 sig := by
  intro x y w h
  change inheresIn x y at h
  cases x <;> cases y <;> simp [inheresIn] at h
  all_goals
    intro w' _hAccessible hEx
    cases w' <;> simp_all [Model3_7.ex]

theorem ax66_sig : ax_a66 sig := by
  intro x y w h
  change inheresIn x y at h
  cases x <;> cases y <;> simp_all [inheresIn]

theorem ax67_sig : ax_a67 sig := by
  intro x y z w h
  change inheresIn x y ∧ inheresIn x z at h
  cases x <;> cases y <;> cases z <;> simp_all [inheresIn]

private theorem objectKind_terminal (w : World) :
    forall y, ¬ sig.InheresIn .objectKind y w := by
  intro y
  cases y <;> simp [sig, inheresIn]

private theorem modeKind_terminal (w : World) :
    forall y, ¬ sig.InheresIn .modeKind y w := by
  intro y
  cases y <;> simp [sig, inheresIn]

/-- Every inherence path has just one edge in this model. The path uniqueness
lemma rules out additional ultimate bearers, including ones that a longer
chain could otherwise reach. -/
theorem ax68_sig : ax_a68 sig := by
  intro m w hMoment
  change Relator.Model3_3.moment m at hMoment
  cases m <;> simp [Relator.Model3_3.moment] at hMoment
  · refine ⟨.objectKind, ⟨by simp, .direct (by simp [sig, inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .objectKind) (x := b)
      (by intro y h; cases y <;> simp_all [sig, inheresIn])
      (objectKind_terminal w) hb.2
  · refine ⟨.objectKind, ⟨by simp, .direct (by simp [sig, inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .objectKind) (x := b)
      (by intro y h; cases y <;> simp_all [sig, inheresIn])
      (objectKind_terminal w) hb.2
  · refine ⟨.modeKind, ⟨by simp, .direct (by simp [sig, inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .modeKind) (x := b)
      (by intro y h; cases y <;> simp_all [sig, inheresIn])
      (modeKind_terminal w) hb.2

instance : UFOAxioms3_9 sig where
  toUFOAxioms3_8 := by
    change UFOAxioms3_8 Model3_8.sig
    infer_instance
  ax65 := ax65_sig
  ax66 := ax66_sig
  ax67 := ax67_sig
  ax68 := ax68_sig

end QuaBearerCountermodel.Model3_9

namespace QuaBearerCountermodel.Model3_10

open Relator.Model3_1

def foundedBy : Thing -> Thing -> Prop
  | .relator, .foundation | .quaA, .foundation | .quaB, .foundation => True
  | _, _ => False

def quaIndividualOf : Thing -> Thing -> Prop
  | .quaA, .objectKind | .quaB, .modeKind => True
  | _, _ => False

def quaIndividual : Thing -> Prop
  | .quaA | .quaB => True
  | _ => False

def externallyDependentMode : Thing -> Prop
  | .quaA | .quaB => True
  | _ => False

def sig : UFOSignature3_10 where
  toUFOSignature3_9 := Model3_9.sig
  ExternallyDependent := fun x y w =>
    Model3_9.sig.ExistentialDependence x y w ∧
      forall z, Model3_9.sig.InheresIn x z w ->
        Model3_9.sig.ExistentialIndependence y z w
  ExternallyDependentMode := fun x _ => externallyDependentMode x
  FoundedBy := fun x y _ => foundedBy x y
  QuaIndividualOf := fun x y _ => quaIndividualOf x y
  QuaIndividual := fun x _ => quaIndividual x
  Mediates := fun x y w =>
    Model3_9.sig.Relator x w ∧
      Model3_9.sig.Endurant y w ∧
      exists z, quaIndividualOf z y ∧ Model3_9.sig.Part z x w

attribute [simp] foundedBy quaIndividualOf quaIndividual externallyDependentMode

theorem ax69_sig : ax_a69 sig := by intro x y w; rfl

private theorem external_independent_objectKind (w : World) :
    sig.ExistentialIndependence .external .objectKind w := by
  change
    (¬ Frame.Box (F := Relator.Model3_1.frame)
      (fun w' => Model3_7.ex .external w' -> Model3_7.ex .objectKind w') w) ∧
    (¬ Frame.Box (F := Relator.Model3_1.frame)
      (fun w' => Model3_7.ex .objectKind w' -> Model3_7.ex .external w') w)
  constructor
  · intro h
    exact h .external trivial (by simp [Model3_7.ex])
  · intro h
    exact h .bearerA trivial (by simp [Model3_7.ex])

private theorem external_independent_modeKind (w : World) :
    sig.ExistentialIndependence .external .modeKind w := by
  change
    (¬ Frame.Box (F := Relator.Model3_1.frame)
      (fun w' => Model3_7.ex .external w' -> Model3_7.ex .modeKind w') w) ∧
    (¬ Frame.Box (F := Relator.Model3_1.frame)
      (fun w' => Model3_7.ex .modeKind w' -> Model3_7.ex .external w') w)
  constructor
  · intro h
    exact h .external trivial (by simp [Model3_7.ex])
  · intro h
    exact h .bearerB trivial (by simp [Model3_7.ex])

private theorem quaA_externallyDependent_external (w : World) :
    sig.ExternallyDependent .quaA .external w := by
  constructor
  · intro w' _ hEx
    cases w' <;> simp_all [Model3_7.ex]
  · intro z hInheres
    change Model3_9.inheresIn .quaA z at hInheres
    cases z <;> simp_all [Model3_9.inheresIn]
    exact external_independent_objectKind w

private theorem quaB_externallyDependent_external (w : World) :
    sig.ExternallyDependent .quaB .external w := by
  constructor
  · intro w' _ hEx
    cases w' <;> simp_all [Model3_7.ex]
  · intro z hInheres
    change Model3_9.inheresIn .quaB z at hInheres
    cases z <;> simp_all [Model3_9.inheresIn]
    exact external_independent_modeKind w

theorem ax70_sig : ax_a70 sig := by
  intro x w
  cases x <;> simp [sig, externallyDependentMode, Relator.Model3_3.mode]
  · exact ⟨.external, quaA_externallyDependent_external w⟩
  · exact ⟨.external, quaB_externallyDependent_external w⟩

theorem externallyDependentMode_iff (x : Thing) (w : World) :
    sig.ExternallyDependentMode x w ↔ x = .quaA ∨ x = .quaB := by
  cases x <;> simp [sig, externallyDependentMode]

theorem properPart_relator_iff (x : Thing) (w : World) :
    sig.ProperPart x .relator w ↔ x = .quaA ∨ x = .quaB := by
  change (Relator.Model3_5.part x .relator ∧ ¬ Relator.Model3_5.part .relator x) ↔ _
  cases x <;> simp [Relator.Model3_5.part]

theorem quaIndividual_iff (x : Thing) (w : World) :
    sig.QuaIndividual x w ↔ x = .quaA ∨ x = .quaB := by
  change quaIndividual x ↔ _
  cases x <;> simp [quaIndividual]

private theorem qua_dependence
    {x y : Thing} (hx : x = .quaA ∨ x = .quaB)
    (hy : y = .quaA ∨ y = .quaB) (w : World) :
    sig.ExistentialDependence x y w := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  all_goals
    intro w' _ hEx
    cases w' <;> simp_all [Model3_7.ex]

theorem ax71_sig : ax_a71 sig := by
  intro x y w h
  change foundedBy x y at h
  change (externallyDependentMode x ∨ Relator.Model3_3.relator x) ∧
    Relator.Model3_1.perdurant y
  cases x <;> cases y <;> simp_all [foundedBy, externallyDependentMode,
    Relator.Model3_3.relator, Relator.Model3_1.perdurant]

private theorem unique_foundation_quaA (w : World) :
    ∃! y, sig.FoundedBy .quaA y w := by
  refine ⟨.foundation, ?_, ?_⟩
  · change foundedBy .quaA .foundation
    trivial
  · intro y h
    change foundedBy .quaA y at h
    cases y <;> simp_all [foundedBy]
    rfl

private theorem unique_foundation_quaB (w : World) :
    ∃! y, sig.FoundedBy .quaB y w := by
  refine ⟨.foundation, ?_, ?_⟩
  · change foundedBy .quaB .foundation
    trivial
  · intro y h
    change foundedBy .quaB y at h
    cases y <;> simp_all [foundedBy]
    rfl

private theorem unique_foundation_relator (w : World) :
    ∃! y, sig.FoundedBy .relator y w := by
  refine ⟨.foundation, ?_, ?_⟩
  · change foundedBy .relator .foundation
    trivial
  · intro y h
    change foundedBy .relator y at h
    cases y <;> simp_all [foundedBy]
    rfl

theorem ax72_sig : ax_a72 sig := by
  intro x w h
  have hx := (externallyDependentMode_iff x w).1 h
  rcases hx with rfl | rfl
  · exact unique_foundation_quaA w
  · exact unique_foundation_quaB w

@[simp] theorem foundationOf_quaA (w : World) :
    FoundationOf sig .quaA w = .foundation :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_quaA w)).2 (by
    change foundedBy .quaA .foundation
    trivial)

@[simp] theorem foundationOf_quaB (w : World) :
    FoundationOf sig .quaB w = .foundation :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_quaB w)).2 (by
    change foundedBy .quaB .foundation
    trivial)

@[simp] theorem foundationOf_relator (w : World) :
    FoundationOf sig .relator w = .foundation :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_relator w)).2 (by
    change foundedBy .relator .foundation
    trivial)

theorem ax74_sig : ax_a74 sig := by
  intro x w
  cases x <;> simp [sig, quaIndividual, quaIndividualOf]
  · exact ⟨.objectKind, trivial⟩
  · exact ⟨.modeKind, trivial⟩

theorem ax75_sig : ax_a75 sig := by
  intro x w h
  change quaIndividual x at h
  change externallyDependentMode x
  cases x <;> simp_all [quaIndividual, externallyDependentMode]

theorem ax76_sig : ax_a76 sig := by
  intro x y y' w h
  change quaIndividualOf x y ∧ quaIndividualOf x y' at h
  cases x <;> cases y <;> cases y' <;> simp_all [quaIndividualOf]
  all_goals rfl

theorem ax77_sig : ax_a77 sig := by
  intro x w h
  change Relator.Model3_3.relator x at h
  cases x <;> simp_all [Relator.Model3_3.relator]
  exact unique_foundation_relator w

theorem ax78_sig : ax_a78 sig := by
  intro x y w h
  rcases h with ⟨hRel, hPart⟩
  change Relator.Model3_3.relator x at hRel
  cases x <;> simp [Relator.Model3_3.relator] at hRel
  change Relator.Model3_5.part y .relator at hPart
  cases y <;> simp [Relator.Model3_5.part] at hPart
  · rfl
  · exact (foundationOf_relator w).trans (foundationOf_quaA w).symm
  · exact (foundationOf_relator w).trans (foundationOf_quaB w).symm

/-- The altered bearer types must not invalidate the relator itself.
Its two proper parts are still qua individuals with the same foundation and
existence at exactly the same worlds. Conversely, only the relator has proper
parts in this model. This verifies both directions of (a79). -/
theorem ax79_sig : ax_a79 sig := by
  intro x w
  constructor
  · intro hRel
    change Relator.Model3_3.relator x at hRel
    cases x <;> simp [Relator.Model3_3.relator] at hRel
    refine ⟨⟨.quaA, ?_⟩, ?_, ?_⟩
    · change Relator.Model3_5.part .quaA .relator ∧
        ¬ Relator.Model3_5.part .relator .quaA
      simp [Relator.Model3_5.part]
    · intro y z h
      rcases h with ⟨hy, hz⟩
      have hyCases := (properPart_relator_iff y w).1 hy
      have hzCases := (properPart_relator_iff z w).1 hz
      refine ⟨(quaIndividual_iff y w).2 hyCases,
        (quaIndividual_iff z w).2 hzCases, ?_,
        qua_dependence hyCases hzCases w, qua_dependence hzCases hyCases w⟩
      rcases hyCases with rfl | rfl <;> rcases hzCases with rfl | rfl
      all_goals
        first
        | rfl
        | exact (foundationOf_quaA w).trans (foundationOf_quaB w).symm
        | exact (foundationOf_quaB w).trans (foundationOf_quaA w).symm
    · intro y z h
      rcases h with ⟨hy, hzQua, _hFoundation, _hYZ, _hZY⟩
      have hzCases := (quaIndividual_iff z w).1 hzQua
      exact (properPart_relator_iff z w).2 hzCases
  · rintro ⟨⟨y, hy⟩, _hPairwise, _hClosure⟩
    clear _hPairwise _hClosure
    change Relator.Model3_5.part y x ∧ ¬ Relator.Model3_5.part x y at hy
    change Relator.Model3_3.relator x
    cases x <;> cases y <;> simp_all [Relator.Model3_5.part]

theorem ax80_sig : ax_a80 sig := by intro x y w; rfl

/-- The part-based characterization must still hold after changing bearers.
Each qua individual has only itself as a part. In the reverse direction,
self-parthood forces the characterized entity to be an externally dependent
mode inhering in the proposed bearer, leaving exactly the two chosen pairs. -/
theorem ax73_part_sig : ax_a73_part_characterization sig := by
  intro x y w
  constructor
  · intro h
    change quaIndividualOf x y at h
    cases x <;> cases y <;> simp [quaIndividualOf] at h
    · intro z
      change Relator.Model3_5.part z .quaA ↔
        (externallyDependentMode z ∧ Model3_9.inheresIn z .objectKind ∧
          FoundationOf sig z w = FoundationOf sig .quaA w)
      cases z <;> simp [Relator.Model3_5.part, externallyDependentMode,
        Model3_9.inheresIn]
    · intro z
      change Relator.Model3_5.part z .quaB ↔
        (externallyDependentMode z ∧ Model3_9.inheresIn z .modeKind ∧
          FoundationOf sig z w = FoundationOf sig .quaB w)
      cases z <;> simp [Relator.Model3_5.part, externallyDependentMode,
        Model3_9.inheresIn]
  · intro h
    have hSelfPart : sig.Part x x w := Relator.Model3_5.ax47_sig x w
    have hSelf := (h x).1 hSelfPart
    have hEDM := hSelf.1
    have hInheres := hSelf.2.1
    change externallyDependentMode x at hEDM
    change Model3_9.inheresIn x y at hInheres
    change quaIndividualOf x y
    cases x <;> cases y <;> simp_all [externallyDependentMode,
      Model3_9.inheresIn, quaIndividualOf]

/-- A qua individual inheres in a type, which is not an endurant. -/
theorem not_bearer_typing : ¬ ax_quaIndividualOf_endurant (Sig := sig) := by
  intro h
  have bad := h .quaA .objectKind .actual (by trivial)
  exact bad

/-- The relator exists in the model, but none of its qua-individual bearers
is an endurant. Axiom (a80) therefore gives no mediated endurant. -/
theorem not_t33 : ¬ (∀ x w, sig.Relator x w → ∃ y z, y ≠ z ∧ sig.Mediates x y w ∧ sig.Mediates x z w) := by
  intro h
  obtain ⟨y, z, _, hy, _⟩ := h .relator .actual (by trivial)
  obtain ⟨_, he, p, hp, _⟩ := hy
  change quaIndividualOf p y at hp
  change Relator.Model3_1.endurant y at he
  cases p <;> cases y <;> first | exact hp | exact he

end QuaBearerCountermodel.Model3_10

/-! ## Full-axiom results

Each countermodel satisfies all 108 numbered axioms as currently encoded,
the three source distance laws, and the other added assumption. In particular,
(a73) is the corrected part-based formula and (a102) has the corrected argument
order. These results do not concern the inconsistent uncorrected formulas.

We list the numbered axioms separately because `UFOAxioms4` also contains the
two assumptions under investigation. Requiring that whole package would assume
the very fact each countermodel must refute. The distance laws and the other
added assumption are proved separately below, so they are not omitted from
the non-derivability result.
-/

namespace Results

/-- The 108 numbered axioms, without either added assumption. -/
def Numbered (S : UFOSignature4) : Prop :=
  ax_a1 S.toUFOSignature3_1 ∧
  ax_a2 S.toUFOSignature3_1 ∧
  ax_a3 S.toUFOSignature3_1 ∧
  ax_a4 S.toUFOSignature3_1 ∧
  ax_a5 S.toUFOSignature3_1 ∧
  ax_a6 S.toUFOSignature3_1 ∧
  ax_a7 S.toUFOSignature3_1 ∧
  ax_a8 S.toUFOSignature3_1 ∧
  ax_a9 S.toUFOSignature3_1 ∧
  ax_a10 S.toUFOSignature3_1 ∧
  ax_a11 S.toUFOSignature3_1 ∧
  ax_a12 S.toUFOSignature3_1 ∧
  ax_a13 S.toUFOSignature3_1 ∧
  ax_a14 S.toUFOSignature3_1 ∧
  ax_a15 S.toUFOSignature3_1 ∧
  ax_a16 S.toUFOSignature3_1 ∧
  ax_a17 S.toUFOSignature3_1 ∧
  ax_a18 S.toUFOSignature3_2 ∧
  ax_a19 S.toUFOSignature3_2 ∧
  ax_a20 S.toUFOSignature3_2 ∧
  ax_a21 S.toUFOSignature3_2 ∧
  ax_a22 S.toUFOSignature3_2 ∧
  ax_a23 S.toUFOSignature3_2 ∧
  ax_a24 S.toUFOSignature3_2 ∧
  ax_a25 S.toUFOSignature3_2 ∧
  ax_a26 S.toUFOSignature3_2 ∧
  ax_a27 S.toUFOSignature3_2 ∧
  ax_a28 S.toUFOSignature3_2 ∧
  ax_a29 S.toUFOSignature3_2 ∧
  ax_a30 S.toUFOSignature3_2 ∧
  ax_a31 S.toUFOSignature3_2 ∧
  ax_a32 S.toUFOSignature3_2 ∧
  ax_a33 S.toUFOSignature3_2 ∧
  ax_a34 S.toUFOSignature3_3 ∧
  ax_a35 S.toUFOSignature3_3 ∧
  ax_a36 S.toUFOSignature3_3 ∧
  ax_a37 S.toUFOSignature3_3 ∧
  ax_a38 S.toUFOSignature3_3 ∧
  ax_a39 S.toUFOSignature3_3 ∧
  ax_a40 S.toUFOSignature3_3 ∧
  ax_a41 S.toUFOSignature3_3 ∧
  ax_a42 S.toUFOSignature3_3 ∧
  ax_a43 S.toUFOSignature3_3 ∧
  ax_a44 S.toUFOSignature3_4 ∧
  ax_a45 S.toUFOSignature3_4 ∧
  ax_a46 S.toUFOSignature3_4 ∧
  ax_a47 S.toUFOSignature3_5 ∧
  ax_a48 S.toUFOSignature3_5 ∧
  ax_a49 S.toUFOSignature3_5 ∧
  ax_a50 S.toUFOSignature3_5 ∧
  ax_a51 S.toUFOSignature3_5 ∧
  ax_a52 S.toUFOSignature3_5 ∧
  ax_a53 S.toUFOSignature3_6 ∧
  ax_a54 S.toUFOSignature3_6 ∧
  ax_a55 S.toUFOSignature3_6 ∧
  ax_a56 S.toUFOSignature3_7 ∧
  ax_a57 S.toUFOSignature3_7 ∧
  ax_a58 S.toUFOSignature3_7 ∧
  ax_a59 S.toUFOSignature3_7 ∧
  ax_a60 S.toUFOSignature3_7 ∧
  ax_a61 S.toUFOSignature3_7 ∧
  ax_a62 S.toUFOSignature3_8 ∧
  ax_a63 S.toUFOSignature3_8 ∧
  ax_a64 S.toUFOSignature3_8 ∧
  ax_a65 S.toUFOSignature3_9 ∧
  ax_a66 S.toUFOSignature3_9 ∧
  ax_a67 S.toUFOSignature3_9 ∧
  ax_a68 S.toUFOSignature3_9 ∧
  ax_a69 S.toUFOSignature3_10 ∧
  ax_a70 S.toUFOSignature3_10 ∧
  ax_a71 S.toUFOSignature3_10 ∧
  ax_a72 S.toUFOSignature3_10 ∧
  ax_a73 S.toUFOSignature3_10 ∧
  ax_a74 S.toUFOSignature3_10 ∧
  ax_a75 S.toUFOSignature3_10 ∧
  ax_a76 S.toUFOSignature3_10 ∧
  ax_a77 S.toUFOSignature3_10 ∧
  ax_a78 S.toUFOSignature3_10 ∧
  ax_a79 S.toUFOSignature3_10 ∧
  ax_a80 S.toUFOSignature3_10 ∧
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

def DistanceLaws (S : UFOSignature4) : Prop :=
  ax_distance_identity S.toUFOSignature3_12 ∧ ax_distance_symmetry S.toUFOSignature3_12 ∧ ax_distance_triangle S.toUFOSignature3_12

def closureModel := EmptyLaterSections.extend NonSortalExtension.extended
def quaModel := EmptyLaterSections.extend QuaBearerCountermodel.Model3_10.sig

theorem closure_numbered : Numbered closureModel := by
  exact ⟨StructuralAssumptions.NonSortalClosure.numbered_3_1.ax1,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax2,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax3,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax4,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax5,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax6,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax7,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax8,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax9,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax10,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax11,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax12,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax13,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax14,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax15,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax16,
    StructuralAssumptions.NonSortalClosure.numbered_3_1.ax17,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.2.2.2.2.2.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_3.2.2.2.2.2.2.2.2.2,
    StructuralAssumptions.NonSortalClosure.numbered_3_4.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_4.2.1,
    StructuralAssumptions.NonSortalClosure.numbered_3_4.2.2,
    NonSortalExtension.a47,
    NonSortalExtension.a48,
    NonSortalExtension.a49,
    NonSortalExtension.a50,
    NonSortalExtension.a51,
    NonSortalExtension.a52,
    NonSortalExtension.a53,
    NonSortalExtension.a54,
    NonSortalExtension.a55,
    NonSortalExtension.a56,
    NonSortalExtension.a57,
    NonSortalExtension.a58,
    NonSortalExtension.a59,
    NonSortalExtension.a60,
    NonSortalExtension.a61,
    NonSortalExtension.a62,
    NonSortalExtension.a63,
    NonSortalExtension.a64,
    NonSortalExtension.a65,
    NonSortalExtension.a66,
    NonSortalExtension.a67,
    NonSortalExtension.a68,
    NonSortalExtension.a69,
    NonSortalExtension.a70,
    NonSortalExtension.a71,
    NonSortalExtension.a72,
    NonSortalExtension.a73,
    NonSortalExtension.a74,
    NonSortalExtension.a75,
    NonSortalExtension.a76,
    NonSortalExtension.a77,
    NonSortalExtension.a78,
    NonSortalExtension.a79,
    NonSortalExtension.a80,
    EmptyLaterSections.a81 _,
    EmptyLaterSections.a82 _,
    EmptyLaterSections.a83 _,
    EmptyLaterSections.a84 _,
    EmptyLaterSections.a85 _,
    EmptyLaterSections.a86 _,
    EmptyLaterSections.a87 _,
    EmptyLaterSections.a88 _,
    EmptyLaterSections.a89 _,
    EmptyLaterSections.a90 _,
    EmptyLaterSections.a91 _ (by intro t w; exact fun h => h),
    EmptyLaterSections.a92 _,
    EmptyLaterSections.a93 _ (by intro t w; exact fun h => h),
    EmptyLaterSections.a94 _,
    EmptyLaterSections.a95 _,
    EmptyLaterSections.a96 _,
    EmptyLaterSections.a97 _ (by intro t w; exact fun h => h),
    EmptyLaterSections.a98 _ (by intro t w; exact fun h => h),
    EmptyLaterSections.a99 _,
    EmptyLaterSections.a100 _,
    EmptyLaterSections.a101 _,
    EmptyLaterSections.a102 _,
    EmptyLaterSections.a103 _,
    EmptyLaterSections.a104 _,
    EmptyLaterSections.a105 _,
    EmptyLaterSections.a106 _,
    EmptyLaterSections.a107 _,
    EmptyLaterSections.a108 _⟩

theorem closure_distance : DistanceLaws closureModel :=
  ⟨EmptyLaterSections.distance_identity _, EmptyLaterSections.distance_symmetry _, EmptyLaterSections.distance_triangle _⟩

theorem qua_numbered : Numbered quaModel := by
  have h : UFOAxioms3_9 QuaBearerCountermodel.Model3_9.sig := inferInstance
  exact ⟨h.ax1,
    h.ax2,
    h.ax3,
    h.ax4,
    h.ax5,
    h.ax6,
    h.ax7,
    h.ax8,
    h.ax9,
    h.ax10,
    h.ax11,
    h.ax12,
    h.ax13,
    h.ax14,
    h.ax15,
    h.ax16,
    h.ax17,
    h.ax18,
    h.ax19,
    h.ax20,
    h.ax21,
    h.ax22,
    h.ax23,
    h.ax24,
    h.ax25,
    h.ax26,
    h.ax27,
    h.ax28,
    h.ax29,
    h.ax30,
    h.ax31,
    h.ax32,
    h.ax33,
    h.ax34,
    h.ax35,
    h.ax36,
    h.ax37,
    h.ax38,
    h.ax39,
    h.ax40,
    h.ax41,
    h.ax42,
    h.ax43,
    h.ax44,
    h.ax45,
    h.ax46,
    h.ax47,
    h.ax48,
    h.ax49,
    h.ax50,
    h.ax51,
    h.ax52,
    h.ax53,
    h.ax54,
    h.ax55,
    h.ax56,
    h.ax57,
    h.ax58,
    h.ax59,
    h.ax60,
    h.ax61,
    h.ax62,
    h.ax63,
    h.ax64,
    h.ax65,
    h.ax66,
    h.ax67,
    h.ax68,
    QuaBearerCountermodel.Model3_10.ax69_sig,
    QuaBearerCountermodel.Model3_10.ax70_sig,
    QuaBearerCountermodel.Model3_10.ax71_sig,
    QuaBearerCountermodel.Model3_10.ax72_sig,
    QuaBearerCountermodel.Model3_10.ax73_part_sig,
    QuaBearerCountermodel.Model3_10.ax74_sig,
    QuaBearerCountermodel.Model3_10.ax75_sig,
    QuaBearerCountermodel.Model3_10.ax76_sig,
    QuaBearerCountermodel.Model3_10.ax77_sig,
    QuaBearerCountermodel.Model3_10.ax78_sig,
    QuaBearerCountermodel.Model3_10.ax79_sig,
    QuaBearerCountermodel.Model3_10.ax80_sig,
    EmptyLaterSections.a81 _,
    EmptyLaterSections.a82 _,
    EmptyLaterSections.a83 _,
    EmptyLaterSections.a84 _,
    EmptyLaterSections.a85 _,
    EmptyLaterSections.a86 _,
    EmptyLaterSections.a87 _,
    EmptyLaterSections.a88 _,
    EmptyLaterSections.a89 _,
    EmptyLaterSections.a90 _,
    EmptyLaterSections.a91 _ (by
      intro t w ht
      change Relator.Model3_4.typedBy (Quality Relator.Model3_3.sig) t w at ht
      obtain ⟨x, hx⟩ := Relator.Model3_1.type_has_instance ht.1
      obtain ⟨k, hk, _⟩ := ht.2 w trivial x hx
      exact hk.1),
    EmptyLaterSections.a92 _,
    EmptyLaterSections.a93 _ (by intro t w; exact fun h => h),
    EmptyLaterSections.a94 _,
    EmptyLaterSections.a95 _,
    EmptyLaterSections.a96 _,
    EmptyLaterSections.a97 _ (by intro t w; exact fun h => h),
    EmptyLaterSections.a98 _ (by intro t w; exact fun h => h),
    EmptyLaterSections.a99 _,
    EmptyLaterSections.a100 _,
    EmptyLaterSections.a101 _,
    EmptyLaterSections.a102 _,
    EmptyLaterSections.a103 _,
    EmptyLaterSections.a104 _,
    EmptyLaterSections.a105 _,
    EmptyLaterSections.a106 _,
    EmptyLaterSections.a107 _,
    EmptyLaterSections.a108 _⟩

theorem qua_distance : DistanceLaws quaModel :=
  ⟨EmptyLaterSections.distance_identity _, EmptyLaterSections.distance_symmetry _, EmptyLaterSections.distance_triangle _⟩

theorem closure_other_assumption :
    ax_quaIndividualOf_endurant (Sig := closureModel.toUFOSignature3_10) :=
  NonSortalExtension.qua_typing

/-- Non-sortal upward closure fails despite every other encoded axiom. -/
theorem closure_fails :
    ¬ ax_nonSortal_upward (Sig := closureModel.toUFOSignature3_2) :=
  StructuralAssumptions.NonSortalClosure.not_nonSortal_upward

/-- The full extension still refutes (t16). Together with `closure_numbered`,
`closure_distance`, and `closure_other_assumption`, this excludes a derivation
from the remaining encoded axioms. It does not identify a weakest extra premise. -/
theorem t16_fails : ¬ T16 closureModel.toUFOSignature3_4 :=
  NonSortalClosure.not_t16

theorem qua_other_assumption :
    ax_nonSortal_upward (Sig := quaModel.toUFOSignature3_2) :=
  (inferInstance : UFOAxioms3_9 QuaBearerCountermodel.Model3_9.sig).ax_nonSortal_up

/-- Qua-individual bearer typing fails despite every other encoded axiom. -/
theorem qua_fails :
    ¬ ax_quaIndividualOf_endurant (Sig := quaModel.toUFOSignature3_10) :=
  QuaBearerCountermodel.Model3_10.not_bearer_typing

theorem t33_fails :
    ¬ (∀ x w, quaModel.Relator x w →
      ∃ y z, y ≠ z ∧ quaModel.Mediates x y w ∧ quaModel.Mediates x z w) :=
  QuaBearerCountermodel.Model3_10.not_t33

end Results

end StructuralAssumptions
