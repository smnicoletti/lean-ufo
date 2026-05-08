import Lean
import LeanUfo.UFO.DSL.Certificate.Tactic
import LeanUfo.UFO.DSL.Compiler

/-!
# Generated certificate source for finite UFO DSL models

This module owns the generated theorem registry and proof-source construction
for `ufo_model ... certify`.  It does not elaborate commands or save diagnostics;
`Syntax.lean` remains responsible for running these generated snippets through
Lean and reporting failures.
-/

open Lean

namespace LeanUfo.UFO.DSL

structure CertField where
  field : String
  prop : String

/-!
## Certificate registry

Each entry below corresponds to one field of `UFOAxioms4`.  The `field` string
is the stable DSL/diagnostics name, while `prop` is the Lean proposition proved
for the generated finite signature.  Keeping this registry explicit makes the
generated declaration names, diagnostics rows, and final bundled certificate use
the same ordering.
-/

def certFields : Array CertField :=
  #[
    ⟨"ax1", "ax_a1 sig.toUFOSignature3_1"⟩,
    ⟨"ax2", "ax_a2 sig.toUFOSignature3_1"⟩,
    ⟨"ax3", "ax_a3 sig.toUFOSignature3_1"⟩,
    ⟨"ax4", "ax_a4 sig.toUFOSignature3_1"⟩,
    ⟨"ax5", "ax_a5 sig.toUFOSignature3_1"⟩,
    ⟨"ax6", "ax_a6 sig.toUFOSignature3_1"⟩,
    ⟨"ax7", "ax_a7 sig.toUFOSignature3_1"⟩,
    ⟨"ax8", "ax_a8 sig.toUFOSignature3_1"⟩,
    ⟨"ax9", "ax_a9 sig.toUFOSignature3_1"⟩,
    ⟨"ax10", "ax_a10 sig.toUFOSignature3_1"⟩,
    ⟨"ax11", "ax_a11 sig.toUFOSignature3_1"⟩,
    ⟨"ax12", "ax_a12 sig.toUFOSignature3_1"⟩,
    ⟨"ax13", "ax_a13 sig.toUFOSignature3_1"⟩,
    ⟨"ax14", "ax_a14 sig.toUFOSignature3_1"⟩,
    ⟨"ax15", "ax_a15 sig.toUFOSignature3_1"⟩,
    ⟨"ax16", "ax_a16 sig.toUFOSignature3_1"⟩,
    ⟨"ax17", "ax_a17 sig.toUFOSignature3_1"⟩,
    ⟨"ax18", "ax_a18 sig.toUFOSignature3_2"⟩,
    ⟨"ax19", "ax_a19 sig.toUFOSignature3_2"⟩,
    ⟨"ax20", "ax_a20 sig.toUFOSignature3_2"⟩,
    ⟨"ax21", "ax_a21 sig.toUFOSignature3_2"⟩,
    ⟨"ax22", "ax_a22 sig.toUFOSignature3_2"⟩,
    ⟨"ax23", "ax_a23 sig.toUFOSignature3_2"⟩,
    ⟨"ax24", "ax_a24 sig.toUFOSignature3_2"⟩,
    ⟨"ax25", "ax_a25 sig.toUFOSignature3_2"⟩,
    ⟨"ax26", "ax_a26 sig.toUFOSignature3_2"⟩,
    ⟨"ax27", "ax_a27 sig.toUFOSignature3_2"⟩,
    ⟨"ax28", "ax_a28 sig.toUFOSignature3_2"⟩,
    ⟨"ax29", "ax_a29 sig.toUFOSignature3_2"⟩,
    ⟨"ax30", "ax_a30 sig.toUFOSignature3_2"⟩,
    ⟨"ax31", "ax_a31 sig.toUFOSignature3_2"⟩,
    ⟨"ax32", "ax_a32 sig.toUFOSignature3_2"⟩,
    ⟨"ax33", "ax_a33 sig.toUFOSignature3_2"⟩,
    ⟨"ax_instEndurant", "ax_instEndurant_of_EndurantType (Sig := sig.toUFOSignature3_2)"⟩,
    ⟨"ax_sub_kind_sortal", "ax_sub_of_kind_is_sortal (Sig := sig.toUFOSignature3_2)"⟩,
    ⟨"ax_nonSortal_up", "ax_nonSortal_upward (Sig := sig.toUFOSignature3_2)"⟩,
    ⟨"ax_kindStable", "ax_kindStable sig.toUFOSignature3_2"⟩,
    ⟨"ax34", "ax_a34 sig.toUFOSignature3_3"⟩,
    ⟨"ax35", "ax_a35 sig.toUFOSignature3_3"⟩,
    ⟨"ax36", "ax_a36 sig.toUFOSignature3_3"⟩,
    ⟨"ax37", "ax_a37 sig.toUFOSignature3_3"⟩,
    ⟨"ax38", "ax_a38 sig.toUFOSignature3_3"⟩,
    ⟨"ax39", "ax_a39 sig.toUFOSignature3_3"⟩,
    ⟨"ax40", "ax_a40 sig.toUFOSignature3_3"⟩,
    ⟨"ax41", "ax_a41 sig.toUFOSignature3_3"⟩,
    ⟨"ax42", "ax_a42 sig.toUFOSignature3_3"⟩,
    ⟨"ax43", "ax_a43 sig.toUFOSignature3_3"⟩,
    ⟨"ax44", "ax_a44 sig.toUFOSignature3_4"⟩,
    ⟨"ax45", "ax_a45 sig.toUFOSignature3_4"⟩,
    ⟨"ax46", "ax_a46 sig.toUFOSignature3_4"⟩,
    ⟨"ax47", "ax_a47 sig.toUFOSignature3_5"⟩,
    ⟨"ax48", "ax_a48 sig.toUFOSignature3_5"⟩,
    ⟨"ax49", "ax_a49 sig.toUFOSignature3_5"⟩,
    ⟨"ax50", "ax_a50 sig.toUFOSignature3_5"⟩,
    ⟨"ax51", "ax_a51 sig.toUFOSignature3_5"⟩,
    ⟨"ax52", "ax_a52 sig.toUFOSignature3_5"⟩,
    ⟨"ax53", "ax_a53 sig.toUFOSignature3_6"⟩,
    ⟨"ax54", "ax_a54 sig.toUFOSignature3_6"⟩,
    ⟨"ax55", "ax_a55 sig.toUFOSignature3_6"⟩,
    ⟨"ax56", "ax_a56 sig.toUFOSignature3_7"⟩,
    ⟨"ax57", "ax_a57 sig.toUFOSignature3_7"⟩,
    ⟨"ax58", "ax_a58 sig.toUFOSignature3_7"⟩,
    ⟨"ax59", "ax_a59 sig.toUFOSignature3_7"⟩,
    ⟨"ax60", "ax_a60 sig.toUFOSignature3_7"⟩,
    ⟨"ax61", "ax_a61 sig.toUFOSignature3_7"⟩,
    ⟨"ax62", "ax_a62 sig.toUFOSignature3_8"⟩,
    ⟨"ax63", "ax_a63 sig.toUFOSignature3_8"⟩,
    ⟨"ax64", "ax_a64 sig.toUFOSignature3_8"⟩,
    ⟨"ax65", "ax_a65 sig.toUFOSignature3_9"⟩,
    ⟨"ax66", "ax_a66 sig.toUFOSignature3_9"⟩,
    ⟨"ax67", "ax_a67 sig.toUFOSignature3_9"⟩,
    ⟨"ax68", "ax_a68 sig.toUFOSignature3_9"⟩,
    ⟨"ax69", "ax_a69 sig.toUFOSignature3_10"⟩,
    ⟨"ax70", "ax_a70 sig.toUFOSignature3_10"⟩,
    ⟨"ax71", "ax_a71 sig.toUFOSignature3_10"⟩,
    ⟨"ax72", "ax_a72 sig.toUFOSignature3_10"⟩,
    ⟨"ax73", "ax_a73 sig.toUFOSignature3_10"⟩,
    ⟨"ax74", "ax_a74 sig.toUFOSignature3_10"⟩,
    ⟨"ax75", "ax_a75 sig.toUFOSignature3_10"⟩,
    ⟨"ax76", "ax_a76 sig.toUFOSignature3_10"⟩,
    ⟨"ax77", "ax_a77 sig.toUFOSignature3_10"⟩,
    ⟨"ax78", "ax_a78 sig.toUFOSignature3_10"⟩,
    ⟨"ax79", "ax_a79 sig.toUFOSignature3_10"⟩,
    ⟨"ax80", "ax_a80 sig.toUFOSignature3_10"⟩,
    ⟨"axQuaIndividualOfEndurant", "ax_quaIndividualOf_endurant sig.toUFOSignature3_10"⟩,
    ⟨"ax81", "ax_a81 sig.toUFOSignature3_11"⟩,
    ⟨"ax82", "ax_a82 sig.toUFOSignature3_11"⟩,
    ⟨"ax83", "ax_a83 sig.toUFOSignature3_12"⟩,
    ⟨"ax84", "ax_a84 sig.toUFOSignature3_12"⟩,
    ⟨"ax85", "ax_a85 sig.toUFOSignature3_12"⟩,
    ⟨"ax86", "ax_a86 sig.toUFOSignature3_12"⟩,
    ⟨"ax87", "ax_a87 sig.toUFOSignature3_12"⟩,
    ⟨"ax88", "ax_a88 sig.toUFOSignature3_12"⟩,
    ⟨"ax89", "ax_a89 sig.toUFOSignature3_12"⟩,
    ⟨"ax90", "ax_a90 sig.toUFOSignature3_12"⟩,
    ⟨"ax91", "ax_a91 sig.toUFOSignature3_12"⟩,
    ⟨"ax92", "ax_a92 sig.toUFOSignature3_12"⟩,
    ⟨"ax93", "ax_a93 sig.toUFOSignature3_12"⟩,
    ⟨"ax94", "ax_a94 sig.toUFOSignature3_12"⟩,
    ⟨"ax95", "ax_a95 sig.toUFOSignature3_12"⟩,
    ⟨"ax96", "ax_a96 sig.toUFOSignature3_12"⟩,
    ⟨"ax97", "ax_a97 sig.toUFOSignature3_12"⟩,
    ⟨"ax98", "ax_a98 sig.toUFOSignature3_12"⟩,
    ⟨"ax99", "ax_a99 sig.toUFOSignature3_12"⟩,
    ⟨"ax100", "ax_a100 sig.toUFOSignature3_12"⟩,
    ⟨"ax101", "ax_a101 sig.toUFOSignature3_12"⟩,
    ⟨"axDistanceIdentity", "ax_distance_identity sig.toUFOSignature3_12"⟩,
    ⟨"axDistanceSymmetry", "ax_distance_symmetry sig.toUFOSignature3_12"⟩,
    ⟨"axDistanceTriangle", "ax_distance_triangle sig.toUFOSignature3_12"⟩,
    ⟨"ax102", "ax_a102 sig.toUFOSignature3_13"⟩,
    ⟨"ax103", "ax_a103 sig.toUFOSignature3_13"⟩,
    ⟨"ax104", "ax_a104 sig.toUFOSignature3_13"⟩,
    ⟨"ax105", "ax_a105 sig"⟩,
    ⟨"ax106", "ax_a106 sig"⟩,
    ⟨"ax107", "ax_a107 sig"⟩,
    ⟨"ax108", "ax_a108 sig"⟩
  ]

def certTheoremName (field : String) : String :=
  s!"certified_{field}"

def certFormula : String → String
  | "ax1" => "Type(x) ↔ ◇(∃ y, y :: x)"
  | "ax2" => "Individual(x) ↔ □(¬∃ y, y :: x)"
  | "ax3" => "x :: y → (Type(x) ∨ Individual(x))"
  | "ax4" => "¬∃ x y z, Type(x) ∧ x :: y ∧ y :: z"
  | "ax5" => "x ⊑ y ↔ Type(x) ∧ Type(y) ∧ □∀z (z :: x → z :: y)"
  | "ax6" => "If x instantiates incomparable t1 and t2, then x also instantiates a common supertype or common subtype"
  | "ax7" => "ConcreteIndividual(x) → Individual(x)"
  | "ax8" => "AbstractIndividual(x) → Individual(x)"
  | "ax9" => "ConcreteIndividual(x) → ¬AbstractIndividual(x)"
  | "ax10" => "Individual(x) ↔ ConcreteIndividual(x) ∨ AbstractIndividual(x)"
  | "ax11" => "Endurant(x) → ConcreteIndividual(x)"
  | "ax12" => "Perdurant(x) → ConcreteIndividual(x)"
  | "ax13" => "Endurant(x) → ¬Perdurant(x)"
  | "ax14" => "ConcreteIndividual(x) ↔ Endurant(x) ∨ Perdurant(x)"
  | "ax15" => "EndurantType(x) → Type(x)"
  | "ax16" => "PerdurantType(x) → Type(x)"
  | "ax17" => "EndurantType(x) → ¬PerdurantType(x)"
  | "ax18" => "Rigid(t) ↔ EndurantType(t) ∧ ∀x (◇(x :: t) → □(x :: t))"
  | "ax19" => "AntiRigid(t) ↔ EndurantType(t) ∧ ∀x (◇(x :: t) → ◇¬(x :: t))"
  | "ax20" => "SemiRigid(t) ↔ EndurantType(t) ∧ ¬Rigid(t) ∧ ¬AntiRigid(t)"
  | "ax21" => "Endurant(x) → ∃ k, Kind(k) ∧ □(x :: k)"
  | "ax22" => "Kind(k) ∧ x :: k → ¬◇(∃ z, Kind(z) ∧ x :: z ∧ z ≠ k)"
  | "ax23" => "Sortal(t) ↔ EndurantType(t) ∧ ∃ k, Kind(k) ∧ □∀x (x :: t → x :: k)"
  | "ax24" => "NonSortal(t) ↔ EndurantType(t) ∧ ¬Sortal(t)"
  | "ax25" => "¬∃ t, Kind(t) ∧ SubKind(t)"
  | "ax26" => "Kind(t) ∨ SubKind(t) ↔ Rigid(t) ∧ Sortal(t)"
  | "ax27" => "¬∃ t, Phase(t) ∧ Role(t)"
  | "ax28" => "Phase(x) ∨ Role(x) ↔ AntiRigid(x) ∧ Sortal(x)"
  | "ax29" => "SemiRigidSortal(x) ↔ SemiRigid(x) ∧ Sortal(x)"
  | "ax30" => "Category(x) ↔ Rigid(x) ∧ NonSortal(x)"
  | "ax31" => "Mixin(x) ↔ SemiRigid(x) ∧ NonSortal(x)"
  | "ax32" => "¬∃ t, PhaseMixin(t) ∧ RoleMixin(t)"
  | "ax33" => "PhaseMixin(t) ∨ RoleMixin(t) ↔ AntiRigid(t) ∧ NonSortal(t)"
  | "ax_instEndurant" => "EndurantType(t) ∧ x :: t → Endurant(x)"
  | "ax_sub_kind_sortal" => "x ⊑ k ∧ Kind(k) → Sortal(x)"
  | "ax_nonSortal_up" => "NonSortal(x) ∧ x ⊑ y → NonSortal(y)"
  | "ax_kindStable" => "Kind(k) → □ Kind(k)"
  | "ax34" => "Substantial(x) ∨ Moment(x) ↔ Endurant(x)"
  | "ax35" => "¬∃ x, Substantial(x) ∧ Moment(x)"
  | "ax36" => "Object(x) ∨ Collective(x) ∨ Quantity(x) ↔ Substantial(x)"
  | "ax37" => "¬∃ x, Object(x) ∧ Collective(x)"
  | "ax38" => "¬∃ x, Object(x) ∧ Quantity(x)"
  | "ax39" => "¬∃ x, Collective(x) ∧ Quantity(x)"
  | "ax40" => "Relator(x) ∨ IntrinsicMoment(x) ↔ Moment(x)"
  | "ax41" => "¬∃ x, Relator(x) ∧ IntrinsicMoment(x)"
  | "ax42" => "Mode(x) ∨ Quality(x) ↔ IntrinsicMoment(x)"
  | "ax43" => "¬∃ x, Mode(x) ∧ Quality(x)"
  | "ax44" => "EndurantType taxonomy mirrors Endurant taxonomy"
  | "ax45" => "Specific kind predicates imply matching type predicate and Kind"
  | "ax46" => "Endurant(x) → ◇∃ k, specific endurant kind k ∧ x :: k"
  | "ax47" => "Part(x, x)"
  | "ax48" => "Part(x, y) ∧ Part(y, x) → x = y"
  | "ax49" => "Part(x, y) ∧ Part(y, z) → Part(x, z)"
  | "ax50" => "Overlap(x, y) ↔ ∃ z, Part(z, x) ∧ Part(z, y)"
  | "ax51" => "¬Part(y, x) → ∃ z, Part(z, y) ∧ ¬Overlap(z, x)"
  | "ax52" => "ProperPart(x, y) ↔ Part(x, y) ∧ ¬Part(y, x)"
  | "ax53" => "GenericFunctionalDependence(x', y') ↔ ∀x, x :: x' ∧ FunctionsAs(x,x') → ∃y, y ≠ x ∧ y :: y' ∧ FunctionsAs(y,y')"
  | "ax54" => "IndividualFunctionalDependence(x,x',y,y') ↔ GFD(x',y') ∧ x :: x' ∧ y :: y' ∧ (FunctionsAs(x,x') → FunctionsAs(y,y'))"
  | "ax55" => "ComponentOf(x,x',y,y') ↔ ProperPart(x,y) ∧ IndividualFunctionalDependence(x,x',y,y')"
  | "ax56" => "constitutedBy(x, y) → ((Endurant(x) ↔ Endurant(y)) ∧ (Perdurant(x) ↔ Perdurant(y)))"
  | "ax57" => "constitutedBy(x, y) ∧ x :: x' ∧ y :: y' ∧ Kind(x') ∧ Kind(y') → x' ≠ y'"
  | "ax58" => "GCD(x', y') ↔ ∀ x, x :: x' → ∃ y, y :: y' ∧ constitutedBy(x, y)"
  | "ax59" => "Constitution(x, x', y, y') ↔ x :: x' ∧ y :: y' ∧ GCD(x', y') ∧ constitutedBy(x, y)"
  | "ax60" => "Perdurant(x) ∧ constitutedBy(x, y) → □(ex(x) → constitutedBy(x, y))"
  | "ax61" => "constitutedBy(x, y) → ¬ constitutedBy(y, x)"
  | "ax62" => "ex(x) → Thing(x) (trivial in the typed Lean encoding)"
  | "ax63" => "ExistentialDependence(x, y) ↔ □(ex(x) → ex(y))"
  | "ax64" => "ExistentialIndependence(x, y) ↔ ¬ExistentialDependence(x, y) ∧ ¬ExistentialDependence(y, x)"
  | "ax65" => "inheresIn(x, y) → ExistentialDependence(x, y)"
  | "ax66" => "inheresIn(x, y) → Moment(x) ∧ (Type(y) ∨ ConcreteIndividual(y))"
  | "ax67" => "inheresIn(x, y) ∧ inheresIn(x, z) → y = z"
  | "ax68" => "Moment(x) → ∃! y, UltimateBearerOf(y, x)"
  | "ax69" => "ExternallyDependent(x, y) ↔ ExistentialDependence(x, y) ∧ ∀z (InheresIn(x,z) → ExistentialIndependence(y,z))"
  | "ax70" => "ExternallyDependentMode(x) ↔ Mode(x) ∧ ∃ y, ExternallyDependent(x, y)"
  | "ax71" => "FoundedBy(x, y) → (ExternallyDependentMode(x) ∨ Relator(x)) ∧ Perdurant(y)"
  | "ax72" => "ExternallyDependentMode(x) → ∃! y, FoundedBy(x, y)"
  | "ax73" => "QuaIndividualOf(x, y) ↔ overlap-defined externally dependent modes sharing x's foundation"
  | "ax74" => "QuaIndividual(x) ↔ ∃ y, QuaIndividualOf(x, y)"
  | "ax75" => "QuaIndividual(x) → ExternallyDependentMode(x)"
  | "ax76" => "QuaIndividualOf(x, y) ∧ QuaIndividualOf(x, y') → y = y'"
  | "ax77" => "Relator(x) → ∃! y, FoundedBy(x, y)"
  | "ax78" => "Relator(x) ∧ Part(y, x) → FoundationOf(x) = FoundationOf(y)"
  | "ax79" => "Relator(x) ↔ sum of mutually dependent qua individuals sharing a foundation"
  | "ax80" => "Mediates(x, y) ↔ Relator(x) ∧ Endurant(y) ∧ ∃z (QuaIndividualOf(z, y) ∧ Part(z, x))"
  | "axQuaIndividualOfEndurant" => "QuaIndividualOf(x, y) → Endurant(y)"
  | "ax81" => "Characterization(t, m) → EndurantType(t) ∧ MomentType(m) ∧ instances of t have inhering m-instances, and m-instances have unique t-bearers"
  | "ax82" => "Characterization(t, q) ∧ QualityType(q) → each q-instance has a unique t-bearer"
  | "ax83" => "Quale(x) → AbstractIndividual(x)"
  | "ax84" => "Set(x) → AbstractIndividual(x)"
  | "ax85" => "¬∃ x, Quale(x) ∧ Set(x)"
  | "ax86" => "QualityStructure(x) → Set(x) ∧ NonEmptySet(x)"
  | "ax87" => "Quale(x) ↔ ∃! y, QualityStructure(y) ∧ MemberOf(x, y)"
  | "ax88" => "QualityStructure(x) ↔ QualityDomain(x) ∨ QualityDimension(x)"
  | "ax89" => "QualityDomain(x) → ¬ QualityDimension(x)"
  | "ax90" => "AssociatedWith(s,t) ∧ AssociatedWith(s',t') ∧ ProperSub(t',t) → ProperSubsetOf(s',s)"
  | "ax91" => "QualityType(t) ↔ IntrinsicMomentType(t) ∧ ∃! x, QualityStructure(x) ∧ AssociatedWith(x,t)"
  | "ax92" => "HasValue(x, y) → Quality(x) ∧ Quale(y)"
  | "ax93" => "Quality(x) → ∃! y, HasValue(x, y)"
  | "ax94" => "HasValue(x, y) → ∃ t s, x :: t ∧ AssociatedWith(s,t) ∧ MemberOf(y,s)"
  | "ax95" => "AssociatedWith(x,y) → (QualityDimension(x) ↔ SimpleQualityType(y))"
  | "ax96" => "AssociatedWith(x,y) → (QualityDomain(x) ↔ ComplexQualityType(y))"
  | "ax97" => "ComplexQuality(x) ∧ y :: Y ∧ z :: Z ∧ InheresIn(y,x) ∧ InheresIn(z,x) ∧ Y = Z → y = z"
  | "ax98" => "ComplexQuality(x) → ∀ y, InheresIn(y,x) → SimpleQuality(y)"
  | "ax99" => "QualityDomain(x) ∧ AssociatedWith(x,t) → product-subset characterization over associated dimensions"
  | "ax100" => "Distance(x,y,r) → Quale(x) ∧ Quale(y) ∧ ∃ z, MemberOf(x,z) ∧ MemberOf(y,z)"
  | "ax101" => "Quale(x) ∧ Quale(y) → ∃! r, Distance(x,y,r)"
  | "axDistanceIdentity" => "x = y ∧ Distance(x,y,r) → DistanceZero(r)"
  | "axDistanceSymmetry" => "Distance(x,y,r) → Distance(y,x,r)"
  | "axDistanceTriangle" => "Distance(x,y,r₀) ∧ Distance(y,z,r₁) ∧ Distance(x,z,r₂) ∧ DistanceSum(r₀,r₁,s) → DistanceGreaterEq(s,r₂)"
  | "ax102" => "manifests(x, y) → Perdurant(x) ∧ Endurant(y)"
  | "ax103" => "lifeOf(x, y) ↔ Perdurant(x) ∧ Endurant(y) ∧ ∀ z, Overlap(z, x) ↔ Perdurant(z) ∧ manifests(z, y)"
  | "ax104" => "meet(x, y) → Perdurant(x) ∧ Perdurant(y)"
  | "ax105" => "isDisjointWith(t, t') ↔ Type(t) ∧ Type(t') ∧ ¬∃ x, x :: t ∧ x :: t'"
  | "ax106" => "isCompletelyCoveredBy(t, t', t'') ↔ ∀ x, x :: t → x :: t' ∨ x :: t''"
  | "ax107" => "isPartitionedInto(t, t', t'') ↔ isCompletelyCoveredBy(t, t', t'') ∧ isDisjointWith(t', t'')"
  | "ax108" => "categorizes(t₁, t₂) ↔ Type(t₁) ∧ ∀ t₃, t₃ :: t₁ → t₃ ⊑ t₂"
  | _ => ""

private def finThingTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)"

private def finWorldTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.worldCount)"

private def localFinThingTerm (idx : Nat) (proofName : String) : String :=
  s!"(⟨{idx}, {proofName}⟩ : Fin data.thingCount)"

private def localFinWorldTerm (idx : Nat) (proofName : String) : String :=
  s!"(⟨{idx}, {proofName}⟩ : Fin data.worldCount)"

private def indentLines (pref source : String) : String :=
  String.intercalate "\n" <| (source.splitOn "\n").map (fun line => pref ++ line)

/-
Special proof generator for ax68.

Most generated axiom fields are discharged by `ufo_cert_tac`.  Ultimate-bearer
uniqueness is more brittle because it goes through the inductive `MomentOf`
closure, so the certificate generator emits explicit finite case splits for
the direct-terminal bearer pattern detected in the compiled tables.
-/
private def natExhaustedContradiction
    (varName boundProofName hypPrefix : String) (count : Nat) : String :=
  let neqProofs := (List.range count).map fun idx =>
    s!"have hne_{idx} : {varName} ≠ {idx} := {hypPrefix}_{idx}"
  String.intercalate "\n" <|
    ["exfalso", s!"have hlt := {boundProofName}", s!"change {varName} < {count} at hlt"] ++
      neqProofs ++ ["omega"]

partial def natByCases (varName boundProofName hypPrefix : String) (count idx : Nat)
    (leaf : Nat → String) : String :=
  if idx < count then
    let yesBranch := indentLines "  " s!"subst {varName}
{leaf idx}"
    let noBranch := indentLines "  " (natByCases varName boundProofName hypPrefix count (idx + 1) leaf)
    s!"by_cases {hypPrefix}_{idx} : {varName} = {idx}
·
{yesBranch}
·
{noBranch}"
  else
    natExhaustedContradiction varName boundProofName hypPrefix count

private def ax68UniqueDirectProof (thingCount _m _w _b : Nat) : String :=
  let cases := natByCases "zVal" "zLt" "h_z" thingCount 0 fun _ =>
    s!"{certificateSimp} at hz ⊢ <;> (try contradiction) <;> (try omega) <;> (try rfl)"
  s!"by
  intro z hz
  rcases z with ⟨zVal, zLt⟩
{indentLines "  " cases}"

private def ax68TerminalProof (thingCount _b _w : Nat) : String :=
  let cases := natByCases "zVal" "zLt" "h_z" thingCount 0 fun _ =>
    s!"{certificateSimp} at hz <;> (try contradiction) <;> (try omega) <;> (try rfl)"
  s!"by
  intro z hz
  rcases z with ⟨zVal, zLt⟩
{indentLines "  " cases}"

private def directTerminalBearer?
    (thingCount : Nat) (tables : FactTables) (w m : Nat) : Option Nat :=
  Id.run do
    let mut found? : Option Nat := none
    for b in [:thingCount] do
      if tables.binaryLookup "inheresIn" m b w &&
          !tables.unaryLookup "moment" b w then
        let mut terminal := true
        for z in [:thingCount] do
          if tables.binaryLookup "inheresIn" b z w then
            terminal := false
        if terminal then
          match found? with
          | none => found? := some b
          | some _ => return none
    return found?

private def ax68DirectBearerLeafTactic (thingCount m w b : Nat) : String :=
  let mTerm := localFinThingTerm m "mLt"
  let wTerm := localFinWorldTerm w "wLt"
  s!"refine ⟨{finThingTerm b}, ?_, ?_⟩
·
  constructor
  ·
    {certificateSimp} <;> (try contradiction) <;> (try omega) <;> (try rfl)
  ·
    exact MomentOf.direct (by {certificateSimp} <;> (try contradiction) <;> (try omega) <;> (try rfl))
·
  intro y hy
  exact momentOf_eq_of_unique_direct_bearer
    (Sig := sig.toUFOSignature3_9)
    (m := {mTerm}) (b := {finThingTerm b}) (x := y) (w := {wTerm})
    ({ax68UniqueDirectProof thingCount m w b})
    ({ax68TerminalProof thingCount b w})
    hy.2"

private def ax68LeafTactic
    (thingCount : Nat) (tables : FactTables) (m w : Nat) : String :=
  if tables.unaryLookup "moment" m w then
    match directTerminalBearer? thingCount tables w m with
    | some b => ax68DirectBearerLeafTactic thingCount m w b
    | none =>
        s!"{certificateSimp} at hm ⊢ <;> (try contradiction) <;> (try omega) <;> (try grind)"
  else
    s!"{certificateSimp} at hm ⊢ <;> contradiction"

partial def ax68WorldCases
    (thingCount worldCount : Nat) (tables : FactTables) (m idx : Nat) : String :=
  natByCases "wVal" "wLt" "h_w" worldCount idx fun w =>
    ax68LeafTactic thingCount tables m w

partial def ax68ThingCases
    (thingCount worldCount : Nat) (tables : FactTables) (idx : Nat) : String :=
  natByCases "mVal" "mLt" "h_m" thingCount idx fun m =>
    ax68WorldCases thingCount worldCount tables m 0

private def numberedAxiomSimpDefs? (field : String) : Option String :=
  match field.dropPrefix? "ax" with
  | some suffix =>
      if suffix.all Char.isDigit then
        some s!"ax_a{suffix}"
      else
        none
  | none => none

private def certificateSimpDefs? (field : CertField) : Option String :=
  match field.field with
  | "ax44" =>
      some
        "ax_a44_endurantType, ax_a44_perdurantType, ax_a44_substantialType, ax_a44_momentType,
        ax_a44_objectType, ax_a44_collectiveType, ax_a44_quantityType, ax_a44_relatorType,
        ax_a44_modeType, ax_a44_qualityType, ax_a44, Quality, ExistsUnique"
  | "ax42" => some "ax_a42, Quality, ExistsUnique"
  | "ax43" => some "ax_a43, Quality, ExistsUnique"
  | "ax45" =>
      some
        "ax_a45_objectKind, ax_a45_collectiveKind, ax_a45_quantityKind, ax_a45_relatorKind,
        ax_a45_modeKind, ax_a45_qualityKind, ax_a45"
  | "ax73" => some "ax_a73, FoundationOf, ExistsUnique"
  | "ax78" => some "ax_a78, FoundationOf"
  | "ax79" => some "ax_a79, FoundationOf"
  | "ax81" => some "ax_a81, ExistsUnique"
  | "ax82" => some "ax_a82, ExistsUnique"
  | "ax86" => some "ax_a86, QualityStructure, NonEmptySet, ExistsUnique"
  | "ax87" => some "ax_a87, QualityStructure, MemberOf, ExistsUnique"
  | "ax88" => some "ax_a88, QualityStructure, ExistsUnique"
  | "ax90" => some "ax_a90, ProperSub, ProperSubsetOf"
  | "ax91" => some "ax_a91, QualityStructure, ExistsUnique"
  | "ax92" => some "ax_a92, Quality, ExistsUnique"
  | "ax93" => some "ax_a93, Quality, ExistsUnique"
  | "ax94" => some "ax_a94, MemberOf"
  | "ax95" => some "ax_a95, SimpleQualityType, SimpleQuality, Quality, ExistsUnique"
  | "ax96" => some "ax_a96, ComplexQualityType, ComplexQuality, SimpleQuality, Quality, ExistsUnique"
  | "ax97" => some "ax_a97, ComplexQuality, SimpleQuality, Quality, ExistsUnique"
  | "ax98" => some "ax_a98, ComplexQuality, SimpleQuality, Quality, ExistsUnique"
  | "ax99" => some "ax_a99, ProductSubsetOf, MemberOf"
  | "ax100" => some "ax_a100, MemberOf"
  | "ax101" => some "ax_a101, ExistsUnique"
  | "axQuaIndividualOfEndurant" => some "ax_quaIndividualOf_endurant"
  | "axDistanceIdentity" => some "ax_distance_identity"
  | "axDistanceSymmetry" => some "ax_distance_symmetry"
  | "axDistanceTriangle" => some "ax_distance_triangle"
  | "ax_instEndurant" => some "ax_instEndurant_of_EndurantType"
  | "ax_sub_kind_sortal" => some "ax_sub_of_kind_is_sortal"
  | "ax_nonSortal_up" => some "ax_nonSortal_upward"
  | "ax_kindStable" => some "ax_kindStable"
  | _ => numberedAxiomSimpDefs? field.field

private def certTactic
    (worldCount thingCount : Nat) (tables : FactTables) (field : CertField) : String :=
  if field.field == "ax68" then
    s!"intro m w hm
rcases m with ⟨mVal, mLt⟩
rcases w with ⟨wVal, wLt⟩
{ax68ThingCases thingCount worldCount tables 0}"
  else
    match certificateSimpDefs? field with
    | some defs =>
        s!"{certificateSimpSelected defs} <;> (try omega) <;> (try grind) <;> (decide +revert)"
    | none =>
        "ufo_cert_tac"

/--
Some axioms must be probed by elaborating the generated theorem command, not by
first elaborating a standalone proof term.

The ordinary term probe is cheaper and keeps successful probes out of the
environment, but it elaborates in a slightly different context from the final
command.  A small number of fields are sensitive to that difference:

* `ax1`-`ax6` reduce to finite definitions over all things/worlds; on larger
  models the standalone term probe can run out before the command theorem does.
* `ax68` uses a generated proof shape that needs command-level context.
* `ax44` reduces to a large finite type-taxonomy proposition; the term probe may
  fail decidability synthesis even when the generated theorem command succeeds.

Keeping this list explicit avoids mistaking probe incompleteness for a semantic
counterexample.
-/
def useCommandCertificateProbe (field : CertField) : Bool :=
  field.field == "ax1" || field.field == "ax2" || field.field == "ax3" ||
    field.field == "ax4" || field.field == "ax5" || field.field == "ax6" ||
    field.field == "ax44" || field.field == "ax68"

def certAxiomTheorem
    (worldCount thingCount : Nat) (tables : FactTables) (field : CertField) : String :=
  s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem {certTheoremName field.field} : {field.prop} := by
{indentLines "  " (certTactic worldCount thingCount tables field)}"

def certificateBody : String :=
  let fieldSource := certFields.map fun field =>
    s!"    {field.field} := {certTheoremName field.field}"
  "by\n  refine\n  {\n" ++ String.intercalate "\n" fieldSource.toList ++ "\n  }"

def derivedFactsType (props : Array String) : String :=
  if props.isEmpty then
    "True"
  else
    String.intercalate " ∧\n  " props.toList

def derivedFactsBody (props : Array String) : String :=
  if props.isEmpty then
    "by trivial"
  else
    "by\n  ufo_cert_tac"

def certAxiomCounterexampleCheck (field : CertField) : String :=
  s!"show ¬ ({field.prop}) from by
  set_option maxHeartbeats 1000000 in
  set_option linter.unusedSimpArgs false in
  {certificateSimp} <;> (try omega) <;> (try grind) <;> native_decide"

def certAxiomProofCheck
    (worldCount thingCount : Nat) (tables : FactTables) (field : CertField) : String :=
  s!"show {field.prop} from by
  set_option maxHeartbeats 1000000 in
  set_option linter.unusedSimpArgs false in
{indentLines "  " (certTactic worldCount thingCount tables field)}"

end LeanUfo.UFO.DSL
