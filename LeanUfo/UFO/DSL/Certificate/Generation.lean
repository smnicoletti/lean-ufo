import Lean
import LeanUfo.UFO.DSL.Certificate.Tactic
import LeanUfo.UFO.DSL.Checker
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

private def indentLines (pref source : String) : String :=
  String.intercalate "\n" <| (source.splitOn "\n").map (fun line => pref ++ line)

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

def checkerBackedField (field : CertField) : Bool :=
  field.field == "ax1" || field.field == "ax2" || field.field == "ax3" ||
    field.field == "ax4" || field.field == "ax5" || field.field == "ax6" ||
    field.field == "ax7" || field.field == "ax8" || field.field == "ax9" ||
    field.field == "ax10" || field.field == "ax11" || field.field == "ax12" ||
    field.field == "ax13" || field.field == "ax14" || field.field == "ax15" ||
    field.field == "ax16" || field.field == "ax17" ||
    field.field == "ax18" || field.field == "ax19" || field.field == "ax20" ||
    field.field == "ax21" || field.field == "ax22" || field.field == "ax23" ||
    field.field == "ax24" || field.field == "ax25" ||
    field.field == "ax26" || field.field == "ax27" || field.field == "ax28" ||
    field.field == "ax29" || field.field == "ax30" || field.field == "ax31" ||
    field.field == "ax32" || field.field == "ax33" ||
    field.field == "ax_instEndurant" || field.field == "ax_sub_kind_sortal" ||
    field.field == "ax_nonSortal_up" || field.field == "ax_kindStable" ||
    field.field == "ax34" || field.field == "ax35" || field.field == "ax36" ||
    field.field == "ax37" || field.field == "ax38" || field.field == "ax39" ||
    field.field == "ax40" || field.field == "ax41" || field.field == "ax42" ||
    field.field == "ax43" ||
    field.field == "ax44" || field.field == "ax45" || field.field == "ax46" ||
    field.field == "ax47" || field.field == "ax48" || field.field == "ax49" ||
    field.field == "ax50" || field.field == "ax51" || field.field == "ax52" ||
    field.field == "ax53" || field.field == "ax54" || field.field == "ax55" ||
    field.field == "ax56" || field.field == "ax57" || field.field == "ax58" ||
    field.field == "ax59" || field.field == "ax60" ||
    field.field == "ax61" || field.field == "ax62" || field.field == "ax63" ||
    field.field == "ax64" || field.field == "ax65" || field.field == "ax66" ||
    field.field == "ax67" || field.field == "ax68" ||
    field.field == "ax69" || field.field == "ax70" || field.field == "ax71" ||
    field.field == "ax72" || field.field == "ax73" || field.field == "ax74" || field.field == "ax75" ||
    field.field == "ax76" || field.field == "ax77" || field.field == "ax78" ||
    field.field == "ax79" || field.field == "ax80" ||
    field.field == "axQuaIndividualOfEndurant" ||
    field.field == "ax81" || field.field == "ax82" ||
    field.field == "ax83" || field.field == "ax84" || field.field == "ax85" ||
    field.field == "ax86" || field.field == "ax87" ||
    field.field == "ax88" || field.field == "ax89" || field.field == "ax90" ||
    field.field == "ax91" ||
    field.field == "ax92" || field.field == "ax93" ||
    field.field == "ax94" || field.field == "ax95" || field.field == "ax96" ||
    field.field == "ax97" || field.field == "ax98" ||
    field.field == "ax99" || field.field == "ax100" || field.field == "ax101" ||
    field.field == "axDistanceIdentity" ||
    field.field == "axDistanceSymmetry" ||
    field.field == "axDistanceTriangle" ||
    field.field == "ax102" || field.field == "ax103" || field.field == "ax104" ||
    field.field == "ax105" || field.field == "ax106" || field.field == "ax107" ||
    field.field == "ax108"

private def checkerSoundnessName? (field : CertField) : Option String :=
  match field.field with
  | "ax1" => some "checkAx1_sound"
  | "ax2" => some "checkAx2_sound"
  | "ax3" => some "checkAx3_sound"
  | "ax4" => some "checkAx4_sound"
  | "ax5" => some "checkAx5_sound"
  | "ax6" => some "checkAx6_sound"
  | "ax7" => some "checkAx7_sound"
  | "ax8" => some "checkAx8_sound"
  | "ax9" => some "checkAx9_sound"
  | "ax10" => some "checkAx10_sound"
  | "ax11" => some "checkAx11_sound"
  | "ax12" => some "checkAx12_sound"
  | "ax13" => some "checkAx13_sound"
  | "ax14" => some "checkAx14_sound"
  | "ax15" => some "checkAx15_sound"
  | "ax16" => some "checkAx16_sound"
  | "ax17" => some "checkAx17_sound"
  | "ax18" => some "checkAx18_sound"
  | "ax19" => some "checkAx19_sound"
  | "ax20" => some "checkAx20_sound"
  | "ax21" => some "checkAx21_sound"
  | "ax22" => some "checkAx22_sound"
  | "ax23" => some "checkAx23_sound"
  | "ax24" => some "checkAx24_sound"
  | "ax25" => some "checkAx25_sound"
  | "ax26" => some "checkAx26_sound"
  | "ax27" => some "checkAx27_sound"
  | "ax28" => some "checkAx28_sound"
  | "ax29" => some "checkAx29_sound"
  | "ax30" => some "checkAx30_sound"
  | "ax31" => some "checkAx31_sound"
  | "ax32" => some "checkAx32_sound"
  | "ax33" => some "checkAx33_sound"
  | "ax_instEndurant" => some "checkAxInstEndurant_sound"
  | "ax_sub_kind_sortal" => some "checkAxSubKindSortal_sound"
  | "ax_nonSortal_up" => some "checkAxNonSortalUp_sound"
  | "ax_kindStable" => some "checkAxKindStable_sound"
  | "ax34" => some "checkAx34_sound"
  | "ax35" => some "checkAx35_sound"
  | "ax36" => some "checkAx36_sound"
  | "ax37" => some "checkAx37_sound"
  | "ax38" => some "checkAx38_sound"
  | "ax39" => some "checkAx39_sound"
  | "ax40" => some "checkAx40_sound"
  | "ax41" => some "checkAx41_sound"
  | "ax42" => some "checkAx42_sound"
  | "ax43" => some "checkAx43_sound"
  | "ax44" => some "checkAx44_sound"
  | "ax45" => some "checkAx45_sound"
  | "ax46" => some "checkAx46_sound"
  | "ax47" => some "checkAx47_sound"
  | "ax48" => some "checkAx48_sound"
  | "ax49" => some "checkAx49_sound"
  | "ax50" => some "checkAx50_sound"
  | "ax51" => some "checkAx51_sound"
  | "ax52" => some "checkAx52_sound"
  | "ax53" => some "checkAx53_sound"
  | "ax54" => some "checkAx54_sound"
  | "ax55" => some "checkAx55_sound"
  | "ax56" => some "checkAx56_sound"
  | "ax57" => some "checkAx57_sound"
  | "ax58" => some "checkAx58_sound"
  | "ax59" => some "checkAx59_sound"
  | "ax60" => some "checkAx60_sound"
  | "ax61" => some "checkAx61_sound"
  | "ax62" => some "checkAx62_sound"
  | "ax63" => some "checkAx63_sound"
  | "ax64" => some "checkAx64_sound"
  | "ax65" => some "checkAx65_sound"
  | "ax66" => some "checkAx66_sound"
  | "ax67" => some "checkAx67_sound"
  | "ax68" => some "checkAx68_sound"
  | "ax69" => some "checkAx69_sound"
  | "ax70" => some "checkAx70_sound"
  | "ax71" => some "checkAx71_sound"
  | "ax72" => some "checkAx72_sound"
  | "ax74" => some "checkAx74_sound"
  | "ax75" => some "checkAx75_sound"
  | "ax76" => some "checkAx76_sound"
  | "ax77" => some "checkAx77_sound"
  | "ax78" => some "checkAx78_sound"
  | "ax79" => some "checkAx79_sound"
  | "ax80" => some "checkAx80_sound"
  | "axQuaIndividualOfEndurant" => some "checkAxQuaIndividualOfEndurant_sound"
  | "ax81" => some "checkAx81_sound"
  | "ax82" => some "checkAx82_sound"
  | "ax83" => some "checkAx83_sound"
  | "ax84" => some "checkAx84_sound"
  | "ax85" => some "checkAx85_sound"
  | "ax86" => some "checkAx86_sound"
  | "ax87" => some "checkAx87_sound"
  | "ax88" => some "checkAx88_sound"
  | "ax89" => some "checkAx89_sound"
  | "ax90" => some "checkAx90_sound"
  | "ax91" => some "checkAx91_sound"
  | "ax92" => some "checkAx92_sound"
  | "ax93" => some "checkAx93_sound"
  | "ax94" => some "checkAx94_sound"
  | "ax95" => some "checkAx95_sound"
  | "ax96" => some "checkAx96_sound"
  | "ax97" => some "checkAx97_sound"
  | "ax98" => some "checkAx98_sound"
  | "ax99" => some "checkAx99_sound"
  | "ax100" => some "checkAx100_sound"
  | "ax101" => some "checkAx101_sound"
  | "axDistanceIdentity" => some "checkAxDistanceIdentity_sound"
  | "axDistanceSymmetry" => some "checkAxDistanceSymmetry_sound"
  | "axDistanceTriangle" => some "checkAxDistanceTriangle_sound"
  | "ax102" => some "checkAx102_sound"
  | "ax103" => some "checkAx103_sound"
  | "ax104" => some "checkAx104_sound"
  | "ax105" => some "checkAx105_sound"
  | "ax106" => some "checkAx106_sound"
  | "ax107" => some "checkAx107_sound"
  | "ax108" => some "checkAx108_sound"
  | _ => none

private structure CheckerCounterexampleBackend where
  checkFn : String
  completeTheorem : String

private def checkerCounterexampleBackend? (field : CertField) : Option CheckerCounterexampleBackend :=
  let direct (checkFn completeTheorem : String) : Option CheckerCounterexampleBackend :=
    some { checkFn, completeTheorem }
  match field.field with
  | "ax1" => direct "checkAx1" "checkAx1_complete"
  | "ax2" => direct "checkAx2" "checkAx2_complete"
  | "ax3" => direct "checkAx3" "checkAx3_complete"
  | "ax4" => direct "checkAx4" "checkAx4_complete"
  | "ax5" => direct "checkAx5" "checkAx5_complete"
  | "ax6" => direct "checkAx6" "checkAx6_complete"
  | "ax7" => direct "checkAx7" "checkAx7_complete"
  | "ax8" => direct "checkAx8" "checkAx8_complete"
  | "ax9" => direct "checkAx9" "checkAx9_complete"
  | "ax10" => direct "checkAx10" "checkAx10_complete"
  | "ax11" => direct "checkAx11" "checkAx11_complete"
  | "ax12" => direct "checkAx12" "checkAx12_complete"
  | "ax13" => direct "checkAx13" "checkAx13_complete"
  | "ax14" => direct "checkAx14" "checkAx14_complete"
  | "ax15" => direct "checkAx15" "checkAx15_complete"
  | "ax16" => direct "checkAx16" "checkAx16_complete"
  | "ax17" => direct "checkAx17" "checkAx17_complete"
  | "ax18" => direct "checkAx18" "checkAx18_complete"
  | "ax19" => direct "checkAx19" "checkAx19_complete"
  | "ax20" => direct "checkAx20" "checkAx20_complete"
  | "ax21" => direct "checkAx21" "checkAx21_complete"
  | "ax22" => direct "checkAx22" "checkAx22_complete"
  | "ax23" => direct "checkAx23" "checkAx23_complete"
  | "ax24" => direct "checkAx24" "checkAx24_complete"
  | "ax25" => direct "checkAx25" "checkAx25_complete"
  | "ax26" => direct "checkAx26" "checkAx26_complete"
  | "ax27" => direct "checkAx27" "checkAx27_complete"
  | "ax28" => direct "checkAx28" "checkAx28_complete"
  | "ax29" => direct "checkAx29" "checkAx29_complete"
  | "ax30" => direct "checkAx30" "checkAx30_complete"
  | "ax31" => direct "checkAx31" "checkAx31_complete"
  | "ax32" => direct "checkAx32" "checkAx32_complete"
  | "ax33" => direct "checkAx33" "checkAx33_complete"
  | "ax_instEndurant" => direct "checkAxInstEndurant" "checkAxInstEndurant_complete"
  | "ax_sub_kind_sortal" => direct "checkAxSubKindSortal" "checkAxSubKindSortal_complete"
  | "ax_nonSortal_up" => direct "checkAxNonSortalUp" "checkAxNonSortalUp_complete"
  | "ax_kindStable" => direct "checkAxKindStable" "checkAxKindStable_complete"
  | "ax34" => direct "checkAx34" "checkAx34_complete"
  | "ax35" => direct "checkAx35" "checkAx35_complete"
  | "ax36" => direct "checkAx36" "checkAx36_complete"
  | "ax37" => direct "checkAx37" "checkAx37_complete"
  | "ax38" => direct "checkAx38" "checkAx38_complete"
  | "ax39" => direct "checkAx39" "checkAx39_complete"
  | "ax40" => direct "checkAx40" "checkAx40_complete"
  | "ax41" => direct "checkAx41" "checkAx41_complete"
  | "ax42" => direct "checkAx42" "checkAx42_complete"
  | "ax43" => direct "checkAx43" "checkAx43_complete"
  | "ax44" => direct "checkAx44" "checkAx44_complete"
  | "ax45" => direct "checkAx45" "checkAx45_complete"
  | "ax46" => direct "checkAx46" "checkAx46_complete"
  | "ax47" => direct "checkAx47" "checkAx47_complete"
  | "ax48" => direct "checkAx48" "checkAx48_complete"
  | "ax49" => direct "checkAx49" "checkAx49_complete"
  | "ax50" => direct "checkAx50" "checkAx50_complete"
  | "ax51" => direct "checkAx51" "checkAx51_complete"
  | "ax52" => direct "checkAx52" "checkAx52_complete"
  | "ax53" => direct "checkAx53" "checkAx53_complete"
  | "ax54" => direct "checkAx54" "checkAx54_complete"
  | "ax55" => direct "checkAx55" "checkAx55_complete"
  | "ax56" => direct "checkAx56" "checkAx56_complete"
  | "ax57" => direct "checkAx57" "checkAx57_complete"
  | "ax58" => direct "checkAx58" "checkAx58_complete"
  | "ax59" => direct "checkAx59" "checkAx59_complete"
  | "ax60" => direct "checkAx60" "checkAx60_complete"
  | "ax61" => direct "checkAx61" "checkAx61_complete"
  | "ax62" => direct "checkAx62" "checkAx62_complete"
  | "ax63" => direct "checkAx63" "checkAx63_complete"
  | "ax64" => direct "checkAx64" "checkAx64_complete"
  | "ax65" => direct "checkAx65" "checkAx65_complete"
  | "ax66" => direct "checkAx66" "checkAx66_complete"
  | "ax67" => direct "checkAx67" "checkAx67_complete"
  | "ax68" => direct "checkAx68" "checkAx68_complete"
  | "ax69" => direct "checkAx69" "checkAx69_complete"
  | "ax70" => direct "checkAx70" "checkAx70_complete"
  | "ax71" => direct "checkAx71" "checkAx71_complete"
  | "ax72" => direct "checkAx72" "checkAx72_complete"
  | "ax74" => direct "checkAx74" "checkAx74_complete"
  | "ax75" => direct "checkAx75" "checkAx75_complete"
  | "ax76" => direct "checkAx76" "checkAx76_complete"
  | "ax77" => direct "checkAx77" "checkAx77_complete"
  | "ax80" => direct "checkAx80" "checkAx80_complete"
  | "axQuaIndividualOfEndurant" =>
      direct "checkAxQuaIndividualOfEndurant" "checkAxQuaIndividualOfEndurant_complete"
  | "ax81" => direct "checkAx81" "checkAx81_complete"
  | "ax82" => direct "checkAx82" "checkAx82_complete"
  | "ax83" => direct "checkAx83" "checkAx83_complete"
  | "ax84" => direct "checkAx84" "checkAx84_complete"
  | "ax85" => direct "checkAx85" "checkAx85_complete"
  | "ax86" => direct "checkAx86" "checkAx86_complete"
  | "ax87" => direct "checkAx87" "checkAx87_complete"
  | "ax88" => direct "checkAx88" "checkAx88_complete"
  | "ax89" => direct "checkAx89" "checkAx89_complete"
  | "ax90" => direct "checkAx90" "checkAx90_complete"
  | "ax91" => direct "checkAx91" "checkAx91_complete"
  | "ax92" => direct "checkAx92" "checkAx92_complete"
  | "ax93" => direct "checkAx93" "checkAx93_complete"
  | "ax94" => direct "checkAx94" "checkAx94_complete"
  | "ax95" => direct "checkAx95" "checkAx95_complete"
  | "ax96" => direct "checkAx96" "checkAx96_complete"
  | "ax97" => direct "checkAx97" "checkAx97_complete"
  | "ax98" => direct "checkAx98" "checkAx98_complete"
  | "ax100" => direct "checkAx100" "checkAx100_complete"
  | "ax101" => direct "checkAx101" "checkAx101_complete"
  | "axDistanceIdentity" =>
      direct "checkAxDistanceIdentity" "checkAxDistanceIdentity_complete"
  | "axDistanceSymmetry" =>
      direct "checkAxDistanceSymmetry" "checkAxDistanceSymmetry_complete"
  | "axDistanceTriangle" =>
      direct "checkAxDistanceTriangle" "checkAxDistanceTriangle_complete"
  | "ax102" => direct "checkAx102" "checkAx102_complete"
  | "ax103" => direct "checkAx103" "checkAx103_complete"
  | "ax104" => direct "checkAx104" "checkAx104_complete"
  | "ax105" => direct "checkAx105" "checkAx105_complete"
  | "ax106" => direct "checkAx106" "checkAx106_complete"
  | "ax107" => direct "checkAx107" "checkAx107_complete"
  | "ax108" => direct "checkAx108" "checkAx108_complete"
  | _ => none

private def checkerCertificateProof? (field : CertField) : Option String :=
  match field.field with
  | "ax73" =>
      some
        "exact LeanUfo.UFO.DSL.Checker.checkAx73_sound data (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)"
  | "ax78" =>
      some
        "exact LeanUfo.UFO.DSL.Checker.checkAx78_sound data (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)"
  | "ax79" =>
      some
        "exact LeanUfo.UFO.DSL.Checker.checkAx79_sound data (by native_decide) (by native_decide) (by native_decide)"
  | _ =>
      checkerSoundnessName? field |>.map fun theoremName =>
        s!"exact LeanUfo.UFO.DSL.Checker.{theoremName} data (by native_decide)"

private def certTactic (field : CertField) : String :=
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
* `ax68` is checker-backed in the final theorem, but the standalone proof-term
  probe can still diverge from command elaboration around the native checker
  call and generated finite closure.
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
    (_worldCount _thingCount : Nat) (_tables : FactTables) (field : CertField) : String :=
  match checkerCertificateProof? field with
  | some proof =>
      s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem {certTheoremName field.field} : {field.prop} := by
  {proof}"
  | none =>
      s!"set_option maxHeartbeats 1000000 in set_option linter.unusedSimpArgs false in theorem {certTheoremName field.field} : {field.prop} := by
{indentLines "  " (certTactic field)}"

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
  if field.field == "ax73" then
    s!"show ¬ ({field.prop}) from by
  set_option maxHeartbeats 1000000 in
  set_option maxRecDepth 20000 in
  set_option linter.unusedSimpArgs false in
  intro h
  have h47 : LeanUfo.UFO.DSL.Checker.checkAx47 data = true := by native_decide
  have h50 : LeanUfo.UFO.DSL.Checker.checkAx50 data = true := by native_decide
  have h72 : LeanUfo.UFO.DSL.Checker.checkAx72 data = true := by native_decide
  have h75 : LeanUfo.UFO.DSL.Checker.checkAx75 data = true := by native_decide
  have hcheck : LeanUfo.UFO.DSL.Checker.checkAx73 data = true :=
    LeanUfo.UFO.DSL.Checker.checkAx73_complete_with_prereqs data
      (LeanUfo.UFO.DSL.Checker.checkAx47_sound data h47)
      (LeanUfo.UFO.DSL.Checker.checkAx50_sound data h50)
      (LeanUfo.UFO.DSL.Checker.checkAx72_sound data h72)
      (LeanUfo.UFO.DSL.Checker.checkAx75_sound data h75)
      h
  have hcheckFalse : LeanUfo.UFO.DSL.Checker.checkAx73 data = false := by
    native_decide
  rw [hcheckFalse] at hcheck
  contradiction"
  else if field.field == "ax78" then
    s!"show ¬ ({field.prop}) from by
  set_option maxHeartbeats 1000000 in
  set_option maxRecDepth 20000 in
  set_option linter.unusedSimpArgs false in
  intro h
  have h48 : LeanUfo.UFO.DSL.Checker.checkAx48 data = true := by native_decide
  have h52 : LeanUfo.UFO.DSL.Checker.checkAx52 data = true := by native_decide
  have h72 : LeanUfo.UFO.DSL.Checker.checkAx72 data = true := by native_decide
  have h75 : LeanUfo.UFO.DSL.Checker.checkAx75 data = true := by native_decide
  have h77 : LeanUfo.UFO.DSL.Checker.checkAx77 data = true := by native_decide
  have h79 : LeanUfo.UFO.DSL.Checker.checkAx79 data = true := by native_decide
  have h72Sem := LeanUfo.UFO.DSL.Checker.checkAx72_sound data h72
  have h75Sem := LeanUfo.UFO.DSL.Checker.checkAx75_sound data h75
  have h79Sem := LeanUfo.UFO.DSL.Checker.checkAx79_sound_with_prereqs data h72Sem h75Sem h79
  have hcheck : LeanUfo.UFO.DSL.Checker.checkAx78 data = true :=
    LeanUfo.UFO.DSL.Checker.checkAx78_complete_with_prereqs data
      (LeanUfo.UFO.DSL.Checker.checkAx48_sound data h48)
      (LeanUfo.UFO.DSL.Checker.checkAx52_sound data h52)
      h72Sem
      h75Sem
      (LeanUfo.UFO.DSL.Checker.checkAx77_sound data h77)
      h79Sem
      h
  have hcheckFalse : LeanUfo.UFO.DSL.Checker.checkAx78 data = false := by
    native_decide
  rw [hcheckFalse] at hcheck
  contradiction"
  else if field.field == "ax79" then
    s!"show ¬ ({field.prop}) from by
  set_option maxHeartbeats 1000000 in
  set_option maxRecDepth 20000 in
  set_option linter.unusedSimpArgs false in
  intro h
  have h72 : LeanUfo.UFO.DSL.Checker.checkAx72 data = true := by native_decide
  have h75 : LeanUfo.UFO.DSL.Checker.checkAx75 data = true := by native_decide
  have hcheck : LeanUfo.UFO.DSL.Checker.checkAx79 data = true :=
    LeanUfo.UFO.DSL.Checker.checkAx79_complete_with_prereqs data
      (LeanUfo.UFO.DSL.Checker.checkAx72_sound data h72)
      (LeanUfo.UFO.DSL.Checker.checkAx75_sound data h75)
      h
  have hcheckFalse : LeanUfo.UFO.DSL.Checker.checkAx79 data = false := by
    native_decide
  rw [hcheckFalse] at hcheck
  contradiction"
  else match checkerCounterexampleBackend? field with
  | some backend =>
    s!"show ¬ ({field.prop}) from by
  set_option maxHeartbeats 1000000 in
  set_option maxRecDepth 20000 in
  set_option linter.unusedSimpArgs false in
  intro h
  have hcheck : LeanUfo.UFO.DSL.Checker.{backend.checkFn} data = true :=
    LeanUfo.UFO.DSL.Checker.{backend.completeTheorem} data h
  have hcheckFalse : LeanUfo.UFO.DSL.Checker.{backend.checkFn} data = false := by
    native_decide
  rw [hcheckFalse] at hcheck
  contradiction"
  | none =>
    s!"show ¬ ({field.prop}) from by
  set_option maxHeartbeats 1000000 in
  set_option maxRecDepth 20000 in
  set_option linter.unusedSimpArgs false in
  {certificateSimp} <;> (try omega) <;> (try grind) <;> native_decide"

def certAxiomProofCheck
    (_worldCount _thingCount : Nat) (_tables : FactTables) (field : CertField) : String :=
  match checkerCertificateProof? field with
  | some proof =>
      s!"show {field.prop} from by
  set_option maxHeartbeats 1000000 in
  set_option linter.unusedSimpArgs false in
  {proof}"
  | none =>
      s!"show {field.prop} from by
  set_option maxHeartbeats 1000000 in
  set_option linter.unusedSimpArgs false in
{indentLines "  " (certTactic field)}"

end LeanUfo.UFO.DSL
