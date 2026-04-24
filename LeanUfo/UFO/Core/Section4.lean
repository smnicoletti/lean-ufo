import LeanUfo.UFO.Core.Signature4
import LeanUfo.UFO.Core.Section3_13

universe u v

variable (Sig : UFOSignature4)

open UFOSignature4

/-
  §4 — Type structures

  This section adds the final structural predicates over types:
  disjointness, complete coverage, binary partitioning, and categorization.
-/

/--
(a105)

isDisjointWith(t, t') ↔
  Type(t) ∧ Type(t') ∧ ¬∃x (x :: t ∧ x :: t')

Natural language:
Two types are disjoint exactly when they are both types and have no common
instance.
-/
def ax_a105 : Prop :=
  ∀ (t t' : Sig.Thing) (w : Sig.F.World),
    Sig.IsDisjointWith t t' w ↔
      (Sig.Type_ t w ∧
       Sig.Type_ t' w ∧
       ¬ ∃ x : Sig.Thing,
         Sig.Inst x t w ∧ Sig.Inst x t' w)

/--
(a106)

isCompletelyCoveredBy(t, t', t'') ↔
  ∀x (x :: t → x :: t' ∨ x :: t'')

Natural language:
A type is completely covered by two other types exactly when every instance of
the first type instantiates at least one of the covering types.
-/
def ax_a106 : Prop :=
  ∀ (t t' t'' : Sig.Thing) (w : Sig.F.World),
    Sig.IsCompletelyCoveredBy t t' t'' w ↔
      ∀ x : Sig.Thing,
        Sig.Inst x t w →
          Sig.Inst x t' w ∨ Sig.Inst x t'' w

/--
(a107)

isPartitionedInto(t, t', t'') ↔
  isCompletelyCoveredBy(t, t', t'') ∧ isDisjointWith(t', t'')

Natural language:
A binary partition is complete coverage by two disjoint types.
-/
def ax_a107 : Prop :=
  ∀ (t t' t'' : Sig.Thing) (w : Sig.F.World),
    Sig.IsPartitionedInto t t' t'' w ↔
      (Sig.IsCompletelyCoveredBy t t' t'' w ∧
       Sig.IsDisjointWith t' t'' w)

/--
(a108)

categorizes(t₁, t₂) ↔
  Type(t₁) ∧ ∀t₃ (t₃ :: t₁ → t₃ ⊑ t₂)

Natural language:
A type categorizes another type exactly when all instances of the categorizing
type are specializations of the categorized type.

Formalization note:
The last relation in the printed formula is encoded as `Sub`, the existing
specialization predicate introduced in §3.1.
-/
def ax_a108 : Prop :=
  ∀ (t1 t2 : Sig.Thing) (w : Sig.F.World),
    Sig.Categorizes t1 t2 w ↔
      (Sig.Type_ t1 w ∧
       ∀ t3 : Sig.Thing,
         Sig.Inst t3 t1 w →
           Sig.Sub t3 t2 w)

/--
Axioms package for §4.

Extends §3.13 axioms with:
- (a105) disjointness,
- (a106) complete coverage,
- (a107) binary partitioning,
- (a108) categorization.
-/
class UFOAxioms4 (Sig : UFOSignature4) : Prop
  extends UFOAxioms3_13 Sig.toUFOSignature3_13 where

  -- §4 axioms
  ax105 : ax_a105 Sig
  ax106 : ax_a106 Sig
  ax107 : ax_a107 Sig
  ax108 : ax_a108 Sig
