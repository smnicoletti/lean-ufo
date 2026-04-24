import LeanUfo.UFO.Core.Signature3_12
import LeanUfo.UFO.Core.Section3_11
import Mathlib.Data.Set.Basic
import Mathlib.Logic.ExistsUnique

universe u v

variable (Sig : UFOSignature3_12)

open UFOSignature3_12

/-
  §3.12 — Qualities and quality structures

  This section adds quales, quality structures, quality values, simple and
  complex qualities, and the abstract distance relation on quales.

  Ordinary set notation from the paper is encoded using Lean sets via
  `Sig.SetExtension`. The finite Cartesian-product subset in (a99) is encoded
  via tuple projections rather than by constructing Lean tuple objects. The
  metric arithmetic constraints remain relational and abstract, matching the
  paper's choice not to fix a specific arithmetic theory.
-/

/-- Membership in the Lean-set extension of a UFO set-like entity. -/
def MemberOf (x s : Sig.Thing) (w : Sig.F.World) : Prop :=
  x ∈ Sig.SetExtension s w

/-- Set inclusion between Lean-set extensions of UFO set-like entities. -/
def SubsetOf (s t : Sig.Thing) (w : Sig.F.World) : Prop :=
  Sig.SetExtension s w ⊆ Sig.SetExtension t w

/-- Proper set inclusion between Lean-set extensions of UFO set-like entities. -/
def ProperSubsetOf (s t : Sig.Thing) (w : Sig.F.World) : Prop :=
  Sig.SetExtension s w ⊂ Sig.SetExtension t w

/-- Non-emptiness of the Lean-set extension of a UFO set-like entity. -/
def NonEmptySet (s : Sig.Thing) (w : Sig.F.World) : Prop :=
  (Sig.SetExtension s w).Nonempty

/--
Subset of a finite Cartesian product, interpreted through tuple projections.

The paper's (a99) uses ordinary set notation:

`x ⊆ y₁ × ... × yₙ`.

Because the UFO domain is still `Sig.Thing`, we do not identify members of
`x` with Lean dependent tuples. Instead, the signature provides
`TupleProjection`, which extracts the `i`-th coordinate of a tuple-like UFO
entity.

Thus `ProductSubsetOf x ys w` says:
every member `p` of the set-extension of `x` has, for each coordinate `i`, its
`i`-th projection in the set-extension of `ys i`.

This exactly captures the subset direction required by (a99). It deliberately
does not assert the converse direction, i.e. it does not claim that every
coordinate-compatible Lean tuple is represented by some UFO `Thing`.
-/
def ProductSubsetOf
    (x : Sig.Thing) {n : Nat} (ys : Fin n → Sig.Thing)
    (w : Sig.F.World) : Prop :=
  ∀ p : Sig.Thing,
    MemberOf Sig p x w →
      ∀ i : Fin n,
        MemberOf Sig (Sig.TupleProjection p i w) (ys i) w

/--
Definition (d5): Quality structure.

QualityStructure(x) ≝ ∃!t (QualityType(t) ∧ AssociatedWith(x, t))

Natural language:
A quality structure is an entity associated with a unique quality type.
-/
def QualityStructure (Sig : UFOSignature3_12)
    (x : Sig.Thing) (w : Sig.F.World) : Prop :=
  ∃! t : Sig.Thing,
    Sig.QualityType t w ∧
    Sig.AssociatedWith x t w

/--
Definition (d7): Simple quality.

SimpleQuality(x) ≝ Quality(x) ∧ ¬∃y inheresIn(y, x)

Natural language:
A simple quality is a quality in which no other entity inheres.
-/
def SimpleQuality (Sig : UFOSignature3_12)
    (x : Sig.Thing) (w : Sig.F.World) : Prop :=
  Quality Sig.toUFOSignature3_3 x w ∧
  ¬ ∃ y : Sig.Thing, Sig.InheresIn y x w

/--
Definition (d8): Complex quality.

ComplexQuality(x) ≝ Quality(x) ∧ ¬SimpleQuality(x)

Natural language:
A complex quality is a quality that is not simple.
-/
def ComplexQuality (Sig : UFOSignature3_12)
    (x : Sig.Thing) (w : Sig.F.World) : Prop :=
  Quality Sig.toUFOSignature3_3 x w ∧
  ¬ SimpleQuality Sig x w

/--
Definition (d9): Simple quality type.

SimpleQualityType(t) ≝ QualityType(t) ∧ ∀x (x :: t → SimpleQuality(x))

Natural language:
A simple quality type has only simple qualities as instances.
-/
def SimpleQualityType (Sig : UFOSignature3_12)
    (t : Sig.Thing) (w : Sig.F.World) : Prop :=
  Sig.QualityType t w ∧
  ∀ x : Sig.Thing,
    Sig.Inst x t w →
      SimpleQuality Sig x w

/--
Definition (d10): Complex quality type.

ComplexQualityType(t) ≝ QualityType(t) ∧ ∀x (x :: t → ComplexQuality(x))

Natural language:
A complex quality type has only complex qualities as instances.
-/
def ComplexQualityType (Sig : UFOSignature3_12)
    (t : Sig.Thing) (w : Sig.F.World) : Prop :=
  Sig.QualityType t w ∧
  ∀ x : Sig.Thing,
    Sig.Inst x t w →
      ComplexQuality Sig x w

/--
(a83)

Quale(x) → AbstractIndividual(x)

Natural language:
Every quale is an abstract individual.
-/
def ax_a83 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Quale x w →
      Sig.AbstractIndividual x w

/--
(a84)

Set(x) → AbstractIndividual(x)

Natural language:
Every set-like UFO entity is an abstract individual.
-/
def ax_a84 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Set_ x w →
      Sig.AbstractIndividual x w

/--
(a85)

¬∃x (Quale(x) ∧ Set(x))

Natural language:
Quales and set-like abstract individuals are disjoint.
-/
def ax_a85 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
      Sig.Quale x w ∧ Sig.Set_ x w

/--
(a86)

QualityStructure(x) → Set(x) ∧ x ≠ ∅

Natural language:
Every quality structure is a non-empty set-like abstract individual.
-/
def ax_a86 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    QualityStructure Sig x w →
      Sig.Set_ x w ∧ NonEmptySet Sig x w

/--
(a87)

Quale(x) ↔ ∃!y (QualityStructure(y) ∧ x ∈ y)

Natural language:
An entity is a quale exactly when it belongs to a unique quality structure.
-/
def ax_a87 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Quale x w ↔
      ∃! y : Sig.Thing,
        QualityStructure Sig y w ∧
        MemberOf Sig x y w

/--
(a88)

QualityStructure(x) ↔ QualityDomain(x) ∨ QualityDimension(x)

Natural language:
Quality structures are partitioned into quality domains and quality dimensions.
-/
def ax_a88 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    QualityStructure Sig x w ↔
      (Sig.QualityDomain x w ∨ Sig.QualityDimension x w)

/--
(a89)

QualityDomain(x) → ¬QualityDimension(x)

Natural language:
No quality domain is a quality dimension.
-/
def ax_a89 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.QualityDomain x w →
      ¬ Sig.QualityDimension x w

/--
(a90)

associatedWith(s, t) ∧ associatedWith(s', t') ∧ t' ⊏ t → s' ⊂ s

Natural language:
If a quality type properly specializes another, then its associated quality
structure is a proper subset of the supertype's associated quality structure.
-/
def ax_a90 : Prop :=
  ∀ (s t s' t' : Sig.Thing) (w : Sig.F.World),
    (Sig.AssociatedWith s t w ∧
     Sig.AssociatedWith s' t' w ∧
     ProperSub Sig.toUFOSignature3_1 t' t w) →
      ProperSubsetOf Sig s' s w

/--
(a91)

QualityType(t) ↔ IntrinsicMomentType(t) ∧
  ∃!x (QualityStructure(x) ∧ AssociatedWith(x, t))

Natural language:
An intrinsic moment type is a quality type exactly when it is associated with
a unique quality structure.
-/
def ax_a91 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.QualityType t w ↔
      (Sig.IntrinsicMomentType t w ∧
       ∃! x : Sig.Thing,
         QualityStructure Sig x w ∧
         Sig.AssociatedWith x t w)

/--
(a92)

hasValue(x, y) → Quality(x) ∧ Quale(y)

Natural language:
The value of a quality is a quale.
-/
def ax_a92 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.HasValue x y w →
      (Quality Sig.toUFOSignature3_3 x w ∧ Sig.Quale y w)

/--
(a93)

Quality(x) → ∃!y hasValue(x, y)

Natural language:
Every quality has a unique quale as value.
-/
def ax_a93 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Quality Sig.toUFOSignature3_3 x w →
      ∃! y : Sig.Thing,
        Sig.HasValue x y w

/--
(a94)

hasValue(x, y) →
  ∃t, s (x :: t ∧ associatedWith(s, t) ∧ y ∈ s)

Natural language:
Every quale value of a quality belongs to a quality structure associated with
one of the quality's types.
-/
def ax_a94 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.HasValue x y w →
      ∃ t s : Sig.Thing,
        Sig.Inst x t w ∧
        Sig.AssociatedWith s t w ∧
        MemberOf Sig y s w

/--
(a95)

associatedWith(x, y) → (QualityDimension(x) ↔ SimpleQualityType(y))

Natural language:
Quality dimensions are associated exactly with simple quality types.
-/
def ax_a95 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.AssociatedWith x y w →
      (Sig.QualityDimension x w ↔ SimpleQualityType Sig y w)

/--
(a96)

associatedWith(x, y) → (QualityDomain(x) ↔ ComplexQualityType(y))

Natural language:
Quality domains are associated exactly with complex quality types.
-/
def ax_a96 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.AssociatedWith x y w →
      (Sig.QualityDomain x w ↔ ComplexQualityType Sig y w)

/--
(a97)

ComplexQuality(x) ∧ y :: Y ∧ z :: Z ∧ inheresIn(y, x) ∧
  inheresIn(z, x) ∧ Y = Z → y = z

Natural language:
No two distinct qualities inhering in the same complex quality can be of the
same type.
-/
def ax_a97 : Prop :=
  ∀ (x y z Y Z : Sig.Thing) (w : Sig.F.World),
    (ComplexQuality Sig x w ∧
     Sig.Inst y Y w ∧
     Sig.Inst z Z w ∧
     Sig.InheresIn y x w ∧
     Sig.InheresIn z x w ∧
     Y = Z) →
      y = z

/--
(a98)

ComplexQuality(x) → ∀y (inheresIn(y, x) → SimpleQuality(y))

Natural language:
Only simple qualities can inhere in a complex quality.
-/
def ax_a98 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    ComplexQuality Sig x w →
      ∀ y : Sig.Thing,
        Sig.InheresIn y x w →
          SimpleQuality Sig y w

/--
(a99)

QualityDomain(x) ∧ associatedWith(x, t) →
  ∃y₁, ..., yₙ, z₁, ..., zₙ
    x ⊆ y₁ × ... × yₙ ∧
    ⋀ᵢ associatedWith(yᵢ, zᵢ) ∧ characterization(t, zᵢ) ∧
    ∀w (characterization(t, w) → ⋁ᵢ w = zᵢ)

Natural language:
A quality domain associated with a complex quality type is constrained by the
quality dimensions associated with the quality types characterizing that type.

Formalization note:
The finite Cartesian product subset is interpreted by `ProductSubsetOf`, using
the tuple-projection interface explained above.
The finite family itself is represented faithfully by a shared finite index
type `Fin n`; `ys i` corresponds to `yᵢ` and `zs i` corresponds to `zᵢ`.
-/
def ax_a99 : Prop :=
  ∀ (x t : Sig.Thing) (w : Sig.F.World),
    (Sig.QualityDomain x w ∧ Sig.AssociatedWith x t w) →
      ∃ n : Nat,
      ∃ ys zs : Fin n → Sig.Thing,
        ProductSubsetOf Sig x ys w ∧
        (∀ i : Fin n,
          Sig.AssociatedWith (ys i) (zs i) w ∧
          Sig.Characterization t (zs i) w) ∧
        (∀ u : Sig.Thing,
          Sig.Characterization t u w →
            ∃ i : Fin n, u = zs i)

/--
(a100)

d(x, y, r) → Quale(x) ∧ Quale(y) ∧ ∃z (x ∈ z ∧ y ∈ z)

Natural language:
The distance relation only relates quales belonging to some common quality
structure.
-/
def ax_a100 : Prop :=
  ∀ (x y r : Sig.Thing) (w : Sig.F.World),
    Sig.Distance x y r w →
      (Sig.Quale x w ∧
       Sig.Quale y w ∧
       ∃ z : Sig.Thing,
         MemberOf Sig x z w ∧
         MemberOf Sig y z w)

/--
(a101)

Quale(x) ∧ Quale(y) → ∃!r d(x, y, r)

Natural language:
Every pair of quales has a unique distance value.
-/
def ax_a101 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    (Sig.Quale x w ∧ Sig.Quale y w) →
      ∃! r : Sig.Thing,
        Sig.Distance x y r w

/--
Distance identity constraint.

x = y ∧ d(x, y, r) → r = 0

The zero-distance value is represented by the abstract predicate
`DistanceZero`.
-/
def ax_distance_identity : Prop :=
  ∀ (x y r : Sig.Thing) (w : Sig.F.World),
    (x = y ∧ Sig.Distance x y r w) →
      Sig.DistanceZero r w

/--
Distance symmetry constraint.

d(x, y, r) → d(y, x, r)
-/
def ax_distance_symmetry : Prop :=
  ∀ (x y r : Sig.Thing) (w : Sig.F.World),
    Sig.Distance x y r w →
      Sig.Distance y x r w

/--
Triangle inequality constraint.

d(x, y, r₀) ∧ d(y, z, r₁) ∧ d(x, z, r₂) ∧ +(r₀, r₁, s) → s ≥ r₂

Addition and order on distance values are represented by the abstract
relations `DistanceSum` and `DistanceGreaterEq`.
-/
def ax_distance_triangle : Prop :=
  ∀ (x y z r0 r1 r2 s : Sig.Thing) (w : Sig.F.World),
    (Sig.Distance x y r0 w ∧
     Sig.Distance y z r1 w ∧
     Sig.Distance x z r2 w ∧
     Sig.DistanceSum r0 r1 s w) →
      Sig.DistanceGreaterEq s r2 w

/--
Axioms package for §3.12.

Extends §3.11 axioms with:
- (a83)–(a101),
- the three distance constraints stated after (a101).

Definitions (d5) and (d7)–(d10) are derived predicates above, following the
convention used for earlier paper definitions such as (d1)–(d4).
-/
class UFOAxioms3_12 (Sig : UFOSignature3_12) : Prop
  extends UFOAxioms3_11 Sig.toUFOSignature3_11 where

  -- §3.12 axioms
  ax83 : ax_a83 Sig
  ax84 : ax_a84 Sig
  ax85 : ax_a85 Sig
  ax86 : ax_a86 Sig
  ax87 : ax_a87 Sig
  ax88 : ax_a88 Sig
  ax89 : ax_a89 Sig
  ax90 : ax_a90 Sig
  ax91 : ax_a91 Sig
  ax92 : ax_a92 Sig
  ax93 : ax_a93 Sig
  ax94 : ax_a94 Sig
  ax95 : ax_a95 Sig
  ax96 : ax_a96 Sig
  ax97 : ax_a97 Sig
  ax98 : ax_a98 Sig
  ax99 : ax_a99 Sig
  ax100 : ax_a100 Sig
  ax101 : ax_a101 Sig
  axDistanceIdentity : ax_distance_identity Sig
  axDistanceSymmetry : ax_distance_symmetry Sig
  axDistanceTriangle : ax_distance_triangle Sig
