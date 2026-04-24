import LeanUfo.UFO.Core.Signature3_11
import Mathlib.Data.Set.Basic

universe u v

/--
Extension of `UFOSignature3_11` with the §3.12
quality and quality-structure predicates.

Set-theoretic notation is grounded by `SetExtension`: a UFO entity classified
as a set-like abstract individual is interpreted by a Lean `Set Thing` at each
world. This lets membership, subset, proper subset, and non-emptiness be
encoded with Lean's set theory while preserving `Thing` as the UFO domain.

The paper does not commit to a full set/arithmetic theory. We therefore use
Lean sets for ordinary membership, subset, proper subset, and non-emptiness.
For finite Cartesian products, we do not construct Lean tuples directly;
instead, tuple-like UFO entities expose coordinate projections. The
distance-arithmetic interface remains relational and abstract.
-/
structure UFOSignature3_12 extends UFOSignature3_11 where

  /- Abstract individuals used in quality structures -/
  Quale : Thing → F.World → Prop

  /-
    UFO's `Set(x)` predicate.
    The trailing underscore follows the existing `Type_` convention and avoids
    clashing with Lean's `Set`.
  -/
  Set_ : Thing → F.World → Prop

  /-- Lean-set extension of UFO set-like abstract individuals. -/
  SetExtension : Thing → F.World → Set Thing

  /- Quality structures -/
  QualityDomain : Thing → F.World → Prop
  QualityDimension : Thing → F.World → Prop
  AssociatedWith : Thing → Thing → F.World → Prop

  /-
    Quality values.
    The predicate `Quality` itself is inherited from §3.3.
  -/
  IntrinsicMomentType : Thing → F.World → Prop
  HasValue : Thing → Thing → F.World → Prop

  /--
  Projection interface for tuple-like UFO entities.

  In (a99), the paper uses the finite Cartesian product
  `y₁ × ... × yₙ` and states that a quality domain `x` is included in such a
  product. Since UFO entities are still represented by `Thing`, not by Lean
  dependent tuples, we interpret members of such a domain as tuple-like
  `Thing`s equipped with coordinate projections.

  `TupleProjection p i w` is the `i`-th coordinate of the tuple-like entity
  `p` at world `w`.

  This is intentionally weaker than postulating a full tuple construction:
  it is enough to interpret the subset claim in (a99), which only requires
  that every member of `x` have coordinates in the corresponding component
  structures.
  -/
  TupleProjection :
    {n : Nat} → Thing → Fin n → F.World → Thing

  /-
    Abstract interfaces for the metric/arithmetic part of §3.12.
    Distance values remain UFO `Thing`s; zero, addition, and order are kept as
    relations rather than committed to a concrete numeric theory.
  -/
  Distance : Thing → Thing → Thing → F.World → Prop
  DistanceZero : Thing → F.World → Prop
  DistanceSum : Thing → Thing → Thing → F.World → Prop
  DistanceGreaterEq : Thing → Thing → F.World → Prop
