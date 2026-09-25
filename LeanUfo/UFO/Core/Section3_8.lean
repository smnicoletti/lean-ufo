import LeanUfo.UFO.Core.Signature3_8
import LeanUfo.UFO.Core.Section3_7

universe u v

variable (Sig : UFOSignature3_8)

open UFOSignature3_8

/-
  §3.8 — Existence and existential dependence

  This section adds the existence-based dependence vocabulary used in the
  paper.
-/

/--
(a62)

ex(x) → Thing(x)

Natural language:
Whatever exists is a thing.

In this Lean formalization, variables already range over `Sig.Thing`, so the
`Thing(x)` part is built into typing. Accordingly, the axiom reduces to a
trivial well-typedness condition.
-/
def ax_a62 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Ex x w → True

/--
(a63)

ed(x, y) ↔ □(ex(x) → ex(y))

Natural language:
`x` existentially depends on `y` exactly when, at every accessible world,
the existence of `x` implies the existence of `y`.
-/
def ax_a63 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.ExistentialDependence x y w ↔
      Frame.Box (F := Sig.F)
        (fun w' => Sig.Ex x w' → Sig.Ex y w')
        w

/--
(a64)

ind(x, y) ↔ ¬ed(x, y) ∧ ¬ed(y, x)

Natural language:
Two entities are existentially independent exactly when neither existentially
depends on the other.
-/
def ax_a64 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.ExistentialIndependence x y w ↔
      (¬ Sig.ExistentialDependence x y w ∧
       ¬ Sig.ExistentialDependence y x w)

/--
Axioms package for §3.8.

Extends §3.7 axioms with:
- (a62) existence is only predicated of things,
- (a63) definition of existential dependence,
- (a64) definition of existential independence.
-/
class UFOAxioms3_8 (Sig : UFOSignature3_8) : Prop
  extends UFOAxioms3_7 Sig.toUFOSignature3_7 where

  -- §3.8 axioms
  ax62 : ax_a62 Sig
  ax63 : ax_a63 Sig
  ax64 : ax_a64 Sig
