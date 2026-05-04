import LeanUfo.UFO.Core.Signature3_6
import LeanUfo.UFO.Core.Section3_5

universe u v

variable (Sig : UFOSignature3_6)

open UFOSignature3_6

/-
  §3.6 — Composition

  This section adds the functional-composition vocabulary used in the paper.
-/

/--
(a53)

gfd(x', y') ↔
  ∀x (x :: x' ∧ FunctionsAs(x, x') →
    ∃y (¬(y = x) ∧ y :: y' ∧ FunctionsAs(y, y')))

Natural language:
Type `x'` generically functionally depends on type `y'` exactly when every
instance of `x'` that functions as `x'` is accompanied by a distinct
instance of `y'` that functions as `y'`.
-/
def ax_a53 : Prop :=
  ∀ (x' y' : Sig.Thing) (w : Sig.F.World),
    Sig.GenericFunctionalDependence x' y' w ↔
      ∀ x : Sig.Thing,
        (Sig.Inst x x' w ∧ Sig.FunctionsAs x x' w) →
          ∃ y : Sig.Thing,
            y ≠ x ∧
            Sig.Inst y y' w ∧
            Sig.FunctionsAs y y' w

/--
(a54)

ifd(x, x', y, y') ↔
  gfd(x', y') ∧ x :: x' ∧ y :: y' ∧ (FunctionsAs(x, x') → FunctionsAs(y, y'))

Natural language:
Individual functional dependence relates individuals of the corresponding
types whenever the type-level generic dependence holds and the relevant
functional roles are aligned.
-/
def ax_a54 : Prop :=
  ∀ (x x' y y' : Sig.Thing) (w : Sig.F.World),
    Sig.IndividualFunctionalDependence x x' y y' w ↔
      (Sig.GenericFunctionalDependence x' y' w ∧
       Sig.Inst x x' w ∧
       Sig.Inst y y' w ∧
       (Sig.FunctionsAs x x' w → Sig.FunctionsAs y y' w))

/--
(a55)

ComponentOf(x, x', y, y') ↔ ProperPart(x, y) ∧ ifd(x, x', y, y')

Natural language:
An individual is a component of another exactly when it is a proper part of
it and stands in the relevant individual functional dependence relation.
-/
def ax_a55 : Prop :=
  ∀ (x x' y y' : Sig.Thing) (w : Sig.F.World),
    Sig.ComponentOf x x' y y' w ↔
      (Sig.ProperPart x y w ∧
       Sig.IndividualFunctionalDependence x x' y y' w)

/--
Axioms package for §3.6.

Extends §3.5 axioms with:
- (a53) generic functional dependence,
- (a54) individual functional dependence,
- (a55) componenthood.
-/
class UFOAxioms3_6 (Sig : UFOSignature3_6) : Prop
  extends UFOAxioms3_5 Sig.toUFOSignature3_5 where

  -- §3.6 axioms
  ax53 : ax_a53 Sig
  ax54 : ax_a54 Sig
  ax55 : ax_a55 Sig
