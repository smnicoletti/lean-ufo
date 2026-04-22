import LeanUfo.UFO.Core.Signature3_10
import LeanUfo.UFO.Core.Section3_9
import Mathlib.Logic.ExistsUnique

universe u v

variable (Sig : UFOSignature3_10)

open UFOSignature3_10

/-
  §3.10 — Relators

  This section adds the core predicates used to characterize externally
  dependent modes, qua individuals, relators, and mediation.
-/

/--
(a69)

externallyDependent(x, y) ↔ ed(x, y) ∧ ∀z (inheresIn(x, z) → ind(y, z))

Natural language:
`x` is externally dependent on `y` exactly when `x` existentially depends on
`y` and every bearer of `x` is existentially independent of `y`.
-/
def ax_a69 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.ExternallyDependent x y w ↔
      (Sig.ExistentialDependence x y w ∧
       ∀ z : Sig.Thing,
         Sig.InheresIn x z w →
           Sig.ExistentialIndependence y z w)

/--
(a70)

ExternallyDependentMode(x) ↔ Mode(x) ∧ ∃y (externallyDependent(x, y))

Natural language:
An externally dependent mode is exactly a mode that is externally dependent on
something.
-/
def ax_a70 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.ExternallyDependentMode x w ↔
      (Sig.Mode x w ∧
       ∃ y : Sig.Thing,
         Sig.ExternallyDependent x y w)

/--
(a71)

foundedBy(x, y) → (ExternallyDependentMode(x) ∨ Relator(x)) ∧ Perdurant(y)

Natural language:
Whatever is founded is either an externally dependent mode or a relator, and
its foundation is a perdurant.
-/
def ax_a71 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.FoundedBy x y w →
      ((Sig.ExternallyDependentMode x w ∨ Sig.Relator x w) ∧
       Sig.Perdurant y w)

/--
(a72)

ExternallyDependentMode(x) → ∃!y (foundedBy(x, y))

Natural language:
Every externally dependent mode has a unique foundation.

We use mathlib's `∃!` / `ExistsUnique` notation here to stay close to the
paper's formulation.
-/
def ax_a72 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.ExternallyDependentMode x w →
      ∃! y : Sig.Thing, Sig.FoundedBy x y w

/--
Definition (d4): foundation of.

The paper presents `foundationOf(x)` as a definite description of the unique
entity on which `x` is founded. We encode it via `Classical.epsilon`, using
the ambient nonemptiness of `Sig.Thing`.

When uniqueness is available, `foundationOf_eq_iff` recovers the intended
definite-description behavior.
-/

noncomputable def FoundationOf (Sig : UFOSignature3_10)
    (x : Sig.Thing) (w : Sig.F.World) :=
  @Classical.epsilon Sig.Thing Sig.thing_nonempty (fun y => Sig.FoundedBy x y w)

/--
Defining property of `FoundationOf`.

This is the exact content of the paper's clause `foundationOf(x) = y ↔
foundedBy(x, y)`, specialized to the unique witness selected by the definite
description.
-/
theorem foundationOf_eq_iff
  {x y : Sig.Thing} {w : Sig.F.World}
  (h : ∃! u : Sig.Thing, Sig.FoundedBy x u w) :
  FoundationOf Sig x w = y ↔ Sig.FoundedBy x y w :=
by
  have hFound : Sig.FoundedBy x (FoundationOf Sig x w) w := by
    exact Classical.epsilon_spec h.exists
  constructor
  · intro hEq
    simpa [hEq] using hFound
  · intro hy
    exact h.unique hFound hy

/--
(a73)

quaIndividualOf(x, y) ↔
  ∀z (O(z, x) ↔ (ExternallyDependentMode(z) ∧ inheresIn(z, y) ∧
                  foundationOf(z) = foundationOf(x)))

Natural language:
`x` is a qua individual of `y` exactly when its overlappers are precisely the
externally dependent modes that inhere in `y` and share the same foundation as
`x`.

We encode equality of `foundationOf` terms directly.
-/
def ax_a73 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.QuaIndividualOf x y w ↔
      ∀ z : Sig.Thing,
        Sig.Overlap z x w ↔
          (Sig.ExternallyDependentMode z w ∧
           Sig.InheresIn z y w ∧
           FoundationOf Sig z w = FoundationOf Sig x w)

/--
(t31)

quaIndividualOf(x, y) ∧ x' P x → foundationOf(x) = foundationOf(x')

Natural language:
Every part of a qua individual has the same foundation as the qua individual.

Again, equality of `foundationOf` terms is encoded directly.
-/
theorem th_t31
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA73 : ax_a73 Sig) :
  ∀ (x x' y : Sig.Thing) (w : Sig.F.World),
    (Sig.QuaIndividualOf x y w ∧ Sig.Part x' x w) →
      FoundationOf Sig x w = FoundationOf Sig x' w :=
by
  intro x x' y w h
  rcases h with ⟨hQua, hPart⟩
  have hOv : Sig.Overlap x' x w :=
    (hA50 x' x w).2 ⟨x', hA47 x' w, hPart⟩
  have hx' : Sig.ExternallyDependentMode x' w ∧
      Sig.InheresIn x' y w ∧
      FoundationOf Sig x' w = FoundationOf Sig x w :=
    ((hA73 x y w).1 hQua x').1 hOv
  grind

/--
(a74)

QuaIndividual(x) ↔ ∃y quaIndividualOf(x, y)

Natural language:
An entity is a qua individual exactly when it is a qua individual of
something.
-/
def ax_a74 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.QuaIndividual x w ↔
      ∃ y : Sig.Thing,
        Sig.QuaIndividualOf x y w

/--
(a75)

QuaIndividual(x) → ExternallyDependentMode(x)

Natural language:
Every qua individual is an externally dependent mode.
-/
def ax_a75 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.QuaIndividual x w →
      Sig.ExternallyDependentMode x w

/--
(a76)

quaIndividualOf(x, y) ∧ quaIndividualOf(x, y') → y = y'

Natural language:
A qua individual cannot be a qua individual of two distinct entities.
-/
def ax_a76 : Prop :=
  ∀ (x y y' : Sig.Thing) (w : Sig.F.World),
    (Sig.QuaIndividualOf x y w ∧ Sig.QuaIndividualOf x y' w) →
      y = y'

/--
(a77)

Relator(x) → ∃!y (foundedBy(x, y))

Natural language:
Every relator has a unique foundation.

As above, we use the paper's `∃!` notation directly.
-/
def ax_a77 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Relator x w →
      ∃! y : Sig.Thing, Sig.FoundedBy x y w

/--
(a78)

Relator(x) ∧ y P x → foundationOf(x) = foundationOf(y)

Natural language:
Every part of a relator shares the relator's foundation.

As above, equality of `foundationOf` terms is encoded directly.
-/
def ax_a78 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    (Sig.Relator x w ∧ Sig.Part y x w) →
      FoundationOf Sig x w = FoundationOf Sig y w

/--
(a79)

Relator(x) ↔
  ∃y (PP(y, x)) ∧
  ∀y, z((PP(y, x) ∧ PP(z, x)) →
    (QuaIndividual(y) ∧ QuaIndividual(z) ∧
     foundationOf(y) = foundationOf(z) ∧ ed(y, z) ∧ ed(z, y))) ∧
  ∀y, z((PP(y, x) ∧ QuaIndividual(z) ∧
         foundationOf(y) = foundationOf(z) ∧ ed(y, z) ∧ ed(z, y)) → PP(z, x))

Natural language:
Relators are exactly sums of qua individuals that share a foundation and are
mutually existentially dependent.

Again, equality of `foundationOf` terms is encoded directly.
-/
def ax_a79 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Relator x w ↔
      (∃ y : Sig.Thing,
        Sig.ProperPart y x w)
      ∧
      (∀ y z : Sig.Thing,
        (Sig.ProperPart y x w ∧ Sig.ProperPart z x w) →
          (Sig.QuaIndividual y w ∧
           Sig.QuaIndividual z w ∧
           (FoundationOf Sig y w = FoundationOf Sig z w) ∧
           Sig.ExistentialDependence y z w ∧
           Sig.ExistentialDependence z y w))
      ∧
      (∀ y z : Sig.Thing,
        (Sig.ProperPart y x w ∧
         Sig.QuaIndividual z w ∧
         (FoundationOf Sig y w = FoundationOf Sig z w) ∧
         Sig.ExistentialDependence y z w ∧
         Sig.ExistentialDependence z y w) →
          Sig.ProperPart z x w)

/--
(t32)

Relator(x) → ∃x', x'', y', y''(quaIndividualOf(x', y') ∧ quaIndividualOf(x'', y''))

Natural language:
Every relator has at least two qua individuals as parts.
-/
theorem th_t32
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA74 : ax_a74 Sig)
  (hA79 : ax_a79 Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Relator x w →
      ∃ x' x'' y' y'' : Sig.Thing,
        Sig.QuaIndividualOf x' y' w ∧
        Sig.QuaIndividualOf x'' y'' w :=
by
  intro x w hRel
  rcases (hA79 x w).1 hRel with ⟨⟨p, hPPp⟩, hPairwise, _hClosure⟩
  rcases (hA52 p x w).1 hPPp with ⟨hpPartx, hNotPartxp⟩
  rcases hA51 p x w hNotPartxp with ⟨q, hqPartx, hNoOvqp⟩
  have hNotPartxq : ¬ Sig.Part x q w := by
    intro hxq
    have hpq : Sig.Part p q w := hA49 p x q w ⟨hpPartx, hxq⟩
    have hOvqp' : Sig.Overlap q p w :=
      (hA50 q p w).2 ⟨p, hpq, hA47 p w⟩
    exact hNoOvqp hOvqp'
  have hPPq : Sig.ProperPart q x w :=
    (hA52 q x w).2 ⟨hqPartx, hNotPartxq⟩
  have hInfo := hPairwise p q ⟨hPPp, hPPq⟩
  have hQp : Sig.QuaIndividual p w := hInfo.1
  have hQq : Sig.QuaIndividual q w := hInfo.2.1
  rcases (hA74 p w).1 hQp with ⟨y', hQOfp⟩
  rcases (hA74 q w).1 hQq with ⟨y'', hQOfq⟩
  exact ⟨p, q, y', y'', hQOfp, hQOfq⟩

/--
(a80)

mediates(x, y) ↔ Relator(x) ∧ Endurant(y) ∧ ∃z (quaIndividualOf(z, y) ∧ P(z, x))

Natural language:
A relator mediates an endurant exactly when one of its parts is a qua
individual of that endurant.
-/
def ax_a80 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Mediates x y w ↔
      (Sig.Relator x w ∧
       Sig.Endurant y w ∧
       ∃ z : Sig.Thing,
         Sig.QuaIndividualOf z y w ∧
         Sig.Part z x w)

/--
NOTE:
Bridge axiom needed for (t33):

(typing of the bearer of a qua individual)
If `x` is a qua individual of `y`, then `y` is an endurant.

This is an implicit typing assumption in the paper:
the entity a relator mediates is an endurant.
-/
def ax_quaIndividualOf_endurant : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.QuaIndividualOf x y w →
      Sig.Endurant y w

/--
(aux)

If two entities overlap exactly the same things, then they are equal.

This is the extensionality principle derivable from the mereology axioms
already used elsewhere in the development.
-/
theorem eq_of_same_overlappers
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA48 : ax_a48 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5) :
  ∀ {x y : Sig.Thing} {w : Sig.F.World},
    (∀ z : Sig.Thing, Sig.Overlap z x w ↔ Sig.Overlap z y w) →
      x = y
:= by
  intro x y w hSame
  apply hA48 x y w
  constructor
  · by_cases hPartxy : Sig.Part x y w
    · exact hPartxy
    · rcases hA51 y x w hPartxy with ⟨z, hzPartx, hzNotOvy⟩
      have hzOvx : Sig.Overlap z x w :=
        (hA50 z x w).2 ⟨z, hA47 z w, hzPartx⟩
      exact False.elim (hzNotOvy ((hSame z).1 hzOvx))
  · by_cases hPartyx : Sig.Part y x w
    · exact hPartyx
    · rcases hA51 x y w hPartyx with ⟨z, hzParty, hzNotOvx⟩
      have hzOvy : Sig.Overlap z y w :=
        (hA50 z y w).2 ⟨z, hA47 z w, hzParty⟩
      exact False.elim (hzNotOvx ((hSame z).2 hzOvy))

/--
(t33)

Relator(x) → ∃y, z(y ≠ z ∧ mediates(x, y) ∧ mediates(x, z))

Natural language:
Every relator mediates at least two distinct endurants.

To derive this in the current formalization, we use the bridge axiom
`ax_quaIndividualOf_endurant`, which makes explicit the intended typing of the
bearer of a qua individual.
-/
theorem th_t33
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA48 : ax_a48 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA73 : ax_a73 Sig)
  (hA74 : ax_a74 Sig)
  (hA79 : ax_a79 Sig)
  (hA80 : ax_a80 Sig)
  (hQuaEnd : ax_quaIndividualOf_endurant (Sig := Sig)) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Relator x w →
      ∃ y z : Sig.Thing,
        y ≠ z ∧ Sig.Mediates x y w ∧ Sig.Mediates x z w
:= by
  intro x w hRel
  rcases (hA79 x w).1 hRel with ⟨⟨p, hPPp⟩, hPairwise, _hClosure⟩
  rcases (hA52 p x w).1 hPPp with ⟨hpPartx, hNotPartxp⟩
  rcases hA51 p x w hNotPartxp with ⟨q, hqPartx, hNoOvqp⟩
  have hNotPartxq : ¬ Sig.Part x q w := by
    intro hxq
    have hpq : Sig.Part p q w := hA49 p x q w ⟨hpPartx, hxq⟩
    have hOvqp' : Sig.Overlap q p w :=
      (hA50 q p w).2 ⟨p, hpq, hA47 p w⟩
    exact hNoOvqp hOvqp'
  have hPPq : Sig.ProperPart q x w :=
    (hA52 q x w).2 ⟨hqPartx, hNotPartxq⟩
  have hpNeq : p ≠ q := by
    intro hpq
    subst hpq
    have hOvpp : Sig.Overlap p p w :=
      (hA50 p p w).2 ⟨p, hA47 p w, hA47 p w⟩
    exact hNoOvqp hOvpp
  rcases hPairwise p q ⟨hPPp, hPPq⟩ with ⟨hQp, hQq, hFoEq, _hEDpq, _hEDqp⟩
  rcases (hA74 p w).1 hQp with ⟨y, hQOfp⟩
  rcases (hA74 q w).1 hQq with ⟨z, hQOfq⟩
  have hEndy : Sig.Endurant y w := hQuaEnd p y w hQOfp
  have hEndz : Sig.Endurant z w := hQuaEnd q z w hQOfq
  have hyNez : y ≠ z := by
    intro hyz
    have hSameOverlaps : ∀ u : Sig.Thing, Sig.Overlap u p w ↔ Sig.Overlap u q w := by
      intro u
      constructor
      · intro huOp
        have huData :=
          ((hA73 p y w).1 hQOfp u).1 huOp
        have huData' :
            Sig.ExternallyDependentMode u w ∧
            Sig.InheresIn u z w ∧
            FoundationOf Sig u w = FoundationOf Sig q w := by
          refine ⟨huData.1, ?_, ?_⟩
          · simpa [hyz] using huData.2.1
          · rw [huData.2.2, hFoEq]
        exact ((hA73 q z w).1 hQOfq u).2 huData'
      · intro huOq
        have huData :=
          ((hA73 q z w).1 hQOfq u).1 huOq
        have huData' :
            Sig.ExternallyDependentMode u w ∧
            Sig.InheresIn u y w ∧
            FoundationOf Sig u w = FoundationOf Sig p w := by
          refine ⟨huData.1, ?_, ?_⟩
          · simpa [hyz] using huData.2.1
          · rw [huData.2.2, hFoEq.symm]
        exact ((hA73 p y w).1 hQOfp u).2 huData'
    have hpEqq : p = q :=
      eq_of_same_overlappers (Sig := Sig) hA47 hA48 hA50 hA51 hSameOverlaps
    exact hpNeq hpEqq
  have hMedy : Sig.Mediates x y w :=
    (hA80 x y w).2 ⟨hRel, hEndy, ⟨p, hQOfp, hpPartx⟩⟩
  have hMedz : Sig.Mediates x z w :=
    (hA80 x z w).2 ⟨hRel, hEndz, ⟨q, hQOfq, hqPartx⟩⟩
  exact ⟨y, z, hyNez, hMedy, hMedz⟩

/--
Axioms package for §3.10.

Extends §3.9 axioms with:
- (a69) external dependence,
- (a70) externally dependent modes,
- (a71) constraints on foundations,
- (a72) uniqueness of foundation for externally dependent modes,
- (a73) qua individuals,
- (a74) definition of qua individual,
- (a75) qua individuals are externally dependent modes,
- (a76) uniqueness of bearer of a qua individual,
- (a77) uniqueness of foundation for relators,
- (a78) parts of relators share the same foundation,
- (a79) definition of relator,
- (a80) mediation.

Also records the bridge axiom required for (t33):
- qua individuals are of endurants.
-/
class UFOAxioms3_10 (Sig : UFOSignature3_10) : Prop
  extends UFOAxioms3_9 Sig.toUFOSignature3_9 where

  -- §3.10 axioms
  ax69 : ax_a69 Sig
  ax70 : ax_a70 Sig
  ax71 : ax_a71 Sig
  ax72 : ax_a72 Sig
  ax73 : ax_a73 Sig
  ax74 : ax_a74 Sig
  ax75 : ax_a75 Sig
  ax76 : ax_a76 Sig
  ax77 : ax_a77 Sig
  ax78 : ax_a78 Sig
  ax79 : ax_a79 Sig
  ax80 : ax_a80 Sig

  -- Bridge assumption required for t33
  axQuaIndividualOfEndurant :
    ax_quaIndividualOf_endurant (Sig := Sig)
