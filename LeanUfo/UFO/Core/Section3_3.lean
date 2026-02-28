import LeanUfo.UFO.Core.Signature3_3
import LeanUfo.UFO.Core.Section3_2
import LeanUfo.UFO.Modal.Basics

universe u v

variable (Sig : UFOSignature3_3)

open UFOSignature3_3

/-
  §3.3 — Endurants

  This section axiomatizes the partition structure of Endurant individuals
  into Substantial and Moment, and their refinements down to the leaf
  individual categories.
-/

/--
(a34)

Substantial(x) ∨ Moment(x) ↔ Endurant(x)

Natural language:
Substantial and Moment form a partition of Endurant individuals.
-/
def ax_a34 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    (Sig.Substantial x w ∨ Sig.Moment x w)
      ↔ Sig.Endurant x w


/--
(a35)

¬∃x (Substantial(x) ∧ Moment(x))

Natural language:
Nothing can be both Substantial and Moment.
-/
def ax_a35 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
        Sig.Substantial x w ∧
        Sig.Moment x w


/--
(a36)

Object(x) ∨ Collective(x) ∨ Quantity(x) ↔ Substantial(x)

Natural language:
Object, Collective and Quantity form a partition of Substantial.
-/
def ax_a36 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    (Sig.Object x w ∨
     Sig.Collective x w ∨
     Sig.Quantity x w)
      ↔ Sig.Substantial x w


/--
(a37)

¬∃x (Object(x) ∧ Collective(x))

Natural language:
Object and Collective are disjoint.
-/
def ax_a37 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
        Sig.Object x w ∧
        Sig.Collective x w


/--
(a38)

¬∃x (Object(x) ∧ Quantity(x))

Natural language:
Object and Quantity are disjoint.
-/
def ax_a38 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
        Sig.Object x w ∧
        Sig.Quantity x w


/--
(a39)

¬∃x (Collective(x) ∧ Quantity(x))

Natural language:
Collective and Quantity are disjoint.
-/
def ax_a39 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
        Sig.Collective x w ∧
        Sig.Quantity x w


/--
(a40)

Relator(x) ∨ IntrinsicMoment(x) ↔ Moment(x)

Natural language:
Relator and IntrinsicMoment form a partition of Moment.
-/
def ax_a40 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    (Sig.Relator x w ∨ Sig.IntrinsicMoment x w)
      ↔ Sig.Moment x w


/--
(a41)

¬∃x (Relator(x) ∧ IntrinsicMoment(x))

Natural language:
Relator and IntrinsicMoment are disjoint.
-/
def ax_a41 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
        Sig.Relator x w ∧
        Sig.IntrinsicMoment x w


/--
(a42)

Mode(x) ∨ Quality(x) ↔ IntrinsicMoment(x)

Natural language:
Mode and Quality form a partition of IntrinsicMoment.
-/
def ax_a42 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    (Sig.Mode x w ∨ Sig.Quality x w)
      ↔ Sig.IntrinsicMoment x w


/--
(a43)

¬∃x (Mode(x) ∧ Quality(x))

Natural language:
Mode and Quality are disjoint.
-/
def ax_a43 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
        Sig.Mode x w ∧
        Sig.Quality x w
/--
(t19)

The six leaf endurant categories
(Object, Collective, Quantity, Relator, Mode, Quality)
are pairwise disjoint.

Natural language:
No individual can belong to two distinct leaf categories.
-/
theorem th_t19
  (hA35 : ax_a35 Sig)
  (hA36 : ax_a36 Sig)
  (hA37 : ax_a37 Sig)
  (hA38 : ax_a38 Sig)
  (hA39 : ax_a39 Sig)
  (hA40 : ax_a40 Sig)
  (hA41 : ax_a41 Sig)
  (hA42 : ax_a42 Sig)
  (hA43 : ax_a43 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),

    (Sig.Object t w →
      ¬ Sig.Collective t w ∧
      ¬ Sig.Quantity t w ∧
      ¬ Sig.Relator t w ∧
      ¬ Sig.Mode t w ∧
      ¬ Sig.Quality t w)

    ∧

    (Sig.Collective t w →
      ¬ Sig.Quantity t w ∧
      ¬ Sig.Relator t w ∧
      ¬ Sig.Mode t w ∧
      ¬ Sig.Quality t w)

    ∧

    (Sig.Quantity t w →
      ¬ Sig.Relator t w ∧
      ¬ Sig.Mode t w ∧
      ¬ Sig.Quality t w)

    ∧

    (Sig.Relator t w →
      ¬ Sig.Mode t w ∧
      ¬ Sig.Quality t w)

    ∧

    (Sig.Mode t w →
      ¬ Sig.Quality t w)
:=
by
  classical
  intro t w
  refine ⟨?obj, ?coll, ?quant, ?rel, ?mode⟩

  --------------------------------------------------
  -- Object block
  --------------------------------------------------
  · intro hObj
    have hSub :
      Sig.Substantial t w :=
      (hA36 t w).1 (Or.inl hObj)

    refine ⟨?_, ?_, ?_, ?_, ?_⟩

    · intro hColl
      exact (hA37 w) ⟨t, hObj, hColl⟩

    · intro hQ
      exact (hA38 w) ⟨t, hObj, hQ⟩

    · intro hRel
      have hMom :
        Sig.Moment t w :=
        (hA40 t w).1 (Or.inl hRel)
      exact (hA35 w) ⟨t, hSub, hMom⟩

    · intro hMode
      have hIM :
        Sig.IntrinsicMoment t w :=
        (hA42 t w).1 (Or.inl hMode)
      have hMom :
        Sig.Moment t w :=
        (hA40 t w).1 (Or.inr hIM)
      exact (hA35 w) ⟨t, hSub, hMom⟩

    · intro hQual
      have hIM :
        Sig.IntrinsicMoment t w :=
        (hA42 t w).1 (Or.inr hQual)
      have hMom :
        Sig.Moment t w :=
        (hA40 t w).1 (Or.inr hIM)
      exact (hA35 w) ⟨t, hSub, hMom⟩

  --------------------------------------------------
  -- Collective block
  --------------------------------------------------
  · intro hColl
    have hSub :
      Sig.Substantial t w :=
      (hA36 t w).1 (Or.inr (Or.inl hColl))

    refine ⟨?_, ?_, ?_, ?_⟩

    · intro hQ
      exact (hA39 w) ⟨t, hColl, hQ⟩

    · intro hRel
      have hMom :=
        (hA40 t w).1 (Or.inl hRel)
      exact (hA35 w) ⟨t, hSub, hMom⟩

    · intro hMode
      have hIM :=
        (hA42 t w).1 (Or.inl hMode)
      have hMom :=
        (hA40 t w).1 (Or.inr hIM)
      exact (hA35 w) ⟨t, hSub, hMom⟩

    · intro hQual
      have hIM :=
        (hA42 t w).1 (Or.inr hQual)
      have hMom :=
        (hA40 t w).1 (Or.inr hIM)
      exact (hA35 w) ⟨t, hSub, hMom⟩

  --------------------------------------------------
  -- Quantity block
  --------------------------------------------------
  · intro hQ
    have hSub :
      Sig.Substantial t w :=
      (hA36 t w).1 (Or.inr (Or.inr hQ))

    refine ⟨?_, ?_, ?_⟩

    · intro hRel
      have hMom :=
        (hA40 t w).1 (Or.inl hRel)
      exact (hA35 w) ⟨t, hSub, hMom⟩

    · intro hMode
      have hIM :=
        (hA42 t w).1 (Or.inl hMode)
      have hMom :=
        (hA40 t w).1 (Or.inr hIM)
      exact (hA35 w) ⟨t, hSub, hMom⟩

    · intro hQual
      have hIM :=
        (hA42 t w).1 (Or.inr hQual)
      have hMom :=
        (hA40 t w).1 (Or.inr hIM)
      exact (hA35 w) ⟨t, hSub, hMom⟩

  --------------------------------------------------
  -- Relator block
  --------------------------------------------------
  · intro hRel
    refine ⟨?_, ?_⟩

    · intro hMode
      have hIM :=
        (hA42 t w).1 (Or.inl hMode)
      exact (hA41 w) ⟨t, hRel, hIM⟩

    · intro hQual
      have hIM :=
        (hA42 t w).1 (Or.inr hQual)
      exact (hA41 w) ⟨t, hRel, hIM⟩

  --------------------------------------------------
  -- Mode block
  --------------------------------------------------
  · intro hMode
    intro hQual
    exact (hA43 w) ⟨t, hMode, hQual⟩

/--
(t20)

Endurant(t) ↔
  Object(t) ∨ Collective(t) ∨ Quantity(t) ∨ Relator(t) ∨ Mode(t) ∨ Quality(t)

Natural language:
Every endurant is either a substantial (object/collective/quantity) or a moment
(relator/mode/quality), and conversely each of these categories is an endurant.
-/
theorem th_t20
  (Sig : UFOSignature3_3)
  (hA34 : ax_a34 Sig)
  (hA36 : ax_a36 Sig)
  (hA40 : ax_a40 Sig)
  (hA42 : ax_a42 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Endurant t w ↔
      (Sig.Object t w ∨
       Sig.Collective t w ∨
       Sig.Quantity t w ∨
       Sig.Relator t w ∨
       Sig.Mode t w ∨
       Sig.Quality t w) :=
by
  classical
  intro t w
  constructor

  ------------------------------------------------------------------
  -- (→) Endurant → leaf disjunction
  ------------------------------------------------------------------
  · intro hEnd
    -- a34 : (Substantial ∨ Moment) ↔ Endurant
    have hSM : Sig.Substantial t w ∨ Sig.Moment t w :=
      (hA34 t w).2 hEnd

    cases hSM with
    | inl hSub =>
        -- a36 : (Object ∨ Collective ∨ Quantity) ↔ Substantial
        have hOCQ : Sig.Object t w ∨ Sig.Collective t w ∨ Sig.Quantity t w :=
          (hA36 t w).2 hSub
        cases hOCQ with
        | inl hObj =>
            exact Or.inl hObj
        | inr hRest =>
            cases hRest with
            | inl hColl =>
                exact Or.inr (Or.inl hColl)
            | inr hQ =>
                exact Or.inr (Or.inr (Or.inl hQ))

    | inr hMom =>
        -- a40 : (Relator ∨ IntrinsicMoment) ↔ Moment
        have hRI : Sig.Relator t w ∨ Sig.IntrinsicMoment t w :=
          (hA40 t w).2 hMom
        cases hRI with
        | inl hRel =>
            exact Or.inr (Or.inr (Or.inr (Or.inl hRel)))
        | inr hIM =>
            -- a42 : (Mode ∨ Quality) ↔ IntrinsicMoment
            have hMQ : Sig.Mode t w ∨ Sig.Quality t w :=
              (hA42 t w).2 hIM
            cases hMQ with
            | inl hMode =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMode))))
            | inr hQual =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQual))))

  ------------------------------------------------------------------
  -- (←) leaf disjunction → Endurant
  ------------------------------------------------------------------
  · intro hLeaf
    -- We build (Substantial ∨ Moment), then use (hA34 t w).1
    have hSM : Sig.Substantial t w ∨ Sig.Moment t w := by
      cases hLeaf with
      | inl hObj =>
          have hSub : Sig.Substantial t w :=
            (hA36 t w).1 (Or.inl hObj)
          exact Or.inl hSub
      | inr hRest =>
        cases hRest with
        | inl hColl =>
            have hSub : Sig.Substantial t w :=
              (hA36 t w).1 (Or.inr (Or.inl hColl))
            exact Or.inl hSub
        | inr hRest =>
          cases hRest with
          | inl hQ =>
              have hSub : Sig.Substantial t w :=
                (hA36 t w).1 (Or.inr (Or.inr hQ))
              exact Or.inl hSub
          | inr hRest =>
            cases hRest with
            | inl hRel =>
                have hMom : Sig.Moment t w :=
                  (hA40 t w).1 (Or.inl hRel)
                exact Or.inr hMom
            | inr hRest =>
              cases hRest with
              | inl hMode =>
                  have hIM : Sig.IntrinsicMoment t w :=
                    (hA42 t w).1 (Or.inl hMode)
                  have hMom : Sig.Moment t w :=
                    (hA40 t w).1 (Or.inr hIM)
                  exact Or.inr hMom
              | inr hQual =>
                  have hIM : Sig.IntrinsicMoment t w :=
                    (hA42 t w).1 (Or.inr hQual)
                  have hMom : Sig.Moment t w :=
                    (hA40 t w).1 (Or.inr hIM)
                  exact Or.inr hMom

    exact (hA34 t w).1 hSM

/--
Axioms package for §3.3.

Extends §3.2 axioms with (a34)–(a43),
axiomatizing the endurant individual partition.
-/
class UFOAxioms3_3 (Sig : UFOSignature3_3) : Prop
  extends UFOAxioms3_2 Sig.toUFOSignature3_2 where

  -- §3.3 axioms
  ax34 : ax_a34 Sig
  ax35 : ax_a35 Sig
  ax36 : ax_a36 Sig
  ax37 : ax_a37 Sig
  ax38 : ax_a38 Sig
  ax39 : ax_a39 Sig
  ax40 : ax_a40 Sig
  ax41 : ax_a41 Sig
  ax42 : ax_a42 Sig
  ax43 : ax_a43 Sig
