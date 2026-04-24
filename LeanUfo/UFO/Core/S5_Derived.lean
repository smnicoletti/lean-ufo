
import LeanUfo.UFO.Modal.S5
import LeanUfo.UFO.Core.Section3_1
import LeanUfo.UFO.Core.Section3_2
import LeanUfo.UFO.Core.Section3_4
import LeanUfo.UFO.Core.Section3_7
import LeanUfo.UFO.Core.Section3_8

/-
  This file collects semantic consequences of adopting S5 modal semantics
  in combination with the UFO axioms of §3.1 and §3.2.

  In particular, modal definitions of key predicates (Type, Individual, Sub)
  collapse to world-invariant notions under S5 accessibility.
-/

universe u v

variable (Sig : UFOSignature3_1)

open UFOSignature3_1

/--
Derived semantic fact:

In S5, possibility is invariant across accessible worlds. Since axiom (a1)
defines `Type` via possible instantiation, this supports cross-world
stability results for `Type`.
-/
theorem type_forward_stable
  (hA1 : ax_a1 Sig) :
  ∀ (x : Sig.Thing) (w v : Sig.F.World),
    Sig.F.R w v →
    Sig.Type_ x w →
    Sig.Type_ x v :=
by
  intro x w v hRv hTw
  rw [hA1 x w] at hTw
  rw [hA1 x v]
  exact (S5Frame.dia_stable (F := Sig.F) (w := w) (v := v) hRv).1 hTw

/--
Derived semantic fact:

In S5, `Type` is invariant across accessible worlds.

That is, if `w` and `v` are S5-accessible, then `x` is a `Type`
at `w` iff it is a `Type` at `v`.
-/
theorem type_stable
  (hA1 : ax_a1 Sig) :
  ∀ (x : Sig.Thing) (w v : Sig.F.World),
    Sig.F.R w v →
    (Sig.Type_ x w ↔ Sig.Type_ x v) :=
by
  intro x w v hRv
  constructor
  · intro hTw
    exact type_forward_stable (Sig := Sig) hA1 x w v hRv hTw
  · intro hTv
    exact type_forward_stable (Sig := Sig) hA1 x v w (Sig.F.symm hRv) hTv

/--
Derived semantic fact:

In S5, necessity is invariant across accessible worlds. Since axiom (a2)
defines `Individual` via necessary non-instantiability, this supports
cross-world stability results for `Individual`.
-/
theorem individual_forward_stable
  (hA2 : ax_a2 Sig) :
  ∀ (x : Sig.Thing) (w v : Sig.F.World),
    Sig.F.R w v →
    Sig.Individual x w →
    Sig.Individual x v :=
by
  intro x w v hRv hIw
  rw [hA2 x w] at hIw
  rw [hA2 x v]
  exact (S5Frame.box_stable (F := Sig.F) (w := w) (v := v) hRv).1 hIw

/--
Derived semantic fact:

In S5, `Individual` is invariant across accessible worlds.

That is, if `w` and `v` are S5-accessible, then `x` is an `Individual`
at `w` iff it is an `Individual` at `v`.
-/
theorem individual_stable
  (hA2 : ax_a2 Sig) :
  ∀ (x : Sig.Thing) (w v : Sig.F.World),
    Sig.F.R w v →
    (Sig.Individual x w ↔ Sig.Individual x v) :=
by
  intro x w v hRv
  constructor
  · intro hIw
    exact individual_forward_stable (Sig := Sig) hA2 x w v hRv hIw
  · intro hIv
    exact individual_forward_stable (Sig := Sig) hA2 x v w (Sig.F.symm hRv) hIv

/--
Derived semantic fact:

Since `Type` and `Box` are stable across accessible worlds in S5,
specialization is also invariant across accessibility.
-/
theorem sub_stable
  (hA1 : ax_a1 Sig)
  (hA5 : ax_a5 Sig) :
  ∀ (x y : Sig.Thing) (w v : Sig.F.World),
    Sig.F.R w v →
    (Sig.Sub x y w ↔ Sig.Sub x y v) :=
by
  intro x y w v hRv
  constructor
  · intro hSub_w
    have hDef_w := (hA5 x y w).1 hSub_w
    rcases hDef_w with ⟨hTx_w, hTy_w, hBox_w⟩

    have hTx_v : Sig.Type_ x v :=
      (type_stable (Sig := Sig) hA1 x w v hRv).1 hTx_w
    have hTy_v : Sig.Type_ y v :=
      (type_stable (Sig := Sig) hA1 y w v hRv).1 hTy_w

    have hBox_v :
      Frame.Box (F := Sig.F)
        (fun w' =>
          ∀ z : Sig.Thing,
            Sig.Inst z x w' →
            Sig.Inst z y w')
        v :=
      (S5Frame.box_stable (F := Sig.F) (w := w) (v := v) hRv).1 hBox_w

    exact (hA5 x y v).2 ⟨hTx_v, hTy_v, hBox_v⟩

  · intro hSub_v
    have hDef_v := (hA5 x y v).1 hSub_v
    rcases hDef_v with ⟨hTx_v, hTy_v, hBox_v⟩

    have hTx_w : Sig.Type_ x w :=
      (type_stable (Sig := Sig) hA1 x v w (Sig.F.symm hRv)).1 hTx_v
    have hTy_w : Sig.Type_ y w :=
      (type_stable (Sig := Sig) hA1 y v w (Sig.F.symm hRv)).1 hTy_v

    have hBox_w :
      Frame.Box (F := Sig.F)
        (fun w' =>
          ∀ z : Sig.Thing,
            Sig.Inst z x w' →
            Sig.Inst z y w')
        w :=
      (S5Frame.box_stable (F := Sig.F) (w := v) (v := w) (Sig.F.symm hRv)).1 hBox_v

    exact (hA5 x y w).2 ⟨hTx_w, hTy_w, hBox_w⟩

/--
Derived semantic fact:

Proper specialization is invariant across accessible worlds, since it is
defined entirely in terms of specialization and its negation.
-/
theorem properSub_stable
  (hA1 : ax_a1 Sig)
  (hA5 : ax_a5 Sig) :
  ∀ (x y : Sig.Thing) (w v : Sig.F.World),
    Sig.F.R w v →
    (ProperSub Sig x y w ↔ ProperSub Sig x y v) :=
by
  intro x y w v hRv
  constructor
  · intro hP
    rcases hP with ⟨hSub_xy_w, hNotSub_yx_w⟩
    refine ⟨?_, ?_⟩
    · exact (sub_stable (Sig := Sig) hA1 hA5 x y w v hRv).1 hSub_xy_w
    · intro hSub_yx_v
      have hSub_yx_w :
        Sig.Sub y x w :=
        (sub_stable (Sig := Sig) hA1 hA5 y x v w (Sig.F.symm hRv)).1 hSub_yx_v
      exact hNotSub_yx_w hSub_yx_w
  · intro hP
    rcases hP with ⟨hSub_xy_v, hNotSub_yx_v⟩
    refine ⟨?_, ?_⟩
    · exact (sub_stable (Sig := Sig) hA1 hA5 x y v w (Sig.F.symm hRv)).1 hSub_xy_v
    · intro hSub_yx_w
      have hSub_yx_v :
        Sig.Sub y x v :=
        (sub_stable (Sig := Sig) hA1 hA5 y x w v hRv).1 hSub_yx_w
      exact hNotSub_yx_v hSub_yx_v

/-
  The following results move to §3.2. Unlike the earlier lemmas for `Type`,
  `Individual`, and `Sub`, they do not follow from S5 alone: they also depend
  on the explicit structural axiom `ax_kindStable`.
-/

variable (Sig2 : UFOSignature3_2)

open UFOSignature3_2

/--
Derived semantic fact (requires `ax_kindStable`), in summary:

def ax_kindStable : Prop :=
  ∀ k w v,
    Kind k w →
    R w v →
    Kind k v

Because `Kind` is postulated to persist along accessibility, and because the
frame is S5, kindhood is invariant across accessible worlds.
-/
theorem kind_stable
  (hKS : ax_kindStable Sig2) :
  ∀ (k : Sig2.Thing) (w v : Sig2.F.World),
    Sig2.F.R w v →
    (Sig2.Kind k w ↔ Sig2.Kind k v) :=
by
  intro k w v hRv
  constructor
  · intro hKw
    exact hKS k w v hKw hRv
  · intro hKv
    exact hKS k v w hKv (Sig2.F.symm hRv)

/--
Derived semantic fact (requires `ax_kindStable`):

If something is a Kind at world `w`, then at every S5-accessible world `v`
it is still rigid, since `Kind` persists and `Kind → Rigid` by (a26).
-/
theorem kind_implies_rigid_accessible
  (hKS  : ax_kindStable Sig2)
  (hA26 : ax_a26 Sig2) :
  ∀ (k : Sig2.Thing) (w v : Sig2.F.World),
    Sig2.F.R w v →
    Sig2.Kind k w →
    Sig2.Rigid k v :=
by
  intro k w v hRv hKw
  have hKv : Sig2.Kind k v :=
    (kind_stable (Sig2 := Sig2) hKS k w v hRv).1 hKw
  exact (hA26 k v).1 (Or.inl hKv) |>.1

/--
Derived semantic fact (requires `ax_kindStable`):

If something is a Kind at world `w`, then at every S5-accessible world `v`
it is still a sortal, since `Kind` persists and `Kind → Sortal` by (a26).
-/
theorem kind_implies_sortal_accessible
  (hKS  : ax_kindStable Sig2)
  (hA26 : ax_a26 Sig2) :
  ∀ (k : Sig2.Thing) (w v : Sig2.F.World),
    Sig2.F.R w v →
    Sig2.Kind k w →
    Sig2.Sortal k v :=
by
  intro k w v hRv hKw
  have hKv : Sig2.Kind k v :=
    (kind_stable (Sig2 := Sig2) hKS k w v hRv).1 hKw
  exact (hA26 k v).1 (Or.inl hKv) |>.2

/-
  §3.4 — S5-derived semantic facts for endurant-type refinements.

  The `a44` clauses define the new type-level predicates as conjunctions of:
  - `Type`
  - a modal `Box` condition over instances

  Since both `Type` and `Box` are stable across accessible worlds in S5,
  each of these §3.4 refinements is also stable across accessibility.

  For the kind-level refinements from `a45`, stability additionally depends on
  the *introduced* structural axiom `ax_kindStable`, exactly as for the earlier
  derived facts about `Kind` in §3.2.
-/

variable (Sig4 : UFOSignature3_4)

open UFOSignature3_4

/--
Derived semantic fact:

In S5, `SubstantialType` is invariant across accessible worlds.

Reason:
- by (a44), `SubstantialType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem substantialType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.SubstantialType t w ↔ Sig4.SubstantialType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, hSubT, _hMomT, _hObjT, _hCollT, _hQtyT, _hRelT, _hModeT, _hQualT⟩
  constructor
  · intro hSub_w
    rcases (hSubT t w).1 hSub_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Substantial x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hSubT t v).2 ⟨hType_v, hBox_v⟩
  · intro hSub_v
    rcases (hSubT t v).1 hSub_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Substantial x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hSubT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact:

In S5, `MomentType` is invariant across accessible worlds.

Reason:
- by (a44), `MomentType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem momentType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.MomentType t w ↔ Sig4.MomentType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, hMomT, _hObjT, _hCollT, _hQtyT, _hRelT, _hModeT, _hQualT⟩
  constructor
  · intro hMom_w
    rcases (hMomT t w).1 hMom_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Moment x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hMomT t v).2 ⟨hType_v, hBox_v⟩
  · intro hMom_v
    rcases (hMomT t v).1 hMom_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Moment x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hMomT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact:

In S5, `ObjectType` is invariant across accessible worlds.

Reason:
- by (a44), `ObjectType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem objectType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.ObjectType t w ↔ Sig4.ObjectType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT, hObjT, _hCollT, _hQtyT, _hRelT, _hModeT, _hQualT⟩
  constructor
  · intro hObj_w
    rcases (hObjT t w).1 hObj_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Object x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hObjT t v).2 ⟨hType_v, hBox_v⟩
  · intro hObj_v
    rcases (hObjT t v).1 hObj_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Object x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hObjT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact:

In S5, `CollectiveType` is invariant across accessible worlds.

Reason:
- by (a44), `CollectiveType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem collectiveType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.CollectiveType t w ↔ Sig4.CollectiveType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT, _hObjT, hCollT, _hQtyT, _hRelT, _hModeT, _hQualT⟩
  constructor
  · intro hColl_w
    rcases (hCollT t w).1 hColl_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Collective x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hCollT t v).2 ⟨hType_v, hBox_v⟩
  · intro hColl_v
    rcases (hCollT t v).1 hColl_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Collective x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hCollT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact:

In S5, `QuantityType` is invariant across accessible worlds.

Reason:
- by (a44), `QuantityType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem quantityType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.QuantityType t w ↔ Sig4.QuantityType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT, _hObjT, _hCollT, hQtyT, _hRelT, _hModeT, _hQualT⟩
  constructor
  · intro hQty_w
    rcases (hQtyT t w).1 hQty_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Quantity x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hQtyT t v).2 ⟨hType_v, hBox_v⟩
  · intro hQty_v
    rcases (hQtyT t v).1 hQty_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Quantity x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hQtyT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact:

In S5, `RelatorType` is invariant across accessible worlds.

Reason:
- by (a44), `RelatorType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem relatorType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.RelatorType t w ↔ Sig4.RelatorType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT, _hObjT, _hCollT, _hQtyT, hRelT, _hModeT, _hQualT⟩
  constructor
  · intro hRel_w
    rcases (hRelT t w).1 hRel_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Relator x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hRelT t v).2 ⟨hType_v, hBox_v⟩
  · intro hRel_v
    rcases (hRelT t v).1 hRel_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Relator x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hRelT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact:

In S5, `ModeType` is invariant across accessible worlds.

Reason:
- by (a44), `ModeType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem modeType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.ModeType t w ↔ Sig4.ModeType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT, _hObjT, _hCollT, _hQtyT, _hRelT, hModeT, _hQualT⟩
  constructor
  · intro hMode_w
    rcases (hModeT t w).1 hMode_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Mode x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hModeT t v).2 ⟨hType_v, hBox_v⟩
  · intro hMode_v
    rcases (hModeT t v).1 hMode_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Sig4.Mode x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hModeT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact:

In S5, `QualityType` is invariant across accessible worlds.

Reason:
- by (a44), `QualityType` is defined as `Type ∧ Box(...)`,
- `Type` is stable in S5 by `type_stable`,
- `Box` is stable in S5 by `S5Frame.box_stable`.
-/
theorem qualityType_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.QualityType t w ↔ Sig4.QualityType t v) :=
by
  intro t w v hRv
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT, _hObjT, _hCollT, _hQtyT, _hRelT, _hModeT, hQualT⟩
  constructor
  · intro hQual_w
    rcases (hQualT t w).1 hQual_w with ⟨hType_w, hBox_w⟩
    have hType_v : Sig4.Type_ t v :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t w v hRv).1 hType_w
    have hBox_v :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Quality Sig4.toUFOSignature3_3 x w')
        v :=
      (S5Frame.box_stable (F := Sig4.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hQualT t v).2 ⟨hType_v, hBox_v⟩
  · intro hQual_v
    rcases (hQualT t v).1 hQual_v with ⟨hType_v, hBox_v⟩
    have hType_w : Sig4.Type_ t w :=
      (type_stable (Sig := Sig4.toUFOSignature3_1) hA1 t v w (Sig4.F.symm hRv)).1 hType_v
    have hBox_w :
      Frame.Box (F := Sig4.F)
        (fun w' =>
          ∀ x : Sig4.Thing,
            Sig4.Inst x t w' →
            Quality Sig4.toUFOSignature3_3 x w')
        w :=
      (S5Frame.box_stable (F := Sig4.F) (w := v) (v := w) (Sig4.F.symm hRv)).1 hBox_v
    exact (hQualT t w).2 ⟨hType_w, hBox_w⟩

/--
Derived semantic fact (requires the *introduced* structural axiom `ax_kindStable`):

In S5, `ObjectKind` is invariant across accessible worlds.

Reason:
- by (a45), `ObjectKind` is defined as `ObjectType ∧ Kind`,
- `ObjectType` is stable in S5 by `objectType_stable`,
- `Kind` is stable across accessible worlds only because of the
  *additional* axiom `ax_kindStable`, via `kind_stable`.
-/
theorem objectKind_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4)
  (hA45 : ax_a45 Sig4)
  (hKS  : ax_kindStable Sig4.toUFOSignature3_2) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.ObjectKind t w ↔ Sig4.ObjectKind t v) :=
by
  intro t w v hRv
  rcases hA45 with
    ⟨hObjK, _hCollK, _hQtyK, _hRelK, _hModeK, _hQualK⟩
  constructor
  · intro hObjK_w
    rcases (hObjK t w).1 hObjK_w with ⟨hObjT_w, hKind_w⟩
    have hObjT_v : Sig4.ObjectType t v :=
      (objectType_stable (Sig4 := Sig4) hA1 hA44 t w v hRv).1 hObjT_w
    have hKind_v : Sig4.Kind t v :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t w v hRv).1 hKind_w
    exact (hObjK t v).2 ⟨hObjT_v, hKind_v⟩
  · intro hObjK_v
    rcases (hObjK t v).1 hObjK_v with ⟨hObjT_v, hKind_v⟩
    have hObjT_w : Sig4.ObjectType t w :=
      (objectType_stable (Sig4 := Sig4) hA1 hA44 t v w (Sig4.F.symm hRv)).1 hObjT_v
    have hKind_w : Sig4.Kind t w :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t v w (Sig4.F.symm hRv)).1 hKind_v
    exact (hObjK t w).2 ⟨hObjT_w, hKind_w⟩

/--
Derived semantic fact (requires the *introduced* structural axiom `ax_kindStable`):

In S5, `CollectiveKind` is invariant across accessible worlds.

Note:
The proof depends essentially on the introduced axiom `ax_kindStable`
in order to transport the `Kind` component of (a45).
-/
theorem collectiveKind_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4)
  (hA45 : ax_a45 Sig4)
  (hKS  : ax_kindStable Sig4.toUFOSignature3_2) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.CollectiveKind t w ↔ Sig4.CollectiveKind t v) :=
by
  intro t w v hRv
  rcases hA45 with
    ⟨_hObjK, hCollK, _hQtyK, _hRelK, _hModeK, _hQualK⟩
  constructor
  · intro hCollK_w
    rcases (hCollK t w).1 hCollK_w with ⟨hCollT_w, hKind_w⟩
    have hCollT_v : Sig4.CollectiveType t v :=
      (collectiveType_stable (Sig4 := Sig4) hA1 hA44 t w v hRv).1 hCollT_w
    have hKind_v : Sig4.Kind t v :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t w v hRv).1 hKind_w
    exact (hCollK t v).2 ⟨hCollT_v, hKind_v⟩
  · intro hCollK_v
    rcases (hCollK t v).1 hCollK_v with ⟨hCollT_v, hKind_v⟩
    have hCollT_w : Sig4.CollectiveType t w :=
      (collectiveType_stable (Sig4 := Sig4) hA1 hA44 t v w (Sig4.F.symm hRv)).1 hCollT_v
    have hKind_w : Sig4.Kind t w :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t v w (Sig4.F.symm hRv)).1 hKind_v
    exact (hCollK t w).2 ⟨hCollT_w, hKind_w⟩

/--
Derived semantic fact (requires the *introduced* structural axiom `ax_kindStable`):

In S5, `QuantityKind` is invariant across accessible worlds.

Note:
The proof depends essentially on the introduced axiom `ax_kindStable`
in order to transport the `Kind` component of (a45).
-/
theorem quantityKind_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4)
  (hA45 : ax_a45 Sig4)
  (hKS  : ax_kindStable Sig4.toUFOSignature3_2) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.QuantityKind t w ↔ Sig4.QuantityKind t v) :=
by
  intro t w v hRv
  rcases hA45 with
    ⟨_hObjK, _hCollK, hQtyK, _hRelK, _hModeK, _hQualK⟩
  constructor
  · intro hQtyK_w
    rcases (hQtyK t w).1 hQtyK_w with ⟨hQtyT_w, hKind_w⟩
    have hQtyT_v : Sig4.QuantityType t v :=
      (quantityType_stable (Sig4 := Sig4) hA1 hA44 t w v hRv).1 hQtyT_w
    have hKind_v : Sig4.Kind t v :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t w v hRv).1 hKind_w
    exact (hQtyK t v).2 ⟨hQtyT_v, hKind_v⟩
  · intro hQtyK_v
    rcases (hQtyK t v).1 hQtyK_v with ⟨hQtyT_v, hKind_v⟩
    have hQtyT_w : Sig4.QuantityType t w :=
      (quantityType_stable (Sig4 := Sig4) hA1 hA44 t v w (Sig4.F.symm hRv)).1 hQtyT_v
    have hKind_w : Sig4.Kind t w :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t v w (Sig4.F.symm hRv)).1 hKind_v
    exact (hQtyK t w).2 ⟨hQtyT_w, hKind_w⟩

/--
Derived semantic fact (requires the *introduced* structural axiom `ax_kindStable`):

In S5, `RelatorKind` is invariant across accessible worlds.

Note:
The proof depends essentially on the introduced axiom `ax_kindStable`
in order to transport the `Kind` component of (a45).
-/
theorem relatorKind_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4)
  (hA45 : ax_a45 Sig4)
  (hKS  : ax_kindStable Sig4.toUFOSignature3_2) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.RelatorKind t w ↔ Sig4.RelatorKind t v) :=
by
  intro t w v hRv
  rcases hA45 with
    ⟨_hObjK, _hCollK, _hQtyK, hRelK, _hModeK, _hQualK⟩
  constructor
  · intro hRelK_w
    rcases (hRelK t w).1 hRelK_w with ⟨hRelT_w, hKind_w⟩
    have hRelT_v : Sig4.RelatorType t v :=
      (relatorType_stable (Sig4 := Sig4) hA1 hA44 t w v hRv).1 hRelT_w
    have hKind_v : Sig4.Kind t v :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t w v hRv).1 hKind_w
    exact (hRelK t v).2 ⟨hRelT_v, hKind_v⟩
  · intro hRelK_v
    rcases (hRelK t v).1 hRelK_v with ⟨hRelT_v, hKind_v⟩
    have hRelT_w : Sig4.RelatorType t w :=
      (relatorType_stable (Sig4 := Sig4) hA1 hA44 t v w (Sig4.F.symm hRv)).1 hRelT_v
    have hKind_w : Sig4.Kind t w :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t v w (Sig4.F.symm hRv)).1 hKind_v
    exact (hRelK t w).2 ⟨hRelT_w, hKind_w⟩

/--
Derived semantic fact (requires the *introduced* structural axiom `ax_kindStable`):

In S5, `ModeKind` is invariant across accessible worlds.

Note:
The proof depends essentially on the introduced axiom `ax_kindStable`
in order to transport the `Kind` component of (a45).
-/
theorem modeKind_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4)
  (hA45 : ax_a45 Sig4)
  (hKS  : ax_kindStable Sig4.toUFOSignature3_2) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.ModeKind t w ↔ Sig4.ModeKind t v) :=
by
  intro t w v hRv
  rcases hA45 with
    ⟨_hObjK, _hCollK, _hQtyK, _hRelK, hModeK, _hQualK⟩
  constructor
  · intro hModeK_w
    rcases (hModeK t w).1 hModeK_w with ⟨hModeT_w, hKind_w⟩
    have hModeT_v : Sig4.ModeType t v :=
      (modeType_stable (Sig4 := Sig4) hA1 hA44 t w v hRv).1 hModeT_w
    have hKind_v : Sig4.Kind t v :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t w v hRv).1 hKind_w
    exact (hModeK t v).2 ⟨hModeT_v, hKind_v⟩
  · intro hModeK_v
    rcases (hModeK t v).1 hModeK_v with ⟨hModeT_v, hKind_v⟩
    have hModeT_w : Sig4.ModeType t w :=
      (modeType_stable (Sig4 := Sig4) hA1 hA44 t v w (Sig4.F.symm hRv)).1 hModeT_v
    have hKind_w : Sig4.Kind t w :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t v w (Sig4.F.symm hRv)).1 hKind_v
    exact (hModeK t w).2 ⟨hModeT_w, hKind_w⟩

/--
Derived semantic fact (requires the *introduced* structural axiom `ax_kindStable`):

In S5, `QualityKind` is invariant across accessible worlds.

Note:
The proof depends essentially on the introduced axiom `ax_kindStable`
in order to transport the `Kind` component of (a45).
-/
theorem qualityKind_stable
  (hA1  : ax_a1 Sig4.toUFOSignature3_1)
  (hA44 : ax_a44 Sig4)
  (hA45 : ax_a45 Sig4)
  (hKS  : ax_kindStable Sig4.toUFOSignature3_2) :
  ∀ (t : Sig4.Thing) (w v : Sig4.F.World),
    Sig4.F.R w v →
    (Sig4.QualityKind t w ↔ Sig4.QualityKind t v) :=
by
  intro t w v hRv
  rcases hA45 with
    ⟨_hObjK, _hCollK, _hQtyK, _hRelK, _hModeK, hQualK⟩
  constructor
  · intro hQualK_w
    rcases (hQualK t w).1 hQualK_w with ⟨hQualT_w, hKind_w⟩
    have hQualT_v : Sig4.QualityType t v :=
      (qualityType_stable (Sig4 := Sig4) hA1 hA44 t w v hRv).1 hQualT_w
    have hKind_v : Sig4.Kind t v :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t w v hRv).1 hKind_w
    exact (hQualK t v).2 ⟨hQualT_v, hKind_v⟩
  · intro hQualK_v
    rcases (hQualK t v).1 hQualK_v with ⟨hQualT_v, hKind_v⟩
    have hQualT_w : Sig4.QualityType t w :=
      (qualityType_stable (Sig4 := Sig4) hA1 hA44 t v w (Sig4.F.symm hRv)).1 hQualT_v
    have hKind_w : Sig4.Kind t w :=
      (kind_stable (Sig2 := Sig4.toUFOSignature3_2) hKS t v w (Sig4.F.symm hRv)).1 hKind_v
    exact (hQualK t w).2 ⟨hQualT_w, hKind_w⟩

/-
  §3.5 and §3.6 add no new genuinely modal clauses:
  their axioms are first-order constraints over the current world, so there are
  no additional S5-specific invariance theorems to extract there.

  §3.7 does add a modal clause, namely (a60), so we record its S5 consequences
  below.
-/

variable (Sig7 : UFOSignature3_7)

open UFOSignature3_7

/--
Derived semantic fact:

In S5, the necessity clause from (a60) is itself invariant across accessible
worlds.

Reason:
- by (a60), if a perdurant `x` is constituted by `y` at `w`, then
  `□(Ex(x) → constitutedBy(x, y))` holds at `w`;
- `Box` is stable across accessible worlds in S5.
-/
theorem perdurant_constitutedBy_necessary_accessible
  (hA60 : ax_a60 Sig7) :
  ∀ (x y : Sig7.Thing) (w v : Sig7.F.World),
    Sig7.F.R w v →
    Sig7.Perdurant x w →
    Sig7.ConstitutedBy x y w →
    Frame.Box (F := Sig7.F)
      (fun w' => Sig7.Ex x w' → Sig7.ConstitutedBy x y w')
      v :=
by
  intro x y w v hRv hPerd_w hConst_w
  have hBox_w :
    Frame.Box (F := Sig7.F)
      (fun w' => Sig7.Ex x w' → Sig7.ConstitutedBy x y w')
      w :=
    hA60 x y w ⟨hPerd_w, hConst_w⟩
  exact (S5Frame.box_stable (F := Sig7.F) (w := w) (v := v) hRv).1 hBox_w

/--
Derived semantic fact:

In S5, if a perdurant `x` is constituted by `y` at `w`, then at every
accessible world `v`, the constitution relation still holds whenever `x`
exists at `v`.
-/
theorem perdurant_constitutedBy_accessible
  (hA60 : ax_a60 Sig7) :
  ∀ (x y : Sig7.Thing) (w v : Sig7.F.World),
    Sig7.F.R w v →
    Sig7.Perdurant x w →
    Sig7.ConstitutedBy x y w →
    Sig7.Ex x v →
    Sig7.ConstitutedBy x y v :=
by
  intro x y w v hRv hPerd_w hConst_w hEx_v
  have hBox_v :
    Frame.Box (F := Sig7.F)
      (fun w' => Sig7.Ex x w' → Sig7.ConstitutedBy x y w')
      v :=
    perdurant_constitutedBy_necessary_accessible
      (Sig7 := Sig7) hA60 x y w v hRv hPerd_w hConst_w
  exact hBox_v v (Sig7.F.refl v) hEx_v

/-
  §3.8 adds one genuinely modal definition, namely existential dependence in
  (a63). This yields the expected S5 stability results below.
-/

variable (Sig8 : UFOSignature3_8)

open UFOSignature3_8

/--
Derived semantic fact:

In S5, existential dependence is invariant across accessible worlds.

Reason:
- by (a63), `ed(x, y)` is defined as `□(Ex(x) → Ex(y))`,
- `Box` is stable across accessible worlds in S5.
-/
theorem existentialDependence_stable
  (hA63 : ax_a63 Sig8) :
  ∀ (x y : Sig8.Thing) (w v : Sig8.F.World),
    Sig8.F.R w v →
    (Sig8.ExistentialDependence x y w ↔
     Sig8.ExistentialDependence x y v) :=
by
  intro x y w v hRv
  constructor
  · intro hED_w
    have hBox_w :
      Frame.Box (F := Sig8.F)
        (fun w' => Sig8.Ex x w' → Sig8.Ex y w')
        w :=
      (hA63 x y w).1 hED_w
    have hBox_v :
      Frame.Box (F := Sig8.F)
        (fun w' => Sig8.Ex x w' → Sig8.Ex y w')
        v :=
      (S5Frame.box_stable (F := Sig8.F) (w := w) (v := v) hRv).1 hBox_w
    exact (hA63 x y v).2 hBox_v
  · intro hED_v
    have hBox_v :
      Frame.Box (F := Sig8.F)
        (fun w' => Sig8.Ex x w' → Sig8.Ex y w')
        v :=
      (hA63 x y v).1 hED_v
    have hBox_w :
      Frame.Box (F := Sig8.F)
        (fun w' => Sig8.Ex x w' → Sig8.Ex y w')
        w :=
      (S5Frame.box_stable (F := Sig8.F) (w := v) (v := w) (Sig8.F.symm hRv)).1 hBox_v
    exact (hA63 x y w).2 hBox_w

/--
Derived semantic fact:

In S5, existential independence is invariant across accessible worlds,
because it is defined in (a64) by mutual failure of existential dependence.
-/
theorem existentialIndependence_stable
  (hA63 : ax_a63 Sig8)
  (hA64 : ax_a64 Sig8) :
  ∀ (x y : Sig8.Thing) (w v : Sig8.F.World),
    Sig8.F.R w v →
    (Sig8.ExistentialIndependence x y w ↔
     Sig8.ExistentialIndependence x y v) :=
by
  intro x y w v hRv
  constructor
  · intro hInd_w
    rcases (hA64 x y w).1 hInd_w with ⟨hNotEDxy_w, hNotEDyx_w⟩
    have hNotEDxy_v : ¬ Sig8.ExistentialDependence x y v := by
      intro hEDxy_v
      have hEDxy_w :
        Sig8.ExistentialDependence x y w :=
        (existentialDependence_stable (Sig8 := Sig8) hA63 x y v w (Sig8.F.symm hRv)).1 hEDxy_v
      exact hNotEDxy_w hEDxy_w
    have hNotEDyx_v : ¬ Sig8.ExistentialDependence y x v := by
      intro hEDyx_v
      have hEDyx_w :
        Sig8.ExistentialDependence y x w :=
        (existentialDependence_stable (Sig8 := Sig8) hA63 y x v w (Sig8.F.symm hRv)).1 hEDyx_v
      exact hNotEDyx_w hEDyx_w
    exact (hA64 x y v).2 ⟨hNotEDxy_v, hNotEDyx_v⟩
  · intro hInd_v
    rcases (hA64 x y v).1 hInd_v with ⟨hNotEDxy_v, hNotEDyx_v⟩
    have hNotEDxy_w : ¬ Sig8.ExistentialDependence x y w := by
      intro hEDxy_w
      have hEDxy_v :
        Sig8.ExistentialDependence x y v :=
        (existentialDependence_stable (Sig8 := Sig8) hA63 x y w v hRv).1 hEDxy_w
      exact hNotEDxy_v hEDxy_v
    have hNotEDyx_w : ¬ Sig8.ExistentialDependence y x w := by
      intro hEDyx_w
      have hEDyx_v :
        Sig8.ExistentialDependence y x v :=
        (existentialDependence_stable (Sig8 := Sig8) hA63 y x w v hRv).1 hEDyx_w
      exact hNotEDyx_v hEDyx_v
    exact (hA64 x y w).2 ⟨hNotEDxy_w, hNotEDyx_w⟩
