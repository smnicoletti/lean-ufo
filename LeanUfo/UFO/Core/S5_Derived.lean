
import LeanUfo.UFO.Modal.S5
import LeanUfo.UFO.Core.Section3_1
import LeanUfo.UFO.Core.Section3_2

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
