import LeanUfo.UFO.Core.Signature3_4
import LeanUfo.UFO.Core.Section3_3
import LeanUfo.UFO.Modal.S5

universe u v

variable (Sig : UFOSignature3_4)

open UFOSignature3_4

/-
  §3.4 — Endurant types

  This section introduces an orthogonal taxonomy of endurant types
  according to the ontological nature of their instances, together with
  the corresponding refinements of kinds.
-/

/--
For clarity we compose a44 building from the schema presented
in the paper.

(a44) for EndurantType

EndurantType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Endurant(x)))

Natural language:
A type is an EndurantType exactly when it is a Type whose instances
are necessarily endurants.
-/
def ax_a44_endurantType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.EndurantType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Endurant x w')
         w)

/--
(a44) for PerdurantType

PerdurantType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Perdurant(x)))

Natural language:
A type is a PerdurantType exactly when it is a Type whose instances
are necessarily perdurants.
-/
def ax_a44_perdurantType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.PerdurantType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Perdurant x w')
         w)

/--
(a44) for SubstantialType

SubstantialType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Substantial(x)))

Natural language:
A type is a SubstantialType exactly when it is a Type whose instances
are necessarily substantials.
-/
def ax_a44_substantialType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.SubstantialType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Substantial x w')
         w)

/--
(a44) for MomentType

MomentType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Moment(x)))

Natural language:
A type is a MomentType exactly when it is a Type whose instances
are necessarily moments.
-/
def ax_a44_momentType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.MomentType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Moment x w')
         w)

/--
(a44) for ObjectType

ObjectType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Object(x)))

Natural language:
A type is an ObjectType exactly when it is a Type whose instances
are necessarily objects.
-/
def ax_a44_objectType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.ObjectType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Object x w')
         w)

/--
(a44) for CollectiveType

CollectiveType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Collective(x)))

Natural language:
A type is a CollectiveType exactly when it is a Type whose instances
are necessarily collectives.
-/
def ax_a44_collectiveType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.CollectiveType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Collective x w')
         w)

/--
(a44) for QuantityType

QuantityType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Quantity(x)))

Natural language:
A type is a QuantityType exactly when it is a Type whose instances
are necessarily quantities.
-/
def ax_a44_quantityType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.QuantityType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Quantity x w')
         w)

/--
(a44) for RelatorType

RelatorType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Relator(x)))

Natural language:
A type is a RelatorType exactly when it is a Type whose instances
are necessarily relators.
-/
def ax_a44_relatorType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.RelatorType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Relator x w')
         w)

/--
(a44) for ModeType

ModeType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Mode(x)))

Natural language:
A type is a ModeType exactly when it is a Type whose instances
are necessarily modes.
-/
def ax_a44_modeType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.ModeType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Mode x w')
         w)

/--
(a44) for QualityType

QualityType(t) ↔
  Type(t) ∧ □(∀x (x :: t → Quality(x)))

Natural language:
A type is a QualityType exactly when it is a Type whose instances
are necessarily qualities.
-/
def ax_a44_qualityType : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.QualityType t w ↔
      (Sig.Type_ t w ∧
       Frame.Box (F := Sig.F)
         (fun w' =>
           ∀ x : Sig.Thing,
             Sig.Inst x t w' →
             Sig.Quality x w')
         w)

/--
(a44)

To reflect the encoding of a44 in the paper we conjunct
each specific instance of the schema.
-/
def ax_a44 : Prop :=
  ax_a44_endurantType Sig ∧
  ax_a44_perdurantType Sig ∧
  ax_a44_substantialType Sig ∧
  ax_a44_momentType Sig ∧
  ax_a44_objectType Sig ∧
  ax_a44_collectiveType Sig ∧
  ax_a44_quantityType Sig ∧
  ax_a44_relatorType Sig ∧
  ax_a44_modeType Sig ∧
  ax_a44_qualityType Sig

/--
(t21)

The six leaf endurant type categories
(ObjectType, CollectiveType, QuantityType, RelatorType, ModeType, QualityType)
are pairwise disjoint.

Natural language:
No type can belong to two distinct leaf endurant type categories.
-/
theorem th_t21
  (hA44 : ax_a44 Sig)
  (hA1 : ax_a1 Sig.toUFOSignature3_1)
  (hA35 : ax_a35 Sig.toUFOSignature3_3)
  (hA36 : ax_a36 Sig.toUFOSignature3_3)
  (hA37 : ax_a37 Sig.toUFOSignature3_3)
  (hA38 : ax_a38 Sig.toUFOSignature3_3)
  (hA39 : ax_a39 Sig.toUFOSignature3_3)
  (hA40 : ax_a40 Sig.toUFOSignature3_3)
  (hA41 : ax_a41 Sig.toUFOSignature3_3)
  (hA42 : ax_a42 Sig.toUFOSignature3_3)
  (hA43 : ax_a43 Sig.toUFOSignature3_3) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),

    (Sig.ObjectType t w →
      ¬ Sig.CollectiveType t w ∧
      ¬ Sig.QuantityType t w ∧
      ¬ Sig.RelatorType t w ∧
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)

    ∧

    (Sig.CollectiveType t w →
      ¬ Sig.QuantityType t w ∧
      ¬ Sig.RelatorType t w ∧
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)

    ∧

    (Sig.QuantityType t w →
      ¬ Sig.RelatorType t w ∧
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)

    ∧

    (Sig.RelatorType t w →
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)

    ∧

    (Sig.ModeType t w →
      ¬ Sig.QualityType t w)
:=
by
  classical
  intro t w
  rcases hA44 with
    ⟨_, _, _, _, hObjType, hCollType, hQtyType, hRelType, hModeType, hQualType⟩
  have hT19 := th_t19
    (Sig := Sig.toUFOSignature3_3)
    hA35 hA36 hA37 hA38 hA39 hA40 hA41 hA42 hA43
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hObjT
    rcases (hObjType t w).1 hObjT with ⟨hType, hBoxObj⟩
    rcases (hA1 t w).1 hType with ⟨v, hv, ⟨x, hxInst⟩⟩
    have hxObj : Sig.Object x v := hBoxObj v hv x hxInst
    have hDisj := hT19 x v
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hCollT
      rcases (hCollType t w).1 hCollT with ⟨_, hBoxColl⟩
      have hxColl : Sig.Collective x v := hBoxColl v hv x hxInst
      exact (hDisj.1 hxObj).1 hxColl
    · intro hQtyT
      rcases (hQtyType t w).1 hQtyT with ⟨_, hBoxQty⟩
      have hxQty : Sig.Quantity x v := hBoxQty v hv x hxInst
      exact (hDisj.1 hxObj).2.1 hxQty
    · intro hRelT
      rcases (hRelType t w).1 hRelT with ⟨_, hBoxRel⟩
      have hxRel : Sig.Relator x v := hBoxRel v hv x hxInst
      exact (hDisj.1 hxObj).2.2.1 hxRel
    · intro hModeT
      rcases (hModeType t w).1 hModeT with ⟨_, hBoxMode⟩
      have hxMode : Sig.Mode x v := hBoxMode v hv x hxInst
      exact (hDisj.1 hxObj).2.2.2.1 hxMode
    · intro hQualT
      rcases (hQualType t w).1 hQualT with ⟨_, hBoxQual⟩
      have hxQual : Sig.Quality x v := hBoxQual v hv x hxInst
      exact (hDisj.1 hxObj).2.2.2.2 hxQual
  · intro hCollT
    rcases (hCollType t w).1 hCollT with ⟨hType, hBoxColl⟩
    rcases (hA1 t w).1 hType with ⟨v, hv, ⟨x, hxInst⟩⟩
    have hxColl : Sig.Collective x v := hBoxColl v hv x hxInst
    have hDisj := hT19 x v
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hQtyT
      rcases (hQtyType t w).1 hQtyT with ⟨_, hBoxQty⟩
      have hxQty : Sig.Quantity x v := hBoxQty v hv x hxInst
      exact (hDisj.2.1 hxColl).1 hxQty
    · intro hRelT
      rcases (hRelType t w).1 hRelT with ⟨_, hBoxRel⟩
      have hxRel : Sig.Relator x v := hBoxRel v hv x hxInst
      exact (hDisj.2.1 hxColl).2.1 hxRel
    · intro hModeT
      rcases (hModeType t w).1 hModeT with ⟨_, hBoxMode⟩
      have hxMode : Sig.Mode x v := hBoxMode v hv x hxInst
      exact (hDisj.2.1 hxColl).2.2.1 hxMode
    · intro hQualT
      rcases (hQualType t w).1 hQualT with ⟨_, hBoxQual⟩
      have hxQual : Sig.Quality x v := hBoxQual v hv x hxInst
      exact (hDisj.2.1 hxColl).2.2.2 hxQual
  · intro hQtyT
    rcases (hQtyType t w).1 hQtyT with ⟨hType, hBoxQty⟩
    rcases (hA1 t w).1 hType with ⟨v, hv, ⟨x, hxInst⟩⟩
    have hxQty : Sig.Quantity x v := hBoxQty v hv x hxInst
    have hDisj := hT19 x v
    refine ⟨?_, ?_, ?_⟩
    · intro hRelT
      rcases (hRelType t w).1 hRelT with ⟨_, hBoxRel⟩
      have hxRel : Sig.Relator x v := hBoxRel v hv x hxInst
      exact (hDisj.2.2.1 hxQty).1 hxRel
    · intro hModeT
      rcases (hModeType t w).1 hModeT with ⟨_, hBoxMode⟩
      have hxMode : Sig.Mode x v := hBoxMode v hv x hxInst
      exact (hDisj.2.2.1 hxQty).2.1 hxMode
    · intro hQualT
      rcases (hQualType t w).1 hQualT with ⟨_, hBoxQual⟩
      have hxQual : Sig.Quality x v := hBoxQual v hv x hxInst
      exact (hDisj.2.2.1 hxQty).2.2 hxQual
  · intro hRelT
    rcases (hRelType t w).1 hRelT with ⟨hType, hBoxRel⟩
    rcases (hA1 t w).1 hType with ⟨v, hv, ⟨x, hxInst⟩⟩
    have hxRel : Sig.Relator x v := hBoxRel v hv x hxInst
    have hDisj := hT19 x v
    refine ⟨?_, ?_⟩
    · intro hModeT
      rcases (hModeType t w).1 hModeT with ⟨_, hBoxMode⟩
      have hxMode : Sig.Mode x v := hBoxMode v hv x hxInst
      exact (hDisj.2.2.2.1 hxRel).1 hxMode
    · intro hQualT
      rcases (hQualType t w).1 hQualT with ⟨_, hBoxQual⟩
      have hxQual : Sig.Quality x v := hBoxQual v hv x hxInst
      exact (hDisj.2.2.2.1 hxRel).2 hxQual
  · intro hModeT
    rcases (hModeType t w).1 hModeT with ⟨hType, hBoxMode⟩
    rcases (hA1 t w).1 hType with ⟨v, hv, ⟨x, hxInst⟩⟩
    have hxMode : Sig.Mode x v := hBoxMode v hv x hxInst
    have hDisj := hT19 x v
    intro hQualT
    rcases (hQualType t w).1 hQualT with ⟨_, hBoxQual⟩
    have hxQual : Sig.Quality x v := hBoxQual v hv x hxInst
    exact (hDisj.2.2.2.2 hxMode) hxQual

/--
(a45) for ObjectKind

ObjectKind(t) ↔ ObjectType(t) ∧ Kind(t)

Natural language:
A type is an ObjectKind exactly when it is both an ObjectType and a Kind.
-/
def ax_a45_objectKind : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.ObjectKind t w ↔
      (Sig.ObjectType t w ∧ Sig.Kind t w)

/--
(a45) for CollectiveKind

CollectiveKind(t) ↔ CollectiveType(t) ∧ Kind(t)

Natural language:
A type is a CollectiveKind exactly when it is both a CollectiveType and a Kind.
-/
def ax_a45_collectiveKind : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.CollectiveKind t w ↔
      (Sig.CollectiveType t w ∧ Sig.Kind t w)

/--
(a45) for QuantityKind

QuantityKind(t) ↔ QuantityType(t) ∧ Kind(t)

Natural language:
A type is a QuantityKind exactly when it is both a QuantityType and a Kind.
-/
def ax_a45_quantityKind : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.QuantityKind t w ↔
      (Sig.QuantityType t w ∧ Sig.Kind t w)

/--
(a45) for RelatorKind

RelatorKind(t) ↔ RelatorType(t) ∧ Kind(t)

Natural language:
A type is a RelatorKind exactly when it is both a RelatorType and a Kind.
-/
def ax_a45_relatorKind : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.RelatorKind t w ↔
      (Sig.RelatorType t w ∧ Sig.Kind t w)

/--
(a45) for ModeKind

ModeKind(t) ↔ ModeType(t) ∧ Kind(t)

Natural language:
A type is a ModeKind exactly when it is both a ModeType and a Kind.
-/
def ax_a45_modeKind : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.ModeKind t w ↔
      (Sig.ModeType t w ∧ Sig.Kind t w)

/--
(a45) for QualityKind

QualityKind(t) ↔ QualityType(t) ∧ Kind(t)

Natural language:
A type is a QualityKind exactly when it is both a QualityType and a Kind.
-/
def ax_a45_qualityKind : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.QualityKind t w ↔
      (Sig.QualityType t w ∧ Sig.Kind t w)

/--
(a45)

As before, we conjunct the axioms to re-create the schema
from the original paper.
-/
def ax_a45 : Prop :=
  ax_a45_objectKind Sig ∧
  ax_a45_collectiveKind Sig ∧
  ax_a45_quantityKind Sig ∧
  ax_a45_relatorKind Sig ∧
  ax_a45_modeKind Sig ∧
  ax_a45_qualityKind Sig

/--
(t22)

All entities that possibly instantiate a specific endurant kind are endurants.

Natural language:
If something possibly instantiates one of the specific endurant kinds
(ObjectKind, CollectiveKind, QuantityKind, RelatorKind, ModeKind, QualityKind),
then it is an endurant.

Proof pattern is:
	1.	from a possible instantiation of a specific endurant kind, pick an accessible world v,
	2.	use (a45) to get the corresponding specific endurant type and Kind at v,
	3.	use ax_kindStable to transport Kind back to w,
	4.	use Kind → Rigid (a26) and Rigid (a18) to get x :: k already at w,
	5.	use S5-stability of the Type and Box parts of (a44) to transport the corresponding specific endurant type back to w,
	6.	conclude that x belongs to the corresponding individual leaf category at w,
	7.	conclude Endurant x w via t20.

-/
theorem th_t22
  (hA1 : ax_a1 Sig.toUFOSignature3_2.toUFOSignature3_1)
  (hA18 : ax_a18 Sig.toUFOSignature3_2)
  (hA26 : ax_a26 Sig.toUFOSignature3_2)
  (hKS : ax_kindStable Sig.toUFOSignature3_2)
  (hA44 : ax_a44 Sig)
  (hA45 : ax_a45 Sig)
  (hT20 : ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Endurant t w ↔
      (Sig.Object t w ∨
       Sig.Collective t w ∨
       Sig.Quantity t w ∨
       Sig.Relator t w ∨
       Sig.Mode t w ∨
       Sig.Quality t w)) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Frame.Dia (F := Sig.F)
      (fun w' =>
        ∃ k : Sig.Thing,
          (Sig.ObjectKind k w' ∨
           Sig.CollectiveKind k w' ∨
           Sig.QuantityKind k w' ∨
           Sig.RelatorKind k w' ∨
           Sig.ModeKind k w' ∨
           Sig.QualityKind k w')
          ∧
          Sig.Inst x k w')
      w →
    Sig.Endurant x w :=
by
  classical
  intro x w hDia

  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT,
     hObjT, hCollT, hQuantT, hRelT, hModeT, hQualT⟩

  rcases hA45 with
    ⟨hObjK, hCollK, hQuantK, hRelK, hModeK, hQualK⟩

  /-
    Generic helper for the six branches.
  -/
  have hCase :
    ∀ {TypePred KindPred LeafPred : Sig.Thing → Sig.F.World → Prop},
      (∀ (t : Sig.Thing) (w : Sig.F.World),
        KindPred t w ↔ (TypePred t w ∧ Sig.Kind t w)) →
      (∀ (t : Sig.Thing) (w : Sig.F.World),
        TypePred t w ↔
          (Sig.Type_ t w ∧
           Frame.Box (F := Sig.F)
             (fun w' =>
               ∀ y : Sig.Thing,
                 Sig.Inst y t w' →
                 LeafPred y w')
             w)) →
      (∀ (y : Sig.Thing) (w : Sig.F.World),
        LeafPred y w →
          (Sig.Object y w ∨
           Sig.Collective y w ∨
           Sig.Quantity y w ∨
           Sig.Relator y w ∨
           Sig.Mode y w ∨
           Sig.Quality y w)) →
      ∀ (k : Sig.Thing) (v : Sig.F.World),
        Sig.F.R w v →
        KindPred k v →
        Sig.Inst x k v →
        Sig.Endurant x w :=
  by
    intro TypePred KindPred LeafPred hKindDef hTypeDef hLeafIntoT20 k v hRv hKind_v hInst_v

    -- unpack the specific kind at v
    have hKindPair_v := (hKindDef k v).1 hKind_v
    rcases hKindPair_v with ⟨hTypePred_v, hKind_v'⟩

    -- transport Kind back to w using the explicit stability axiom
    have hKind_w : Sig.Kind k w :=
      hKS k v w hKind_v' (Sig.F.symm hRv)

    -- from Kind at w, obtain Rigid at w
    have hRigid_w : Sig.Rigid k w :=
      (hA26 k w).1 (Or.inl hKind_w) |>.1

    -- from possible instantiation at w and rigidity, get actual instantiation at w
    have hDiaInst_w :
      Frame.Dia (F := Sig.F) (fun w' => Sig.Inst x k w') w :=
      ⟨v, hRv, hInst_v⟩

    have hRigidDef_w := (hA18 k w).1 hRigid_w
    have hBoxInst_w :
      Frame.Box (F := Sig.F) (fun w' => Sig.Inst x k w') w :=
      hRigidDef_w.2 x hDiaInst_w

    have hInst_w : Sig.Inst x k w :=
      hBoxInst_w w (Sig.F.refl w)

    -- unpack the specific type at v
    have hTypePair_v := (hTypeDef k v).1 hTypePred_v
    rcases hTypePair_v with ⟨hType_v, hBoxLeaf_v⟩

    -- transport Type from v to w using a1 + S5 stability of Dia
    have hDiaType_v :
      Frame.Dia (F := Sig.F) (fun w' => ∃ y : Sig.Thing, Sig.Inst y k w') v :=
      (hA1 k v).1 hType_v

    have hDiaType_w :
      Frame.Dia (F := Sig.F) (fun w' => ∃ y : Sig.Thing, Sig.Inst y k w') w :=
      (S5Frame.dia_stable (F := Sig.F) (w := v) (v := w) (Sig.F.symm hRv)).1 hDiaType_v

    have hType_w : Sig.Type_ k w :=
      (hA1 k w).2 hDiaType_w

    -- transport the Box clause from v to w using S5 stability of Box
    have hBoxLeaf_w :
      Frame.Box (F := Sig.F)
        (fun w' =>
          ∀ y : Sig.Thing,
            Sig.Inst y k w' →
            LeafPred y w')
        w :=
      (S5Frame.box_stable (F := Sig.F) (w := v) (v := w) (Sig.F.symm hRv)).1 hBoxLeaf_v

    -- hence x belongs to the corresponding leaf category already at w
    have hLeaf_x_w : LeafPred x w :=
      hBoxLeaf_w w (Sig.F.refl w) x hInst_w

    -- now use t20
    exact (hT20 x w).2 (hLeafIntoT20 x w hLeaf_x_w)

  -- main case split over the six specific kinds
  rcases hDia with ⟨v, hRv, ⟨k, hLeafKind, hInst_v⟩⟩
  cases hLeafKind with
  | inl hObjKind =>
      exact hCase
        hObjK
        hObjT
        (fun y w hy => Or.inl hy)
        k v hRv hObjKind hInst_v

  | inr hRest =>
      cases hRest with
      | inl hCollKind =>
          exact hCase
            hCollK
            hCollT
            (fun y w hy => Or.inr (Or.inl hy))
            k v hRv hCollKind hInst_v

      | inr hRest =>
          cases hRest with
          | inl hQuantKind =>
              exact hCase
                hQuantK
                hQuantT
                (fun y w hy => Or.inr (Or.inr (Or.inl hy)))
                k v hRv hQuantKind hInst_v

          | inr hRest =>
              cases hRest with
              | inl hRelKind =>
                  exact hCase
                    hRelK
                    hRelT
                    (fun y w hy => Or.inr (Or.inr (Or.inr (Or.inl hy))))
                    k v hRv hRelKind hInst_v

              | inr hRest =>
                  cases hRest with
                  | inl hModeKind =>
                      exact hCase
                        hModeK
                        hModeT
                        (fun y w hy => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hy)))))
                        k v hRv hModeKind hInst_v

                  | inr hQualKind =>
                      exact hCase
                        hQualK
                        hQualT
                        (fun y w hy => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hy)))))
                        k v hRv hQualKind hInst_v

/--
(a46)

Endurant(x) →
  ◇(∃k ((ObjectKind(k) ∨ CollectiveKind(k) ∨ QuantityKind(k) ∨
          RelatorKind(k) ∨ ModeKind(k) ∨ QualityKind(k)) ∧ x :: k))

Natural language:
Every endurant possibly instantiates one of the specific endurant kinds.
-/
def ax_a46 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Endurant x w →
      Frame.Dia (F := Sig.F)
        (fun w' =>
          ∃ k : Sig.Thing,
            (Sig.ObjectKind k w' ∨
             Sig.CollectiveKind k w' ∨
             Sig.QuantityKind k w' ∨
             Sig.RelatorKind k w' ∨
             Sig.ModeKind k w' ∨
             Sig.QualityKind k w')
            ∧
            Sig.Inst x k w')
        w

/--
Helper theorem:

Every `Kind` in the endurant branch is one of the six specific endurant kinds.

Proof idea:
1. obtain a possible instance of the kind from `a1`,
2. show that this instance is an endurant,
3. apply `a46` to get a possible instantiation of one of the six specific kinds,
4. use `a22` to rule out any specific kind distinct from the original kind,
5. transport the corresponding specific-type classification back to the original world.
-/
theorem kind_implies_specific_kind
  (hA1 : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA22 : ax_a22 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA23 : ax_a23 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA26 : ax_a26 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hKS : ax_kindStable Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hInstEnd : ax_instEndurant_of_EndurantType (Sig := Sig.toUFOSignature3_3.toUFOSignature3_2))
  (hA44 : ax_a44 Sig)
  (hA45 : ax_a45 Sig)
  (hA46 : ax_a46 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Kind t w →
      (Sig.ObjectKind t w ∨
       Sig.CollectiveKind t w ∨
       Sig.QuantityKind t w ∨
       Sig.RelatorKind t w ∨
       Sig.ModeKind t w ∨
       Sig.QualityKind t w) :=
by
  classical
  intro t w hKind

  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT,
     hObjT, hCollT, hQtyT, hRelT, hModeT, hQualT⟩

  rcases hA45 with
    ⟨hObjK, hCollK, hQtyK, hRelK, hModeK, hQualK⟩

  have hSortal_w : Sig.Sortal t w :=
    th_t12 (Sig := Sig.toUFOSignature3_2) hA26 t w hKind

  have hEnd_w : Sig.EndurantType t w :=
    (hA23 t w).1 hSortal_w |>.1

  have hType_w : Sig.Type_ t w :=
    hA15 t w hEnd_w

  have hDiaInst_t :
    Frame.Dia (F := Sig.F) (fun w' => ∃ x : Sig.Thing, Sig.Inst x t w') w :=
    (hA1 t w).1 hType_w

  /-
    Every specific endurant kind is, in particular, a Kind.
  -/
  have hSpecificImpliesKind :
    ∀ (a : Sig.Thing) (v : Sig.F.World),
      (Sig.ObjectKind a v ∨
       Sig.CollectiveKind a v ∨
       Sig.QuantityKind a v ∨
       Sig.RelatorKind a v ∨
      Sig.ModeKind a v ∨
      Sig.QualityKind a v) →
      Sig.Kind a v :=
  by
    intro a v hSpecific
    cases hSpecific with
    | inl hObjKind =>
        have : Sig.ObjectType a v ∧ Sig.Kind a v := (hObjK a v).1 hObjKind
        grind
    | inr hRest =>
        cases hRest with
        | inl hCollKind =>
            have : Sig.CollectiveType a v ∧ Sig.Kind a v := (hCollK a v).1 hCollKind
            grind
        | inr hRest =>
            cases hRest with
            | inl hQtyKind =>
                have : Sig.QuantityType a v ∧ Sig.Kind a v := (hQtyK a v).1 hQtyKind
                grind
            | inr hRest =>
                cases hRest with
                | inl hRelKind =>
                    have : Sig.RelatorType a v ∧ Sig.Kind a v := (hRelK a v).1 hRelKind
                    grind
                | inr hRest =>
                    cases hRest with
                    | inl hModeKind =>
                        have : Sig.ModeType a v ∧ Sig.Kind a v := (hModeK a v).1 hModeKind
                        grind
                    | inr hQualKind =>
                        have : Sig.QualityType a v ∧ Sig.Kind a v := (hQualK a v).1 hQualKind
                        grind

  /-
    Generic transport from a specific kind at an accessible world
    back to the original world.
  -/
  have hTransportSpecific :
    ∀ {TypePred KindPred LeafPred : Sig.Thing → Sig.F.World → Prop},
      (∀ (a : Sig.Thing) (v : Sig.F.World),
        KindPred a v ↔ (TypePred a v ∧ Sig.Kind a v)) →
      (∀ (a : Sig.Thing) (v : Sig.F.World),
        TypePred a v ↔
          (Sig.Type_ a v ∧
           Frame.Box (F := Sig.F)
             (fun v' =>
               ∀ y : Sig.Thing,
                 Sig.Inst y a v' →
                 LeafPred y v')
             v)) →
      ∀ {u : Sig.F.World},
        Sig.F.R w u →
        KindPred t u →
        KindPred t w :=
  by
    intro TypePred KindPred LeafPred hKindDef hTypeDef u hRu hKind_u

    have hPair_u := (hKindDef t u).1 hKind_u
    rcases hPair_u with ⟨hTypePred_u, hKind_u'⟩

    have hKind_w' : Sig.Kind t w :=
      hKS t u w hKind_u' (Sig.F.symm hRu)

    have hTypePair_u := (hTypeDef t u).1 hTypePred_u
    rcases hTypePair_u with ⟨hType_u, hBoxLeaf_u⟩

    have hDiaType_u :
      Frame.Dia (F := Sig.F) (fun v' => ∃ y : Sig.Thing, Sig.Inst y t v') u :=
      (hA1 t u).1 hType_u

    have hDiaType_w' :
      Frame.Dia (F := Sig.F) (fun v' => ∃ y : Sig.Thing, Sig.Inst y t v') w :=
      (S5Frame.dia_stable (F := Sig.F) (w := u) (v := w) (Sig.F.symm hRu)).1 hDiaType_u

    have hType_w' : Sig.Type_ t w :=
      (hA1 t w).2 hDiaType_w'

    have hBoxLeaf_w :
      Frame.Box (F := Sig.F)
        (fun v' =>
          ∀ y : Sig.Thing,
            Sig.Inst y t v' →
            LeafPred y v')
        w :=
      (S5Frame.box_stable (F := Sig.F) (w := u) (v := w) (Sig.F.symm hRu)).1 hBoxLeaf_u

    have hTypePred_w : TypePred t w :=
      (hTypeDef t w).2 ⟨hType_w', hBoxLeaf_w⟩

    exact (hKindDef t w).2 ⟨hTypePred_w, hKind_w'⟩

  /-
    If `t` is a specific endurant kind at an accessible world,
    then it is already that same specific endurant kind at `w`.
  -/
  have hTransportSpecificDisj :
    ∀ {u : Sig.F.World},
      Sig.F.R w u →
      (Sig.ObjectKind t u ∨
       Sig.CollectiveKind t u ∨
       Sig.QuantityKind t u ∨
       Sig.RelatorKind t u ∨
       Sig.ModeKind t u ∨
       Sig.QualityKind t u) →
      (Sig.ObjectKind t w ∨
       Sig.CollectiveKind t w ∨
       Sig.QuantityKind t w ∨
       Sig.RelatorKind t w ∨
       Sig.ModeKind t w ∨
       Sig.QualityKind t w) :=
  by
    intro u hRu hSpecific_u
    cases hSpecific_u with
    | inl hObjKind_u =>
        exact Or.inl <|
          hTransportSpecific hObjK hObjT hRu hObjKind_u
    | inr hRest =>
        cases hRest with
        | inl hCollKind_u =>
            exact Or.inr <| Or.inl <|
              hTransportSpecific hCollK hCollT hRu hCollKind_u
        | inr hRest =>
            cases hRest with
            | inl hQtyKind_u =>
                exact Or.inr <| Or.inr <| Or.inl <|
                  hTransportSpecific hQtyK hQtyT hRu hQtyKind_u
            | inr hRest =>
                cases hRest with
                | inl hRelKind_u =>
                    exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
                      hTransportSpecific hRelK hRelT hRu hRelKind_u
                | inr hRest =>
                    cases hRest with
                    | inl hModeKind_u =>
                        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
                          hTransportSpecific hModeK hModeT hRu hModeKind_u
                    | inr hQualKind_u =>
                        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                          hTransportSpecific hQualK hQualT hRu hQualKind_u

  rcases hDiaInst_t with ⟨v, hRv, ⟨x, hInst_xt_v⟩⟩

  have hKind_v : Sig.Kind t v :=
    hKS t w v hKind hRv

  have hSortal_v : Sig.Sortal t v :=
    th_t12 (Sig := Sig.toUFOSignature3_2) hA26 t v hKind_v

  have hEnd_v : Sig.EndurantType t v :=
    (hA23 t v).1 hSortal_v |>.1

  have hEnd_x_v : Sig.Endurant x v :=
    hInstEnd t x v hEnd_v hInst_xt_v

  have hDiaSpecific :=
    hA46 x v hEnd_x_v

  rcases hDiaSpecific with ⟨u, hVu, ⟨k, hSpecific_u, hInst_xk_u⟩⟩

  have hWtU : Sig.F.R w u :=
    Sig.F.trans hRv hVu

  have hk_eq_t : k = t := by
    by_cases hEq : k = t
    · exact hEq
    · have hNoOtherKind :
        ¬ Frame.Dia (F := Sig.F)
            (fun v' =>
              ∃ z : Sig.Thing,
                Sig.Kind z v' ∧
                Sig.Inst x z v' ∧
                z ≠ t)
            v :=
        hA22 t x v ⟨hKind_v, hInst_xt_v⟩

      have hBad :
        Frame.Dia (F := Sig.F)
          (fun v' =>
            ∃ z : Sig.Thing,
              Sig.Kind z v' ∧
              Sig.Inst x z v' ∧
              z ≠ t)
          v :=
      by
        exact ⟨u, hVu, ⟨k, hSpecificImpliesKind k u hSpecific_u, hInst_xk_u, hEq⟩⟩

      exact False.elim (hNoOtherKind hBad)

  subst k
  exact hTransportSpecificDisj hWtU hSpecific_u

/--
(t23)

EndurantType(x) ∧ Sortal(x) →
  ObjectKind(x) ∨ CollectiveKind(x) ∨ QuantityKind(x) ∨
  RelatorKind(x) ∨ ModeKind(x) ∨ QualityKind(x) ∨
  SubKind(x) ∨ Phase(x) ∨ Role(x) ∨ SemiRigidSortal(x)

Natural language:
Every endurant sortal belongs to one of the leaves of the taxonomy
of endurant sortals.
-/
theorem th_t23
  (hA1 : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA19 : ax_a19 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA20 : ax_a20 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA22 : ax_a22 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA23 : ax_a23 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA26 : ax_a26 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA28 : ax_a28 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA29 : ax_a29 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hKS : ax_kindStable Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hInstEnd : ax_instEndurant_of_EndurantType (Sig := Sig.toUFOSignature3_3.toUFOSignature3_2))
  (hA44 : ax_a44 Sig)
  (hA45 : ax_a45 Sig)
  (hA46 : ax_a46 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.EndurantType t w ∧ Sig.Sortal t w →
      (Sig.ObjectKind t w ∨
       Sig.CollectiveKind t w ∨
       Sig.QuantityKind t w ∨
       Sig.RelatorKind t w ∨
       Sig.ModeKind t w ∨
       Sig.QualityKind t w ∨
       Sig.SubKind t w ∨
       Sig.Phase t w ∨
       Sig.Role t w ∨
       Sig.SemiRigidSortal t w) :=
by
  classical
  intro t w h
  rcases h with ⟨hEnd, hSortal⟩

  have hRigiditySplit :
    Sig.Rigid t w ∨ Sig.AntiRigid t w ∨ Sig.SemiRigid t w :=
    (th_t5 (Sig := Sig.toUFOSignature3_2) hA18 hA19 hA20 t w).1 hEnd
  cases hRigiditySplit with
  | inl hRigid =>
      have hKindOrSubkind : Sig.Kind t w ∨ Sig.SubKind t w :=
        (hA26 t w).2 ⟨hRigid, hSortal⟩
      cases hKindOrSubkind with
      | inl hKind =>
          have hSpecific :=
            kind_implies_specific_kind
              (Sig := Sig)
              hA1 hA15 hA22 hA23 hA26 hKS hInstEnd hA44 hA45 hA46 t w hKind
          grind
      | inr hSubkind => grind
  | inr hRest =>
      cases hRest with
      | inl hAntiRigid =>
          have hPhaseOrRole : Sig.Phase t w ∨ Sig.Role t w :=
            (hA28 t w).2 ⟨hAntiRigid, hSortal⟩
          grind
      | inr hSemiRigid =>
          have hSRS : Sig.SemiRigidSortal t w :=
            (hA29 t w).2 ⟨hSemiRigid, hSortal⟩
          grind

/--
Helper theorem:

If a type specializes a specific endurant kind, then it belongs to the
corresponding specific endurant type.

-/
theorem sub_specific_kind_implies_specific_type
  (hA5 : ax_a5 Sig.toUFOSignature3_1)
  (hA44 : ax_a44 Sig)
  (hA45 : ax_a45 Sig) :
  ∀ (t k : Sig.Thing) (w : Sig.F.World),
    Sig.Sub t k w →
      (Sig.ObjectKind k w →
        Sig.ObjectType t w)
      ∧
      (Sig.CollectiveKind k w →
        Sig.CollectiveType t w)
      ∧
      (Sig.QuantityKind k w →
        Sig.QuantityType t w)
      ∧
      (Sig.RelatorKind k w →
        Sig.RelatorType t w)
      ∧
      (Sig.ModeKind k w →
        Sig.ModeType t w)
      ∧
      (Sig.QualityKind k w →
        Sig.QualityType t w) :=
by
  intro t k w hSub
  rcases (hA5 t k w).1 hSub with ⟨hType_t, _hType_k, hBoxSub⟩
  rcases hA44 with
    ⟨_hEndT, _hPerdT, _hSubT, _hMomT,
     hObjT, hCollT, hQtyT, hRelT, hModeT, hQualT⟩
  rcases hA45 with
    ⟨hObjK, hCollK, hQtyK, hRelK, hModeK, hQualK⟩

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro hObjKind
    have hObjType_k : Sig.ObjectType k w :=
      (hObjK k w).1 hObjKind |>.1
    rcases (hObjT k w).1 hObjType_k with ⟨_hType_k, hBoxObj⟩
    refine (hObjT t w).2 ⟨hType_t, ?_⟩
    intro v hRv x hxInst
    exact hBoxObj v hRv x (hBoxSub v hRv x hxInst)

  · intro hCollKind
    have hCollType_k : Sig.CollectiveType k w :=
      (hCollK k w).1 hCollKind |>.1
    rcases (hCollT k w).1 hCollType_k with ⟨_hType_k, hBoxColl⟩
    refine (hCollT t w).2 ⟨hType_t, ?_⟩
    intro v hRv x hxInst
    exact hBoxColl v hRv x (hBoxSub v hRv x hxInst)

  · intro hQtyKind
    have hQtyType_k : Sig.QuantityType k w :=
      (hQtyK k w).1 hQtyKind |>.1
    rcases (hQtyT k w).1 hQtyType_k with ⟨_hType_k, hBoxQty⟩
    refine (hQtyT t w).2 ⟨hType_t, ?_⟩
    intro v hRv x hxInst
    exact hBoxQty v hRv x (hBoxSub v hRv x hxInst)

  · intro hRelKind
    have hRelType_k : Sig.RelatorType k w :=
      (hRelK k w).1 hRelKind |>.1
    rcases (hRelT k w).1 hRelType_k with ⟨_hType_k, hBoxRel⟩
    refine (hRelT t w).2 ⟨hType_t, ?_⟩
    intro v hRv x hxInst
    exact hBoxRel v hRv x (hBoxSub v hRv x hxInst)

  · intro hModeKind
    have hModeType_k : Sig.ModeType k w :=
      (hModeK k w).1 hModeKind |>.1
    rcases (hModeT k w).1 hModeType_k with ⟨_hType_k, hBoxMode⟩
    refine (hModeT t w).2 ⟨hType_t, ?_⟩
    intro v hRv x hxInst
    exact hBoxMode v hRv x (hBoxSub v hRv x hxInst)

  · intro hQualKind
    have hQualType_k : Sig.QualityType k w :=
      (hQualK k w).1 hQualKind |>.1
    rcases (hQualT k w).1 hQualType_k with ⟨_hType_k, hBoxQual⟩
    refine (hQualT t w).2 ⟨hType_t, ?_⟩
    intro v hRv x hxInst
    exact hBoxQual v hRv x (hBoxSub v hRv x hxInst)

/--
(t24)

(Sortal(t) ∧
 (ObjectType(t) ∨ CollectiveType(t) ∨ QuantityType(t) ∨
  RelatorType(t) ∨ ModeType(t) ∨ QualityType(t)))
↔
∃k ((ObjectKind(k) ∨ CollectiveKind(k) ∨ QuantityKind(k) ∨
     RelatorKind(k) ∨ ModeKind(k) ∨ QualityKind(k)) ∧ t ⊑ k)

Natural language:
A sortal that is already classified in one of the six specific endurant
type categories specializes some corresponding specific endurant kind,
and conversely any specialization of a specific endurant kind inherits
the corresponding specific endurant type.
-/
theorem th_t24
  (hA1 : ax_a1 Sig.toUFOSignature3_1)
  (hA5 : ax_a5 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA22 : ax_a22 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA23 : ax_a23 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA26 : ax_a26 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hKS : ax_kindStable Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hInstEnd : ax_instEndurant_of_EndurantType (Sig := Sig.toUFOSignature3_3.toUFOSignature3_2))
  (hSubKindSortal : ax_sub_of_kind_is_sortal (Sig := Sig.toUFOSignature3_3.toUFOSignature3_2))
  (hA44 : ax_a44 Sig)
  (hA45 : ax_a45 Sig)
  (hA46 : ax_a46 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    (Sig.Sortal t w ∧
      (Sig.ObjectType t w ∨
       Sig.CollectiveType t w ∨
       Sig.QuantityType t w ∨
       Sig.RelatorType t w ∨
       Sig.ModeType t w ∨
       Sig.QualityType t w))
    ↔
    ∃ k : Sig.Thing,
      (Sig.ObjectKind k w ∨
       Sig.CollectiveKind k w ∨
       Sig.QuantityKind k w ∨
       Sig.RelatorKind k w ∨
       Sig.ModeKind k w ∨
       Sig.QualityKind k w)
      ∧
      Sig.Sub t k w :=
by
  intro t w
  constructor

  · intro h
    rcases h with ⟨hSortal, _hSpecificType⟩
    rcases th_t13
      (Sig := Sig.toUFOSignature3_2)
      hA5 hA15 hA23 hA26 t w hSortal with ⟨k, hKind_k, hSub_tk⟩

    have hSpecificKind_k :
      Sig.ObjectKind k w ∨
      Sig.CollectiveKind k w ∨
      Sig.QuantityKind k w ∨
      Sig.RelatorKind k w ∨
      Sig.ModeKind k w ∨
      Sig.QualityKind k w :=
      kind_implies_specific_kind
        (Sig := Sig)
        hA1 hA15 hA22 hA23 hA26 hKS hInstEnd hA44 hA45 hA46 k w hKind_k

    exact ⟨k, hSpecificKind_k, hSub_tk⟩

  · intro h
    rcases h with ⟨k, hSpecificKind_k, hSub_tk⟩
    rcases hA45 with
      ⟨hObjK, hCollK, hQtyK, hRelK, hModeK, hQualK⟩

    have hKind_k : Sig.Kind k w := by
      cases hSpecificKind_k with
      | inl hObjKind =>
          have : Sig.ObjectType k w ∧ Sig.Kind k w := (hObjK k w).1 hObjKind
          grind
      | inr hRest =>
          cases hRest with
          | inl hCollKind =>
              have : Sig.CollectiveType k w ∧ Sig.Kind k w := (hCollK k w).1 hCollKind
              grind
          | inr hRest =>
              cases hRest with
              | inl hQtyKind =>
                  have : Sig.QuantityType k w ∧ Sig.Kind k w := (hQtyK k w).1 hQtyKind
                  grind
              | inr hRest =>
                  cases hRest with
                  | inl hRelKind =>
                      have : Sig.RelatorType k w ∧ Sig.Kind k w := (hRelK k w).1 hRelKind
                      grind
                  | inr hRest =>
                      cases hRest with
                      | inl hModeKind =>
                          have : Sig.ModeType k w ∧ Sig.Kind k w := (hModeK k w).1 hModeKind
                          grind
                      | inr hQualKind =>
                          have : Sig.QualityType k w ∧ Sig.Kind k w := (hQualK k w).1 hQualKind
                          grind

    have hSortal_t : Sig.Sortal t w :=
      hSubKindSortal t k w hSub_tk hKind_k

    have hSpecificType_t :=
      sub_specific_kind_implies_specific_type
        (Sig := Sig)
        hA5 hA44 ⟨hObjK, hCollK, hQtyK, hRelK, hModeK, hQualK⟩ t k w hSub_tk

    refine ⟨hSortal_t, ?_⟩
    cases hSpecificKind_k with
    | inl hObjKind =>
        have : Sig.ObjectType t w := hSpecificType_t.1 hObjKind
        grind
    | inr hRest =>
        cases hRest with
        | inl hCollKind =>
            have : Sig.CollectiveType t w := hSpecificType_t.2.1 hCollKind
            grind
        | inr hRest =>
            cases hRest with
            | inl hQtyKind =>
                have : Sig.QuantityType t w := hSpecificType_t.2.2.1 hQtyKind
                grind
            | inr hRest =>
                cases hRest with
                | inl hRelKind =>
                    have : Sig.RelatorType t w := hSpecificType_t.2.2.2.1 hRelKind
                    grind
                | inr hRest =>
                    cases hRest with
                    | inl hModeKind =>
                        have : Sig.ModeType t w := hSpecificType_t.2.2.2.2.1 hModeKind
                        grind
                    | inr hQualKind =>
                        have : Sig.QualityType t w := hSpecificType_t.2.2.2.2.2 hQualKind
                        grind

/--
Helper theorem:

Every specific endurant kind is, in particular, a `Kind`.
-/
theorem specific_kind_implies_kind
  (hA45 : ax_a45 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    (Sig.ObjectKind t w ∨
     Sig.CollectiveKind t w ∨
     Sig.QuantityKind t w ∨
     Sig.RelatorKind t w ∨
     Sig.ModeKind t w ∨
     Sig.QualityKind t w) →
    Sig.Kind t w :=
by
  intro t w h
  rcases hA45 with
    ⟨hObjK, hCollK, hQtyK, hRelK, hModeK, hQualK⟩
  cases h with
  | inl hObjKind =>
      have : Sig.ObjectType t w ∧ Sig.Kind t w := (hObjK t w).1 hObjKind
      grind
  | inr hRest =>
      cases hRest with
      | inl hCollKind =>
          have : Sig.CollectiveType t w ∧ Sig.Kind t w := (hCollK t w).1 hCollKind
          grind
      | inr hRest =>
          cases hRest with
          | inl hQtyKind =>
              have : Sig.QuantityType t w ∧ Sig.Kind t w := (hQtyK t w).1 hQtyKind
              grind
          | inr hRest =>
              cases hRest with
              | inl hRelKind =>
                  have : Sig.RelatorType t w ∧ Sig.Kind t w := (hRelK t w).1 hRelKind
                  grind
              | inr hRest =>
                  cases hRest with
                  | inl hModeKind =>
                      have : Sig.ModeType t w ∧ Sig.Kind t w := (hModeK t w).1 hModeKind
                      grind
                  | inr hQualKind =>
                      have : Sig.QualityType t w ∧ Sig.Kind t w := (hQualK t w).1 hQualKind
                      grind

/--
(t25)

The leaves of the taxonomy of endurant types are pairwise disjoint.

Natural language:
No endurant type can belong to two distinct leaves among
`ObjectKind`, `CollectiveKind`, `QuantityKind`, `SubKind`,
`RelatorKind`, `ModeKind`, `QualityKind`, `SemiRigidSortal`,
`Category`, `Phase`, `Mixin`, `Role`, `PhaseMixin`, `RoleMixin`.
-/
theorem th_t25
  (hA45 : ax_a45 Sig)
  (hT17 : ∀ t w,
    (Sig.Kind t w →
      (¬ Sig.SubKind t w ∧
       ¬ Sig.Role t w ∧
       ¬ Sig.Phase t w ∧
       ¬ Sig.SemiRigidSortal t w ∧
       ¬ Sig.Category t w ∧
       ¬ Sig.Mixin t w ∧
       ¬ Sig.PhaseMixin t w ∧
       ¬ Sig.RoleMixin t w))
    ∧
    (Sig.SubKind t w →
      (¬ Sig.Kind t w ∧
       ¬ Sig.Role t w ∧
       ¬ Sig.Phase t w ∧
       ¬ Sig.SemiRigidSortal t w ∧
       ¬ Sig.Category t w ∧
       ¬ Sig.Mixin t w ∧
       ¬ Sig.PhaseMixin t w ∧
       ¬ Sig.RoleMixin t w))
    ∧
    (Sig.Role t w →
      (¬ Sig.Phase t w ∧
       ¬ Sig.SemiRigidSortal t w ∧
       ¬ Sig.Category t w ∧
       ¬ Sig.Mixin t w ∧
       ¬ Sig.PhaseMixin t w ∧
       ¬ Sig.RoleMixin t w))
    ∧
    (Sig.Phase t w →
      (¬ Sig.SemiRigidSortal t w ∧
       ¬ Sig.Category t w ∧
       ¬ Sig.Mixin t w ∧
       ¬ Sig.PhaseMixin t w ∧
       ¬ Sig.RoleMixin t w))
    ∧
    (Sig.SemiRigidSortal t w →
      (¬ Sig.Category t w ∧
       ¬ Sig.Mixin t w ∧
       ¬ Sig.PhaseMixin t w ∧
       ¬ Sig.RoleMixin t w))
    ∧
    (Sig.Category t w →
      (¬ Sig.Mixin t w ∧
       ¬ Sig.PhaseMixin t w ∧
       ¬ Sig.RoleMixin t w))
    ∧
    (Sig.Mixin t w →
      (¬ Sig.PhaseMixin t w ∧
       ¬ Sig.RoleMixin t w))
    ∧
    (Sig.PhaseMixin t w →
      ¬ Sig.RoleMixin t w))
  (hT21 : ∀ (t : Sig.Thing) (w : Sig.F.World),
    (Sig.ObjectType t w →
      ¬ Sig.CollectiveType t w ∧
      ¬ Sig.QuantityType t w ∧
      ¬ Sig.RelatorType t w ∧
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)
    ∧
    (Sig.CollectiveType t w →
      ¬ Sig.QuantityType t w ∧
      ¬ Sig.RelatorType t w ∧
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)
    ∧
    (Sig.QuantityType t w →
      ¬ Sig.RelatorType t w ∧
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)
    ∧
    (Sig.RelatorType t w →
      ¬ Sig.ModeType t w ∧
      ¬ Sig.QualityType t w)
    ∧
    (Sig.ModeType t w →
      ¬ Sig.QualityType t w)) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    (Sig.ObjectKind t w →
      ¬ Sig.CollectiveKind t w ∧
      ¬ Sig.QuantityKind t w ∧
      ¬ Sig.SubKind t w ∧
      ¬ Sig.RelatorKind t w ∧
      ¬ Sig.ModeKind t w ∧
      ¬ Sig.QualityKind t w ∧
      ¬ Sig.SemiRigidSortal t w ∧
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.CollectiveKind t w →
      ¬ Sig.QuantityKind t w ∧
      ¬ Sig.SubKind t w ∧
      ¬ Sig.RelatorKind t w ∧
      ¬ Sig.ModeKind t w ∧
      ¬ Sig.QualityKind t w ∧
      ¬ Sig.SemiRigidSortal t w ∧
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.QuantityKind t w →
      ¬ Sig.SubKind t w ∧
      ¬ Sig.RelatorKind t w ∧
      ¬ Sig.ModeKind t w ∧
      ¬ Sig.QualityKind t w ∧
      ¬ Sig.SemiRigidSortal t w ∧
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.SubKind t w →
      ¬ Sig.RelatorKind t w ∧
      ¬ Sig.ModeKind t w ∧
      ¬ Sig.QualityKind t w ∧
      ¬ Sig.SemiRigidSortal t w ∧
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.RelatorKind t w →
      ¬ Sig.ModeKind t w ∧
      ¬ Sig.QualityKind t w ∧
      ¬ Sig.SemiRigidSortal t w ∧
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.ModeKind t w →
      ¬ Sig.QualityKind t w ∧
      ¬ Sig.SemiRigidSortal t w ∧
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.QualityKind t w →
      ¬ Sig.SemiRigidSortal t w ∧
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.SemiRigidSortal t w →
      ¬ Sig.Category t w ∧
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.Category t w →
      ¬ Sig.Phase t w ∧
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.Phase t w →
      ¬ Sig.Mixin t w ∧
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.Mixin t w →
      ¬ Sig.Role t w ∧
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.Role t w →
      ¬ Sig.PhaseMixin t w ∧
      ¬ Sig.RoleMixin t w)
    ∧
    (Sig.PhaseMixin t w →
      ¬ Sig.RoleMixin t w) :=
by
  classical
  intro t w
  rcases hA45 with
    ⟨hObjK, hCollK, hQtyK, hRelK, hModeK, hQualK⟩
  have h17 := hT17 t w
  have h21 := hT21 t w
  have hSpecToKind :
    (Sig.ObjectKind t w → Sig.Kind t w) ∧
    (Sig.CollectiveKind t w → Sig.Kind t w) ∧
    (Sig.QuantityKind t w → Sig.Kind t w) ∧
    (Sig.RelatorKind t w → Sig.Kind t w) ∧
    (Sig.ModeKind t w → Sig.Kind t w) ∧
    (Sig.QualityKind t w → Sig.Kind t w) :=
  by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;>
    exact specific_kind_implies_kind (Sig := Sig) ⟨hObjK, hCollK, hQtyK, hRelK, hModeK, hQualK⟩ t w <|
      by
        first
        | exact Or.inl h
        | exact Or.inr (Or.inl h)
        | exact Or.inr (Or.inr (Or.inl h))
        | exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hObjKind
    have hKind : Sig.Kind t w := hSpecToKind.1 hObjKind
    have hKindNo := h17.1 hKind
    have hObjType : Sig.ObjectType t w := (hObjK t w).1 hObjKind |>.1
    have hObjNo := (h21.1 hObjType)
    have hSpecType :
      Sig.ObjectKind t w → Sig.ObjectType t w := fun h => (hObjK t w).1 h |>.1
    have hCollType :
      Sig.CollectiveKind t w → Sig.CollectiveType t w := fun h => (hCollK t w).1 h |>.1
    have hQtyType :
      Sig.QuantityKind t w → Sig.QuantityType t w := fun h => (hQtyK t w).1 h |>.1
    have hRelType :
      Sig.RelatorKind t w → Sig.RelatorType t w := fun h => (hRelK t w).1 h |>.1
    have hModeType :
      Sig.ModeKind t w → Sig.ModeType t w := fun h => (hModeK t w).1 h |>.1
    have hQualType :
      Sig.QualityKind t w → Sig.QualityType t w := fun h => (hQualK t w).1 h |>.1
    grind
  · intro hCollKind
    have hKind : Sig.Kind t w := hSpecToKind.2.1 hCollKind
    have hKindNo := h17.1 hKind
    have hCollType : Sig.CollectiveType t w := (hCollK t w).1 hCollKind |>.1
    have hCollNo := (h21.2.1 hCollType)
    have hQtyType :
      Sig.QuantityKind t w → Sig.QuantityType t w := fun h => (hQtyK t w).1 h |>.1
    have hRelType :
      Sig.RelatorKind t w → Sig.RelatorType t w := fun h => (hRelK t w).1 h |>.1
    have hModeType :
      Sig.ModeKind t w → Sig.ModeType t w := fun h => (hModeK t w).1 h |>.1
    have hQualType :
      Sig.QualityKind t w → Sig.QualityType t w := fun h => (hQualK t w).1 h |>.1
    grind
  · intro hQtyKind
    have hKind : Sig.Kind t w := hSpecToKind.2.2.1 hQtyKind
    have hKindNo := h17.1 hKind
    have hQtyType : Sig.QuantityType t w := (hQtyK t w).1 hQtyKind |>.1
    have hQtyNo := (h21.2.2.1 hQtyType)
    have hRelType :
      Sig.RelatorKind t w → Sig.RelatorType t w := fun h => (hRelK t w).1 h |>.1
    have hModeType :
      Sig.ModeKind t w → Sig.ModeType t w := fun h => (hModeK t w).1 h |>.1
    have hQualType :
      Sig.QualityKind t w → Sig.QualityType t w := fun h => (hQualK t w).1 h |>.1
    grind
  · intro hSubKind
    have hSubNo := h17.2.1 hSubKind
    have hNotKind : ¬ Sig.Kind t w := hSubNo.1
    grind
  · intro hRelKind
    have hKind : Sig.Kind t w := hSpecToKind.2.2.2.1 hRelKind
    have hKindNo := h17.1 hKind
    have hRelType : Sig.RelatorType t w := (hRelK t w).1 hRelKind |>.1
    have hRelNo := (h21.2.2.2.1 hRelType)
    have hModeType :
      Sig.ModeKind t w → Sig.ModeType t w := fun h => (hModeK t w).1 h |>.1
    have hQualType :
      Sig.QualityKind t w → Sig.QualityType t w := fun h => (hQualK t w).1 h |>.1
    grind
  · intro hModeKind
    have hKind : Sig.Kind t w := hSpecToKind.2.2.2.2.1 hModeKind
    have hKindNo := h17.1 hKind
    have hModeType : Sig.ModeType t w := (hModeK t w).1 hModeKind |>.1
    have hModeNo := (h21.2.2.2.2 hModeType)
    have hQualType :
      Sig.QualityKind t w → Sig.QualityType t w := fun h => (hQualK t w).1 h |>.1
    grind
  · intro hQualKind
    have hKind : Sig.Kind t w := hSpecToKind.2.2.2.2.2 hQualKind
    have hKindNo := h17.1 hKind
    grind
  · intro hSRS
    have hSRSNo := h17.2.2.2.2.1 hSRS
    have hNotPhase : ¬ Sig.Phase t w := by
      intro hPhase
      exact (h17.2.2.2.1 hPhase).1 hSRS
    have hNotRole : ¬ Sig.Role t w := by
      intro hRole
      exact (h17.2.2.1 hRole).2.1 hSRS
    have hNotKind : ¬ Sig.Kind t w := by
      intro hKind
      exact (h17.1 hKind).2.2.2.1 hSRS
    exact ⟨hSRSNo.1, hNotPhase, hSRSNo.2.1, hNotRole, hSRSNo.2.2.1, hSRSNo.2.2.2⟩
  · intro hCat
    have hCatNo := h17.2.2.2.2.2.1 hCat
    have hNotPhase : ¬ Sig.Phase t w := by
      intro hPhase
      exact (h17.2.2.2.1 hPhase).2.1 hCat
    have hNotRole : ¬ Sig.Role t w := by
      intro hRole
      exact (h17.2.2.1 hRole).2.2.1 hCat
    have hNotKind : ¬ Sig.Kind t w := by
      intro hKind
      exact (h17.1 hKind).2.2.2.2.1 hCat
    exact ⟨hNotPhase, hCatNo.1, hNotRole, hCatNo.2.1, hCatNo.2.2⟩
  · intro hPhase
    have hPhaseNo := h17.2.2.2.1 hPhase
    have hNotRole : ¬ Sig.Role t w := by
      intro hRole
      exact (h17.2.2.1 hRole).1 hPhase
    have hNotKind : ¬ Sig.Kind t w := by
      intro hKind
      exact (h17.1 hKind).2.2.1 hPhase
    exact ⟨hPhaseNo.2.2.1, hNotRole, hPhaseNo.2.2.2.1, hPhaseNo.2.2.2.2⟩
  · intro hMix
    have hMixNo := h17.2.2.2.2.2.2.1 hMix
    have hNotRole : ¬ Sig.Role t w := by
      intro hRole
      exact (h17.2.2.1 hRole).2.2.2.1 hMix
    have hNotKind : ¬ Sig.Kind t w := by
      intro hKind
      exact (h17.1 hKind).2.2.2.2.2.1 hMix
    exact ⟨hNotRole, hMixNo.1, hMixNo.2⟩
  · intro hRole
    have hRoleNo := h17.2.2.1 hRole
    have hNotKind : ¬ Sig.Kind t w := by
      intro hKind
      exact (h17.1 hKind).2.1 hRole
    exact ⟨hRoleNo.2.2.2.2.1, hRoleNo.2.2.2.2.2⟩
  · intro hPM
    exact h17.2.2.2.2.2.2.2 hPM

/--
(t26)

Every endurant type belongs to one of the leaves of the taxonomy of
endurant types.
-/
theorem th_t26
  (hA1 : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA22 : ax_a22 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA23 : ax_a23 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hA26 : ax_a26 Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hKS : ax_kindStable Sig.toUFOSignature3_3.toUFOSignature3_2)
  (hInstEnd : ax_instEndurant_of_EndurantType (Sig := Sig.toUFOSignature3_3.toUFOSignature3_2))
  (hA44 : ax_a44 Sig)
  (hA45 : ax_a45 Sig)
  (hA46 : ax_a46 Sig)
  (hT18 : ∀ t w,
    Sig.EndurantType t w ↔
      (Sig.Kind t w ∨
       Sig.SubKind t w ∨
       Sig.Role t w ∨
       Sig.Phase t w ∨
       Sig.SemiRigidSortal t w ∨
       Sig.Category t w ∨
       Sig.Mixin t w ∨
       Sig.PhaseMixin t w ∨
       Sig.RoleMixin t w)) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.EndurantType t w →
      (Sig.ObjectKind t w ∨
       Sig.CollectiveKind t w ∨
       Sig.QuantityKind t w ∨
       Sig.SubKind t w ∨
       Sig.RelatorKind t w ∨
       Sig.ModeKind t w ∨
       Sig.QualityKind t w ∨
       Sig.SemiRigidSortal t w ∨
       Sig.Category t w ∨
       Sig.Phase t w ∨
       Sig.Mixin t w ∨
       Sig.Role t w ∨
       Sig.PhaseMixin t w ∨
       Sig.RoleMixin t w) :=
by
  classical
  intro t w hEnd
  have hLeaf := (hT18 t w).1 hEnd
  cases hLeaf with
  | inl hKind =>
      have hSpecific :=
        kind_implies_specific_kind
          (Sig := Sig)
          hA1 hA15 hA22 hA23 hA26 hKS hInstEnd hA44 hA45 hA46 t w hKind
      grind
  | inr hRest =>
      cases hRest with
      | inl hSubKind =>
          grind
      | inr hRest =>
          cases hRest with
          | inl hRole =>
              grind
          | inr hRest =>
              cases hRest with
              | inl hPhase =>
                  grind
              | inr hRest =>
                  cases hRest with
                  | inl hSRS =>
                      grind
                  | inr hRest =>
                      cases hRest with
                      | inl hCat =>
                          grind
                      | inr hRest =>
                          cases hRest with
                          | inl hMix =>
                              grind
                          | inr hRest =>
                              cases hRest with
                              | inl hPM =>
                                  grind
                              | inr hRM =>
                                  grind

/--
Axioms package for §3.4.

Extends §3.3 axioms with:
- (a44) the endurant-type refinements,
- (a45) the corresponding specific kind definitions,
- (a46) existence of some specific endurant kind for every endurant.
-/
class UFOAxioms3_4 (Sig : UFOSignature3_4) : Prop
  extends UFOAxioms3_3 Sig.toUFOSignature3_3 where

  -- §3.4 axioms
  ax44 : ax_a44 Sig
  ax45 : ax_a45 Sig
  ax46 : ax_a46 Sig
