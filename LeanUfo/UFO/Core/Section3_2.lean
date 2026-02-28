import LeanUfo.UFO.Core.Signature3_2
import LeanUfo.UFO.Core.Section3_1
import LeanUfo.UFO.Modal.Basics

universe u v

variable (Sig : UFOSignature3_2)

open UFOSignature3_2

/--
(a18)

Rigid(t) ↔ EndurantType(t) ∧ ∀x (◇(x :: t) → □(x :: t))

Natural language:
A rigid endurant type is one such that any thing that can possibly instantiate it
must instantiate it in all accessible worlds.
-/
def ax_a18 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Rigid t w ↔
      (Sig.EndurantType t w ∧
        ∀ x : Sig.Thing,
          (S5Frame.Dia (F := Sig.F) (fun w' => Sig.Inst x t w') w →
           S5Frame.Box (F := Sig.F) (fun w' => Sig.Inst x t w') w))

/--
(a19)

AntiRigid(t) ↔ EndurantType(t) ∧ ∀x (◇(x :: t) → ◇(¬ x :: t))

Natural language:
An anti-rigid endurant type admits possible non-instantiation: if x can instantiate t,
then it is also possible that x does not instantiate t.
-/
def ax_a19 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.AntiRigid t w ↔
      (Sig.EndurantType t w ∧
        ∀ x : Sig.Thing,
          (S5Frame.Dia (F := Sig.F) (fun w' => Sig.Inst x t w') w →
           S5Frame.Dia (F := Sig.F) (fun w' => ¬ Sig.Inst x t w') w))

/--
(a20)

SemiRigid(t) ↔ EndurantType(t) ∧ ¬Rigid(t) ∧ ¬AntiRigid(t)

Natural language:
A semi-rigid endurant type is an endurant type that is neither rigid nor anti-rigid.
-/
def ax_a20 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.SemiRigid t w ↔
      (Sig.EndurantType t w ∧
       ¬ Sig.Rigid t w ∧
       ¬ Sig.AntiRigid t w)

/--
(t5)

EndurantType(t) ↔ Rigid(t) ∨ AntiRigid(t) ∨ SemiRigid(t)

Natural language:
Every endurant type is one of: rigid, anti-rigid, or semi-rigid.
-/
theorem th_t5
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.EndurantType t w ↔
      (Sig.Rigid t w ∨ Sig.AntiRigid t w ∨ Sig.SemiRigid t w) :=
by
  classical
  intro t w
  constructor
  · intro hEnd
    by_cases hR : Sig.Rigid t w
    · exact Or.inl hR
    · by_cases hAR : Sig.AntiRigid t w
      · exact Or.inr (Or.inl hAR)
      · -- neither rigid nor anti-rigid, so semi-rigid by (a20)
        have hSemi : Sig.SemiRigid t w := (hA20 t w).2 ⟨hEnd, hR, hAR⟩
        exact Or.inr (Or.inr hSemi)
  · intro h
    rcases h with hR | hRest
    · -- rigid → endurantType via (a18)
      exact (hA18 t w).1 hR |>.1
    rcases hRest with hAR | hSemi
    · -- antiRigid → endurantType via (a19)
      exact (hA19 t w).1 hAR |>.1
    · -- semiRigid → endurantType via (a20)
      exact (hA20 t w).1 hSemi |>.1

/--
Lemma:

Rigid(x) ∧ AntiRigid(x) leads to modal inconsistency:
for any y, if y possibly instantiates x, then contradiction.

This captures the S5 clash:
Rigid gives  ◇φ → □φ
AntiRigid gives ◇φ → ◇¬φ
But in S5, □φ implies ¬◇¬φ.
-/
theorem rigid_antirigid_clash
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  {x : Sig.Thing} {w : Sig.F.World}
  (hR : Sig.Rigid x w)
  (hAR : Sig.AntiRigid x w) :
  ∀ y : Sig.Thing,
    (S5Frame.Dia (F := Sig.F) (fun w' => Sig.Inst y x w') w →
     False) :=
by
  classical
  intro y hDia

  -- unfold definitions of rigid and anti-rigid
  have hRigid := (hA18 x w).1 hR
  have hAnti  := (hA19 x w).1 hAR

  rcases hRigid with ⟨_, hRigidCond⟩
  rcases hAnti  with ⟨_, hAntiCond⟩

  -- From rigidity: ◇Inst → □Inst
  have hBox := hRigidCond y hDia

  -- From anti-rigidity: ◇Inst → ◇¬Inst
  have hDiaNot := hAntiCond y hDia

  -- But □Inst implies ¬◇¬Inst
  have hNoDiaNot :
    ¬ S5Frame.Dia (F := Sig.F) (fun w' => ¬ Sig.Inst y x w') w :=
  by
    intro hContra
    rcases hContra with ⟨v, hvR, hNotInst⟩
    have hInst := hBox v hvR
    exact hNotInst hInst

  exact hNoDiaNot hDiaNot

/--
Lemma:

If x is rigid (hence an EndurantType by a18), then x is a Type by a15,
and thus (by a1) x is possibly instantiated.
So we can extract some y with ◇(y :: x).
-/
theorem rigid_has_possible_instance
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  {x : Sig.Thing} {w : Sig.F.World}
  (hR : Sig.Rigid x w) :
  ∃ y : Sig.Thing,
    S5Frame.Dia (F := Sig.F) (fun w' => Sig.Inst y x w') w :=
by
  -- from rigid: EndurantType(x)
  have hEnd : Sig.EndurantType x w := (hA18 x w).1 hR |>.1

  -- a15: EndurantType(x) → Type(x)
  have hType : Sig.Type_ x w := hA15 x w hEnd

  -- a1: Type(x) ↔ ◇(∃ y, y :: x)
  have hDiaEx :
      S5Frame.Dia (F := Sig.F) (fun w' => ∃ y : Sig.Thing, Sig.Inst y x w') w :=
    (hA1 x w).1 hType

  -- pick witness world and witness y
  rcases hDiaEx with ⟨v, hvR, ⟨y, hy⟩⟩
  refine ⟨y, ?_⟩
  exact ⟨v, hvR, hy⟩

/--
(t6)
¬∃x ((Rigid(x) ∧ AntiRigid(x)) ∨
      (Rigid(x) ∧ SemiRigid(x)) ∨
      (SemiRigid(x) ∧ AntiRigid(x)))

Natural language:
The rigidity classes are pairwise disjoint.

Remark on (t6):

The disjointness of rigidity classes is not merely definitional.
It follows from the interaction between:

- (a1) Types are possibly instantiated.
- (a15) EndurantTypes are Types.
- (a18) Rigid types make instantiation necessary once possible.
- (a19) AntiRigid types allow possible non-instantiation.
- S5 modal duality: □φ implies ¬◇¬φ.

Thus, if a type were both Rigid and AntiRigid, then for some
possible instance y we would obtain both:

  □(y :: x)   and   ◇¬(y :: x),

which is impossible in S5 semantics.

The incompatibility is therefore semantic (modal), not purely syntactic.
-/
theorem th_t6
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ (w : Sig.F.World),
    ¬ ∃ x : Sig.Thing,
        (Sig.Rigid x w ∧ Sig.AntiRigid x w) ∨
        (Sig.Rigid x w ∧ Sig.SemiRigid x w) ∨
        (Sig.SemiRigid x w ∧ Sig.AntiRigid x w) :=
by
  intro w
  intro h
  rcases h with ⟨x, hCases⟩

  rcases hCases with hRA | hRest

  · -- case: Rigid(x) ∧ AntiRigid(x)
    rcases hRA with ⟨hR, hAR⟩
    obtain ⟨y, hDia⟩ :=
      rigid_has_possible_instance (Sig := Sig) hA1 hA15 hA18 (x := x) (w := w) hR
    exact rigid_antirigid_clash (Sig := Sig) hA18 hA19 (x := x) (w := w) hR hAR y hDia

  · rcases hRest with hRS | hSAR

    · -- case: Rigid(x) ∧ SemiRigid(x)
      rcases hRS with ⟨hR, hS⟩
      have hNotR : ¬ Sig.Rigid x w := (hA20 x w).1 hS |>.2.1
      exact hNotR hR

    · -- case: SemiRigid(x) ∧ AntiRigid(x)
      rcases hSAR with ⟨hS, hAR⟩
      have hNotAR : ¬ Sig.AntiRigid x w := (hA20 x w).1 hS |>.2.2
      exact hNotAR hAR

/--
(t7)

¬∃x,y (Rigid(x) ∧ AntiRigid(y) ∧ x ⊑ y)

Natural language:
No rigid type can specialize an anti-rigid type.
-/
theorem th_t7
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA5  : ax_a5 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig) :
  ∀ (w : Sig.F.World),
    ¬ ∃ x y : Sig.Thing,
        Sig.Rigid x w ∧
        Sig.AntiRigid y w ∧
        Sig.Sub x y w :=
by
  classical
  intro w
  intro h
  rcases h with ⟨x, y, hR, hAR, hSub⟩

  -- From rigidity of x: obtain possible instance
  obtain ⟨z, hDia_x⟩ :=
    rigid_has_possible_instance (Sig := Sig)
      hA1 hA15 hA18 (x := x) (w := w) hR

  -- Unfold specialization x ⊑ y
  have hSubDef := (hA5 x y w).1 hSub
  rcases hSubDef with ⟨_, _, hBoxIncl⟩

  -- From rigidity of x: ◇(z :: x) → □(z :: x)
  have hRigidDef := (hA18 x w).1 hR
  rcases hRigidDef with ⟨_, hRigidCond⟩

  have hBox_x := hRigidCond z hDia_x

  -- Using specialization: □(z :: y)
  have hBox_y :
    S5Frame.Box (F := Sig.F)
      (fun w' => Sig.Inst z y w') w :=
  by
    intro v hvR
    have hInst_x := hBox_x v hvR
    exact hBoxIncl v hvR z hInst_x

  -- From anti-rigidity of y
  have hAntiDef := (hA19 y w).1 hAR
  rcases hAntiDef with ⟨_, hAntiCond⟩

  -- From possible instantiation of x and specialization,
  -- we get possible instantiation of y
  have hDia_y :
    S5Frame.Dia (F := Sig.F)
      (fun w' => Sig.Inst z y w') w :=
  by
    rcases hDia_x with ⟨v, hvR, hInst_x⟩
    refine ⟨v, hvR, ?_⟩
    exact hBoxIncl v hvR z hInst_x

  -- AntiRigid(y): ◇(z :: y) → ◇¬(z :: y)
  have hDiaNot_y := hAntiCond z hDia_y

  -- But □(z :: y) implies ¬◇¬(z :: y)
  have hNoDiaNot :
    ¬ S5Frame.Dia (F := Sig.F)
        (fun w' => ¬ Sig.Inst z y w') w :=
  by
    intro hContra
    rcases hContra with ⟨v, hvR, hNotInst⟩
    have hInst := hBox_y v hvR
    exact hNotInst hInst

  exact hNoDiaNot hDiaNot_y


/--
Lemma (used for t8):

If y is AntiRigid and x ⊑ y, then x is AntiRigid *provided x is an EndurantType*.

Why the extra assumption `EndurantType(x)`?
Because AntiRigid(x) is defined (a19) as `EndurantType(x) ∧ ...`,
and with the current axioms we cannot infer `EndurantType(x)` purely from `x ⊑ y`.
In t8 we will supply it from `SemiRigid(x)` via (a20).
-/
theorem antiRigid_downward
  (Sig : UFOSignature3_2)
  (hA5  : ax_a5 Sig.toUFOSignature3_1)
  (hA19 : ax_a19 Sig)
  {x y : Sig.Thing} {w : Sig.F.World}
  (hEndx : Sig.EndurantType x w)
  (hARy  : Sig.AntiRigid y w)
  (hSub  : Sig.Sub x y w) :
  Sig.AntiRigid x w :=
by
  -- unpack AntiRigid(y)
  have hAntiY := (hA19 y w).1 hARy
  rcases hAntiY with ⟨_hEndy, hAntiCondY⟩
  -- hAntiCondY :
  --   ∀ z, ◇(z :: y) → ◇(¬ z :: y)

  -- unpack specialization x ⊑ y (a5), obtaining the necessary inclusion box
  have hSubDef := (hA5 x y w).1 hSub
  rcases hSubDef with ⟨_hTx, _hTy, hBoxIncl⟩
  -- hBoxIncl :
  --   □ (∀ z, z :: x → z :: y)

  -- now prove AntiRigid(x) using (a19) in the → direction
  apply (hA19 x w).2
  refine ⟨hEndx, ?_⟩
  intro z hDia_zx
  -- hDia_zx : ◇(z :: x)

  -- from ◇(z :: x) and x ⊑ y, get ◇(z :: y)
  have hDia_zy :
      S5Frame.Dia (F := Sig.F) (fun w' => Sig.Inst z y w') w :=
  by
    rcases hDia_zx with ⟨v, hvR, hvInstX⟩
    refine ⟨v, hvR, ?_⟩
    -- use the Box-inclusion at v to push Inst(z,x) → Inst(z,y)
    exact hBoxIncl v hvR z hvInstX

  -- anti-rigidity of y gives ◇(¬ z :: y)
  have hDiaNot_zy :
      S5Frame.Dia (F := Sig.F) (fun w' => ¬ Sig.Inst z y w') w :=
    hAntiCondY z hDia_zy

  -- from ◇(¬ z :: y) and □(z::x → z::y), we obtain ◇(¬ z :: x)
  rcases hDiaNot_zy with ⟨u, huR, huNotY⟩
  refine ⟨u, huR, ?_⟩
  intro huInstX
  -- use inclusion at u: Inst(z,x) → Inst(z,y), contradict ¬Inst(z,y)
  have huInstY : Sig.Inst z y u := hBoxIncl u huR z huInstX
  exact huNotY huInstY

/--
(t8)

¬∃x,y (SemiRigid(x) ∧ AntiRigid(y) ∧ x ⊑ y)

Natural language:
A semi-rigid type cannot specialize an anti-rigid type.
-/
theorem th_t8
  (hA5  : ax_a5 Sig.toUFOSignature3_1)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ (w : Sig.F.World),
    ¬ ∃ x y : Sig.Thing,
        Sig.SemiRigid x w ∧
        Sig.AntiRigid y w ∧
        Sig.Sub x y w :=
by
  intro w
  intro h
  rcases h with ⟨x, y, hSemi, hAR, hSub⟩

  -- SemiRigid(x) gives EndurantType(x) and ¬AntiRigid(x)
  have hSemiDef := (hA20 x w).1 hSemi
  rcases hSemiDef with ⟨hEndx, _hNotRigid, hNotAntiRigid_x⟩

  -- Downward propagation: AntiRigid(y) and x ⊑ y imply AntiRigid(x)
  have hAnti_x : Sig.AntiRigid x w :=
    antiRigid_downward (Sig := Sig) hA5 hA19 hEndx hAR hSub

  exact hNotAntiRigid_x hAnti_x

/--
(a21)

Endurant(x) → ∃k (Kind(k) ∧ □(x :: k))

Natural language:
Every endurant necessarily instantiates some kind.
-/
def ax_a21 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Endurant x w →
      ∃ k : Sig.Thing,
        Sig.Kind k w ∧
        S5Frame.Box (F := Sig.F)
          (fun w' => Sig.Inst x k w')
          w

/--
(a22)

Kind(k) ∧ x :: k → ¬◇(∃z (Kind(z) ∧ x :: z ∧ z ≠ k))

Natural language:
If x instantiates a kind k, then it is not possible that x instantiates
a different kind.
-/
def ax_a22 : Prop :=
  ∀ (k x : Sig.Thing) (w : Sig.F.World),
    (Sig.Kind k w ∧ Sig.Inst x k w) →
      ¬ S5Frame.Dia (F := Sig.F)
          (fun w' => ∃ z : Sig.Thing,
            Sig.Kind z w' ∧
            Sig.Inst x z w' ∧
            z ≠ k)
          w

/--
(a23)

Sortal(t) ↔
  EndurantType(t) ∧
  ∃k (Kind(k) ∧ □(∀x (x :: t → x :: k)))

Natural language:
A sortal is an endurant type whose instances necessarily
instantiate the same kind.
-/
def ax_a23 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Sortal t w ↔
      (Sig.EndurantType t w ∧
        ∃ k : Sig.Thing,
          Sig.Kind k w ∧
          S5Frame.Box (F := Sig.F)
            (fun w' =>
              ∀ x : Sig.Thing,
                Sig.Inst x t w' →
                Sig.Inst x k w')
            w)

/--
(a24)

NonSortal(t) ↔ EndurantType(t) ∧ ¬Sortal(t)

Natural language:
A non-sortal is an endurant type that is not a sortal.
-/
def ax_a24 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.NonSortal t w ↔
      (Sig.EndurantType t w ∧
       ¬ Sig.Sortal t w)

/--
(a25)

¬∃t (Kind(t) ∧ SubKind(t))

Natural language:
Kinds and subkinds are disjoint.
-/
def ax_a25 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ t : Sig.Thing,
        Sig.Kind t w ∧
        Sig.SubKind t w

/--
(a26)

Kind(t) ∨ SubKind(t) ↔ Rigid(t) ∧ Sortal(t)

Natural language:
Kinds and subkinds together encompass all rigid sortals.
-/
def ax_a26 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    (Sig.Kind t w ∨ Sig.SubKind t w) ↔
      (Sig.Rigid t w ∧ Sig.Sortal t w)

/--
(t9)

Kind(k) → Rigid(k)

Natural language:
Kinds are rigid.
-/
theorem th_t9
  (hA26 : ax_a26 Sig) :
  ∀ (k : Sig.Thing) (w : Sig.F.World),
    Sig.Kind k w →
      Sig.Rigid k w :=
by
  intro k w hKind
  have h := (hA26 k w).1 (Or.inl hKind)
  exact h.1

/--
NOTE:
Kind-stability (explicit semantic assumption), needed for (t10):

If something is a Kind at world w, then it is a Kind at every accessible world v.
-/
def ax_kindStable : Prop :=
  ∀ (k : Sig.Thing) (w v : Sig.F.World),
    Sig.Kind k w → Sig.F.R w v → Sig.Kind k v

/--
(t10)

Kind(x) ∧ Kind(y) ∧ x ≠ y → □(¬∃z (z :: x ∧ z :: y))

Natural language:
Distinct kinds are necessarily disjoint.
-/
theorem th_t10
  (hA22 : ax_a22 Sig)
  (hKS  : ax_kindStable Sig) :
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Kind x w ∧ Sig.Kind y w ∧ x ≠ y →
      S5Frame.Box (F := Sig.F)
        (fun v =>
          ¬ ∃ z : Sig.Thing,
              Sig.Inst z x v ∧
              Sig.Inst z y v)
        w :=
by
  classical
  intro x y w h
  rcases h with ⟨hKx_w, hKy_w, hNe_xy⟩

  intro v hvR
  intro hEx
  rcases hEx with ⟨z, hz_x, hz_y⟩

  -- transport Kind facts from w to v using hKS
  have hKx_v : Sig.Kind x v := hKS x w v hKx_w hvR
  have hKy_v : Sig.Kind y v := hKS y w v hKy_w hvR

  -- apply a22 at world v with k := x and instance z :: x
  have hNoOtherKind :
    ¬ S5Frame.Dia (F := Sig.F)
        (fun v' => ∃ k : Sig.Thing,
          Sig.Kind k v' ∧ Sig.Inst z k v' ∧ k ≠ x)
        v :=
    hA22 x z v ⟨hKx_v, hz_x⟩

  -- build the forbidden possibility at v using k := y (and R v v via refl)
  have hBad :
    S5Frame.Dia (F := Sig.F)
        (fun v' => ∃ k : Sig.Thing,
          Sig.Kind k v' ∧ Sig.Inst z k v' ∧ k ≠ x)
        v :=
  by
    refine ⟨v, Sig.F.refl v, ?_⟩
    refine ⟨y, hKy_v, hz_y, ?_⟩
    exact Ne.symm hNe_xy

  exact hNoOtherKind hBad

/--
(t11)

Kind(x) ∧ Kind(y) ∧ x ≠ y → (¬(x ⊑ y) ∧ ¬(y ⊑ x))

Natural language:
Distinct kinds do not specialize each other.
-/
theorem th_t11
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA5  : ax_a5 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA23 : ax_a23 Sig)
  (hA26 : ax_a26 Sig)
  (hA22 : ax_a22 Sig)
  (hKS  : ax_kindStable Sig) :
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Kind x w ∧ Sig.Kind y w ∧ x ≠ y →
      (¬ Sig.Sub x y w ∧ ¬ Sig.Sub y x w) :=
by
  classical
  intro x y w hKinds
  rcases hKinds with ⟨hKx, hKy, hNe⟩
  constructor

  · -- show ¬(x ⊑ y)
    intro hSub_xy

    -- Use t10 directly
    have hBoxDisj :=
      th_t10 (Sig := Sig) hA22 hKS x y w ⟨hKx, hKy, hNe⟩

    -- unpack specialization definition
    have hSubDef := (hA5 x y w).1 hSub_xy
    rcases hSubDef with ⟨_hTx, _hTy, hBoxIncl⟩

    -- From a26: Kind → Rigid ∧ Sortal
    have hSortal_x : Sig.Sortal x w :=
      (hA26 x w).1 (Or.inl hKx) |>.2

    -- From a23: Sortal → EndurantType
    have hEndType_x : Sig.EndurantType x w :=
      (hA23 x w).1 hSortal_x |>.1

    -- From a15: EndurantType → Type
    have hType_x : Sig.Type_ x w :=
      hA15 x w hEndType_x

    -- From a1: Type → ◇(∃ instance)
    have hDiaEx_x :
        S5Frame.Dia (F := Sig.F)
          (fun w' => ∃ z : Sig.Thing, Sig.Inst z x w')
          w :=
      (hA1 x w).1 hType_x

    rcases hDiaEx_x with ⟨v, hvR, ⟨z, hz_x⟩⟩

    -- inclusion from x ⊑ y
    have hz_y : Sig.Inst z y v :=
      (hBoxIncl v hvR) z hz_x

    -- contradiction with disjointness
    have hNoBoth := hBoxDisj v hvR
    exact hNoBoth ⟨z, hz_x, hz_y⟩

  · -- show ¬(y ⊑ x)
    intro hSub_yx

    have hBoxDisj :=
      th_t10 (Sig := Sig) hA22 hKS y x w ⟨hKy, hKx, Ne.symm hNe⟩

    have hSubDef := (hA5 y x w).1 hSub_yx
    rcases hSubDef with ⟨_hTy, _hTx, hBoxIncl⟩

    have hSortal_y : Sig.Sortal y w :=
      (hA26 y w).1 (Or.inl hKy) |>.2

    have hEndType_y : Sig.EndurantType y w :=
      (hA23 y w).1 hSortal_y |>.1

    have hType_y : Sig.Type_ y w :=
      hA15 y w hEndType_y

    have hDiaEx_y :
        S5Frame.Dia (F := Sig.F)
          (fun w' => ∃ z : Sig.Thing, Sig.Inst z y w')
          w :=
      (hA1 y w).1 hType_y

    rcases hDiaEx_y with ⟨v, hvR, ⟨z, hz_y⟩⟩

    have hz_x : Sig.Inst z x v :=
      (hBoxIncl v hvR) z hz_y

    have hNoBoth := hBoxDisj v hvR
    exact hNoBoth ⟨z, hz_y, hz_x⟩

/--
(t12)

Kind(t) → Sortal(t)

Natural language:
Every kind is a sortal.
-/
theorem th_t12
  (hA26 : ax_a26 Sig) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Kind t w →
      Sig.Sortal t w :=
by
  intro t w hK
  exact (hA26 t w).1 (Or.inl hK) |>.2

/--
(t13)

Sortal(x) → ∃k (Kind(k) ∧ x ⊑ k)

Natural language:
Every sortal specializes some kind.
-/
theorem th_t13
  (hA5  : ax_a5 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA23 : ax_a23 Sig)
  (hA26 : ax_a26 Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Sortal x w →
      ∃ k : Sig.Thing,
        Sig.Kind k w ∧ Sig.Sub x k w :=
by
  intro x w hSortal

  -- unpack a23 for x
  have hDef := (hA23 x w).1 hSortal
  rcases hDef with ⟨hEnd_x, ⟨k, hKind_k, hBoxIncl⟩⟩

  -- need Type(x) and Type(k) to build Sub x k via a5
  have hType_x : Sig.Type_ x w :=
    hA15 x w hEnd_x

  -- k is a kind, hence (by a26) a sortal, hence endurant type, hence a type
  have hSortal_k : Sig.Sortal k w :=
    (hA26 k w).1 (Or.inl hKind_k) |>.2
  have hEnd_k : Sig.EndurantType k w :=
    (hA23 k w).1 hSortal_k |>.1
  have hType_k : Sig.Type_ k w :=
    hA15 k w hEnd_k

  -- package everything into specialization using a5
  refine ⟨k, hKind_k, ?_⟩
  exact (hA5 x k w).2 ⟨hType_x, hType_k, hBoxIncl⟩

/--
(t14)

¬∃x,y,z (Kind(y) ∧ Kind(z) ∧ y ≠ z ∧ x ⊑ y ∧ x ⊑ z)

Natural language:
No type can specialize two distinct kinds.
-/
theorem th_t14
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA5  : ax_a5 Sig.toUFOSignature3_1)
  (hA22 : ax_a22 Sig)
  (hKS  : ax_kindStable Sig) :
  ∀ (w : Sig.F.World),
    ¬ ∃ x y z : Sig.Thing,
        Sig.Kind y w ∧ Sig.Kind z w ∧ y ≠ z ∧
        Sig.Sub x y w ∧ Sig.Sub x z w :=
by
  classical
  intro w
  intro h
  rcases h with ⟨x, y, z, hKy, hKz, hNe_yz, hSub_xy, hSub_xz⟩

  -- use t10
  have hBoxDisj :=
    th_t10 (Sig := Sig) hA22 hKS y z w ⟨hKy, hKz, hNe_yz⟩

  -- unpack specialization
  have hxy := (hA5 x y w).1 hSub_xy
  have hxz := (hA5 x z w).1 hSub_xz
  rcases hxy with ⟨hType_x, _hType_y, hBoxIncl_xy⟩
  rcases hxz with ⟨_hType_x', _hType_z, hBoxIncl_xz⟩

  -- get possible instance of x
  have hDiaEx :=
    (hA1 x w).1 hType_x

  rcases hDiaEx with ⟨v, hvR, ⟨t, ht_x⟩⟩

  -- propagate instantiation
  have ht_y := (hBoxIncl_xy v hvR) t ht_x
  have ht_z := (hBoxIncl_xz v hvR) t ht_x

  -- contradict t10
  have hNoBoth := hBoxDisj v hvR
  exact hNoBoth ⟨t, ht_y, ht_z⟩

/--
(t15)

¬∃x,y (NonSortal(x) ∧ Sortal(y) ∧ x ⊑ y)

Natural language:
A non-sortal cannot specialize a sortal.
-/
theorem th_t15
  (hA5  : ax_a5 Sig.toUFOSignature3_1)
  (hA23 : ax_a23 Sig)
  (hA24 : ax_a24 Sig) :
  ∀ (w : Sig.F.World),
    ¬ ∃ x y : Sig.Thing,
        Sig.NonSortal x w ∧
        Sig.Sortal y w ∧
        Sig.Sub x y w :=
by
  classical
  intro w
  intro h
  rcases h with ⟨x, y, hNonSortal_x, hSortal_y, hSub_xy⟩

  -- from NonSortal(x)
  have hNonDef := (hA24 x w).1 hNonSortal_x
  rcases hNonDef with ⟨hEnd_x, hNotSortal_x⟩

  -- unpack specialization
  have hSubDef := (hA5 x y w).1 hSub_xy
  rcases hSubDef with ⟨_hType_x, _hType_y, hBox_xy⟩

  -- unpack Sortal(y)
  have hSortDef := (hA23 y w).1 hSortal_y
  rcases hSortDef with ⟨_hEnd_y, ⟨k, hKind_k, hBox_yk⟩⟩

  -- compose boxes: x -> y -> k
  have hBox_xk :
      S5Frame.Box (F := Sig.F)
        (fun v =>
          ∀ z : Sig.Thing,
            Sig.Inst z x v →
            Sig.Inst z k v)
        w :=
  by
    intro v hvR
    intro z hz_x
    have hz_y := (hBox_xy v hvR) z hz_x
    exact (hBox_yk v hvR) z hz_y

  -- now rebuild Sortal(x) via a23
  have hSortal_x :
      Sig.Sortal x w :=
    (hA23 x w).2
      ⟨hEnd_x, ⟨k, hKind_k, hBox_xk⟩⟩

  exact hNotSortal_x hSortal_x

/--
NOTE:
Bridge axioms needed for (t16):

(typing of instantiation for endurant types)
If `t` is an EndurantType and `x :: t`, then `x` is an Endurant.

This is an implicit typing assumption in the paper:
instances of endurant types are endurants.
-/
def ax_instEndurant_of_EndurantType : Prop :=
  ∀ (t x : Sig.Thing) (w : Sig.F.World),
    Sig.EndurantType t w →
    Sig.Inst x t w →
    Sig.Endurant x w

/--
NOTE:
Also needed for (t16).
Structural axiom (subtypes of kinds are sortals):

If a specializes a kind k,
then a is a sortal.

This reflects the intended taxonomy:
kinds and their subkinds are rigid sortals.
-/
def ax_sub_of_kind_is_sortal : Prop :=
  ∀ (a k : Sig.Thing) (w : Sig.F.World),
    Sig.Sub a k w →
    Sig.Kind k w →
    Sig.Sortal a w

/--
NOTE:
Also needed for (t16).
Structural axiom (closure of NonSortal under specialization upward):

If a is NonSortal and a ⊑ b,
then b is NonSortal.

This reflects the intended taxonomy:
NonSortal is a proper branch under EndurantType,
and no supertype of a NonSortal can be a Sortal.
-/
def ax_nonSortal_upward : Prop :=
  ∀ (a b : Sig.Thing) (w : Sig.F.World),
    Sig.NonSortal a w →
    Sig.Sub a b w →
    Sig.NonSortal b w

/--
(t16)

(NonSortal(t) ∧ x :: t) →
  (∃ s, Sortal(s) ∧ s ⊑ t ∧ x :: s) ∨
  (∃ n s, NonSortal(n) ∧ Sortal(s) ∧ s ⊑ n ∧ t ⊑ n ∧ x :: s)

Natural language:
Non-sortals do not have direct instances: any instance of a non-sortal
is also an instance of some sortal that either specializes it,
or specializes a common non-sortal supertype.
-/
theorem th_t16
  (hA5   : ax_a5 Sig.toUFOSignature3_1)
  (hA6   : ax_a6 Sig.toUFOSignature3_1)
  (hA21  : ax_a21 Sig)
  (hA23  : ax_a23 Sig)
  (hA24  : ax_a24 Sig)
  (hA26  : ax_a26 Sig)
  (hInstEnd : ax_instEndurant_of_EndurantType (Sig := Sig))
  (hSubKindSortal : ax_sub_of_kind_is_sortal (Sig := Sig))
  (hNonUp   : ax_nonSortal_upward (Sig := Sig)) :
  ∀ (t x : Sig.Thing) (w : Sig.F.World),
    (Sig.NonSortal t w ∧ Sig.Inst x t w) →
      ( (∃ s : Sig.Thing,
            Sig.Sortal s w ∧
            Sig.Sub s t w ∧
            Sig.Inst x s w)
        ∨
        (∃ n s : Sig.Thing,
            Sig.NonSortal n w ∧
            Sig.Sortal s w ∧
            Sig.Sub s n w ∧
            Sig.Sub t n w ∧
            Sig.Inst x s w) )
:= by
  classical
  intro t x w h
  rcases h with ⟨hNon_t, hInst_xt⟩

  -- unfold NonSortal(t)
  have hNonDef := (hA24 t w).1 hNon_t
  rcases hNonDef with ⟨hEnd_t, hNotSortal_t⟩

  -- instance typing: x is an Endurant
  have hEnd_x : Sig.Endurant x w :=
    hInstEnd t x w hEnd_t hInst_xt

  -- from a21: x necessarily instantiates some kind k
  obtain ⟨k, hKind_k, hBox_xk⟩ :=
    hA21 x w hEnd_x

  -- x :: k at w (via reflexivity of R)
  have hInst_xk : Sig.Inst x k w :=
    hBox_xk w (Sig.F.refl w)

  -- k is a sortal (directly from a26)
  have hSortal_k : Sig.Sortal k w :=
    (hA26 k w).1 (Or.inl hKind_k) |>.2

  -- check comparability of t and k
  by_cases hSub_tk : Sig.Sub t k w

  ------------------------------------------------------------------
  -- Case 1: t ⊑ k  → contradiction (would force Sortal(t))
  ------------------------------------------------------------------
  · exfalso
    have hSubDef := (hA5 t k w).1 hSub_tk
    rcases hSubDef with ⟨_, _, hBox_tk⟩
    have hSortal_t : Sig.Sortal t w :=
      (hA23 t w).2 ⟨hEnd_t, ⟨k, hKind_k, hBox_tk⟩⟩
    exact hNotSortal_t hSortal_t

  ------------------------------------------------------------------
  -- Case 2: ¬(t ⊑ k)
  ------------------------------------------------------------------
  · by_cases hSub_kt : Sig.Sub k t w

    --------------------------------------------------------------
    -- Case 2a: k ⊑ t  → pick s := k
    --------------------------------------------------------------
    · exact Or.inl ⟨k, hSortal_k, hSub_kt, hInst_xk⟩

    --------------------------------------------------------------
    -- Case 2b: incomparable t and k  → use a6
    --------------------------------------------------------------
    · have hA6app :=
        hA6 t k x w ⟨hInst_xt, hInst_xk, hSub_tk, hSub_kt⟩
      cases hA6app with
      | inl hSuper =>
          -- common supertype n: t ⊑ n, k ⊑ n, and x :: n
          rcases hSuper with ⟨n, ht_n, hk_n, _hInst_xn⟩
          have hNon_n : Sig.NonSortal n w :=
            hNonUp t n w hNon_t ht_n
          -- choose s := k, since we already have Sortal(k) and x::k and k ⊑ n
          exact Or.inr ⟨n, k, hNon_n, hSortal_k, hk_n, ht_n, hInst_xk⟩

      | inr hSubcase =>
          -- common subtype s: s ⊑ t, s ⊑ k, and x :: s
          rcases hSubcase with ⟨s, hs_t, hs_k, hInst_xs⟩
          have hSortal_s : Sig.Sortal s w :=
            hSubKindSortal s k w hs_k hKind_k
          exact Or.inl ⟨s, hSortal_s, hs_t, hInst_xs⟩

/--
(a27)

¬∃t (Phase(t) ∧ Role(t))

Natural language:
Phases and roles are disjoint.
-/
def ax_a27 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ t : Sig.Thing,
        Sig.Phase t w ∧
        Sig.Role t w

/--
(a28)

Phase(t) ∨ Role(t) ↔ AntiRigid(t) ∧ Sortal(t)

Natural language:
Phases and roles together encompass all anti-rigid sortals.
-/
def ax_a28 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    (Sig.Phase t w ∨ Sig.Role t w) ↔
      (Sig.AntiRigid t w ∧ Sig.Sortal t w)

/--
(a29)

SemiRigidSortal(t) ↔ SemiRigid(t) ∧ Sortal(t)

Natural language:
Semi-rigid sortals are exactly semi-rigid that are sortals.
-/
def ax_a29 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.SemiRigidSortal t w ↔
      (Sig.SemiRigid t w ∧ Sig.Sortal t w)

/--
(a30)

Category(t) ↔ Rigid(t) ∧ NonSortal(t)

Natural language:
Categories are rigid non-sortals.
-/
def ax_a30 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Category t w ↔
      (Sig.Rigid t w ∧ Sig.NonSortal t w)

/--
(a31)

Mixin(t) ↔ SemiRigid(t) ∧ NonSortal(t)

Natural language:
Mixins are semi-rigid non-sortals.
-/
def ax_a31 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    Sig.Mixin t w ↔
      (Sig.SemiRigid t w ∧ Sig.NonSortal t w)

/--
(a32)

¬∃t (PhaseMixin(t) ∧ RoleMixin(t))

Natural language:
Phase-mixins and role-mixins are disjoint.
-/
def ax_a32 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ t : Sig.Thing,
        Sig.PhaseMixin t w ∧
        Sig.RoleMixin t w

/--
(a33)

PhaseMixin(t) ∨ RoleMixin(t) ↔ AntiRigid(t) ∧ NonSortal(t)

Natural language:
Phase-mixins and role-mixins together encompass all anti-rigid non-sortals.
-/
def ax_a33 : Prop :=
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    (Sig.PhaseMixin t w ∨ Sig.RoleMixin t w) ↔
      (Sig.AntiRigid t w ∧ Sig.NonSortal t w)

/--
To prove (t17), we introduce some auxiliary lemmas and prove each of
 the pairwise disjoints of categories one by one.
-/
theorem rigid_sortal_of_kind
  (hA26 : ax_a26 Sig) :
  ∀ t w, Sig.Kind t w →
    Sig.Rigid t w ∧ Sig.Sortal t w :=
by
  intro t w hK
  exact (hA26 t w).1 (Or.inl hK)

theorem rigid_sortal_of_subkind
  (hA26 : ax_a26 Sig) :
  ∀ t w, Sig.SubKind t w →
    Sig.Rigid t w ∧ Sig.Sortal t w :=
by
  intro t w hSK
  exact (hA26 t w).1 (Or.inr hSK)

/--
Pairwise disjointness lemmas:
-/
theorem kind_not_subkind
  (hA25 : ax_a25 Sig) :
  ∀ t w, Sig.Kind t w → ¬ Sig.SubKind t w :=
by
  intro t w hK hSK
  exact (hA25 w) ⟨t, hK, hSK⟩

theorem kind_not_role
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.Kind t w → ¬ Sig.Role t w :=
by
  intro t w hK hRole

  -- Kind → Rigid ∧ Sortal
  have hRS := rigid_sortal_of_kind (Sig := Sig) hA26 t w hK

  -- Role → AntiRigid ∧ Sortal
  have hAR := (hA28 t w).1 (Or.inr hRole)

  -- rigid ∧ antiRigid contradiction via t6
  have hClash :
    (Sig.Rigid t w ∧ Sig.AntiRigid t w) :=
    ⟨hRS.1, hAR.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inl hClash⟩

theorem kind_not_phase
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.Kind t w → ¬ Sig.Phase t w :=
by
  intro t w hK hPhase

  have hRS := rigid_sortal_of_kind (Sig := Sig) hA26 t w hK
  have hAR := (hA28 t w).1 (Or.inl hPhase)

  have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
    ⟨hRS.1, hAR.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inl hClash⟩

theorem kind_not_semirigid_sortal
  (hA26 : ax_a26 Sig)
  (hA29 : ax_a29 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.Kind t w → ¬ Sig.SemiRigidSortal t w :=
by
  intro t w hK hSRS

  have hRS := rigid_sortal_of_kind (Sig := Sig) hA26 t w hK
  have hSemi := (hA29 t w).1 hSRS

  have hClash : Sig.Rigid t w ∧ Sig.SemiRigid t w :=
    ⟨hRS.1, hSemi.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inr (Or.inl hClash)⟩

theorem kind_not_category
  (hA26 : ax_a26 Sig)
  (hA30 : ax_a30 Sig)
  (hA24 : ax_a24 Sig) :
  ∀ t w, Sig.Kind t w → ¬ Sig.Category t w :=
by
  intro t w hK hCat

  have hSortal := (hA26 t w).1 (Or.inl hK) |>.2
  have hCatDef := (hA30 t w).1 hCat
  have hNon := hCatDef.2

  have hNonDef := (hA24 t w).1 hNon
  exact hNonDef.2 hSortal

theorem kind_not_mixin
  (hA26 : ax_a26 Sig)
  (hA31 : ax_a31 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.Kind t w → ¬ Sig.Mixin t w :=
by
  intro t w hK hMix

  have hRS := rigid_sortal_of_kind (Sig := Sig) hA26 t w hK
  have hMixDef := (hA31 t w).1 hMix

  have hClash : Sig.Rigid t w ∧ Sig.SemiRigid t w :=
    ⟨hRS.1, hMixDef.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inr (Or.inl hClash)⟩

theorem kind_not_pm_rm
  (hA26 : ax_a26 Sig)
  (hA33 : ax_a33 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w,
    Sig.Kind t w →
    ¬ (Sig.PhaseMixin t w ∨ Sig.RoleMixin t w) :=
by
  intro t w hK hMix

  have hRS := rigid_sortal_of_kind (Sig := Sig) hA26 t w hK
  have hAR := (hA33 t w).1 hMix

  have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
    ⟨hRS.1, hAR.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inl hClash⟩

theorem subkind_not_kind
  (hA25 : ax_a25 Sig) :
  ∀ t w, Sig.SubKind t w → ¬ Sig.Kind t w :=
by
  intro t w hSK hK
  exact (hA25 w) ⟨t, hK, hSK⟩

theorem subkind_not_role
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.SubKind t w → ¬ Sig.Role t w :=
by
  intro t w hSK hRole

  have hRS := rigid_sortal_of_subkind (Sig := Sig) hA26 t w hSK
  have hAR := (hA28 t w).1 (Or.inr hRole)

  have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
    ⟨hRS.1, hAR.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inl hClash⟩

theorem subkind_not_phase
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.SubKind t w → ¬ Sig.Phase t w :=
by
  intro t w hSK hPhase

  have hRS := rigid_sortal_of_subkind (Sig := Sig) hA26 t w hSK
  have hAR := (hA28 t w).1 (Or.inl hPhase)

  have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
    ⟨hRS.1, hAR.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inl hClash⟩

theorem subkind_not_semirigid_sortal
  (hA26 : ax_a26 Sig)
  (hA29 : ax_a29 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.SubKind t w → ¬ Sig.SemiRigidSortal t w :=
by
  intro t w hSK hSRS

  have hRS := rigid_sortal_of_subkind (Sig := Sig) hA26 t w hSK
  have hSemi := (hA29 t w).1 hSRS

  have hClash : Sig.Rigid t w ∧ Sig.SemiRigid t w :=
    ⟨hRS.1, hSemi.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inr (Or.inl hClash)⟩

theorem subkind_not_category
  (hA26 : ax_a26 Sig)
  (hA30 : ax_a30 Sig)
  (hA24 : ax_a24 Sig) :
  ∀ t w, Sig.SubKind t w → ¬ Sig.Category t w :=
by
  intro t w hSK hCat

  have hSortal := (hA26 t w).1 (Or.inr hSK) |>.2
  have hCatDef := (hA30 t w).1 hCat
  have hNon := hCatDef.2

  have hNonDef := (hA24 t w).1 hNon
  exact hNonDef.2 hSortal

theorem subkind_not_mixin
  (hA26 : ax_a26 Sig)
  (hA31 : ax_a31 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w, Sig.SubKind t w → ¬ Sig.Mixin t w :=
by
  intro t w hSK hMix

  have hRS := rigid_sortal_of_subkind (Sig := Sig) hA26 t w hSK
  have hMixDef := (hA31 t w).1 hMix

  have hClash : Sig.Rigid t w ∧ Sig.SemiRigid t w :=
    ⟨hRS.1, hMixDef.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inr (Or.inl hClash)⟩

theorem subkind_not_pm_rm
  (hA26 : ax_a26 Sig)
  (hA33 : ax_a33 Sig)
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig) :
  ∀ t w,
    Sig.SubKind t w →
    ¬ (Sig.PhaseMixin t w ∨ Sig.RoleMixin t w) :=
by
  intro t w hSK hMix

  have hRS := rigid_sortal_of_subkind (Sig := Sig) hA26 t w hSK
  have hAR := (hA33 t w).1 hMix

  have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
    ⟨hRS.1, hAR.1⟩

  have hNo :=
    th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w

  exact hNo ⟨t, Or.inl hClash⟩

theorem role_not_phase
  (hA27 : ax_a27 Sig) :
  ∀ t w, Sig.Role t w → ¬ Sig.Phase t w :=
by
  intro t w hR hP
  exact (hA27 w) ⟨t, hP, hR⟩

theorem pm_not_rm
  (hA32 : ax_a32 Sig) :
  ∀ t w, Sig.PhaseMixin t w → ¬ Sig.RoleMixin t w :=
by
  intro t w hPM hRM
  exact (hA32 w) ⟨t, hPM, hRM⟩

/--
(t17)

The eight endurant type categories form a strict partition:
(t17) proves that they are pairwise disjoint.
-/
theorem th_t17
  (hA1  : ax_a1 Sig.toUFOSignature3_1)
  (hA15 : ax_a15 Sig.toUFOSignature3_1)
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig)
  (hA24 : ax_a24 Sig)
  (hA25 : ax_a25 Sig)
  (hA27 : ax_a27 Sig)
  (hA32 : ax_a32 Sig)
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA29 : ax_a29 Sig)
  (hA30 : ax_a30 Sig)
  (hA31 : ax_a31 Sig)
  (hA33 : ax_a33 Sig) :
  ∀ t w,

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
      ¬ Sig.RoleMixin t w)
      :=
by
  classical
  intro t w

  refine ⟨
    ?kindBlock,
    ?subkindBlock,
    ?roleBlock,
    ?phaseBlock,
    ?srsBlock,
    ?catBlock,
    ?mixinBlock,
    ?pmBlock
  ⟩
  · intro hKind
    refine ⟨
      kind_not_subkind (Sig := Sig) hA25 t w hKind,
      kind_not_role (Sig := Sig) hA26 hA28 hA1 hA15 hA18 hA19 hA20 t w hKind,
      kind_not_phase (Sig := Sig) hA26 hA28 hA1 hA15 hA18 hA19 hA20 t w hKind,
      kind_not_semirigid_sortal (Sig := Sig) hA26 hA29 hA1 hA15 hA18 hA19 hA20 t w hKind,
      kind_not_category (Sig := Sig) hA26 hA30 hA24 t w hKind,
      kind_not_mixin (Sig := Sig) hA26 hA31 hA1 hA15 hA18 hA19 hA20 t w hKind,
      ?_,
      ?_
    ⟩
    · intro hPM
      exact (kind_not_pm_rm (Sig := Sig)
        hA26 hA33 hA1 hA15 hA18 hA19 hA20 t w hKind)
        (Or.inl hPM)
    · intro hRM
      exact (kind_not_pm_rm (Sig := Sig)
        hA26 hA33 hA1 hA15 hA18 hA19 hA20 t w hKind)
        (Or.inr hRM)
  · intro hSK
    refine ⟨
      subkind_not_kind (Sig := Sig) hA25 t w hSK,
      subkind_not_role (Sig := Sig) hA26 hA28 hA1 hA15 hA18 hA19 hA20 t w hSK,
      subkind_not_phase (Sig := Sig) hA26 hA28 hA1 hA15 hA18 hA19 hA20 t w hSK,
      subkind_not_semirigid_sortal (Sig := Sig) hA26 hA29 hA1 hA15 hA18 hA19 hA20 t w hSK,
      subkind_not_category (Sig := Sig) hA26 hA30 hA24 t w hSK,
      subkind_not_mixin (Sig := Sig) hA26 hA31 hA1 hA15 hA18 hA19 hA20 t w hSK,
      ?_,
      ?_
    ⟩
    · intro hPM
      exact (subkind_not_pm_rm (Sig := Sig)
        hA26 hA33 hA1 hA15 hA18 hA19 hA20 t w hSK)
        (Or.inl hPM)
    · intro hRM
      exact (subkind_not_pm_rm (Sig := Sig)
        hA26 hA33 hA1 hA15 hA18 hA19 hA20 t w hSK)
        (Or.inr hRM)
  · intro hRole
    refine ⟨
      role_not_phase (Sig := Sig) hA27 t w hRole,
      ?_, ?_, ?_, ?_, ?_
    ⟩

    -- not SemiRigidSortal
    · intro hSRS
      have hAR := (hA28 t w).1 (Or.inr hRole)
      have hSemi := (hA29 t w).1 hSRS
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi.1, hAR.1⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩

    -- not Category
    · intro hCat
      have hAR := (hA28 t w).1 (Or.inr hRole)
      have hRigid := (hA30 t w).1 hCat |>.1
      have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
        ⟨hRigid, hAR.1⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inl hClash⟩

    -- not Mixin
    · intro hMix
      have hAR := (hA28 t w).1 (Or.inr hRole)
      have hSemi := (hA31 t w).1 hMix |>.1
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi, hAR.1⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩

    -- not PhaseMixin
    · intro hPM
      have hAR1 := (hA28 t w).1 (Or.inr hRole)
      have hAR2 := (hA33 t w).1 (Or.inl hPM)
      have hSortal := hAR1.2
      have hNon := hAR2.2
      have hNonDef := (hA24 t w).1 hNon
      exact hNonDef.2 hSortal

    -- not RoleMixin
    · intro hRM
      have hAR1 := (hA28 t w).1 (Or.inr hRole)
      have hAR2 := (hA33 t w).1 (Or.inr hRM)
      have hSortal := hAR1.2
      have hNon := hAR2.2
      have hNonDef := (hA24 t w).1 hNon
      exact hNonDef.2 hSortal
  · intro hPhase
    refine ⟨
      ?notSRS,
      ?notCategory,
      ?notMixin,
      ?notPM,
      ?notRM
    ⟩

    -- 1. not SemiRigidSortal
    · intro hSRS
      have hAR := (hA28 t w).1 (Or.inl hPhase)
      have hSemi := (hA29 t w).1 hSRS
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi.1, hAR.1⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩

    -- 2. not Category
    · intro hCat
      have hAR := (hA28 t w).1 (Or.inl hPhase)
      have hRigid := (hA30 t w).1 hCat |>.1
      have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
        ⟨hRigid, hAR.1⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inl hClash⟩

    -- 3. not Mixin
    · intro hMix
      have hAR := (hA28 t w).1 (Or.inl hPhase)
      have hSemi := (hA31 t w).1 hMix |>.1
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi, hAR.1⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩

    -- 4. not PhaseMixin
    · intro hPM
      have hAR1 := (hA28 t w).1 (Or.inl hPhase)
      have hAR2 := (hA33 t w).1 (Or.inl hPM)
      have hSortal := hAR1.2
      have hNon := hAR2.2
      have hNonDef := (hA24 t w).1 hNon
      exact hNonDef.2 hSortal

    -- 5. not RoleMixin
    · intro hRM
      have hAR1 := (hA28 t w).1 (Or.inl hPhase)
      have hAR2 := (hA33 t w).1 (Or.inr hRM)
      have hSortal := hAR1.2
      have hNon := hAR2.2
      have hNonDef := (hA24 t w).1 hNon
      exact hNonDef.2 hSortal
  · intro hSRS
    refine ⟨?_, ?_, ?_, ?_⟩

    -- 1. not Category
    · intro hCat
      have hSemi := (hA29 t w).1 hSRS |>.1
      have hRigid := (hA30 t w).1 hCat |>.1
      have hClash : Sig.Rigid t w ∧ Sig.SemiRigid t w :=
        ⟨hRigid, hSemi⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inl hClash)⟩

    -- 2. not Mixin
    · intro hMix
      have hSortal := (hA29 t w).1 hSRS |>.2
      have hNon := (hA31 t w).1 hMix |>.2
      have hNonDef := (hA24 t w).1 hNon
      exact hNonDef.2 hSortal

    -- 3. not PhaseMixin
    · intro hPM
      have hSemi := (hA29 t w).1 hSRS |>.1
      have hAR := (hA33 t w).1 (Or.inl hPM) |>.1
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi, hAR⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩

    -- 4. not RoleMixin
    · intro hRM
      have hSemi := (hA29 t w).1 hSRS |>.1
      have hAR := (hA33 t w).1 (Or.inr hRM) |>.1
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi, hAR⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩
  · intro hCat
    refine ⟨?_, ?_, ?_⟩

    -- not Mixin
    · intro hMix
      have hRigid := (hA30 t w).1 hCat |>.1
      have hSemi := (hA31 t w).1 hMix |>.1
      have hClash : Sig.Rigid t w ∧ Sig.SemiRigid t w :=
        ⟨hRigid, hSemi⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inl hClash)⟩

    -- not PhaseMixin
    · intro hPM
      have hRigid := (hA30 t w).1 hCat |>.1
      have hAR := (hA33 t w).1 (Or.inl hPM) |>.1
      have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
        ⟨hRigid, hAR⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inl hClash⟩

    -- not RoleMixin
    · intro hRM
      have hRigid := (hA30 t w).1 hCat |>.1
      have hAR := (hA33 t w).1 (Or.inr hRM) |>.1
      have hClash : Sig.Rigid t w ∧ Sig.AntiRigid t w :=
        ⟨hRigid, hAR⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inl hClash⟩
  · intro hMix
    refine ⟨?_, ?_⟩

    -- not PhaseMixin
    · intro hPM
      have hSemi := (hA31 t w).1 hMix |>.1
      have hAR := (hA33 t w).1 (Or.inl hPM) |>.1
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi, hAR⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩

    -- not RoleMixin
    · intro hRM
      have hSemi := (hA31 t w).1 hMix |>.1
      have hAR := (hA33 t w).1 (Or.inr hRM) |>.1
      have hClash : Sig.SemiRigid t w ∧ Sig.AntiRigid t w :=
        ⟨hSemi, hAR⟩
      have hNo :=
        th_t6 (Sig := Sig) hA1 hA15 hA18 hA19 hA20 w
      exact hNo ⟨t, Or.inr (Or.inr hClash)⟩
  · intro hPM
    exact pm_not_rm (Sig := Sig) hA32 t w hPM

/--
(t18)

The eight endurant type categories form a strict partition:
(t18) proves exhaustiveness. Let's prove the two directions of the biconditional:
-/

theorem leaf_implies_endurantType
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig)
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA29 : ax_a29 Sig)
  (hA30 : ax_a30 Sig)
  (hA31 : ax_a31 Sig)
  (hA33 : ax_a33 Sig) :
  ∀ t w,
    (Sig.Kind t w ∨
     Sig.SubKind t w ∨
     Sig.Role t w ∨
     Sig.Phase t w ∨
     Sig.SemiRigidSortal t w ∨
     Sig.Category t w ∨
     Sig.Mixin t w ∨
     Sig.PhaseMixin t w ∨
     Sig.RoleMixin t w)
    →
    Sig.EndurantType t w :=
by
  classical
  intro t w h
  cases h with
  | inl hK =>
      exact ((hA18 t w).1 ((hA26 t w).1 (Or.inl hK)).1).1
  | inr hRest =>
    cases hRest with
    | inl hSK =>
        exact ((hA18 t w).1 ((hA26 t w).1 (Or.inr hSK)).1).1
    | inr hRest =>
      cases hRest with
      | inl hRole =>
          exact ((hA19 t w).1 ((hA28 t w).1 (Or.inr hRole)).1).1
      | inr hRest =>
        cases hRest with
        | inl hPhase =>
            exact ((hA19 t w).1 ((hA28 t w).1 (Or.inl hPhase)).1).1
        | inr hRest =>
          cases hRest with
          | inl hSRS =>
              exact ((hA20 t w).1 ((hA29 t w).1 hSRS).1).1
          | inr hRest =>
            cases hRest with
            | inl hCat =>
                exact ((hA18 t w).1 ((hA30 t w).1 hCat).1).1
            | inr hRest =>
              cases hRest with
              | inl hMix =>
                  exact ((hA20 t w).1 ((hA31 t w).1 hMix).1).1
              | inr hRest =>
                cases hRest with
                | inl hPM =>
                    exact ((hA19 t w).1 ((hA33 t w).1 (Or.inl hPM)).1).1
                | inr hRM =>
                    exact ((hA19 t w).1 ((hA33 t w).1 (Or.inr hRM)).1).1

theorem endurant_Type_implies_leaf
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig)
  (hA24 : ax_a24 Sig)
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA29 : ax_a29 Sig)
  (hA30 : ax_a30 Sig)
  (hA31 : ax_a31 Sig)
  (hA33 : ax_a33 Sig) :
  ∀ t w,
    Sig.EndurantType t w →
      (Sig.Kind t w ∨
       Sig.SubKind t w ∨
       Sig.Role t w ∨
       Sig.Phase t w ∨
       Sig.SemiRigidSortal t w ∨
       Sig.Category t w ∨
       Sig.Mixin t w ∨
       Sig.PhaseMixin t w ∨
       Sig.RoleMixin t w) :=
by
  classical
  intro t w hEnd

  have hRig :=
    (th_t5 (Sig := Sig) hA18 hA19 hA20 t w).1 hEnd

  rcases hRig with hRigid | hRest
  · -- Rigid
    by_cases hSortal : Sig.Sortal t w
    · -- Rigid ∧ Sortal → Kind ∨ SubKind
      have h := (hA26 t w).2 ⟨hRigid, hSortal⟩
      cases h with
      | inl hK =>
          -- Kind
          exact Or.inl hK
      | inr hSK =>
          -- SubKind
          exact Or.inr (Or.inl hSK)
    · -- Rigid ∧ NonSortal → Category
      have hNon : Sig.NonSortal t w :=
        (hA24 t w).2 ⟨hEnd, hSortal⟩
      have hCat : Sig.Category t w :=
        (hA30 t w).2 ⟨hRigid, hNon⟩
      -- inject Category (past Kind, SubKind, Role, Phase, SRS)
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hCat)))))
  · -- AntiRigid ∨ SemiRigid
    rcases hRest with hAnti | hSemi
    · -- AntiRigid
      by_cases hSortal : Sig.Sortal t w
      · -- AntiRigid ∧ Sortal → Phase ∨ Role  (note order in goal: Role before Phase)
        have hPR : Sig.Phase t w ∨ Sig.Role t w :=
          (hA28 t w).2 ⟨hAnti, hSortal⟩
        cases hPR with
        | inl hP =>
            -- Phase: past Kind, SubKind, Role
            exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
        | inr hR =>
            -- Role: past Kind, SubKind
            exact Or.inr (Or.inr (Or.inl hR))
      · -- AntiRigid ∧ NonSortal → PhaseMixin ∨ RoleMixin
        have hNon : Sig.NonSortal t w :=
          (hA24 t w).2 ⟨hEnd, hSortal⟩
        have hPMRM : Sig.PhaseMixin t w ∨ Sig.RoleMixin t w :=
          (hA33 t w).2 ⟨hAnti, hNon⟩
        cases hPMRM with
        | inl hPM =>
            -- PhaseMixin: past Kind, SubKind, Role, Phase, SRS, Category, Mixin
            exact
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPM)))))))
        | inr hRM =>
            -- RoleMixin: past Kind, SubKind, Role, Phase, SRS, Category, Mixin, PhaseMixin
            exact
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hRM)))))))
    · -- SemiRigid
      by_cases hSortal : Sig.Sortal t w
      · -- SemiRigid ∧ Sortal → SemiRigidSortal
        have hSRS : Sig.SemiRigidSortal t w :=
          (hA29 t w).2 ⟨hSemi, hSortal⟩
        -- inject SRS: past Kind, SubKind, Role, Phase
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSRS))))
      · -- SemiRigid ∧ NonSortal → Mixin
        have hNon : Sig.NonSortal t w :=
          (hA24 t w).2 ⟨hEnd, hSortal⟩
        have hMix : Sig.Mixin t w :=
          (hA31 t w).2 ⟨hSemi, hNon⟩
        -- inject Mixin: past Kind, SubKind, Role, Phase, SRS, Category
        exact
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMix))))))

/--
Now the biconditional itself:
-/
theorem th_t18
  (hA18 : ax_a18 Sig)
  (hA19 : ax_a19 Sig)
  (hA20 : ax_a20 Sig)
  (hA24 : ax_a24 Sig)
  (hA26 : ax_a26 Sig)
  (hA28 : ax_a28 Sig)
  (hA29 : ax_a29 Sig)
  (hA30 : ax_a30 Sig)
  (hA31 : ax_a31 Sig)
  (hA33 : ax_a33 Sig) :
  ∀ t w,
    Sig.EndurantType t w ↔
      (Sig.Kind t w ∨
       Sig.SubKind t w ∨
       Sig.Role t w ∨
       Sig.Phase t w ∨
       Sig.SemiRigidSortal t w ∨
       Sig.Category t w ∨
       Sig.Mixin t w ∨
       Sig.PhaseMixin t w ∨
       Sig.RoleMixin t w) :=
by
  intro t w
  constructor
  · exact endurant_Type_implies_leaf (Sig := Sig)
      hA18 hA19 hA20
      hA24 hA26 hA28 hA29 hA30 hA31 hA33
      t w
  · exact leaf_implies_endurantType (Sig := Sig)
      hA18 hA19 hA20
      hA26 hA28 hA29 hA30 hA31 hA33
      t w

/--
A UFO model for Section 3.2 extends a Section 3.1 model
with axioms (a18)–(a33) and structural assumptions used in (t16).
-/
structure UFOModel3_2
  extends UFOModel3_1, UFOSignature3_2 where

  -- Section 3.2 axioms
  ax18 : ax_a18 toUFOSignature3_2
  ax19 : ax_a19 toUFOSignature3_2
  ax20 : ax_a20 toUFOSignature3_2
  ax21 : ax_a21 toUFOSignature3_2
  ax22 : ax_a22 toUFOSignature3_2
  ax23 : ax_a23 toUFOSignature3_2
  ax24 : ax_a24 toUFOSignature3_2
  ax25 : ax_a25 toUFOSignature3_2
  ax26 : ax_a26 toUFOSignature3_2
  ax27 : ax_a27 toUFOSignature3_2
  ax28 : ax_a28 toUFOSignature3_2
  ax29 : ax_a29 toUFOSignature3_2
  ax30 : ax_a30 toUFOSignature3_2
  ax31 : ax_a31 toUFOSignature3_2
  ax32 : ax_a32 toUFOSignature3_2
  ax33 : ax_a33 toUFOSignature3_2

  -- Structural axioms for t16
  ax_instEndurant :
    ax_instEndurant_of_EndurantType (Sig := toUFOSignature3_2)

  ax_sub_kind_sortal :
    ax_sub_of_kind_is_sortal (Sig := toUFOSignature3_2)

  ax_nonSortal_up :
    ax_nonSortal_upward (Sig := toUFOSignature3_2)

  ax_kindStable :
    ax_kindStable toUFOSignature3_2
