import LeanUfo.UFO.DSL.Checker.Basic
import LeanUfo.UFO.DSL.Complexity.Closure

/-!
# Boolean checks for reflective finite-model certification

These explicit Boolean finite-model checks mirror the corresponding UFO axioms
over the compiled finite tables and derived finite predicates. Generated DSL
certificates use these checkers through reusable soundness theorems.

Most axiom families use the same four-part pattern:

1. a `...Costed` definition computes the result and counts its own operations;
2. the production definition projects that computation's `value` field;
3. a value theorem relates the counted definition to a readable Boolean form;
4. a bound theorem derives a cost from the loops and lookups actually used.

This is a cost-aware semantics in the style of Niu et al., *Cost-Aware Type
Theory* (POPL 2022), and Haslbeck, *Hoare Logics for Time Bounds* (2018). The
important idea is simple: cost is recorded while the program runs, rather than
assigned afterwards by an unrelated upper-bound function. Consequently, the
complexity theorem concerns the checker that production certification executes.

Boolean conjunction and implication preserve Lean's left-to-right
**short-circuit** order: evaluation stops when the result is already known. For
example, a false left side decides a conjunction, so its right side is neither
evaluated nor charged.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

def impliesB (p q : Bool) : Bool :=
  !p || q

def iffB (p q : Bool) : Bool :=
  (p && q) || (!p && !q)

/-!
The two helpers below are the counted executable cores for the common unary
table implications in the UFO registry.  They make table accesses and Lean's
left-to-right short circuit explicit.  Following Niu et al. (POPL 2022) and
Haslbeck (2018), the cost is composed at the operation that computes the value;
it is not attached afterwards as an envelope.
-/

def checkUnaryTableImplicationCosted (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (left x w) 1) fun _ =>
        Complexity.Costed.tick (right x w) 1

def checkUnaryTableDisjointCosted (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (left x w) 1) fun _ =>
        (Complexity.Costed.tick (right x w) 1).not

theorem checkUnaryTableImplicationCosted_value (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableImplicationCosted M left right).value =
      allThings M (fun x => allWorlds M (fun w => impliesB (left x w) (right x w))) := by
  unfold checkUnaryTableImplicationCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem checkUnaryTableDisjointCosted_value (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableDisjointCosted M left right).value =
      allThings M (fun x => allWorlds M (fun w => impliesB (left x w) (!(right x w)))) := by
  unfold checkUnaryTableDisjointCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem checkUnaryTableImplicationCosted_cost_le (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableImplicationCosted M left right).cost ≤
      M.thingCount * (M.worldCount * 6 + 2) := by
  unfold checkUnaryTableImplicationCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 6)
  intro x
  apply allWorldsEvalCosted_cost_le M _ 4
  intro w
  cases h : left x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

theorem checkUnaryTableDisjointCosted_cost_le (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableDisjointCosted M left right).cost ≤
      M.thingCount * (M.worldCount * 7 + 2) := by
  unfold checkUnaryTableDisjointCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 7)
  intro x
  apply allWorldsEvalCosted_cost_le M _ 5
  intro w
  cases h : left x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

/--
Operational evaluation of the derived `Type` predicate.  The apparently unused
current-world argument is retained because it is part of the semantic checker
interface; the executable definition scans every explicit world and thing and
charges each `inst` table access.  Keeping this as the production core follows
the verified-interpreter discipline illustrated by RadixExperiment, while the
cost composition follows Niu et al.; these are separate methodological roles.
-/
def typeBCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (_w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyWorldsEvalCosted M fun v =>
    anyThingsEvalCosted M fun y =>
      Complexity.Costed.tick (M.inst y x v) 1

def typeB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (typeBCosted M x w).value

@[simp] theorem typeBCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : (typeBCosted M x w).value = typeB M x w := rfl

theorem typeB_eq_legacy (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    typeB M x w = anyWorlds M (fun v => anyThings M (fun y => M.inst y x v)) := by
  unfold typeB typeBCosted
  rw [anyWorldsEvalCosted_value]
  congr 1

theorem typeBCosted_cost_le (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (typeBCosted M x w).cost ≤
      M.worldCount * (M.thingCount * 3 + 2) := by
  unfold typeBCosted
  apply anyWorldsEvalCosted_cost_le M _ (M.thingCount * 3)
  intro v
  apply anyThingsEvalCosted_cost_le M _ 1
  intro y
  simp

/-- Counted complement of `typeB`; the negation itself is charged. -/
def individualBCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  (typeBCosted M x w).not

def individualB (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Bool :=
  (individualBCosted M x w).value

@[simp] theorem individualBCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (individualBCosted M x w).value = individualB M x w := rfl

theorem individualB_eq_legacy (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    individualB M x w =
      !(anyWorlds M (fun v => anyThings M (fun y => M.inst y x v))) := by
  simp [individualB, individualBCosted, typeB_eq_legacy]

theorem individualBCosted_cost_le (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (individualBCosted M x w).cost ≤
      M.worldCount * (M.thingCount * 3 + 2) + 1 := by
  unfold individualBCosted
  simp only [Complexity.Costed.not_cost]
  exact Nat.add_le_add_right (typeBCosted_cost_le M x w) 1

def instSubsumptionCosted
    (M : FiniteModel4) (x y : Fin M.thingCount) : Complexity.Costed Bool :=
  allWorldsEvalCosted M fun w =>
    allThingsEvalCosted M fun z =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (M.inst z x w) 1) fun _ =>
        Complexity.Costed.tick (M.inst z y w) 1

theorem instSubsumptionCosted_value_eq_decide
    (M : FiniteModel4) (x y : Fin M.thingCount) :
    (instSubsumptionCosted M x y).value =
      decide (∀ w : Fin M.worldCount, ∀ z : Fin M.thingCount,
        M.inst z x w = true → M.inst z y w = true) := by
  unfold instSubsumptionCosted
  rw [allWorldsEvalCosted_value]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, allWorlds_eq_true_iff]
  simp only [allThingsEvalCosted_value]
  simp_rw [allThings_eq_true_iff]
  simp [Complexity.Costed.implies_value]
  grind

theorem instSubsumptionCosted_cost_le
    (M : FiniteModel4) (x y : Fin M.thingCount) :
    (instSubsumptionCosted M x y).cost ≤
      M.worldCount * (M.thingCount * 6 + 2) := by
  unfold instSubsumptionCosted
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * 6)
  intro w
  apply allThingsEvalCosted_cost_le M _ 4
  intro z
  cases h : M.inst z x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def subDefBCosted
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen (typeBCosted M x w) fun _ =>
    Complexity.Costed.andThen (typeBCosted M y w) fun _ =>
      instSubsumptionCosted M x y

def subDefB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (subDefBCosted M x y w).value

theorem subDefB_eq_legacy
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    subDefB M x y w =
      (typeB M x w &&
        (typeB M y w && decide (∀ w' : Fin M.worldCount, ∀ z : Fin M.thingCount,
          M.inst z x w' = true → M.inst z y w' = true))) := by
  unfold subDefB subDefBCosted
  cases hx : (typeBCosted M x w).value
  all_goals cases hy : (typeBCosted M y w).value
  all_goals simp only [Complexity.Costed.andThen, hx, hy, typeB,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and,
    Bool.true_and]
  exact instSubsumptionCosted_value_eq_decide M x y

theorem subDefBCosted_cost_le
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (subDefBCosted M x y w).cost ≤
      2 * (M.worldCount * (M.thingCount * 3 + 2)) +
        M.worldCount * (M.thingCount * 6 + 2) + 2 := by
  let q := M.worldCount * (M.thingCount * 3 + 2)
  let s := M.worldCount * (M.thingCount * 6 + 2)
  have hx := typeBCosted_cost_le M x w
  have hy := typeBCosted_cost_le M y w
  have hs := instSubsumptionCosted_cost_le M x y
  cases htx : typeB M x w
  all_goals cases hty : typeB M y w
  all_goals simp [subDefBCosted, Complexity.Costed.andThen, htx, hty]
  all_goals omega

def boxExImpB
    (M : FiniteModel4) (x y : Fin M.thingCount) (_w : Fin M.worldCount) : Bool :=
  decide (∀ w' : Fin M.worldCount, M.ex x w' = true → M.ex y w' = true)

def externallyDependentB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    ((∀ w' : Fin M.worldCount, M.ex x w' = true → M.ex y w' = true) ∧
      ∀ z : Fin M.thingCount,
        M.inheresIn x z w = true →
          ((∃ w' : Fin M.worldCount, M.ex y w' = true ∧ M.ex z w' = false) ∧
           ∃ w' : Fin M.worldCount, M.ex z w' = true ∧ M.ex y w' = false))

def externallyDependentModeB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (M.mode x w = true ∧
      ∃ y : Fin M.thingCount,
        (∀ w' : Fin M.worldCount, M.ex x w' = true → M.ex y w' = true) ∧
          ∀ z : Fin M.thingCount,
            M.inheresIn x z w = true →
              ((∃ w' : Fin M.worldCount, M.ex y w' = true ∧ M.ex z w' = false) ∧
               ∃ w' : Fin M.worldCount, M.ex z w' = true ∧ M.ex y w' = false))

def existsUniqueFoundedByB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ y : Fin M.thingCount,
      M.foundedBy x y w = true ∧
        ∀ z : Fin M.thingCount, M.foundedBy x z w = true → z = y)

def sameFoundationB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  anyThings M fun u => M.foundedBy x u w && M.foundedBy y u w

def existsUniqueInstInheresB
    (M : FiniteModel4) (z t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ y : Fin M.thingCount,
      M.inst y t w = true ∧ M.inheresIn z y w = true ∧
        ∀ y' : Fin M.thingCount,
          M.inst y' t w = true ∧ M.inheresIn z y' w = true → y' = y)

/-!
`ax68` is about `UltimateBearerOf`, whose definition uses the inductive
transitive closure `MomentOf`. The terminal-direct predicates cover the
one-step bearer case, and the reachability predicates below implement the
bounded finite closure used by the checker-backed `ax68` certificate.
-/

def terminalDirectBearerB
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.inheresIn m b w && !(M.moment b w) &&
    (allThings M fun z => !(M.inheresIn b z w))

def existsUniqueTerminalDirectBearerB
    (M : FiniteModel4) (m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ b : Fin M.thingCount,
      terminalDirectBearerB M m b w = true ∧
        ∀ z : Fin M.thingCount, M.inheresIn m z w = true → z = b)

def reachableInheresInFuel
    (M : FiniteModel4) : Nat → Fin M.thingCount → Fin M.thingCount → Fin M.worldCount → Bool
  | 0, _m, _b, _w => false
  | fuel + 1, m, b, w =>
      M.inheresIn m b w ||
        (anyThings M fun y => M.inheresIn m y w && reachableInheresInFuel M fuel y b w)

def reachableInheresInVia
    (M : FiniteModel4) (pivots : List (Fin M.thingCount))
    (m b : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  match pivots with
  | [] => decide (m = b) || M.inheresIn m b w
  | List.cons pivot pivots =>
      reachableInheresInVia M pivots m b w ||
        (reachableInheresInVia M pivots m pivot w &&
          reachableInheresInVia M pivots pivot b w)

def reachableInheresInB
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  reachableInheresInVia M (List.finRange M.thingCount) m b w

/-- The generic closure specification is exactly the legacy checker recurrence. -/
theorem reachableInheresInVia_eq_reachableVia
    (M : FiniteModel4) (pivots : List (Fin M.thingCount))
    (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    reachableInheresInVia M pivots m b w =
      Complexity.reachableVia (fun x y => M.inheresIn x y w) pivots m b := by
  induction pivots generalizing m b with
  | nil => rfl
  | cons pivot pivots ih =>
      simp [reachableInheresInVia, Complexity.reachableVia, ih]

/-- Build and charge the verified Warshall matrix once for every model world. -/
def inherenceMatricesCosted (M : FiniteModel4) :
    Complexity.Costed
      (Vector (Complexity.BoolMatrix M.thingCount) M.worldCount) :=
  ⟨Vector.ofFn fun w =>
      Complexity.warshallMatrix M.thingCount (fun x y => M.inheresIn x y w),
    M.worldCount * (7 * M.thingCount ^ 3 + 5 * M.thingCount ^ 2)⟩

def inherenceMatrices (M : FiniteModel4) :
    Vector (Complexity.BoolMatrix M.thingCount) M.worldCount :=
  (inherenceMatricesCosted M).value

@[simp] theorem inherenceMatricesCosted_value (M : FiniteModel4) :
    (inherenceMatricesCosted M).value = inherenceMatrices M := rfl

@[simp] theorem inherenceMatricesCosted_cost (M : FiniteModel4) :
    (inherenceMatricesCosted M).cost =
      M.worldCount * (7 * M.thingCount ^ 3 + 5 * M.thingCount ^ 2) := rfl

/-- Constant-time reachability lookup after per-world closure construction. -/
def reachableInheresInWarshallB
    (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount)
    (m b : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  Complexity.BoolMatrix.get closures[w.val] m b

theorem reachableInheresInWarshallB_eq
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    reachableInheresInWarshallB M (inherenceMatrices M) m b w =
      reachableInheresInB M m b w := by
  rw [reachableInheresInB, reachableInheresInWarshallB, inherenceMatrices]
  simp only [inherenceMatricesCosted, Vector.getElem_ofFn]
  rw [Complexity.warshallMatrix_get]
  exact (reachableInheresInVia_eq_reachableVia
    M (List.finRange M.thingCount) m b w).symm

def ultimateBearerOfWarshallB
    (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  !(M.moment b w) && reachableInheresInWarshallB M closures m b w

def ultimateBearerOfWarshallCosted
    (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.not (Complexity.Costed.tick (M.moment b w) 1)) fun _ =>
    Complexity.Costed.tick (reachableInheresInWarshallB M closures m b w) 1

theorem ultimateBearerOfWarshallCosted_value (M : FiniteModel4) (closures)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ultimateBearerOfWarshallCosted M closures b m w).value =
      ultimateBearerOfWarshallB M closures b m w := by
  simp [ultimateBearerOfWarshallCosted, ultimateBearerOfWarshallB,
    Complexity.Costed.andThen_value]

theorem ultimateBearerOfWarshallCosted_cost_le (M : FiniteModel4) (closures)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ultimateBearerOfWarshallCosted M closures b m w).cost ≤ 4 := by
  cases h : M.moment b w <;>
    simp [ultimateBearerOfWarshallCosted, Complexity.Costed.andThen, h,
      Complexity.Costed.not]

def ultimateBearerUniqueForCosted
    (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun b' =>
    Complexity.Costed.implies
      (ultimateBearerOfWarshallCosted M closures b' m w) fun _ =>
      Complexity.Costed.tick (decide (b' = b)) 1

theorem ultimateBearerUniqueForCosted_value (M : FiniteModel4) (closures)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ultimateBearerUniqueForCosted M closures b m w).value =
      allThings M (fun b' => impliesB
        (ultimateBearerOfWarshallB M closures b' m w) (decide (b' = b))) := by
  unfold ultimateBearerUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ultimateBearerOfWarshallCosted_value,
    impliesB]

theorem ultimateBearerUniqueForCosted_cost_le (M : FiniteModel4) (closures)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ultimateBearerUniqueForCosted M closures b m w).cost ≤ M.thingCount * 9 := by
  unfold ultimateBearerUniqueForCosted
  apply allThingsEvalCosted_cost_le M _ 7
  intro b'
  have hb := ultimateBearerOfWarshallCosted_cost_le M closures b' m w
  cases h : (ultimateBearerOfWarshallCosted M closures b' m w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def ultimateBearerWitnessCosted
    (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (ultimateBearerOfWarshallCosted M closures b m w) fun _ =>
    ultimateBearerUniqueForCosted M closures b m w

theorem ultimateBearerWitnessCosted_value (M : FiniteModel4) (closures)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ultimateBearerWitnessCosted M closures b m w).value =
      (ultimateBearerOfWarshallB M closures b m w &&
        allThings M (fun b' => impliesB
          (ultimateBearerOfWarshallB M closures b' m w) (decide (b' = b)))) := by
  simp [ultimateBearerWitnessCosted, Complexity.Costed.andThen_value,
    ultimateBearerOfWarshallCosted_value, ultimateBearerUniqueForCosted_value]

theorem ultimateBearerWitnessCosted_cost_le (M : FiniteModel4) (closures)
    (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ultimateBearerWitnessCosted M closures b m w).cost ≤ M.thingCount * 9 + 5 := by
  have hb := ultimateBearerOfWarshallCosted_cost_le M closures b m w
  have hu := ultimateBearerUniqueForCosted_cost_le M closures b m w
  cases h : (ultimateBearerOfWarshallCosted M closures b m w).value <;>
    simp [ultimateBearerWitnessCosted, Complexity.Costed.andThen, h] <;> omega

def existsUniqueUltimateBearerWarshallCosted
    (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount)
    (m : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun b => ultimateBearerWitnessCosted M closures b m w

def existsUniqueUltimateBearerWarshallB
    (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount)
    (m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (existsUniqueUltimateBearerWarshallCosted M closures m w).value

theorem existsUniqueUltimateBearerWarshallB_eq_legacy (M : FiniteModel4) (closures)
    (m : Fin M.thingCount) (w : Fin M.worldCount) :
    existsUniqueUltimateBearerWarshallB M closures m w = decide
      (∃ b : Fin M.thingCount,
        ultimateBearerOfWarshallB M closures b m w = true ∧
          ∀ b' : Fin M.thingCount,
            ultimateBearerOfWarshallB M closures b' m w = true → b' = b) := by
  apply Bool.eq_iff_iff.mpr
  unfold existsUniqueUltimateBearerWarshallB existsUniqueUltimateBearerWarshallCosted
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [ultimateBearerWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

def ultimateBearerUniquenessBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 9 + 7)

theorem existsUniqueUltimateBearerWarshallCosted_cost_le (M : FiniteModel4) (closures)
    (m : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueUltimateBearerWarshallCosted M closures m w).cost ≤
      ultimateBearerUniquenessBound M := by
  unfold existsUniqueUltimateBearerWarshallCosted ultimateBearerUniquenessBound
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 9 + 5)
  intro b
  exact ultimateBearerWitnessCosted_cost_le M closures b m w

def ultimateBearerOfB
    (M : FiniteModel4) (b m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  !(M.moment b w) && reachableInheresInB M m b w

def existsUniqueUltimateBearerB
    (M : FiniteModel4) (m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ b : Fin M.thingCount,
      ultimateBearerOfB M b m w = true ∧
        ∀ b' : Fin M.thingCount, ultimateBearerOfB M b' m w = true → b' = b)

def checkAx68Closure
    (M : FiniteModel4) : Bool :=
  allThings M fun m =>
    allWorlds M fun w =>
      impliesB (M.moment m w) (existsUniqueUltimateBearerB M m w)

theorem ultimateBearerOfWarshallB_eq
    (M : FiniteModel4) (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    ultimateBearerOfWarshallB M (inherenceMatrices M) b m w =
      ultimateBearerOfB M b m w := by
  unfold ultimateBearerOfWarshallB ultimateBearerOfB
  rw [reachableInheresInWarshallB_eq]

theorem existsUniqueUltimateBearerWarshallB_eq
    (M : FiniteModel4) (m : Fin M.thingCount) (w : Fin M.worldCount) :
    existsUniqueUltimateBearerWarshallB M (inherenceMatrices M) m w =
      existsUniqueUltimateBearerB M m w := by
  rw [existsUniqueUltimateBearerWarshallB_eq_legacy]
  unfold existsUniqueUltimateBearerB
  simp only [ultimateBearerOfWarshallB_eq]

/-- Polynomial axiom-68 checker: construct each world matrix once, then lookup. -/
def checkAx68Warshall (M : FiniteModel4) : Bool :=
  let closures := inherenceMatrices M
  allThings M fun m =>
    allWorlds M fun w =>
      impliesB (M.moment m w)
        (existsUniqueUltimateBearerWarshallB M closures m w)

/-- The cubic checker is value-equivalent to the original recursive specification. -/
theorem checkAx68Warshall_eq (M : FiniteModel4) :
    checkAx68Warshall M = checkAx68Closure M := by
  unfold checkAx68Warshall checkAx68Closure
  simp only [existsUniqueUltimateBearerWarshallB_eq]

def checkAx1Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (typeBCosted M x w) fun _ => typeBCosted M x w

def checkAx1 (M : FiniteModel4) : Bool :=
  (checkAx1Costed M).value

theorem checkAx1_eq_legacy (M : FiniteModel4) :
    checkAx1 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (typeB M x w)
        (anyWorlds M (fun v => anyThings M (fun y => M.inst y x v))))) := by
  unfold checkAx1 checkAx1Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp only [Complexity.Costed.iff_value, typeBCosted_value]
  simp [typeB_eq_legacy, iffB]

/--
The two syntactic sides of axiom 1 are evaluated independently.  Although
their values coincide, the operational theorem charges both
scans instead of simplifying the checker to `true`.
-/
theorem checkAx1Costed_cost_le (M : FiniteModel4) :
    (checkAx1Costed M).cost ≤ M.thingCount *
      (M.worldCount * (2 * (M.worldCount * (M.thingCount * 3 + 2)) + 4) + 2) := by
  unfold checkAx1Costed
  let q := M.worldCount * (M.thingCount * 3 + 2)
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (2 * q + 4))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (2 * q + 2)
  intro w
  have ht := typeBCosted_cost_le M x w
  cases h : typeB M x w
  all_goals simp [Complexity.Costed.iff, h]
  all_goals omega

def noInstancesEveryWorldCosted (M : FiniteModel4) (x : Fin M.thingCount) :
    Complexity.Costed Bool :=
  allWorldsEvalCosted M fun v =>
    (anyThingsEvalCosted M fun y =>
      Complexity.Costed.tick (M.inst y x v) 1).not

theorem noInstancesEveryWorldCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) :
    (noInstancesEveryWorldCosted M x).value =
      allWorlds M (fun v => !(anyThings M (fun y => M.inst y x v))) := by
  unfold noInstancesEveryWorldCosted
  rw [allWorldsEvalCosted_value]
  congr 1

theorem noInstancesEveryWorldCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) :
    (noInstancesEveryWorldCosted M x).cost ≤
      M.worldCount * (M.thingCount * 3 + 3) := by
  unfold noInstancesEveryWorldCosted
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * 3 + 1)
  intro v
  simp only [Complexity.Costed.not_cost]
  have h := anyThingsEvalCosted_cost_le M
    (fun y => Complexity.Costed.tick (M.inst y x v) 1) 1 (by intro y; simp)
  omega

def checkAx2Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (individualBCosted M x w) fun _ =>
        noInstancesEveryWorldCosted M x

def checkAx2 (M : FiniteModel4) : Bool :=
  (checkAx2Costed M).value

theorem checkAx2_eq_legacy (M : FiniteModel4) :
    checkAx2 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (individualB M x w)
        (allWorlds M (fun v => !(anyThings M (fun y => M.inst y x v)))))) := by
  unfold checkAx2 checkAx2Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp only [Complexity.Costed.iff_value, individualBCosted_value,
    noInstancesEveryWorldCosted_value]
  congr 1
  funext w
  cases hi : individualB M x w <;>
    cases hn : allWorlds M (fun v => !(anyThings M (fun y => M.inst y x v))) <;>
      rfl

theorem checkAx2Costed_cost_le (M : FiniteModel4) :
    (checkAx2Costed M).cost ≤ M.thingCount *
      (M.worldCount *
        (M.worldCount * (M.thingCount * 3 + 2) +
          M.worldCount * (M.thingCount * 3 + 3) + 5) + 2) := by
  unfold checkAx2Costed
  let q := M.worldCount * (M.thingCount * 3 + 2)
  let r := M.worldCount * (M.thingCount * 3 + 3)
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (q + r + 5))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (q + r + 3)
  intro w
  have hi := individualBCosted_cost_le M x w
  have hn := noInstancesEveryWorldCosted_cost_le M x
  cases h : individualB M x w
  all_goals simp [Complexity.Costed.iff, h]
  all_goals omega

def axiom1To2RegistryCosted (M : FiniteModel4) :
    Array Complexity.CheckThunk := #[
  fun _ => checkAx1Costed M,
  fun _ => checkAx2Costed M
]

def checkAxioms1To2Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.checkRegistryCosted (axiom1To2RegistryCosted M)

def checkAxioms1To2 (M : FiniteModel4) : Bool :=
  (checkAxioms1To2Costed M).value

theorem checkAxioms1To2_eq_true_iff (M : FiniteModel4) :
    checkAxioms1To2 M = true ↔ checkAx1 M = true ∧ checkAx2 M = true := by
  unfold checkAxioms1To2 checkAxioms1To2Costed
    Complexity.checkRegistryCosted Complexity.allArrayCosted
  rw [Complexity.allListCosted_eq_true_iff]
  simp [axiom1To2RegistryCosted, checkAx1, checkAx2]

theorem checkAxioms1To2Costed_cost_le (M : FiniteModel4) :
    (checkAxioms1To2Costed M).cost ≤ 2 *
      (M.thingCount * (M.worldCount *
        (M.worldCount * (M.thingCount * 3 + 2) +
          M.worldCount * (M.thingCount * 3 + 3) + 5) + 2) + 2) := by
  let q := M.worldCount * (M.thingCount * 3 + 2)
  let r := M.worldCount * (M.thingCount * 3 + 3)
  let bound := M.thingCount * (M.worldCount * (q + r + 5) + 2)
  have hqr : q ≤ r := by
    exact Nat.mul_le_mul_left M.worldCount (by omega)
  have hAx1 : M.thingCount * (M.worldCount * (2 * q + 4) + 2) ≤ bound := by
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega
  unfold checkAxioms1To2Costed
  change (Complexity.checkRegistryCosted (axiom1To2RegistryCosted M)).cost ≤
    2 * (bound + 2)
  apply Complexity.checkRegistryCosted_cost_le _ bound
  intro check hcheck
  simp [axiom1To2RegistryCosted] at hcheck
  rcases hcheck with rfl | rfl
  · exact le_trans (checkAx1Costed_cost_le M) hAx1
  · exact checkAx2Costed_cost_le M

def checkAx3Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allThingsEvalCosted M fun _y =>
      allWorldsEvalCosted M fun w =>
        Complexity.Costed.implies
          (Complexity.Costed.tick (M.inst x _y w) 1) fun _ =>
          Complexity.Costed.orElse (typeBCosted M x w) fun _ =>
            individualBCosted M x w

def checkAx3 (M : FiniteModel4) : Bool :=
  (checkAx3Costed M).value

theorem checkAx3_eq_legacy (M : FiniteModel4) :
    checkAx3 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w =>
        impliesB (M.inst x y w) (typeB M x w || individualB M x w)))) := by
  unfold checkAx3 checkAx3Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allThingsEvalCosted_value]
  congr 1
  funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.orElse_value, impliesB]

theorem checkAx3Costed_cost_le (M : FiniteModel4) :
    (checkAx3Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * (M.worldCount * (M.thingCount * 3 + 2)) + 7) + 2) + 2) := by
  unfold checkAx3Costed
  let q := M.worldCount * (M.thingCount * 3 + 2)
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (2 * q + 7) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (2 * q + 7))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (2 * q + 5)
  intro w
  have ht := typeBCosted_cost_le M x w
  have hi := individualBCosted_cost_le M x w
  cases hinst : M.inst x y w
  all_goals cases htype : typeB M x w
  all_goals simp [Complexity.Costed.implies, Complexity.Costed.orElse,
    Complexity.Costed.not, htype]
  all_goals omega

def checkAx4Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allWorldsEvalCosted M fun w =>
    allThingsEvalCosted M fun x =>
      allThingsEvalCosted M fun y =>
        allThingsEvalCosted M fun z =>
          (Complexity.Costed.andThen (typeBCosted M x w) fun _ =>
            Complexity.Costed.andThen
              (Complexity.Costed.tick (M.inst x y w) 1) fun _ =>
              Complexity.Costed.tick (M.inst y z w) 1).not

def checkAx4 (M : FiniteModel4) : Bool :=
  (checkAx4Costed M).value

theorem checkAx4_eq_legacy (M : FiniteModel4) :
    checkAx4 M = allWorlds M (fun w => allThings M (fun x =>
      allThings M (fun y => allThings M (fun z =>
        !(typeB M x w && M.inst x y w && M.inst y z w))))) := by
  unfold checkAx4 checkAx4Costed
  rw [allWorldsEvalCosted_value]
  congr 1
  funext w
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allThingsEvalCosted_value]
  congr 1
  funext y
  rw [allThingsEvalCosted_value]
  simp
  congr 1
  funext z
  cases ht : typeB M x w <;>
    cases hxy : M.inst x y w <;>
      cases hyz : M.inst y z w <;> rfl

theorem checkAx4Costed_cost_le (M : FiniteModel4) :
    (checkAx4Costed M).cost ≤ M.worldCount *
      (M.thingCount * (M.thingCount *
        (M.thingCount * (M.worldCount * (M.thingCount * 3 + 2) + 7) + 2) + 2) + 2) := by
  unfold checkAx4Costed
  let q := M.worldCount * (M.thingCount * 3 + 2)
  apply allWorldsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.thingCount * (q + 7) + 2) + 2))
  intro w
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (q + 7) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _ (M.thingCount * (q + 7))
  intro y
  apply allThingsEvalCosted_cost_le M _ (q + 5)
  intro z
  have ht := typeBCosted_cost_le M x w
  cases htype : typeB M x w
  all_goals cases hxy : M.inst x y w
  all_goals simp [Complexity.Costed.andThen, Complexity.Costed.not,
    htype]
  all_goals omega

def checkAx5Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allThingsEvalCosted M fun y =>
      allWorldsEvalCosted M fun w =>
        Complexity.Costed.iff (Complexity.Costed.tick (M.sub x y w) 1) fun _ =>
          subDefBCosted M x y w

def checkAx5 (M : FiniteModel4) : Bool :=
  (checkAx5Costed M).value

theorem checkAx5_eq_legacy (M : FiniteModel4) :
    checkAx5 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (M.sub x y w) (subDefB M x y w)))) := by
  unfold checkAx5 checkAx5Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allThingsEvalCosted_value]
  congr 1
  funext y
  rw [allWorldsEvalCosted_value]
  simp only [Complexity.Costed.iff_value, Complexity.Costed.tick_value]
  congr 1
  funext w
  cases hs : M.sub x y w <;>
    cases hd : (subDefBCosted M x y w).value <;>
      simp [subDefB, hd, iffB]

theorem checkAx5Costed_cost_le (M : FiniteModel4) :
    (checkAx5Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (2 * (M.worldCount * (M.thingCount * 3 + 2)) +
          M.worldCount * (M.thingCount * 6 + 2) + 7) + 2) + 2) := by
  unfold checkAx5Costed
  let q := M.worldCount * (M.thingCount * 3 + 2)
  let s := M.worldCount * (M.thingCount * 6 + 2)
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (2 * q + s + 7) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (2 * q + s + 7))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (2 * q + s + 5)
  intro w
  have hd := subDefBCosted_cost_le M x y w
  cases hs : M.sub x y w
  all_goals simp [Complexity.Costed.iff]
  all_goals omega

def ax6AntecedentCosted (M : FiniteModel4)
    (t1 t2 x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x t1 w) 1) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x t2 w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.sub t1 t2 w) 1).not fun _ =>
        (Complexity.Costed.tick (M.sub t2 t1 w) 1).not

theorem ax6AntecedentCosted_value (M : FiniteModel4)
    (t1 t2 x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6AntecedentCosted M t1 t2 x w).value =
      (M.inst x t1 w && M.inst x t2 w && !(M.sub t1 t2 w) && !(M.sub t2 t1 w)) := by
  unfold ax6AntecedentCosted
  cases h1 : M.inst x t1 w <;> cases h2 : M.inst x t2 w <;>
    cases h12 : M.sub t1 t2 w <;> cases h21 : M.sub t2 t1 w <;>
      simp [Complexity.Costed.andThen, Complexity.Costed.not]

theorem ax6AntecedentCosted_cost_le (M : FiniteModel4)
    (t1 t2 x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6AntecedentCosted M t1 t2 x w).cost ≤ 9 := by
  unfold ax6AntecedentCosted
  cases h1 : M.inst x t1 w <;> cases h2 : M.inst x t2 w <;>
    cases h12 : M.sub t1 t2 w <;>
      simp [Complexity.Costed.andThen, Complexity.Costed.not]

def ax6WitnessCosted (M : FiniteModel4)
    (a b x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun t3 =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.sub a t3 w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.sub b t3 w) 1) fun _ =>
        Complexity.Costed.tick (M.inst x t3 w) 1

theorem ax6WitnessCosted_value (M : FiniteModel4)
    (a b x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6WitnessCosted M a b x w).value =
      anyThings M (fun t3 => M.sub a t3 w && M.sub b t3 w && M.inst x t3 w) := by
  unfold ax6WitnessCosted
  rw [anyThingsEvalCosted_value]
  congr 1
  funext t3
  cases h1 : M.sub a t3 w <;> cases h2 : M.sub b t3 w <;>
    cases hi : M.inst x t3 w <;>
      simp [Complexity.Costed.andThen]

theorem ax6WitnessCosted_cost_le (M : FiniteModel4)
    (a b x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6WitnessCosted M a b x w).cost ≤ M.thingCount * 7 := by
  unfold ax6WitnessCosted
  apply anyThingsEvalCosted_cost_le M _ 5
  intro t3
  cases h1 : M.sub a t3 w <;> cases h2 : M.sub b t3 w <;>
    simp [Complexity.Costed.andThen]

def ax6LowerWitnessCosted (M : FiniteModel4)
    (a b x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun t3 =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.sub t3 a w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.sub t3 b w) 1) fun _ =>
        Complexity.Costed.tick (M.inst x t3 w) 1

theorem ax6LowerWitnessCosted_value (M : FiniteModel4)
    (a b x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6LowerWitnessCosted M a b x w).value =
      anyThings M (fun t3 => M.sub t3 a w && M.sub t3 b w && M.inst x t3 w) := by
  unfold ax6LowerWitnessCosted
  rw [anyThingsEvalCosted_value]
  congr 1
  funext t3
  cases h1 : M.sub t3 a w <;> cases h2 : M.sub t3 b w <;>
    cases hi : M.inst x t3 w <;>
      simp [Complexity.Costed.andThen]

theorem ax6LowerWitnessCosted_cost_le (M : FiniteModel4)
    (a b x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6LowerWitnessCosted M a b x w).cost ≤ M.thingCount * 7 := by
  unfold ax6LowerWitnessCosted
  apply anyThingsEvalCosted_cost_le M _ 5
  intro t3
  cases h1 : M.sub t3 a w <;> cases h2 : M.sub t3 b w <;>
    simp [Complexity.Costed.andThen]

def ax6ConsequentCosted (M : FiniteModel4)
    (t1 t2 x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.orElse (ax6WitnessCosted M t1 t2 x w) fun _ =>
    ax6LowerWitnessCosted M t1 t2 x w

theorem ax6ConsequentCosted_value (M : FiniteModel4)
    (t1 t2 x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6ConsequentCosted M t1 t2 x w).value =
      ((anyThings M fun t3 => M.sub t1 t3 w && M.sub t2 t3 w && M.inst x t3 w) ||
       (anyThings M fun t3 => M.sub t3 t1 w && M.sub t3 t2 w && M.inst x t3 w)) := by
  unfold ax6ConsequentCosted
  rw [Complexity.Costed.orElse_value, ax6WitnessCosted_value,
    ax6LowerWitnessCosted_value]

theorem ax6ConsequentCosted_cost_le (M : FiniteModel4)
    (t1 t2 x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax6ConsequentCosted M t1 t2 x w).cost ≤ 14 * M.thingCount + 1 := by
  have h1 := ax6WitnessCosted_cost_le M t1 t2 x w
  have h2 := ax6LowerWitnessCosted_cost_le M t1 t2 x w
  cases h : (ax6WitnessCosted M t1 t2 x w).value <;>
    simp [ax6ConsequentCosted, Complexity.Costed.orElse, h] <;> omega

def checkAx6Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t1 =>
    allThingsEvalCosted M fun t2 =>
      allThingsEvalCosted M fun x =>
        allWorldsEvalCosted M fun w =>
          Complexity.Costed.implies (ax6AntecedentCosted M t1 t2 x w) fun _ =>
            ax6ConsequentCosted M t1 t2 x w

def checkAx6 (M : FiniteModel4) : Bool :=
  (checkAx6Costed M).value

theorem checkAx6_eq_legacy (M : FiniteModel4) :
    checkAx6 M = allThings M (fun t1 => allThings M (fun t2 =>
      allThings M (fun x => allWorlds M (fun w =>
        impliesB
          (M.inst x t1 w && M.inst x t2 w && !(M.sub t1 t2 w) && !(M.sub t2 t1 w))
          ((anyThings M fun t3 =>
            M.sub t1 t3 w && M.sub t2 t3 w && M.inst x t3 w) ||
           (anyThings M fun t3 =>
            M.sub t3 t1 w && M.sub t3 t2 w && M.inst x t3 w)))))) := by
  unfold checkAx6 checkAx6Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext t1
  rw [allThingsEvalCosted_value]
  congr 1
  funext t2
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax6AntecedentCosted_value,
    ax6ConsequentCosted_value, impliesB]

theorem checkAx6Costed_cost_le (M : FiniteModel4) :
    (checkAx6Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (14 * M.thingCount + 14) + 2) + 2) + 2) := by
  unfold checkAx6Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.worldCount * (14 * M.thingCount + 14) + 2) + 2))
  intro t1
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (14 * M.thingCount + 14) + 2))
  intro t2
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (14 * M.thingCount + 14))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (14 * M.thingCount + 12)
  intro w
  have ha := ax6AntecedentCosted_cost_le M t1 t2 x w
  have hc := ax6ConsequentCosted_cost_le M t1 t2 x w
  cases h : (ax6AntecedentCosted M t1 t2 x w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def checkUnaryTableToIndividualCosted (M : FiniteModel4)
    (left : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (left x w) 1) fun _ => individualBCosted M x w

theorem checkUnaryTableToIndividualCosted_value (M : FiniteModel4)
    (left : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableToIndividualCosted M left).value =
      allThings M (fun x => allWorlds M (fun w =>
        impliesB (left x w) (individualB M x w))) := by
  unfold checkUnaryTableToIndividualCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem checkUnaryTableToIndividualCosted_cost_le (M : FiniteModel4)
    (left : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableToIndividualCosted M left).cost ≤
      M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 6) + 2) := by
  unfold checkUnaryTableToIndividualCosted
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 6))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 3 + 2) + 4)
  intro w
  have hi := individualBCosted_cost_le M x w
  cases h : left x w
  all_goals simp [Complexity.Costed.implies, Complexity.Costed.orElse,
    Complexity.Costed.not]
  all_goals omega

def checkAx7Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableToIndividualCosted M M.concreteIndividual

def checkAx7 (M : FiniteModel4) : Bool :=
  (checkAx7Costed M).value

theorem checkAx7_eq_legacy (M : FiniteModel4) :
    checkAx7 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.concreteIndividual x w) (individualB M x w))) := by
  exact checkUnaryTableToIndividualCosted_value M M.concreteIndividual

theorem checkAx7Costed_cost_le (M : FiniteModel4) :
    (checkAx7Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 6) + 2) :=
  checkUnaryTableToIndividualCosted_cost_le M M.concreteIndividual

def checkAx8Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableToIndividualCosted M M.abstractIndividual

def checkAx8 (M : FiniteModel4) : Bool :=
  (checkAx8Costed M).value

theorem checkAx8_eq_legacy (M : FiniteModel4) :
    checkAx8 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.abstractIndividual x w) (individualB M x w))) := by
  exact checkUnaryTableToIndividualCosted_value M M.abstractIndividual

theorem checkAx8Costed_cost_le (M : FiniteModel4) :
    (checkAx8Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 6) + 2) :=
  checkUnaryTableToIndividualCosted_cost_le M M.abstractIndividual

/--
Operational checker for axiom 9.  Every dense-table access is charged where it
is executed, and the abstract-individual lookup is skipped when implication
short-circuits.  This follows the cost-aware operational style of Niu et al.
(POPL 2022); unlike an envelope, the returned Boolean and cost are produced by
one computation.  See `docs/dsl/complexity.md` for the full reference.
-/
def checkAx9Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (M.concreteIndividual x w) 1) fun _ =>
        (Complexity.Costed.tick (M.abstractIndividual x w) 1).not

/-- The production axiom-9 checker is the erasure of its counted evaluator. -/
def checkAx9 (M : FiniteModel4) : Bool :=
  (checkAx9Costed M).value

@[simp] theorem checkAx9Costed_value (M : FiniteModel4) :
    (checkAx9Costed M).value = checkAx9 M := rfl

theorem checkAx9Costed_value_eq_legacy (M : FiniteModel4) :
    (checkAx9Costed M).value =
      allThings M (fun x => allWorlds M (fun w =>
        impliesB (M.concreteIndividual x w) (!(M.abstractIndividual x w)))) := by
  unfold checkAx9Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem checkAx9_eq_legacy (M : FiniteModel4) :
    checkAx9 M =
      allThings M (fun x => allWorlds M (fun w =>
        impliesB (M.concreteIndividual x w) (!(M.abstractIndividual x w)))) := by
  unfold checkAx9
  exact checkAx9Costed_value_eq_legacy M

/-- Concrete worst-case cost of axiom 9 over the explicit world/thing tables. -/
theorem checkAx9Costed_cost_le (M : FiniteModel4) :
    (checkAx9Costed M).cost ≤ M.thingCount * (M.worldCount * 7 + 2) := by
  unfold checkAx9Costed
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 7)
  intro x
  apply allWorldsEvalCosted_cost_le M _ 5
  intro w
  cases h : M.concreteIndividual x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def checkAx10Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (individualBCosted M x w) fun _ =>
        Complexity.Costed.orElse
          (Complexity.Costed.tick (M.concreteIndividual x w) 1) fun _ =>
          Complexity.Costed.tick (M.abstractIndividual x w) 1

def checkAx10 (M : FiniteModel4) : Bool :=
  (checkAx10Costed M).value

theorem checkAx10_eq_legacy (M : FiniteModel4) :
    checkAx10 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (individualB M x w)
        (M.concreteIndividual x w || M.abstractIndividual x w))) := by
  unfold checkAx10 checkAx10Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.iff_value, Complexity.Costed.orElse_value, iffB]
  grind

theorem checkAx10Costed_cost_le (M : FiniteModel4) :
    (checkAx10Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 8) + 2) := by
  unfold checkAx10Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 8))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 3 + 2) + 6)
  intro w
  have hi := individualBCosted_cost_le M x w
  cases hii : individualB M x w
  all_goals cases hc : M.concreteIndividual x w
  all_goals simp [Complexity.Costed.iff, Complexity.Costed.orElse, hii]
  all_goals omega

def checkAx11Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableImplicationCosted M M.endurant M.concreteIndividual

def checkAx11 (M : FiniteModel4) : Bool :=
  (checkAx11Costed M).value

theorem checkAx11_eq_legacy (M : FiniteModel4) :
    checkAx11 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.endurant x w) (M.concreteIndividual x w))) := by
  exact checkUnaryTableImplicationCosted_value M M.endurant M.concreteIndividual

theorem checkAx11Costed_cost_le (M : FiniteModel4) :
    (checkAx11Costed M).cost ≤ M.thingCount * (M.worldCount * 6 + 2) :=
  checkUnaryTableImplicationCosted_cost_le M M.endurant M.concreteIndividual

def checkAx12Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableImplicationCosted M M.perdurant M.concreteIndividual

def checkAx12 (M : FiniteModel4) : Bool :=
  (checkAx12Costed M).value

theorem checkAx12_eq_legacy (M : FiniteModel4) :
    checkAx12 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.perdurant x w) (M.concreteIndividual x w))) := by
  exact checkUnaryTableImplicationCosted_value M M.perdurant M.concreteIndividual

theorem checkAx12Costed_cost_le (M : FiniteModel4) :
    (checkAx12Costed M).cost ≤ M.thingCount * (M.worldCount * 6 + 2) :=
  checkUnaryTableImplicationCosted_cost_le M M.perdurant M.concreteIndividual

def checkAx13Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableDisjointCosted M M.endurant M.perdurant

def checkAx13 (M : FiniteModel4) : Bool :=
  (checkAx13Costed M).value

theorem checkAx13_eq_legacy (M : FiniteModel4) :
    checkAx13 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.endurant x w) (!(M.perdurant x w)))) := by
  exact checkUnaryTableDisjointCosted_value M M.endurant M.perdurant

theorem checkAx13Costed_cost_le (M : FiniteModel4) :
    (checkAx13Costed M).cost ≤ M.thingCount * (M.worldCount * 7 + 2) :=
  checkUnaryTableDisjointCosted_cost_le M M.endurant M.perdurant

def checkAx14Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff
        (Complexity.Costed.tick (M.concreteIndividual x w) 1) fun _ =>
        Complexity.Costed.orElse
          (Complexity.Costed.tick (M.endurant x w) 1) fun _ =>
          Complexity.Costed.tick (M.perdurant x w) 1

def checkAx14 (M : FiniteModel4) : Bool :=
  (checkAx14Costed M).value

theorem checkAx14_eq_legacy (M : FiniteModel4) :
    checkAx14 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (M.concreteIndividual x w) (M.endurant x w || M.perdurant x w))) := by
  unfold checkAx14 checkAx14Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.iff_value, Complexity.Costed.orElse_value, iffB]
  grind

theorem checkAx14Costed_cost_le (M : FiniteModel4) :
    (checkAx14Costed M).cost ≤ M.thingCount * (M.worldCount * 8 + 2) := by
  unfold checkAx14Costed
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 8)
  intro x
  apply allWorldsEvalCosted_cost_le M _ 6
  intro w
  cases hc : M.concreteIndividual x w <;>
    cases he : M.endurant x w <;>
      simp [Complexity.Costed.iff, Complexity.Costed.orElse]

def checkUnaryTableToTypeCosted (M : FiniteModel4)
    (left : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (left x w) 1) fun _ => typeBCosted M x w

theorem checkUnaryTableToTypeCosted_value (M : FiniteModel4)
    (left : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableToTypeCosted M left).value =
      allThings M (fun x => allWorlds M (fun w => impliesB (left x w) (typeB M x w))) := by
  unfold checkUnaryTableToTypeCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem checkUnaryTableToTypeCosted_cost_le (M : FiniteModel4)
    (left : Fin M.thingCount → Fin M.worldCount → Bool) :
    (checkUnaryTableToTypeCosted M left).cost ≤
      M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 5) + 2) := by
  unfold checkUnaryTableToTypeCosted
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 5))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 3 + 2) + 3)
  intro w
  have ht := typeBCosted_cost_le M x w
  cases h : left x w
  all_goals simp [Complexity.Costed.implies, Complexity.Costed.orElse,
    Complexity.Costed.not]
  all_goals omega

def checkAx15Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableToTypeCosted M M.endurantType

def checkAx15 (M : FiniteModel4) : Bool :=
  (checkAx15Costed M).value

theorem checkAx15_eq_legacy (M : FiniteModel4) :
    checkAx15 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.endurantType x w) (typeB M x w))) := by
  exact checkUnaryTableToTypeCosted_value M M.endurantType

theorem checkAx15Costed_cost_le (M : FiniteModel4) :
    (checkAx15Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 5) + 2) :=
  checkUnaryTableToTypeCosted_cost_le M M.endurantType

def checkAx16Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableToTypeCosted M M.perdurantType

def checkAx16 (M : FiniteModel4) : Bool :=
  (checkAx16Costed M).value

theorem checkAx16_eq_legacy (M : FiniteModel4) :
    checkAx16 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.perdurantType x w) (typeB M x w))) := by
  exact checkUnaryTableToTypeCosted_value M M.perdurantType

theorem checkAx16Costed_cost_le (M : FiniteModel4) :
    (checkAx16Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 5) + 2) :=
  checkUnaryTableToTypeCosted_cost_le M M.perdurantType

def checkAx17Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableDisjointCosted M M.endurantType M.perdurantType

def checkAx17 (M : FiniteModel4) : Bool :=
  (checkAx17Costed M).value

theorem checkAx17_eq_legacy (M : FiniteModel4) :
    checkAx17 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.endurantType x w) (!(M.perdurantType x w)))) := by
  exact checkUnaryTableDisjointCosted_value M M.endurantType M.perdurantType

theorem checkAx17Costed_cost_le (M : FiniteModel4) :
    (checkAx17Costed M).cost ≤ M.thingCount * (M.worldCount * 7 + 2) :=
  checkUnaryTableDisjointCosted_cost_le M M.endurantType M.perdurantType

/-!
The first fully operational registry slice.  It uses delayed checks, so failure
really prevents later axioms from running.  This is a staging theorem for the
production 116-check registry, not a claim that the remaining axioms have
already been instrumented.
-/

def axiom7To17RegistryCosted (M : FiniteModel4) :
    Array Complexity.CheckThunk := #[
  fun _ => checkAx7Costed M,
  fun _ => checkAx8Costed M,
  fun _ => checkAx9Costed M,
  fun _ => checkAx10Costed M,
  fun _ => checkAx11Costed M,
  fun _ => checkAx12Costed M,
  fun _ => checkAx13Costed M,
  fun _ => checkAx14Costed M,
  fun _ => checkAx15Costed M,
  fun _ => checkAx16Costed M,
  fun _ => checkAx17Costed M
]

def checkAxioms7To17Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.checkRegistryCosted (axiom7To17RegistryCosted M)

/-- Production value for this registry slice is obtained only by erasing cost. -/
def checkAxioms7To17 (M : FiniteModel4) : Bool :=
  (checkAxioms7To17Costed M).value

@[simp] theorem checkAxioms7To17Costed_value (M : FiniteModel4) :
    (checkAxioms7To17Costed M).value = checkAxioms7To17 M := rfl

@[simp] theorem axiom7To17RegistryCosted_size (M : FiniteModel4) :
    (axiom7To17RegistryCosted M).size = 11 := rfl

theorem checkAxioms7To17_eq_true_iff (M : FiniteModel4) :
    checkAxioms7To17 M = true ↔
      checkAx7 M = true ∧ checkAx8 M = true ∧ checkAx9 M = true ∧
      checkAx10 M = true ∧ checkAx11 M = true ∧ checkAx12 M = true ∧
        checkAx13 M = true ∧ checkAx14 M = true ∧ checkAx15 M = true ∧
          checkAx16 M = true ∧ checkAx17 M = true := by
  unfold checkAxioms7To17 checkAxioms7To17Costed
    Complexity.checkRegistryCosted Complexity.allArrayCosted
  rw [Complexity.allListCosted_eq_true_iff]
  simp [axiom7To17RegistryCosted, checkAx7, checkAx8, checkAx10,
    checkAx11, checkAx12, checkAx13, checkAx14, checkAx15, checkAx16, checkAx17]

theorem checkAxioms7To17Costed_cost_le (M : FiniteModel4) :
    (checkAxioms7To17Costed M).cost ≤
      11 * (M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 8) + 2) + 2) := by
  let q := M.worldCount * (M.thingCount * 3 + 2)
  let bound := M.thingCount * (M.worldCount * (q + 8) + 2)
  have hDirect : M.thingCount * (M.worldCount * 8 + 2) ≤ bound := by
    exact Nat.mul_le_mul_left M.thingCount (Nat.add_le_add_right
      (Nat.mul_le_mul_left M.worldCount (Nat.le_add_left 8 q)) 2)
  have hType : M.thingCount * (M.worldCount * (q + 5) + 2) ≤ bound := by
    exact Nat.mul_le_mul_left M.thingCount (Nat.add_le_add_right
      (Nat.mul_le_mul_left M.worldCount
        (Nat.add_le_add_left (show 5 ≤ 8 by omega) q)) 2)
  have hIndividual : M.thingCount * (M.worldCount * (q + 6) + 2) ≤ bound := by
    exact Nat.mul_le_mul_left M.thingCount (Nat.add_le_add_right
      (Nat.mul_le_mul_left M.worldCount
        (Nat.add_le_add_left (show 6 ≤ 8 by omega) q)) 2)
  unfold checkAxioms7To17Costed
  change (Complexity.checkRegistryCosted (axiom7To17RegistryCosted M)).cost ≤
    11 * (bound + 2)
  apply Complexity.checkRegistryCosted_cost_le _ bound
  intro check hcheck
  simp [axiom7To17RegistryCosted] at hcheck
  rcases hcheck with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact le_trans (checkAx7Costed_cost_le M) hIndividual
  · exact le_trans (checkAx8Costed_cost_le M) hIndividual
  · exact le_trans (checkAx9Costed_cost_le M) (le_trans
      (Nat.mul_le_mul_left M.thingCount (by omega)) hDirect)
  · exact checkAx10Costed_cost_le M
  · exact le_trans (checkAx11Costed_cost_le M) (le_trans
      (Nat.mul_le_mul_left M.thingCount (by omega)) hDirect)
  · exact le_trans (checkAx12Costed_cost_le M) (le_trans
      (Nat.mul_le_mul_left M.thingCount (by omega)) hDirect)
  · exact le_trans (checkAx13Costed_cost_le M) (le_trans
      (Nat.mul_le_mul_left M.thingCount (by omega)) hDirect)
  · exact le_trans (checkAx14Costed_cost_le M) hDirect
  · exact le_trans (checkAx15Costed_cost_le M) hType
  · exact le_trans (checkAx16Costed_cost_le M) hType
  · exact le_trans (checkAx17Costed_cost_le M) (le_trans
      (Nat.mul_le_mul_left M.thingCount (by omega)) hDirect)

def axioms1To17CostBound (M : FiniteModel4) : Nat :=
  2 * (M.thingCount * (M.worldCount *
      (M.worldCount * (M.thingCount * 3 + 2) +
        M.worldCount * (M.thingCount * 3 + 3) + 5) + 2) + 2) +
  M.thingCount * (M.thingCount *
      (M.worldCount * (2 * (M.worldCount * (M.thingCount * 3 + 2)) + 7) + 2) + 2) +
  M.worldCount * (M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 3 + 2) + 7) + 2) + 2) + 2) +
  M.thingCount * (M.thingCount * (M.worldCount *
      (2 * (M.worldCount * (M.thingCount * 3 + 2)) +
        M.worldCount * (M.thingCount * 6 + 2) + 7) + 2) + 2) +
  M.thingCount * (M.thingCount * (M.thingCount *
      (M.worldCount * (14 * M.thingCount + 14) + 2) + 2) + 2) +
  11 * (M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 8) + 2) + 2) +
  5

/-- Ordered short-circuit composition of every counted checker from 1 to 17. -/
def checkAxioms1To17Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (checkAxioms1To2Costed M) fun _ =>
    Complexity.Costed.andThen (checkAx3Costed M) fun _ =>
      Complexity.Costed.andThen (checkAx4Costed M) fun _ =>
        Complexity.Costed.andThen (checkAx5Costed M) fun _ =>
          Complexity.Costed.andThen (checkAx6Costed M) fun _ =>
            checkAxioms7To17Costed M

def checkAxioms1To17 (M : FiniteModel4) : Bool :=
  (checkAxioms1To17Costed M).value

@[simp] theorem checkAxioms1To17Costed_value (M : FiniteModel4) :
    (checkAxioms1To17Costed M).value = checkAxioms1To17 M := rfl

theorem checkAxioms1To17_eq_true_iff (M : FiniteModel4) :
    checkAxioms1To17 M = true ↔
      checkAxioms1To2 M = true ∧ checkAx3 M = true ∧ checkAx4 M = true ∧
        checkAx5 M = true ∧ checkAx6 M = true ∧ checkAxioms7To17 M = true := by
  unfold checkAxioms1To17 checkAxioms1To17Costed
  simp only [Complexity.Costed.andThen_value]
  unfold checkAxioms1To2 checkAx3 checkAx4 checkAx5 checkAx6 checkAxioms7To17
  simp only [Bool.and_eq_true]

theorem checkAxioms1To17Costed_cost_le (M : FiniteModel4) :
    (checkAxioms1To17Costed M).cost ≤ axioms1To17CostBound M := by
  have h12 := checkAxioms1To2Costed_cost_le M
  have h3 := checkAx3Costed_cost_le M
  have h4 := checkAx4Costed_cost_le M
  have h5 := checkAx5Costed_cost_le M
  have h6 := checkAx6Costed_cost_le M
  have h717 := checkAxioms7To17Costed_cost_le M
  cases h12v : (checkAxioms1To2Costed M).value
  all_goals cases h3v : (checkAx3Costed M).value
  all_goals cases h4v : (checkAx4Costed M).value
  all_goals cases h5v : (checkAx5Costed M).value
  all_goals cases h6v : (checkAx6Costed M).value
  all_goals simp [checkAxioms1To17Costed, Complexity.Costed.andThen,
    h12v, h3v, h4v, h5v, h6v, axioms1To17CostBound]
  all_goals omega

def instanceSomeWorldCosted (M : FiniteModel4)
    (x t : Fin M.thingCount) : Complexity.Costed Bool :=
  anyWorldsEvalCosted M fun v => Complexity.Costed.tick (M.inst x t v) 1

def instanceAllWorldsCosted (M : FiniteModel4)
    (x t : Fin M.thingCount) : Complexity.Costed Bool :=
  allWorldsEvalCosted M fun v => Complexity.Costed.tick (M.inst x t v) 1

theorem instanceSomeWorldCosted_value (M : FiniteModel4)
    (x t : Fin M.thingCount) :
    (instanceSomeWorldCosted M x t).value = anyWorlds M (fun v => M.inst x t v) := by
  unfold instanceSomeWorldCosted
  rw [anyWorldsEvalCosted_value]
  rfl

theorem instanceAllWorldsCosted_value (M : FiniteModel4)
    (x t : Fin M.thingCount) :
    (instanceAllWorldsCosted M x t).value = allWorlds M (fun v => M.inst x t v) := by
  unfold instanceAllWorldsCosted
  rw [allWorldsEvalCosted_value]
  rfl

theorem instanceSomeWorldCosted_cost_le (M : FiniteModel4)
    (x t : Fin M.thingCount) :
    (instanceSomeWorldCosted M x t).cost ≤ M.worldCount * 3 := by
  unfold instanceSomeWorldCosted
  apply anyWorldsEvalCosted_cost_le M _ 1
  intro v
  simp

theorem instanceAllWorldsCosted_cost_le (M : FiniteModel4)
    (x t : Fin M.thingCount) :
    (instanceAllWorldsCosted M x t).cost ≤ M.worldCount * 3 := by
  unfold instanceAllWorldsCosted
  apply allWorldsEvalCosted_cost_le M _ 1
  intro v
  simp

def rigidInstancesCosted (M : FiniteModel4)
    (t : Fin M.thingCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    Complexity.Costed.implies (instanceSomeWorldCosted M x t) fun _ =>
      instanceAllWorldsCosted M x t

theorem rigidInstancesCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) :
    (rigidInstancesCosted M t).value = allThings M (fun x =>
      impliesB (anyWorlds M (fun v => M.inst x t v))
        (allWorlds M (fun v => M.inst x t v))) := by
  unfold rigidInstancesCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  simp [Complexity.Costed.implies_value, instanceSomeWorldCosted_value,
    instanceAllWorldsCosted_value, impliesB]

theorem rigidInstancesCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) :
    (rigidInstancesCosted M t).cost ≤ M.thingCount * (6 * M.worldCount + 4) := by
  unfold rigidInstancesCosted
  apply allThingsEvalCosted_cost_le M _ (6 * M.worldCount + 2)
  intro x
  have hs := instanceSomeWorldCosted_cost_le M x t
  have ha := instanceAllWorldsCosted_cost_le M x t
  cases h : (instanceSomeWorldCosted M x t).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def checkAx18ConsequentCosted (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.endurantType t w) 1) fun _ =>
    rigidInstancesCosted M t

theorem checkAx18ConsequentCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx18ConsequentCosted M t w).value =
      (M.endurantType t w && allThings M (fun x =>
        impliesB (anyWorlds M (fun v => M.inst x t v))
          (allWorlds M (fun v => M.inst x t v)))) := by
  unfold checkAx18ConsequentCosted
  cases h : M.endurantType t w <;>
    simp [Complexity.Costed.andThen, rigidInstancesCosted_value]

theorem checkAx18ConsequentCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx18ConsequentCosted M t w).cost ≤
      M.thingCount * (6 * M.worldCount + 4) + 2 := by
  have hr := rigidInstancesCosted_cost_le M t
  cases h : M.endurantType t w
  · simp [checkAx18ConsequentCosted, Complexity.Costed.andThen, h]
  · simp [checkAx18ConsequentCosted, Complexity.Costed.andThen, h]
    omega

def checkAx18Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (Complexity.Costed.tick (M.rigid t w) 1) fun _ =>
        checkAx18ConsequentCosted M t w

def checkAx18 (M : FiniteModel4) : Bool :=
  (checkAx18Costed M).value

theorem checkAx18_eq_legacy (M : FiniteModel4) :
    checkAx18 M = allThings M (fun t => allWorlds M (fun w =>
      iffB (M.rigid t w)
        (M.endurantType t w && allThings M (fun x =>
          impliesB (anyWorlds M (fun v => M.inst x t v))
            (allWorlds M (fun v => M.inst x t v)))))) := by
  unfold checkAx18 checkAx18Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext t
  rw [allWorldsEvalCosted_value]
  simp only [Complexity.Costed.iff_value, Complexity.Costed.tick_value,
    checkAx18ConsequentCosted_value]
  congr 1
  funext w
  cases hr : M.rigid t w <;>
    cases hc : (M.endurantType t w && allThings M (fun x =>
      impliesB (anyWorlds M (fun v => M.inst x t v))
        (allWorlds M (fun v => M.inst x t v)))) <;> simp [iffB]

theorem checkAx18Costed_cost_le (M : FiniteModel4) :
    (checkAx18Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (6 * M.worldCount + 4) + 7) + 2) := by
  unfold checkAx18Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * (6 * M.worldCount + 4) + 7))
  intro t
  apply allWorldsEvalCosted_cost_le M _
    (M.thingCount * (6 * M.worldCount + 4) + 5)
  intro w
  have hc := checkAx18ConsequentCosted_cost_le M t w
  cases h : M.rigid t w <;>
    simp [Complexity.Costed.iff] <;> omega

/-!
The modal-classification checkers below use the same compositional cost
instrumentation as `Complexity.CostModel`: costs follow the executable's
left-to-right short-circuit order (Niu et al.; Haslbeck), while each production
Boolean is literally the erasure of its counted definition.  The latter is the
implementation-correspondence pattern used here under inspiration from
Forster et al. and de Moura's RadixExperiment; it is distinct from the later
semantic soundness theorem for each UFO axiom.
-/

def instanceAbsentSomeWorldCosted (M : FiniteModel4)
    (x t : Fin M.thingCount) : Complexity.Costed Bool :=
  anyWorldsEvalCosted M fun v =>
    (Complexity.Costed.tick (M.inst x t v) 1).not

theorem instanceAbsentSomeWorldCosted_value (M : FiniteModel4)
    (x t : Fin M.thingCount) :
    (instanceAbsentSomeWorldCosted M x t).value =
      anyWorlds M (fun v => !(M.inst x t v)) := by
  unfold instanceAbsentSomeWorldCosted
  rw [anyWorldsEvalCosted_value]
  rfl

theorem instanceAbsentSomeWorldCosted_cost_le (M : FiniteModel4)
    (x t : Fin M.thingCount) :
    (instanceAbsentSomeWorldCosted M x t).cost ≤ M.worldCount * 4 := by
  unfold instanceAbsentSomeWorldCosted
  apply anyWorldsEvalCosted_cost_le M _ 2
  intro v
  simp

def antiRigidInstancesCosted (M : FiniteModel4)
    (t : Fin M.thingCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    Complexity.Costed.implies (instanceSomeWorldCosted M x t) fun _ =>
      instanceAbsentSomeWorldCosted M x t

theorem antiRigidInstancesCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) :
    (antiRigidInstancesCosted M t).value = allThings M (fun x =>
      impliesB (anyWorlds M (fun v => M.inst x t v))
        (anyWorlds M (fun v => !(M.inst x t v)))) := by
  unfold antiRigidInstancesCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  simp [Complexity.Costed.implies_value, instanceSomeWorldCosted_value,
    instanceAbsentSomeWorldCosted_value, impliesB]

theorem antiRigidInstancesCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) :
    (antiRigidInstancesCosted M t).cost ≤
      M.thingCount * (7 * M.worldCount + 4) := by
  unfold antiRigidInstancesCosted
  apply allThingsEvalCosted_cost_le M _ (7 * M.worldCount + 2)
  intro x
  have hs := instanceSomeWorldCosted_cost_le M x t
  have ha := instanceAbsentSomeWorldCosted_cost_le M x t
  cases h : (instanceSomeWorldCosted M x t).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def checkAx19ConsequentCosted (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.tick (M.endurantType t w) 1) fun _ =>
      antiRigidInstancesCosted M t

theorem checkAx19ConsequentCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx19ConsequentCosted M t w).value =
      (M.endurantType t w && allThings M (fun x =>
        impliesB (anyWorlds M (fun v => M.inst x t v))
          (anyWorlds M (fun v => !(M.inst x t v))))) := by
  unfold checkAx19ConsequentCosted
  cases h : M.endurantType t w <;>
    simp [Complexity.Costed.andThen, antiRigidInstancesCosted_value]

theorem checkAx19ConsequentCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx19ConsequentCosted M t w).cost ≤
      M.thingCount * (7 * M.worldCount + 4) + 2 := by
  have ha := antiRigidInstancesCosted_cost_le M t
  cases h : M.endurantType t w
  · simp [checkAx19ConsequentCosted, Complexity.Costed.andThen, h]
  · simp [checkAx19ConsequentCosted, Complexity.Costed.andThen, h]
    omega

def checkAx19Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff
        (Complexity.Costed.tick (M.antiRigid t w) 1) fun _ =>
          checkAx19ConsequentCosted M t w

def checkAx19 (M : FiniteModel4) : Bool :=
  (checkAx19Costed M).value

theorem checkAx19_eq_legacy (M : FiniteModel4) :
    checkAx19 M = allThings M (fun t =>
      allWorlds M (fun w =>
        iffB (M.antiRigid t w)
          (M.endurantType t w && allThings M (fun x =>
            impliesB
              (anyWorlds M (fun v => M.inst x t v))
              (anyWorlds M (fun v => !(M.inst x t v))))))) := by
  unfold checkAx19 checkAx19Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext t
  rw [allWorldsEvalCosted_value]
  simp only [Complexity.Costed.iff_value, Complexity.Costed.tick_value,
    checkAx19ConsequentCosted_value]
  congr 1
  funext w
  cases ha : M.antiRigid t w <;>
    cases hc : (M.endurantType t w && allThings M (fun x =>
      impliesB (anyWorlds M (fun v => M.inst x t v))
        (anyWorlds M (fun v => !(M.inst x t v))))) <;> simp [iffB]

theorem checkAx19Costed_cost_le (M : FiniteModel4) :
    (checkAx19Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (7 * M.worldCount + 4) + 7) + 2) := by
  unfold checkAx19Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * (7 * M.worldCount + 4) + 7))
  intro t
  apply allWorldsEvalCosted_cost_le M _
    (M.thingCount * (7 * M.worldCount + 4) + 5)
  intro w
  have hc := checkAx19ConsequentCosted_cost_le M t w
  cases h : M.antiRigid t w <;>
    simp [Complexity.Costed.iff] <;> omega

def checkAx20ConsequentCosted (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.tick (M.endurantType t w) 1) fun _ =>
      Complexity.Costed.andThen
        (Complexity.Costed.tick (M.rigid t w) 1).not fun _ =>
          (Complexity.Costed.tick (M.antiRigid t w) 1).not

theorem checkAx20ConsequentCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx20ConsequentCosted M t w).value =
      (M.endurantType t w && !(M.rigid t w) && !(M.antiRigid t w)) := by
  unfold checkAx20ConsequentCosted
  cases he : M.endurantType t w <;> cases hr : M.rigid t w <;>
    cases ha : M.antiRigid t w <;>
      simp [Complexity.Costed.andThen, Complexity.Costed.not]

theorem checkAx20ConsequentCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx20ConsequentCosted M t w).cost ≤ 7 := by
  unfold checkAx20ConsequentCosted
  cases he : M.endurantType t w <;> cases hr : M.rigid t w <;>
    simp [Complexity.Costed.andThen, Complexity.Costed.not]

def checkAx20Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff
        (Complexity.Costed.tick (M.semiRigid t w) 1) fun _ =>
          checkAx20ConsequentCosted M t w

def checkAx20 (M : FiniteModel4) : Bool :=
  (checkAx20Costed M).value

theorem checkAx20_eq_legacy (M : FiniteModel4) :
    checkAx20 M = allThings M (fun t => allWorlds M (fun w =>
      iffB (M.semiRigid t w)
        (M.endurantType t w && !(M.rigid t w) && !(M.antiRigid t w)))) := by
  unfold checkAx20 checkAx20Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext t
  rw [allWorldsEvalCosted_value]
  simp only [Complexity.Costed.iff_value, Complexity.Costed.tick_value,
    checkAx20ConsequentCosted_value]
  congr 1
  funext w
  cases hs : M.semiRigid t w <;>
    cases hc : (M.endurantType t w && !(M.rigid t w) && !(M.antiRigid t w)) <;>
      simp [iffB]

theorem checkAx20Costed_cost_le (M : FiniteModel4) :
    (checkAx20Costed M).cost ≤ M.thingCount * (M.worldCount * 12 + 2) := by
  unfold checkAx20Costed
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 12)
  intro t
  apply allWorldsEvalCosted_cost_le M _ 10
  intro w
  have hc := checkAx20ConsequentCosted_cost_le M t w
  cases h : M.semiRigid t w <;>
    simp [Complexity.Costed.iff] <;> omega

def ax21KindWitnessCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun k =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.kind k w) 1) fun _ =>
      instanceAllWorldsCosted M x k

theorem ax21KindWitnessCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax21KindWitnessCosted M x w).value = anyThings M (fun k =>
      M.kind k w && allWorlds M (fun v => M.inst x k v)) := by
  unfold ax21KindWitnessCosted
  rw [anyThingsEvalCosted_value]
  congr 1
  funext k
  cases hk : M.kind k w <;>
    simp [Complexity.Costed.andThen, instanceAllWorldsCosted_value]

theorem ax21KindWitnessCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax21KindWitnessCosted M x w).cost ≤
      M.thingCount * (3 * M.worldCount + 4) := by
  unfold ax21KindWitnessCosted
  apply anyThingsEvalCosted_cost_le M _ (3 * M.worldCount + 2)
  intro k
  have hi := instanceAllWorldsCosted_cost_le M x k
  cases hk : M.kind k w
  · simp [Complexity.Costed.andThen]
  · simp [Complexity.Costed.andThen]
    omega

def checkAx21Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (M.endurant x w) 1) fun _ =>
          ax21KindWitnessCosted M x w

def checkAx21 (M : FiniteModel4) : Bool :=
  (checkAx21Costed M).value

theorem checkAx21_eq_legacy (M : FiniteModel4) :
    checkAx21 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.endurant x w)
        (anyThings M (fun k =>
          M.kind k w && allWorlds M (fun v => M.inst x k v))))) := by
  unfold checkAx21 checkAx21Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax21KindWitnessCosted_value, impliesB]

theorem checkAx21Costed_cost_le (M : FiniteModel4) :
    (checkAx21Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (3 * M.worldCount + 4) + 5) + 2) := by
  unfold checkAx21Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * (3 * M.worldCount + 4) + 5))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (M.thingCount * (3 * M.worldCount + 4) + 3)
  intro w
  have hw := ax21KindWitnessCosted_cost_le M x w
  cases he : M.endurant x w
  · simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]
  · simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]
    omega

def ax22AntecedentCosted (M : FiniteModel4)
    (k x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.kind k w) 1) fun _ =>
    Complexity.Costed.tick (M.inst x k w) 1

theorem ax22AntecedentCosted_value (M : FiniteModel4)
    (k x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax22AntecedentCosted M k x w).value = (M.kind k w && M.inst x k w) := by
  unfold ax22AntecedentCosted
  cases hk : M.kind k w <;> simp [Complexity.Costed.andThen]

theorem ax22AntecedentCosted_cost_le (M : FiniteModel4)
    (k x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax22AntecedentCosted M k x w).cost ≤ 3 := by
  unfold ax22AntecedentCosted
  cases hk : M.kind k w <;> simp [Complexity.Costed.andThen]

/--
One alternative-kind test. The finite-index disequality is charged as one
comparison under the documented unit-cost model; this is an explicit operation,
not a hidden proposition-level decision procedure.
-/
def ax22AlternativeCosted (M : FiniteModel4)
    (k x z : Fin M.thingCount) (v : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.kind z v) 1) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x z v) 1) fun _ =>
      Complexity.Costed.tick (decide (z ≠ k)) 1

theorem ax22AlternativeCosted_value (M : FiniteModel4)
    (k x z : Fin M.thingCount) (v : Fin M.worldCount) :
    (ax22AlternativeCosted M k x z v).value =
      (M.kind z v && M.inst x z v && decide (z ≠ k)) := by
  unfold ax22AlternativeCosted
  cases hk : M.kind z v <;> cases hi : M.inst x z v <;>
    simp [Complexity.Costed.andThen]

theorem ax22AlternativeCosted_cost_le (M : FiniteModel4)
    (k x z : Fin M.thingCount) (v : Fin M.worldCount) :
    (ax22AlternativeCosted M k x z v).cost ≤ 5 := by
  unfold ax22AlternativeCosted
  cases hk : M.kind z v <;> cases hi : M.inst x z v <;>
    simp [Complexity.Costed.andThen]

def ax22CounterexampleCosted (M : FiniteModel4)
    (k x : Fin M.thingCount) : Complexity.Costed Bool :=
  anyWorldsEvalCosted M fun v =>
    anyThingsEvalCosted M fun z => ax22AlternativeCosted M k x z v

theorem ax22CounterexampleCosted_value (M : FiniteModel4)
    (k x : Fin M.thingCount) :
    (ax22CounterexampleCosted M k x).value = anyWorlds M (fun v =>
      anyThings M (fun z => M.kind z v && M.inst x z v && decide (z ≠ k))) := by
  unfold ax22CounterexampleCosted
  rw [anyWorldsEvalCosted_value]
  congr 1
  funext v
  rw [anyThingsEvalCosted_value]
  simp [ax22AlternativeCosted_value]

theorem ax22CounterexampleCosted_cost_le (M : FiniteModel4)
    (k x : Fin M.thingCount) :
    (ax22CounterexampleCosted M k x).cost ≤
      M.worldCount * (M.thingCount * 7 + 2) := by
  unfold ax22CounterexampleCosted
  apply anyWorldsEvalCosted_cost_le M _ (M.thingCount * 7)
  intro v
  apply anyThingsEvalCosted_cost_le M _ 5
  intro z
  exact ax22AlternativeCosted_cost_le M k x z v

def checkAx22Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun k =>
    allThingsEvalCosted M fun x =>
      allWorldsEvalCosted M fun w =>
        Complexity.Costed.implies (ax22AntecedentCosted M k x w) fun _ =>
          (ax22CounterexampleCosted M k x).not

def checkAx22 (M : FiniteModel4) : Bool :=
  (checkAx22Costed M).value

theorem checkAx22_eq_legacy (M : FiniteModel4) :
    checkAx22 M = allThings M (fun k => allThings M (fun x =>
      allWorlds M (fun w =>
        impliesB (M.kind k w && M.inst x k w)
          (!(anyWorlds M (fun v => anyThings M (fun z =>
            M.kind z v && M.inst x z v && decide (z ≠ k)))))))) := by
  unfold checkAx22 checkAx22Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext k
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax22AntecedentCosted_value,
    ax22CounterexampleCosted_value, impliesB]

theorem checkAx22Costed_cost_le (M : FiniteModel4) :
    (checkAx22Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 7 + 2) + 8) + 2) + 2) := by
  unfold checkAx22Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 7 + 2) + 8) + 2))
  intro k
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.worldCount * (M.thingCount * 7 + 2) + 8))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 7 + 2) + 6)
  intro w
  have ha := ax22AntecedentCosted_cost_le M k x w
  have hc := ax22CounterexampleCosted_cost_le M k x
  cases h : (ax22AntecedentCosted M k x w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def ax23SubsumesInstancesCosted (M : FiniteModel4)
    (t k : Fin M.thingCount) : Complexity.Costed Bool :=
  allWorldsEvalCosted M fun v =>
    allThingsEvalCosted M fun x =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.inst x t v) 1) fun _ =>
        Complexity.Costed.tick (M.inst x k v) 1

theorem ax23SubsumesInstancesCosted_value (M : FiniteModel4)
    (t k : Fin M.thingCount) :
    (ax23SubsumesInstancesCosted M t k).value = allWorlds M (fun v =>
      allThings M (fun x => impliesB (M.inst x t v) (M.inst x k v))) := by
  unfold ax23SubsumesInstancesCosted
  rw [allWorldsEvalCosted_value]
  congr 1
  funext v
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem ax23SubsumesInstancesCosted_cost_le (M : FiniteModel4)
    (t k : Fin M.thingCount) :
    (ax23SubsumesInstancesCosted M t k).cost ≤
      M.worldCount * (M.thingCount * 6 + 2) := by
  unfold ax23SubsumesInstancesCosted
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * 6)
  intro v
  apply allThingsEvalCosted_cost_le M _ 4
  intro x
  cases hi : M.inst x t v <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def ax23KindWitnessCosted (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun k =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.kind k w) 1) fun _ =>
      ax23SubsumesInstancesCosted M t k

theorem ax23KindWitnessCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax23KindWitnessCosted M t w).value = anyThings M (fun k =>
      M.kind k w && allWorlds M (fun v => allThings M (fun x =>
        impliesB (M.inst x t v) (M.inst x k v)))) := by
  unfold ax23KindWitnessCosted
  rw [anyThingsEvalCosted_value]
  congr 1
  funext k
  cases hk : M.kind k w <;>
    simp [Complexity.Costed.andThen, ax23SubsumesInstancesCosted_value]

theorem ax23KindWitnessCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax23KindWitnessCosted M t w).cost ≤
      M.thingCount * (M.worldCount * (M.thingCount * 6 + 2) + 4) := by
  unfold ax23KindWitnessCosted
  apply anyThingsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 6 + 2) + 2)
  intro k
  have hs := ax23SubsumesInstancesCosted_cost_le M t k
  cases hk : M.kind k w
  · simp [Complexity.Costed.andThen]
  · simp [Complexity.Costed.andThen]
    omega

def checkAx23ConsequentCosted (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.tick (M.endurantType t w) 1) fun _ =>
      ax23KindWitnessCosted M t w

theorem checkAx23ConsequentCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx23ConsequentCosted M t w).value =
      (M.endurantType t w && anyThings M (fun k =>
        M.kind k w && allWorlds M (fun v => allThings M (fun x =>
          impliesB (M.inst x t v) (M.inst x k v))))) := by
  unfold checkAx23ConsequentCosted
  cases he : M.endurantType t w <;>
    simp [Complexity.Costed.andThen, ax23KindWitnessCosted_value]

theorem checkAx23ConsequentCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (checkAx23ConsequentCosted M t w).cost ≤
      M.thingCount * (M.worldCount * (M.thingCount * 6 + 2) + 4) + 2 := by
  have hw := ax23KindWitnessCosted_cost_le M t w
  cases he : M.endurantType t w
  · simp [checkAx23ConsequentCosted, Complexity.Costed.andThen, he]
  · simp [checkAx23ConsequentCosted, Complexity.Costed.andThen, he]
    omega

def checkAx23Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (Complexity.Costed.tick (M.sortal t w) 1) fun _ =>
        checkAx23ConsequentCosted M t w

def checkAx23 (M : FiniteModel4) : Bool :=
  (checkAx23Costed M).value

theorem checkAx23_eq_legacy (M : FiniteModel4) :
    checkAx23 M = allThings M (fun t => allWorlds M (fun w =>
      iffB (M.sortal t w)
        (M.endurantType t w && anyThings M (fun k =>
          M.kind k w && allWorlds M (fun v => allThings M (fun x =>
            impliesB (M.inst x t v) (M.inst x k v))))))) := by
  unfold checkAx23 checkAx23Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext t
  rw [allWorldsEvalCosted_value]
  simp only [Complexity.Costed.iff_value, Complexity.Costed.tick_value,
    checkAx23ConsequentCosted_value]
  congr 1
  funext w
  cases hs : M.sortal t w <;>
    cases hc : (M.endurantType t w && anyThings M (fun k =>
      M.kind k w && allWorlds M (fun v => allThings M (fun x =>
        impliesB (M.inst x t v) (M.inst x k v))))) <;> simp [iffB]

theorem checkAx23Costed_cost_le (M : FiniteModel4) :
    (checkAx23Costed M).cost ≤ M.thingCount *
      (M.worldCount *
        (M.thingCount * (M.worldCount * (M.thingCount * 6 + 2) + 4) + 7) + 2) := by
  unfold checkAx23Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 6 + 2) + 4) + 7))
  intro t
  apply allWorldsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (M.thingCount * 6 + 2) + 4) + 5)
  intro w
  have hc := checkAx23ConsequentCosted_cost_le M t w
  cases h : M.sortal t w <;>
    simp [Complexity.Costed.iff] <;> omega

/-!
Shared counted cores for the direct classification-table axioms.  Factoring
the executable shapes mirrors RadixExperiment's pass-local correspondence
style: each axiom below is a thin erasure of a proved core, while its UFO
semantic theorem remains a distinct result.
-/

def checkUnaryIffAndCosted (M : FiniteModel4)
    (left first second : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (Complexity.Costed.tick (left t w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (first t w) 1) fun _ =>
        Complexity.Costed.tick (second t w) 1

def checkUnaryIffAndNotCosted (M : FiniteModel4)
    (left first second : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (Complexity.Costed.tick (left t w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (first t w) 1) fun _ =>
        (Complexity.Costed.tick (second t w) 1).not

def checkUnaryIffOrAndCosted (M : FiniteModel4)
    (leftA leftB rightA rightB : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff
      (Complexity.Costed.orElse (Complexity.Costed.tick (leftA t w) 1) fun _ =>
        Complexity.Costed.tick (leftB t w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (rightA t w) 1) fun _ =>
        Complexity.Costed.tick (rightB t w) 1

def checkWorldFirstDisjointCosted (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allWorldsEvalCosted M fun w => allThingsEvalCosted M fun t =>
    (Complexity.Costed.andThen (Complexity.Costed.tick (left t w) 1) fun _ =>
      Complexity.Costed.tick (right t w) 1).not

theorem checkUnaryIffAndCosted_value (M : FiniteModel4) (left first second) :
    (checkUnaryIffAndCosted M left first second).value = allThings M (fun t =>
      allWorlds M (fun w => iffB (left t w) (first t w && second t w))) := by
  unfold checkUnaryIffAndCosted
  rw [allThingsEvalCosted_value]
  congr 1; funext t
  rw [allWorldsEvalCosted_value]
  congr 1; funext w
  cases hl : left t w <;> cases hf : first t w <;> cases hs : second t w <;>
    simp [Complexity.Costed.iff_value, Complexity.Costed.andThen_value, iffB]

theorem checkUnaryIffAndNotCosted_value (M : FiniteModel4) (left first second) :
    (checkUnaryIffAndNotCosted M left first second).value = allThings M (fun t =>
      allWorlds M (fun w => iffB (left t w) (first t w && !(second t w)))) := by
  unfold checkUnaryIffAndNotCosted
  rw [allThingsEvalCosted_value]
  congr 1; funext t
  rw [allWorldsEvalCosted_value]
  congr 1; funext w
  cases hl : left t w <;> cases hf : first t w <;> cases hs : second t w <;>
    simp [Complexity.Costed.iff_value, Complexity.Costed.andThen_value, iffB]

theorem checkUnaryIffOrAndCosted_value (M : FiniteModel4) (leftA leftB rightA rightB) :
    (checkUnaryIffOrAndCosted M leftA leftB rightA rightB).value =
      allThings M (fun t => allWorlds M (fun w =>
        iffB (leftA t w || leftB t w) (rightA t w && rightB t w))) := by
  unfold checkUnaryIffOrAndCosted
  rw [allThingsEvalCosted_value]
  congr 1; funext t
  rw [allWorldsEvalCosted_value]
  congr 1; funext w
  cases ha : leftA t w <;> cases hb : leftB t w <;>
    cases hc : rightA t w <;> cases hd : rightB t w <;>
      simp [Complexity.Costed.iff_value, Complexity.Costed.orElse_value,
        Complexity.Costed.andThen_value, iffB]

theorem checkWorldFirstDisjointCosted_value (M : FiniteModel4) (left right) :
    (checkWorldFirstDisjointCosted M left right).value = allWorlds M (fun w =>
      allThings M (fun t => !(left t w && right t w))) := by
  unfold checkWorldFirstDisjointCosted
  rw [allWorldsEvalCosted_value]
  congr 1; funext w
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

theorem checkUnaryIffAndCosted_cost_le (M : FiniteModel4) (left first second) :
    (checkUnaryIffAndCosted M left first second).cost ≤
      M.thingCount * (M.worldCount * 8 + 2) := by
  unfold checkUnaryIffAndCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 8)
  intro t; apply allWorldsEvalCosted_cost_le M _ 6; intro w
  cases hl : left t w <;> cases hf : first t w <;>
    simp [Complexity.Costed.iff, Complexity.Costed.andThen]

theorem checkUnaryIffAndNotCosted_cost_le (M : FiniteModel4) (left first second) :
    (checkUnaryIffAndNotCosted M left first second).cost ≤
      M.thingCount * (M.worldCount * 9 + 2) := by
  unfold checkUnaryIffAndNotCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 9)
  intro t; apply allWorldsEvalCosted_cost_le M _ 7; intro w
  cases hl : left t w <;> cases hf : first t w <;>
    simp [Complexity.Costed.iff, Complexity.Costed.andThen, Complexity.Costed.not]

theorem checkUnaryIffOrAndCosted_cost_le (M : FiniteModel4) (leftA leftB rightA rightB) :
    (checkUnaryIffOrAndCosted M leftA leftB rightA rightB).cost ≤
      M.thingCount * (M.worldCount * 10 + 2) := by
  unfold checkUnaryIffOrAndCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 10)
  intro t; apply allWorldsEvalCosted_cost_le M _ 8; intro w
  cases ha : leftA t w <;> cases hb : leftB t w <;>
    cases hc : rightA t w <;>
      simp [Complexity.Costed.iff, Complexity.Costed.orElse,
        Complexity.Costed.andThen]

theorem checkWorldFirstDisjointCosted_cost_le (M : FiniteModel4) (left right) :
    (checkWorldFirstDisjointCosted M left right).cost ≤
      M.worldCount * (M.thingCount * 6 + 2) := by
  unfold checkWorldFirstDisjointCosted
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * 6)
  intro w; apply allThingsEvalCosted_cost_le M _ 4; intro t
  cases hl : left t w <;>
    simp [Complexity.Costed.andThen, Complexity.Costed.not]

def checkAx24Costed (M : FiniteModel4) :=
  checkUnaryIffAndNotCosted M M.nonSortal M.endurantType M.sortal
def checkAx24 (M : FiniteModel4) := (checkAx24Costed M).value
theorem checkAx24_eq_legacy (M : FiniteModel4) : checkAx24 M = allThings M (fun t => allWorlds M (fun w => iffB (M.nonSortal t w) (M.endurantType t w && !(M.sortal t w)))) := checkUnaryIffAndNotCosted_value M M.nonSortal M.endurantType M.sortal
theorem checkAx24Costed_cost_le (M : FiniteModel4) : (checkAx24Costed M).cost ≤ M.thingCount * (M.worldCount * 9 + 2) := checkUnaryIffAndNotCosted_cost_le M M.nonSortal M.endurantType M.sortal

def checkAx25Costed (M : FiniteModel4) := checkWorldFirstDisjointCosted M M.kind M.subKind
def checkAx25 (M : FiniteModel4) := (checkAx25Costed M).value
theorem checkAx25_eq_legacy (M : FiniteModel4) : checkAx25 M = allWorlds M (fun w => allThings M (fun t => !(M.kind t w && M.subKind t w))) := checkWorldFirstDisjointCosted_value M M.kind M.subKind
theorem checkAx25Costed_cost_le (M : FiniteModel4) : (checkAx25Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) := checkWorldFirstDisjointCosted_cost_le M M.kind M.subKind

def checkAx26Costed (M : FiniteModel4) := checkUnaryIffOrAndCosted M M.kind M.subKind M.rigid M.sortal
def checkAx26 (M : FiniteModel4) := (checkAx26Costed M).value
theorem checkAx26_eq_legacy (M : FiniteModel4) : checkAx26 M = allThings M (fun t => allWorlds M (fun w => iffB (M.kind t w || M.subKind t w) (M.rigid t w && M.sortal t w))) := checkUnaryIffOrAndCosted_value M M.kind M.subKind M.rigid M.sortal
theorem checkAx26Costed_cost_le (M : FiniteModel4) : (checkAx26Costed M).cost ≤ M.thingCount * (M.worldCount * 10 + 2) := checkUnaryIffOrAndCosted_cost_le M M.kind M.subKind M.rigid M.sortal

def checkAx27Costed (M : FiniteModel4) := checkWorldFirstDisjointCosted M M.phase M.role
def checkAx27 (M : FiniteModel4) := (checkAx27Costed M).value
theorem checkAx27_eq_legacy (M : FiniteModel4) : checkAx27 M = allWorlds M (fun w => allThings M (fun t => !(M.phase t w && M.role t w))) := checkWorldFirstDisjointCosted_value M M.phase M.role
theorem checkAx27Costed_cost_le (M : FiniteModel4) : (checkAx27Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) := checkWorldFirstDisjointCosted_cost_le M M.phase M.role

def checkAx28Costed (M : FiniteModel4) := checkUnaryIffOrAndCosted M M.phase M.role M.antiRigid M.sortal
def checkAx28 (M : FiniteModel4) := (checkAx28Costed M).value
theorem checkAx28_eq_legacy (M : FiniteModel4) : checkAx28 M = allThings M (fun t => allWorlds M (fun w => iffB (M.phase t w || M.role t w) (M.antiRigid t w && M.sortal t w))) := checkUnaryIffOrAndCosted_value M M.phase M.role M.antiRigid M.sortal
theorem checkAx28Costed_cost_le (M : FiniteModel4) : (checkAx28Costed M).cost ≤ M.thingCount * (M.worldCount * 10 + 2) := checkUnaryIffOrAndCosted_cost_le M M.phase M.role M.antiRigid M.sortal

def checkAx29Costed (M : FiniteModel4) := checkUnaryIffAndCosted M M.semiRigidSortal M.semiRigid M.sortal
def checkAx29 (M : FiniteModel4) := (checkAx29Costed M).value
theorem checkAx29_eq_legacy (M : FiniteModel4) : checkAx29 M = allThings M (fun t => allWorlds M (fun w => iffB (M.semiRigidSortal t w) (M.semiRigid t w && M.sortal t w))) := checkUnaryIffAndCosted_value M M.semiRigidSortal M.semiRigid M.sortal
theorem checkAx29Costed_cost_le (M : FiniteModel4) : (checkAx29Costed M).cost ≤ M.thingCount * (M.worldCount * 8 + 2) := checkUnaryIffAndCosted_cost_le M M.semiRigidSortal M.semiRigid M.sortal

def checkAx30Costed (M : FiniteModel4) := checkUnaryIffAndCosted M M.category M.rigid M.nonSortal
def checkAx30 (M : FiniteModel4) := (checkAx30Costed M).value
theorem checkAx30_eq_legacy (M : FiniteModel4) : checkAx30 M = allThings M (fun t => allWorlds M (fun w => iffB (M.category t w) (M.rigid t w && M.nonSortal t w))) := checkUnaryIffAndCosted_value M M.category M.rigid M.nonSortal
theorem checkAx30Costed_cost_le (M : FiniteModel4) : (checkAx30Costed M).cost ≤ M.thingCount * (M.worldCount * 8 + 2) := checkUnaryIffAndCosted_cost_le M M.category M.rigid M.nonSortal

def checkAx31Costed (M : FiniteModel4) := checkUnaryIffAndCosted M M.mixin M.semiRigid M.nonSortal
def checkAx31 (M : FiniteModel4) := (checkAx31Costed M).value
theorem checkAx31_eq_legacy (M : FiniteModel4) : checkAx31 M = allThings M (fun t => allWorlds M (fun w => iffB (M.mixin t w) (M.semiRigid t w && M.nonSortal t w))) := checkUnaryIffAndCosted_value M M.mixin M.semiRigid M.nonSortal
theorem checkAx31Costed_cost_le (M : FiniteModel4) : (checkAx31Costed M).cost ≤ M.thingCount * (M.worldCount * 8 + 2) := checkUnaryIffAndCosted_cost_le M M.mixin M.semiRigid M.nonSortal

def checkAx32Costed (M : FiniteModel4) := checkWorldFirstDisjointCosted M M.phaseMixin M.roleMixin
def checkAx32 (M : FiniteModel4) := (checkAx32Costed M).value
theorem checkAx32_eq_legacy (M : FiniteModel4) : checkAx32 M = allWorlds M (fun w => allThings M (fun t => !(M.phaseMixin t w && M.roleMixin t w))) := checkWorldFirstDisjointCosted_value M M.phaseMixin M.roleMixin
theorem checkAx32Costed_cost_le (M : FiniteModel4) : (checkAx32Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) := checkWorldFirstDisjointCosted_cost_le M M.phaseMixin M.roleMixin

def checkAx33Costed (M : FiniteModel4) := checkUnaryIffOrAndCosted M M.phaseMixin M.roleMixin M.antiRigid M.nonSortal
def checkAx33 (M : FiniteModel4) := (checkAx33Costed M).value
theorem checkAx33_eq_legacy (M : FiniteModel4) : checkAx33 M = allThings M (fun t => allWorlds M (fun w => iffB (M.phaseMixin t w || M.roleMixin t w) (M.antiRigid t w && M.nonSortal t w))) := checkUnaryIffOrAndCosted_value M M.phaseMixin M.roleMixin M.antiRigid M.nonSortal
theorem checkAx33Costed_cost_le (M : FiniteModel4) : (checkAx33Costed M).cost ≤ M.thingCount * (M.worldCount * 10 + 2) := checkUnaryIffOrAndCosted_cost_le M M.phaseMixin M.roleMixin M.antiRigid M.nonSortal

/-!
Delayed composition for axioms 18--33.  As in the cost-aware semantics of Niu
et al., registry traversal is charged where it executes; the array entries are
thunks so a failed axiom prevents all later computations.
-/

def axiom18To33RegistryCosted (M : FiniteModel4) :
    Array Complexity.CheckThunk := #[
  fun _ => checkAx18Costed M, fun _ => checkAx19Costed M,
  fun _ => checkAx20Costed M, fun _ => checkAx21Costed M,
  fun _ => checkAx22Costed M, fun _ => checkAx23Costed M,
  fun _ => checkAx24Costed M, fun _ => checkAx25Costed M,
  fun _ => checkAx26Costed M, fun _ => checkAx27Costed M,
  fun _ => checkAx28Costed M, fun _ => checkAx29Costed M,
  fun _ => checkAx30Costed M, fun _ => checkAx31Costed M,
  fun _ => checkAx32Costed M, fun _ => checkAx33Costed M
]

def checkAxioms18To33Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.checkRegistryCosted (axiom18To33RegistryCosted M)

def checkAxioms18To33 (M : FiniteModel4) : Bool :=
  (checkAxioms18To33Costed M).value

@[simp] theorem axiom18To33RegistryCosted_size (M : FiniteModel4) :
    (axiom18To33RegistryCosted M).size = 16 := rfl

theorem checkAxioms18To33_eq_true_iff (M : FiniteModel4) :
    checkAxioms18To33 M = true ↔
      checkAx18 M = true ∧ checkAx19 M = true ∧ checkAx20 M = true ∧
      checkAx21 M = true ∧ checkAx22 M = true ∧ checkAx23 M = true ∧
      checkAx24 M = true ∧ checkAx25 M = true ∧ checkAx26 M = true ∧
      checkAx27 M = true ∧ checkAx28 M = true ∧ checkAx29 M = true ∧
      checkAx30 M = true ∧ checkAx31 M = true ∧ checkAx32 M = true ∧
      checkAx33 M = true := by
  unfold checkAxioms18To33 checkAxioms18To33Costed
    Complexity.checkRegistryCosted Complexity.allArrayCosted
  rw [Complexity.allListCosted_eq_true_iff]
  simp [axiom18To33RegistryCosted, checkAx18, checkAx19, checkAx20, checkAx21,
    checkAx22, checkAx23, checkAx24, checkAx25, checkAx26, checkAx27, checkAx28,
    checkAx29, checkAx30, checkAx31, checkAx32, checkAx33]

def axioms18To33PerCheckBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.worldCount * (M.thingCount * (6 * M.worldCount + 4) + 7) + 2) +
  M.thingCount * (M.worldCount * (M.thingCount * (7 * M.worldCount + 4) + 7) + 2) +
  M.thingCount * (M.worldCount * 12 + 2) +
  M.thingCount * (M.worldCount * (M.thingCount * (3 * M.worldCount + 4) + 5) + 2) +
  M.thingCount * (M.thingCount *
    (M.worldCount * (M.worldCount * (M.thingCount * 7 + 2) + 8) + 2) + 2) +
  M.thingCount * (M.worldCount *
    (M.thingCount * (M.worldCount * (M.thingCount * 6 + 2) + 4) + 7) + 2) +
  M.thingCount * (M.worldCount * 9 + 2) +
  M.worldCount * (M.thingCount * 6 + 2) +
  M.thingCount * (M.worldCount * 10 + 2) +
  M.thingCount * (M.worldCount * 8 + 2)

theorem checkAxioms18To33Costed_cost_le (M : FiniteModel4) :
    (checkAxioms18To33Costed M).cost ≤
      16 * (axioms18To33PerCheckBound M + 2) := by
  unfold checkAxioms18To33Costed
  apply Complexity.checkRegistryCosted_cost_le _ (axioms18To33PerCheckBound M)
  intro check hcheck
  simp [axiom18To33RegistryCosted] at hcheck
  rcases hcheck with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp
  · have h := checkAx18Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx19Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx20Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx21Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx22Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx23Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx24Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx25Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx26Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx27Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx28Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx29Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx30Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx31Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx32Costed_cost_le M; unfold axioms18To33PerCheckBound; omega
  · have h := checkAx33Costed_cost_le M; unfold axioms18To33PerCheckBound; omega

def checkTwoThingsWorldsImpCosted (M : FiniteModel4)
    (first second consequent :
      Fin M.thingCount → Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun a => allThingsEvalCosted M fun b =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.andThen (Complexity.Costed.tick (first a b w) 1) fun _ =>
          Complexity.Costed.tick (second a b w) 1) fun _ =>
        Complexity.Costed.tick (consequent a b w) 1

theorem checkTwoThingsWorldsImpCosted_value (M : FiniteModel4) (first second consequent) :
    (checkTwoThingsWorldsImpCosted M first second consequent).value =
      allThings M (fun a => allThings M (fun b => allWorlds M (fun w =>
        impliesB (first a b w && second a b w) (consequent a b w)))) := by
  unfold checkTwoThingsWorldsImpCosted
  rw [allThingsEvalCosted_value]; congr 1; funext a
  rw [allThingsEvalCosted_value]; congr 1; funext b
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value, impliesB]

theorem checkTwoThingsWorldsImpCosted_cost_le (M : FiniteModel4)
    (first second consequent) :
    (checkTwoThingsWorldsImpCosted M first second consequent).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) := by
  unfold checkTwoThingsWorldsImpCosted
  apply allThingsEvalCosted_cost_le M _ (M.thingCount * (M.worldCount * 8 + 2))
  intro a; apply allThingsEvalCosted_cost_le M _ (M.worldCount * 8)
  intro b; apply allWorldsEvalCosted_cost_le M _ 6; intro w
  cases hf : first a b w <;> cases hs : second a b w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not]

def checkThingWorldWorldImpCosted (M : FiniteModel4)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allWorldsEvalCosted M fun w =>
    allWorldsEvalCosted M fun v =>
      Complexity.Costed.implies (Complexity.Costed.tick (left t w) 1) fun _ =>
        Complexity.Costed.tick (right t v) 1

theorem checkThingWorldWorldImpCosted_value (M : FiniteModel4) (left right) :
    (checkThingWorldWorldImpCosted M left right).value = allThings M (fun t =>
      allWorlds M (fun w => allWorlds M (fun v => impliesB (left t w) (right t v)))) := by
  unfold checkThingWorldWorldImpCosted
  rw [allThingsEvalCosted_value]; congr 1; funext t
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem checkThingWorldWorldImpCosted_cost_le (M : FiniteModel4) (left right) :
    (checkThingWorldWorldImpCosted M left right).cost ≤
      M.thingCount * (M.worldCount * (M.worldCount * 6 + 2) + 2) := by
  unfold checkThingWorldWorldImpCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (M.worldCount * 6 + 2))
  intro t; apply allWorldsEvalCosted_cost_le M _ (M.worldCount * 6)
  intro w; apply allWorldsEvalCosted_cost_le M _ 4; intro v
  cases hl : left t w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse, Complexity.Costed.not]

def checkAxInstEndurantCosted (M : FiniteModel4) :=
  checkTwoThingsWorldsImpCosted M
    (fun t _ w => M.endurantType t w) (fun t x w => M.inst x t w)
    (fun _ x w => M.endurant x w)
def checkAxInstEndurant (M : FiniteModel4) := (checkAxInstEndurantCosted M).value
theorem checkAxInstEndurant_eq_legacy (M : FiniteModel4) :
    checkAxInstEndurant M = allThings M (fun t => allThings M (fun x =>
      allWorlds M (fun w => impliesB (M.endurantType t w && M.inst x t w)
        (M.endurant x w)))) := checkTwoThingsWorldsImpCosted_value M _ _ _
theorem checkAxInstEndurantCosted_cost_le (M : FiniteModel4) :
    (checkAxInstEndurantCosted M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  checkTwoThingsWorldsImpCosted_cost_le M _ _ _

def checkAxSubKindSortalCosted (M : FiniteModel4) :=
  checkTwoThingsWorldsImpCosted M (fun a k w => M.sub a k w)
    (fun _ k w => M.kind k w) (fun a _ w => M.sortal a w)
def checkAxSubKindSortal (M : FiniteModel4) := (checkAxSubKindSortalCosted M).value
theorem checkAxSubKindSortal_eq_legacy (M : FiniteModel4) :
    checkAxSubKindSortal M = allThings M (fun a => allThings M (fun k =>
      allWorlds M (fun w => impliesB (M.sub a k w && M.kind k w)
        (M.sortal a w)))) := checkTwoThingsWorldsImpCosted_value M _ _ _
theorem checkAxSubKindSortalCosted_cost_le (M : FiniteModel4) :
    (checkAxSubKindSortalCosted M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  checkTwoThingsWorldsImpCosted_cost_le M _ _ _

def checkAxNonSortalUpCosted (M : FiniteModel4) :=
  checkTwoThingsWorldsImpCosted M (fun a _ w => M.nonSortal a w)
    (fun a b w => M.sub a b w) (fun _ b w => M.nonSortal b w)
def checkAxNonSortalUp (M : FiniteModel4) := (checkAxNonSortalUpCosted M).value
theorem checkAxNonSortalUp_eq_legacy (M : FiniteModel4) :
    checkAxNonSortalUp M = allThings M (fun a => allThings M (fun b =>
      allWorlds M (fun w => impliesB (M.nonSortal a w && M.sub a b w)
        (M.nonSortal b w)))) := checkTwoThingsWorldsImpCosted_value M _ _ _
theorem checkAxNonSortalUpCosted_cost_le (M : FiniteModel4) :
    (checkAxNonSortalUpCosted M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  checkTwoThingsWorldsImpCosted_cost_le M _ _ _

def checkAxKindStableCosted (M : FiniteModel4) :=
  checkThingWorldWorldImpCosted M M.kind M.kind
def checkAxKindStable (M : FiniteModel4) := (checkAxKindStableCosted M).value
theorem checkAxKindStable_eq_legacy (M : FiniteModel4) :
    checkAxKindStable M = allThings M (fun k => allWorlds M (fun w =>
      allWorlds M (fun v => impliesB (M.kind k w) (M.kind k v)))) :=
  checkThingWorldWorldImpCosted_value M M.kind M.kind
theorem checkAxKindStableCosted_cost_le (M : FiniteModel4) :
    (checkAxKindStableCosted M).cost ≤
      M.thingCount * (M.worldCount * (M.worldCount * 6 + 2) + 2) :=
  checkThingWorldWorldImpCosted_cost_le M M.kind M.kind

/-!
Operational existence-and-uniqueness for qualities.  This replaces the former
opaque `decide (∃! ...)` with the actual finite candidate and competitor scans.
The explicit equality charge follows the unit-cost model; keeping production as
the counted erasure follows the implementation-correspondence methodology of
Forster et al. and the verified-interpreter organization exemplified by
RadixExperiment.
-/

def qualityCandidateCosted (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.qualityKind t w) 1) fun _ =>
    Complexity.Costed.tick (M.inst x t w) 1

theorem qualityCandidateCosted_value (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (qualityCandidateCosted M x t w).value =
      (M.qualityKind t w && M.inst x t w) := by
  unfold qualityCandidateCosted
  cases h : M.qualityKind t w <;> simp [Complexity.Costed.andThen]

theorem qualityCandidateCosted_cost_le (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) : (qualityCandidateCosted M x t w).cost ≤ 3 := by
  unfold qualityCandidateCosted
  cases h : M.qualityKind t w <;> simp [Complexity.Costed.andThen]

def qualityUniqueForCosted (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t' =>
    Complexity.Costed.implies (qualityCandidateCosted M x t' w) fun _ =>
      Complexity.Costed.tick (decide (t' = t)) 1

theorem qualityUniqueForCosted_value (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (qualityUniqueForCosted M x t w).value = allThings M (fun t' =>
      impliesB (M.qualityKind t' w && M.inst x t' w) (decide (t' = t))) := by
  unfold qualityUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, qualityCandidateCosted_value, impliesB]

theorem qualityUniqueForCosted_cost_le (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (qualityUniqueForCosted M x t w).cost ≤ M.thingCount * 8 := by
  unfold qualityUniqueForCosted
  apply allThingsEvalCosted_cost_le M _ 6
  intro t'
  have hc := qualityCandidateCosted_cost_le M x t' w
  cases h : (qualityCandidateCosted M x t' w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def qualityWitnessCosted (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityCandidateCosted M x t w) fun _ =>
    qualityUniqueForCosted M x t w

theorem qualityWitnessCosted_value (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (qualityWitnessCosted M x t w).value =
      ((M.qualityKind t w && M.inst x t w) && allThings M (fun t' =>
        impliesB (M.qualityKind t' w && M.inst x t' w) (decide (t' = t)))) := by
  simp [qualityWitnessCosted, Complexity.Costed.andThen_value,
    qualityCandidateCosted_value, qualityUniqueForCosted_value]

theorem qualityWitnessCosted_cost_le (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (qualityWitnessCosted M x t w).cost ≤ M.thingCount * 8 + 4 := by
  have hc := qualityCandidateCosted_cost_le M x t w
  have hu := qualityUniqueForCosted_cost_le M x t w
  cases h : (qualityCandidateCosted M x t w).value <;>
    simp [qualityWitnessCosted, Complexity.Costed.andThen, h] <;> omega

def qualityBCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun t => qualityWitnessCosted M x t w

def qualityB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (qualityBCosted M x w).value

theorem qualityBCosted_cost_le (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (qualityBCosted M x w).cost ≤ M.thingCount * (M.thingCount * 8 + 6) := by
  unfold qualityBCosted
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 8 + 4)
  intro t
  exact qualityWitnessCosted_cost_le M x t w

theorem qualityB_eq_legacy (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    qualityB M x w = decide
      (∃ t : Fin M.thingCount,
        (M.qualityKind t w = true ∧ M.inst x t w = true) ∧
          ∀ t' : Fin M.thingCount,
            M.qualityKind t' w = true ∧ M.inst x t' w = true → t' = t) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  unfold qualityB qualityBCosted
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff]
  simp [qualityWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

def qualityStructureB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ t : Fin M.thingCount,
      (M.qualityType t w = true ∧ M.associatedWith x t w = true) ∧
        ∀ t' : Fin M.thingCount,
          M.qualityType t' w = true ∧ M.associatedWith x t' w = true → t' = t)

def simpleQualityB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  qualityB M x w && (allThings M fun y => !(M.inheresIn y x w))

def complexQualityB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  qualityB M x w && !(simpleQualityB M x w)

def simpleQualityTypeB (M : FiniteModel4) (t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.qualityType t w &&
    (allThings M fun x => impliesB (M.inst x t w) (simpleQualityB M x w))

def complexQualityTypeB (M : FiniteModel4) (t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.qualityType t w &&
    (allThings M fun x => impliesB (M.inst x t w) (complexQualityB M x w))

def nonEmptySetB (M : FiniteModel4) (s : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  anyThings M fun x => M.memberOf x s w

def properSubsetB (M : FiniteModel4) (s t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (allThings M fun x => impliesB (M.memberOf x s w) (M.memberOf x t w)) &&
    (anyThings M fun x => M.memberOf x t w && !(M.memberOf x s w))

def existsUniqueQualityStructureMemberB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ s : Fin M.thingCount,
      (qualityStructureB M s w = true ∧ M.memberOf x s w = true) ∧
        ∀ s' : Fin M.thingCount,
          qualityStructureB M s' w = true ∧ M.memberOf x s' w = true → s' = s)

def existsUniqueHasValueB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ y : Fin M.thingCount,
      M.hasValue x y w = true ∧
        ∀ y' : Fin M.thingCount, M.hasValue x y' w = true → y' = y)

def checkUnaryIffOrSingleCosted (M : FiniteModel4)
    (leftA leftB right : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff
      (Complexity.Costed.orElse (Complexity.Costed.tick (leftA x w) 1) fun _ =>
        Complexity.Costed.tick (leftB x w) 1) fun _ =>
      Complexity.Costed.tick (right x w) 1

theorem checkUnaryIffOrSingleCosted_value (M : FiniteModel4) (leftA leftB right) :
    (checkUnaryIffOrSingleCosted M leftA leftB right).value = allThings M (fun x =>
      allWorlds M (fun w => iffB (leftA x w || leftB x w) (right x w))) := by
  unfold checkUnaryIffOrSingleCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  cases ha : leftA x w <;> cases hb : leftB x w <;> cases hr : right x w <;>
    simp [Complexity.Costed.iff_value, Complexity.Costed.orElse_value, iffB]

theorem checkUnaryIffOrSingleCosted_cost_le (M : FiniteModel4) (leftA leftB right) :
    (checkUnaryIffOrSingleCosted M leftA leftB right).cost ≤
      M.thingCount * (M.worldCount * 8 + 2) := by
  unfold checkUnaryIffOrSingleCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 8)
  intro x; apply allWorldsEvalCosted_cost_le M _ 6; intro w
  cases ha : leftA x w <;> cases hb : leftB x w <;>
    simp [Complexity.Costed.iff, Complexity.Costed.orElse]

def checkAx34Costed (M : FiniteModel4) :=
  checkUnaryIffOrSingleCosted M M.substantial M.moment M.endurant

def checkAx34 (M : FiniteModel4) := (checkAx34Costed M).value

theorem checkAx34_eq_legacy (M : FiniteModel4) :
    checkAx34 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (M.substantial x w || M.moment x w) (M.endurant x w))) :=
  checkUnaryIffOrSingleCosted_value M M.substantial M.moment M.endurant

theorem checkAx34Costed_cost_le (M : FiniteModel4) :
    (checkAx34Costed M).cost ≤ M.thingCount * (M.worldCount * 8 + 2) :=
  checkUnaryIffOrSingleCosted_cost_le M M.substantial M.moment M.endurant

def checkUnaryIffThreeOrSingleCosted (M : FiniteModel4)
    (leftA leftB leftC right : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff
      (Complexity.Costed.orElse (Complexity.Costed.tick (leftA x w) 1) fun _ =>
        Complexity.Costed.orElse (Complexity.Costed.tick (leftB x w) 1) fun _ =>
          Complexity.Costed.tick (leftC x w) 1) fun _ =>
      Complexity.Costed.tick (right x w) 1

theorem checkUnaryIffThreeOrSingleCosted_value (M : FiniteModel4)
    (leftA leftB leftC right) :
    (checkUnaryIffThreeOrSingleCosted M leftA leftB leftC right).value =
      allThings M (fun x => allWorlds M (fun w =>
        iffB (leftA x w || leftB x w || leftC x w) (right x w))) := by
  unfold checkUnaryIffThreeOrSingleCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  cases ha : leftA x w <;> cases hb : leftB x w <;>
    cases hc : leftC x w <;> cases hr : right x w <;>
      simp [Complexity.Costed.iff_value, Complexity.Costed.orElse_value, iffB]

theorem checkUnaryIffThreeOrSingleCosted_cost_le (M : FiniteModel4)
    (leftA leftB leftC right) :
    (checkUnaryIffThreeOrSingleCosted M leftA leftB leftC right).cost ≤
      M.thingCount * (M.worldCount * 10 + 2) := by
  unfold checkUnaryIffThreeOrSingleCosted
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 10)
  intro x; apply allWorldsEvalCosted_cost_le M _ 8; intro w
  cases ha : leftA x w <;> cases hb : leftB x w <;>
    cases hc : leftC x w <;>
      simp [Complexity.Costed.iff, Complexity.Costed.orElse]

def checkAx35Costed (M : FiniteModel4) :=
  checkWorldFirstDisjointCosted M M.substantial M.moment
def checkAx35 (M : FiniteModel4) := (checkAx35Costed M).value
theorem checkAx35_eq_legacy (M : FiniteModel4) :
    checkAx35 M = allWorlds M (fun w => allThings M (fun x =>
      !(M.substantial x w && M.moment x w))) :=
  checkWorldFirstDisjointCosted_value M M.substantial M.moment
theorem checkAx35Costed_cost_le (M : FiniteModel4) :
    (checkAx35Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) :=
  checkWorldFirstDisjointCosted_cost_le M M.substantial M.moment

def checkAx36Costed (M : FiniteModel4) :=
  checkUnaryIffThreeOrSingleCosted M M.object M.collective M.quantity M.substantial
def checkAx36 (M : FiniteModel4) := (checkAx36Costed M).value
theorem checkAx36_eq_legacy (M : FiniteModel4) :
    checkAx36 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (M.object x w || M.collective x w || M.quantity x w)
        (M.substantial x w))) :=
  checkUnaryIffThreeOrSingleCosted_value M M.object M.collective M.quantity M.substantial
theorem checkAx36Costed_cost_le (M : FiniteModel4) :
    (checkAx36Costed M).cost ≤ M.thingCount * (M.worldCount * 10 + 2) :=
  checkUnaryIffThreeOrSingleCosted_cost_le M M.object M.collective M.quantity M.substantial

def checkAx37Costed (M : FiniteModel4) := checkWorldFirstDisjointCosted M M.object M.collective
def checkAx37 (M : FiniteModel4) := (checkAx37Costed M).value
theorem checkAx37_eq_legacy (M : FiniteModel4) : checkAx37 M = allWorlds M (fun w => allThings M (fun x => !(M.object x w && M.collective x w))) := checkWorldFirstDisjointCosted_value M M.object M.collective
theorem checkAx37Costed_cost_le (M : FiniteModel4) : (checkAx37Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) := checkWorldFirstDisjointCosted_cost_le M M.object M.collective

def checkAx38Costed (M : FiniteModel4) := checkWorldFirstDisjointCosted M M.object M.quantity
def checkAx38 (M : FiniteModel4) := (checkAx38Costed M).value
theorem checkAx38_eq_legacy (M : FiniteModel4) : checkAx38 M = allWorlds M (fun w => allThings M (fun x => !(M.object x w && M.quantity x w))) := checkWorldFirstDisjointCosted_value M M.object M.quantity
theorem checkAx38Costed_cost_le (M : FiniteModel4) : (checkAx38Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) := checkWorldFirstDisjointCosted_cost_le M M.object M.quantity

def checkAx39Costed (M : FiniteModel4) := checkWorldFirstDisjointCosted M M.collective M.quantity
def checkAx39 (M : FiniteModel4) := (checkAx39Costed M).value
theorem checkAx39_eq_legacy (M : FiniteModel4) : checkAx39 M = allWorlds M (fun w => allThings M (fun x => !(M.collective x w && M.quantity x w))) := checkWorldFirstDisjointCosted_value M M.collective M.quantity
theorem checkAx39Costed_cost_le (M : FiniteModel4) : (checkAx39Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) := checkWorldFirstDisjointCosted_cost_le M M.collective M.quantity

def checkAx40Costed (M : FiniteModel4) :=
  checkUnaryIffOrSingleCosted M M.relator M.intrinsicMoment M.moment
def checkAx40 (M : FiniteModel4) := (checkAx40Costed M).value
theorem checkAx40_eq_legacy (M : FiniteModel4) : checkAx40 M = allThings M (fun x => allWorlds M (fun w => iffB (M.relator x w || M.intrinsicMoment x w) (M.moment x w))) := checkUnaryIffOrSingleCosted_value M M.relator M.intrinsicMoment M.moment
theorem checkAx40Costed_cost_le (M : FiniteModel4) : (checkAx40Costed M).cost ≤ M.thingCount * (M.worldCount * 8 + 2) := checkUnaryIffOrSingleCosted_cost_le M M.relator M.intrinsicMoment M.moment

def checkAx41Costed (M : FiniteModel4) := checkWorldFirstDisjointCosted M M.relator M.intrinsicMoment
def checkAx41 (M : FiniteModel4) := (checkAx41Costed M).value
theorem checkAx41_eq_legacy (M : FiniteModel4) : checkAx41 M = allWorlds M (fun w => allThings M (fun x => !(M.relator x w && M.intrinsicMoment x w))) := checkWorldFirstDisjointCosted_value M M.relator M.intrinsicMoment
theorem checkAx41Costed_cost_le (M : FiniteModel4) : (checkAx41Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) := checkWorldFirstDisjointCosted_cost_le M M.relator M.intrinsicMoment

def ax42LeftCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.orElse (Complexity.Costed.tick (M.mode x w) 1) fun _ =>
    qualityBCosted M x w

theorem ax42LeftCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax42LeftCosted M x w).value = (M.mode x w || qualityB M x w) := by
  simp [ax42LeftCosted, Complexity.Costed.orElse_value, qualityB]

theorem ax42LeftCosted_cost_le (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax42LeftCosted M x w).cost ≤ M.thingCount * (M.thingCount * 8 + 6) + 2 := by
  have hq := qualityBCosted_cost_le M x w
  cases hm : M.mode x w
  · simp [ax42LeftCosted, Complexity.Costed.orElse, hm]
    omega
  · simp [ax42LeftCosted, Complexity.Costed.orElse, hm]

def checkAx42Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (ax42LeftCosted M x w) fun _ =>
      Complexity.Costed.tick (M.intrinsicMoment x w) 1

def checkAx42 (M : FiniteModel4) : Bool := (checkAx42Costed M).value

theorem checkAx42_eq_legacy (M : FiniteModel4) :
    checkAx42 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (M.mode x w || qualityB M x w) (M.intrinsicMoment x w))) := by
  unfold checkAx42 checkAx42Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value, ax42LeftCosted_value]
  cases hl : (M.mode x w || qualityB M x w) <;>
    cases hr : M.intrinsicMoment x w <;> simp [iffB]

theorem checkAx42Costed_cost_le (M : FiniteModel4) :
    (checkAx42Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (M.thingCount * 8 + 6) + 7) + 2) := by
  unfold checkAx42Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * (M.thingCount * 8 + 6) + 7))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * 8 + 6) + 5)
  intro w
  have hl := ax42LeftCosted_cost_le M x w
  cases h : (ax42LeftCosted M x w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def ax43BodyCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  (Complexity.Costed.andThen (Complexity.Costed.tick (M.mode x w) 1) fun _ =>
    qualityBCosted M x w).not

theorem ax43BodyCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax43BodyCosted M x w).value = !(M.mode x w && qualityB M x w) := by
  simp [ax43BodyCosted, Complexity.Costed.andThen_value, qualityB]

theorem ax43BodyCosted_cost_le (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax43BodyCosted M x w).cost ≤ M.thingCount * (M.thingCount * 8 + 6) + 3 := by
  have hq := qualityBCosted_cost_le M x w
  cases hm : M.mode x w
  · simp [ax43BodyCosted, Complexity.Costed.andThen, Complexity.Costed.not, hm]
  · simp [ax43BodyCosted, Complexity.Costed.andThen, Complexity.Costed.not, hm]
    omega

def checkAx43Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allWorldsEvalCosted M fun w => allThingsEvalCosted M fun x => ax43BodyCosted M x w

def checkAx43 (M : FiniteModel4) : Bool := (checkAx43Costed M).value

theorem checkAx43_eq_legacy (M : FiniteModel4) :
    checkAx43 M = allWorlds M (fun w => allThings M (fun x =>
      !(M.mode x w && qualityB M x w))) := by
  unfold checkAx43 checkAx43Costed
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [allThingsEvalCosted_value]
  simp [ax43BodyCosted_value]

theorem checkAx43Costed_cost_le (M : FiniteModel4) :
    (checkAx43Costed M).cost ≤ M.worldCount *
      (M.thingCount * (M.thingCount * (M.thingCount * 8 + 6) + 5) + 2) := by
  unfold checkAx43Costed
  apply allWorldsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.thingCount * 8 + 6) + 5))
  intro w
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * 8 + 6) + 3)
  intro x
  exact ax43BodyCosted_cost_le M x w

def typeInstancesConditionCosted (M : FiniteModel4) (t : Fin M.thingCount)
    (leaf : Fin M.thingCount → Fin M.worldCount → Complexity.Costed Bool) :
    Complexity.Costed Bool :=
  allWorldsEvalCosted M fun v => allThingsEvalCosted M fun x =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.inst x t v) 1) fun _ =>
      leaf x v

theorem typeInstancesConditionCosted_value (M : FiniteModel4) (t : Fin M.thingCount)
    (leaf : Fin M.thingCount → Fin M.worldCount → Complexity.Costed Bool) :
    (typeInstancesConditionCosted M t leaf).value = allWorlds M (fun v =>
      allThings M (fun x => impliesB (M.inst x t v) (leaf x v).value)) := by
  unfold typeInstancesConditionCosted
  rw [allWorldsEvalCosted_value]; congr 1; funext v
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem typeInstancesConditionCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount)
    (leaf : Fin M.thingCount → Fin M.worldCount → Complexity.Costed Bool)
    (leafBound : Nat) (hLeaf : ∀ x v, (leaf x v).cost ≤ leafBound) :
    (typeInstancesConditionCosted M t leaf).cost ≤
      M.worldCount * (M.thingCount * (leafBound + 5) + 2) := by
  unfold typeInstancesConditionCosted
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * (leafBound + 5))
  intro v
  apply allThingsEvalCosted_cost_le M _ (leafBound + 3)
  intro x
  have hl := hLeaf x v
  cases hi : M.inst x t v <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def typeByInstancesEvalCosted (M : FiniteModel4)
    (typePred : Fin M.thingCount → Fin M.worldCount → Bool)
    (leaf : Fin M.thingCount → Fin M.worldCount → Complexity.Costed Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (Complexity.Costed.tick (typePred t w) 1) fun _ =>
      Complexity.Costed.andThen (typeBCosted M t w) fun _ =>
        typeInstancesConditionCosted M t leaf

theorem typeByInstancesEvalCosted_value (M : FiniteModel4) (typePred leaf) :
    (typeByInstancesEvalCosted M typePred leaf).value = allThings M (fun t =>
      allWorlds M (fun w => iffB (typePred t w)
        (typeB M t w && allWorlds M (fun v => allThings M (fun x =>
          impliesB (M.inst x t v) (leaf x v).value))))) := by
  unfold typeByInstancesEvalCosted
  rw [allThingsEvalCosted_value]; congr 1; funext t
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value, Complexity.Costed.andThen_value,
    typeBCosted_value, typeInstancesConditionCosted_value]
  cases hl : typePred t w <;>
    cases hr : (typeB M t w && allWorlds M (fun v => allThings M (fun x =>
      impliesB (M.inst x t v) (leaf x v).value))) <;> simp [iffB]

theorem typeByInstancesEvalCosted_cost_le (M : FiniteModel4) (typePred leaf)
    (leafBound : Nat) (hLeaf : ∀ x v, (leaf x v).cost ≤ leafBound) :
    (typeByInstancesEvalCosted M typePred leaf).cost ≤ M.thingCount *
      (M.worldCount *
        (M.worldCount * (M.thingCount * 3 + 2) +
          M.worldCount * (M.thingCount * (leafBound + 5) + 2) + 6) + 2) := by
  unfold typeByInstancesEvalCosted
  let q := M.worldCount * (M.thingCount * 3 + 2)
  let c := M.worldCount * (M.thingCount * (leafBound + 5) + 2)
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (q + c + 6))
  intro t
  apply allWorldsEvalCosted_cost_le M _ (q + c + 4)
  intro w
  have ht := typeBCosted_cost_le M t w
  have hc := typeInstancesConditionCosted_cost_le M t leaf leafBound hLeaf
  cases hp : typePred t w <;> cases hb : typeB M t w <;>
    simp [Complexity.Costed.iff, Complexity.Costed.andThen,
      typeBCosted_value, hb] <;>
    dsimp [q, c] at * <;> omega

def typeByInstancesCosted (M : FiniteModel4)
    (typePred leafPred : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  typeByInstancesEvalCosted M typePred fun x w => Complexity.Costed.tick (leafPred x w) 1

def typeByInstancesB (M : FiniteModel4)
    (typePred leafPred : Fin M.thingCount → Fin M.worldCount → Bool) : Bool :=
  (typeByInstancesCosted M typePred leafPred).value

theorem typeByInstancesB_eq_legacy (M : FiniteModel4) (typePred leafPred) :
    typeByInstancesB M typePred leafPred = allThings M (fun t =>
      allWorlds M (fun w => iffB (typePred t w)
        (typeB M t w && allWorlds M (fun v => allThings M (fun x =>
          impliesB (M.inst x t v) (leafPred x v)))))) := by
  exact typeByInstancesEvalCosted_value M typePred _

theorem typeByInstancesCosted_cost_le (M : FiniteModel4) (typePred leafPred) :
    (typeByInstancesCosted M typePred leafPred).cost ≤ M.thingCount *
      (M.worldCount *
        (M.worldCount * (M.thingCount * 3 + 2) +
          M.worldCount * (M.thingCount * 6 + 2) + 6) + 2) := by
  apply typeByInstancesEvalCosted_cost_le M typePred _ 1
  intro x v
  simp

/-!
Axiom 44 uses a delayed registry. Nine families have unit-cost
leaf predicates; the quality family instead reuses the counted uniqueness scan.
Keeping those bounds separate prevents the quadratic quality test from being
silently presented as a primitive table lookup.  The delayed organization also
mirrors the verified-interpreter structure exemplified by RadixExperiment,
while the quantitative theorem remains a distinct operational guarantee.
-/

def ax44DirectFamilyBound (M : FiniteModel4) : Nat :=
  M.thingCount *
    (M.worldCount *
      (M.worldCount * (M.thingCount * 3 + 2) +
        M.worldCount * (M.thingCount * 6 + 2) + 6) + 2)

def ax44QualityFamilyBound (M : FiniteModel4) : Nat :=
  M.thingCount *
    (M.worldCount *
      (M.worldCount * (M.thingCount * 3 + 2) +
        M.worldCount *
          (M.thingCount * (M.thingCount * (M.thingCount * 8 + 6) + 5) + 2) +
        6) + 2)

def checkAx44QualityCosted (M : FiniteModel4) : Complexity.Costed Bool :=
  typeByInstancesEvalCosted M M.qualityType (qualityBCosted M)

theorem checkAx44QualityCosted_value (M : FiniteModel4) :
    (checkAx44QualityCosted M).value =
      typeByInstancesB M M.qualityType (qualityB M) := by
  unfold checkAx44QualityCosted typeByInstancesB typeByInstancesCosted
  rw [typeByInstancesEvalCosted_value, typeByInstancesEvalCosted_value]
  rfl

theorem checkAx44QualityCosted_cost_le (M : FiniteModel4) :
    (checkAx44QualityCosted M).cost ≤ ax44QualityFamilyBound M := by
  unfold checkAx44QualityCosted ax44QualityFamilyBound
  apply typeByInstancesEvalCosted_cost_le M M.qualityType _
    (M.thingCount * (M.thingCount * 8 + 6))
  exact qualityBCosted_cost_le M

def axiom44RegistryCosted (M : FiniteModel4) : Array Complexity.CheckThunk := #[
  fun _ => typeByInstancesCosted M M.endurantType M.endurant,
  fun _ => typeByInstancesCosted M M.perdurantType M.perdurant,
  fun _ => typeByInstancesCosted M M.substantialType M.substantial,
  fun _ => typeByInstancesCosted M M.momentType M.moment,
  fun _ => typeByInstancesCosted M M.objectType M.object,
  fun _ => typeByInstancesCosted M M.collectiveType M.collective,
  fun _ => typeByInstancesCosted M M.quantityType M.quantity,
  fun _ => typeByInstancesCosted M M.relatorType M.relator,
  fun _ => typeByInstancesCosted M M.modeType M.mode,
  fun _ => checkAx44QualityCosted M
]

@[simp] theorem axiom44RegistryCosted_size (M : FiniteModel4) :
    (axiom44RegistryCosted M).size = 10 := rfl

def checkAx44Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.checkRegistryCosted (axiom44RegistryCosted M)

def checkAx44 (M : FiniteModel4) : Bool := (checkAx44Costed M).value

theorem checkAx44_eq_legacy (M : FiniteModel4) :
    checkAx44 M =
      (typeByInstancesB M M.endurantType M.endurant &&
       typeByInstancesB M M.perdurantType M.perdurant &&
       typeByInstancesB M M.substantialType M.substantial &&
       typeByInstancesB M M.momentType M.moment &&
       typeByInstancesB M M.objectType M.object &&
       typeByInstancesB M M.collectiveType M.collective &&
       typeByInstancesB M M.quantityType M.quantity &&
       typeByInstancesB M M.relatorType M.relator &&
       typeByInstancesB M M.modeType M.mode &&
       typeByInstancesB M M.qualityType (qualityB M)) := by
  apply Bool.eq_iff_iff.mpr
  unfold checkAx44 checkAx44Costed Complexity.checkRegistryCosted
    Complexity.allArrayCosted
  rw [Complexity.allListCosted_eq_true_iff]
  simp [axiom44RegistryCosted, typeByInstancesB, checkAx44QualityCosted_value]
  grind

def ax44CostBound (M : FiniteModel4) : Nat :=
  9 * (ax44DirectFamilyBound M + 2) + ax44QualityFamilyBound M + 2

theorem checkAx44Costed_cost_le (M : FiniteModel4) :
    (checkAx44Costed M).cost ≤ ax44CostBound M := by
  have hd1 := typeByInstancesCosted_cost_le M M.endurantType M.endurant
  have hd2 := typeByInstancesCosted_cost_le M M.perdurantType M.perdurant
  have hd3 := typeByInstancesCosted_cost_le M M.substantialType M.substantial
  have hd4 := typeByInstancesCosted_cost_le M M.momentType M.moment
  have hd5 := typeByInstancesCosted_cost_le M M.objectType M.object
  have hd6 := typeByInstancesCosted_cost_le M M.collectiveType M.collective
  have hd7 := typeByInstancesCosted_cost_le M M.quantityType M.quantity
  have hd8 := typeByInstancesCosted_cost_le M M.relatorType M.relator
  have hd9 := typeByInstancesCosted_cost_le M M.modeType M.mode
  have hq := checkAx44QualityCosted_cost_le M
  unfold checkAx44Costed Complexity.checkRegistryCosted Complexity.allArrayCosted
  simp only [axiom44RegistryCosted]
  simp only [Complexity.allListCosted]
  cases h1 : (typeByInstancesCosted M M.endurantType M.endurant).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge, h1,
      Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h2 : (typeByInstancesCosted M M.perdurantType M.perdurant).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge, h1, h2,
      Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h3 : (typeByInstancesCosted M M.substantialType M.substantial).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge, h1, h2, h3,
      Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h4 : (typeByInstancesCosted M M.momentType M.moment).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge, h1, h2, h3, h4,
      Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h5 : (typeByInstancesCosted M M.objectType M.object).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge,
      h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h6 : (typeByInstancesCosted M M.collectiveType M.collective).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge,
      h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h7 : (typeByInstancesCosted M M.quantityType M.quantity).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge,
      h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h8 : (typeByInstancesCosted M M.relatorType M.relator).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge,
      h1, h2, h3, h4, h5, h6, h7, h8,
      Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases h9 : (typeByInstancesCosted M M.modeType M.mode).value
  · simp only [Complexity.Costed.andThen, Complexity.Costed.charge,
      h1, h2, h3, h4, h5, h6, h7, h8, h9,
      Bool.false_eq_true, ↓reduceIte]
    unfold ax44CostBound ax44DirectFamilyBound at *
    omega
  cases hqv : (checkAx44QualityCosted M).value <;>
    simp only [Complexity.Costed.andThen, Complexity.Costed.charge,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, hqv,
      Bool.false_eq_true, ↓reduceIte,
      Complexity.Costed.pure_cost] <;>
    unfold ax44CostBound ax44DirectFamilyBound at * <;> omega

def kindByTypeCosted
    (M : FiniteModel4)
    (kindPred typePred : Fin M.thingCount → Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  checkUnaryIffAndCosted M kindPred typePred M.kind

def kindByTypeB
    (M : FiniteModel4)
    (kindPred typePred : Fin M.thingCount → Fin M.worldCount → Bool) : Bool :=
  (kindByTypeCosted M kindPred typePred).value

theorem kindByTypeB_eq_legacy (M : FiniteModel4) (kindPred typePred) :
    kindByTypeB M kindPred typePred = allThings M (fun t =>
      allWorlds M (fun w => iffB (kindPred t w) (typePred t w && M.kind t w))) :=
  checkUnaryIffAndCosted_value M kindPred typePred M.kind

theorem kindByTypeCosted_cost_le (M : FiniteModel4) (kindPred typePred) :
    (kindByTypeCosted M kindPred typePred).cost ≤
      M.thingCount * (M.worldCount * 8 + 2) :=
  checkUnaryIffAndCosted_cost_le M kindPred typePred M.kind

def axiom45RegistryCosted (M : FiniteModel4) : Array Complexity.CheckThunk := #[
  fun _ => kindByTypeCosted M M.objectKind M.objectType,
  fun _ => kindByTypeCosted M M.collectiveKind M.collectiveType,
  fun _ => kindByTypeCosted M M.quantityKind M.quantityType,
  fun _ => kindByTypeCosted M M.relatorKind M.relatorType,
  fun _ => kindByTypeCosted M M.modeKind M.modeType,
  fun _ => kindByTypeCosted M M.qualityKind M.qualityType
]

@[simp] theorem axiom45RegistryCosted_size (M : FiniteModel4) :
    (axiom45RegistryCosted M).size = 6 := rfl

def checkAx45Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.checkRegistryCosted (axiom45RegistryCosted M)

def checkAx45 (M : FiniteModel4) : Bool := (checkAx45Costed M).value

theorem checkAx45_eq_legacy (M : FiniteModel4) :
    checkAx45 M =
      (kindByTypeB M M.objectKind M.objectType &&
       kindByTypeB M M.collectiveKind M.collectiveType &&
       kindByTypeB M M.quantityKind M.quantityType &&
       kindByTypeB M M.relatorKind M.relatorType &&
       kindByTypeB M M.modeKind M.modeType &&
       kindByTypeB M M.qualityKind M.qualityType) := by
  apply Bool.eq_iff_iff.mpr
  unfold checkAx45 checkAx45Costed Complexity.checkRegistryCosted
    Complexity.allArrayCosted
  rw [Complexity.allListCosted_eq_true_iff]
  simp [axiom45RegistryCosted, kindByTypeB]
  grind

theorem checkAx45Costed_cost_le (M : FiniteModel4) :
    (checkAx45Costed M).cost ≤
      6 * (M.thingCount * (M.worldCount * 8 + 2) + 2) := by
  unfold checkAx45Costed
  apply Complexity.checkRegistryCosted_cost_le _
    (M.thingCount * (M.worldCount * 8 + 2))
  intro check hcheck
  simp [axiom45RegistryCosted] at hcheck
  rcases hcheck with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp
  all_goals exact kindByTypeCosted_cost_le M _ _

def specificEndurantKindCosted (M : FiniteModel4) (k : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.orElse (Complexity.Costed.tick (M.objectKind k w) 1) fun _ =>
    Complexity.Costed.orElse (Complexity.Costed.tick (M.collectiveKind k w) 1) fun _ =>
      Complexity.Costed.orElse (Complexity.Costed.tick (M.quantityKind k w) 1) fun _ =>
        Complexity.Costed.orElse (Complexity.Costed.tick (M.relatorKind k w) 1) fun _ =>
          Complexity.Costed.orElse (Complexity.Costed.tick (M.modeKind k w) 1) fun _ =>
            Complexity.Costed.tick (M.qualityKind k w) 1

def specificEndurantKindB (M : FiniteModel4) (k : Fin M.thingCount)
    (w : Fin M.worldCount) : Bool :=
  (specificEndurantKindCosted M k w).value

theorem specificEndurantKindB_eq_legacy (M : FiniteModel4)
    (k : Fin M.thingCount) (w : Fin M.worldCount) :
    specificEndurantKindB M k w =
      (M.objectKind k w || M.collectiveKind k w || M.quantityKind k w ||
        M.relatorKind k w || M.modeKind k w || M.qualityKind k w) := by
  unfold specificEndurantKindB specificEndurantKindCosted
  simp only [Complexity.Costed.orElse_value, Complexity.Costed.tick_value]
  cases M.objectKind k w <;> cases M.collectiveKind k w <;>
    cases M.quantityKind k w <;> cases M.relatorKind k w <;>
      cases M.modeKind k w <;> cases M.qualityKind k w <;> decide

theorem specificEndurantKindCosted_cost_le (M : FiniteModel4)
    (k : Fin M.thingCount) (w : Fin M.worldCount) :
    (specificEndurantKindCosted M k w).cost ≤ 11 := by
  unfold specificEndurantKindCosted
  cases h1 : M.objectKind k w <;> cases h2 : M.collectiveKind k w <;>
    cases h3 : M.quantityKind k w <;> cases h4 : M.relatorKind k w <;>
      cases h5 : M.modeKind k w <;>
        simp [Complexity.Costed.orElse]

def ax46WitnessCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (v : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun k =>
    Complexity.Costed.andThen (specificEndurantKindCosted M k v) fun _ =>
      Complexity.Costed.tick (M.inst x k v) 1

theorem ax46WitnessCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (v : Fin M.worldCount) :
    (ax46WitnessCosted M x v).value = anyThings M (fun k =>
      specificEndurantKindB M k v && M.inst x k v) := by
  unfold ax46WitnessCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value, specificEndurantKindB]

theorem ax46WitnessCosted_cost_le (M : FiniteModel4) (x : Fin M.thingCount)
    (v : Fin M.worldCount) :
    (ax46WitnessCosted M x v).cost ≤ M.thingCount * 15 := by
  unfold ax46WitnessCosted
  apply anyThingsEvalCosted_cost_le M _ 13
  intro k
  have hk := specificEndurantKindCosted_cost_le M k v
  cases h : (specificEndurantKindCosted M k v).value <;>
    simp [Complexity.Costed.andThen, h] <;> omega

def checkAx46Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.endurant x w) 1) fun _ =>
      anyWorldsEvalCosted M fun v => ax46WitnessCosted M x v

def checkAx46 (M : FiniteModel4) : Bool := (checkAx46Costed M).value

theorem checkAx46_eq_legacy (M : FiniteModel4) :
    checkAx46 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.endurant x w) (anyWorlds M (fun v =>
        anyThings M (fun k => specificEndurantKindB M k v && M.inst x k v))))) := by
  unfold checkAx46 checkAx46Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  simp [Complexity.Costed.implies_value, anyWorldsEvalCosted_value,
    ax46WitnessCosted_value, impliesB]

theorem checkAx46Costed_cost_le (M : FiniteModel4) :
    (checkAx46Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 15 + 2) + 5) + 2) := by
  unfold checkAx46Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.worldCount * (M.thingCount * 15 + 2) + 5))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 15 + 2) + 3)
  intro w
  have hw : (anyWorldsEvalCosted M fun v => ax46WitnessCosted M x v).cost ≤
      M.worldCount * (M.thingCount * 15 + 2) := by
    apply anyWorldsEvalCosted_cost_le M _ (M.thingCount * 15)
    exact ax46WitnessCosted_cost_le M x
  cases h : M.endurant x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def checkAx47Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.tick (M.part x x w) 1

def checkAx47 (M : FiniteModel4) : Bool := (checkAx47Costed M).value

theorem checkAx47_eq_legacy (M : FiniteModel4) :
  checkAx47 M = allThings M (fun x => allWorlds M (fun w => M.part x x w)) := by
  unfold checkAx47 checkAx47Costed
  rw [allThingsEvalCosted_value]
  rfl

theorem checkAx47Costed_cost_le (M : FiniteModel4) :
    (checkAx47Costed M).cost ≤ M.thingCount * (M.worldCount * 3 + 2) := by
  unfold checkAx47Costed
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 3)
  intro x
  apply allWorldsEvalCosted_cost_le M _ 1
  intro w
  simp

def checkAx48Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkTwoThingsWorldsImpCosted M
    (fun x y w => M.part x y w) (fun x y w => M.part y x w)
    (fun x y _ => decide (x = y))

def checkAx48 (M : FiniteModel4) : Bool := (checkAx48Costed M).value

theorem checkAx48_eq_legacy (M : FiniteModel4) :
    checkAx48 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w =>
        impliesB (M.part x y w && M.part y x w) (decide (x = y))))) :=
  checkTwoThingsWorldsImpCosted_value M _ _ _

theorem checkAx48Costed_cost_le (M : FiniteModel4) :
    (checkAx48Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  checkTwoThingsWorldsImpCosted_cost_le M _ _ _

def checkThreeThingsWorldsImpCosted (M : FiniteModel4)
    (first second consequent : Fin M.thingCount → Fin M.thingCount →
      Fin M.thingCount → Fin M.worldCount → Bool) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allThingsEvalCosted M fun z => allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.andThen (Complexity.Costed.tick (first x y z w) 1) fun _ =>
          Complexity.Costed.tick (second x y z w) 1) fun _ =>
        Complexity.Costed.tick (consequent x y z w) 1

theorem checkThreeThingsWorldsImpCosted_value (M : FiniteModel4)
    (first second consequent) :
    (checkThreeThingsWorldsImpCosted M first second consequent).value =
      allThings M (fun x => allThings M (fun y => allThings M (fun z =>
        allWorlds M (fun w => impliesB (first x y z w && second x y z w)
          (consequent x y z w))))) := by
  unfold checkThreeThingsWorldsImpCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext z
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value, impliesB]

theorem checkThreeThingsWorldsImpCosted_cost_le (M : FiniteModel4)
    (first second consequent) :
    (checkThreeThingsWorldsImpCosted M first second consequent).cost ≤
      M.thingCount * (M.thingCount *
        (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) := by
  unfold checkThreeThingsWorldsImpCosted
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * 8 + 2))
  intro y
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 8)
  intro z
  apply allWorldsEvalCosted_cost_le M _ 6
  intro w
  cases hf : first x y z w <;> cases hs : second x y z w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not]

def checkAx49Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkThreeThingsWorldsImpCosted M
    (fun x y _ w => M.part x y w) (fun _ y z w => M.part y z w)
    (fun x _ z w => M.part x z w)

def checkAx49 (M : FiniteModel4) : Bool := (checkAx49Costed M).value

theorem checkAx49_eq_legacy (M : FiniteModel4) :
    checkAx49 M = allThings M (fun x => allThings M (fun y =>
      allThings M (fun z => allWorlds M (fun w =>
        impliesB (M.part x y w && M.part y z w) (M.part x z w))))) :=
  checkThreeThingsWorldsImpCosted_value M _ _ _

theorem checkAx49Costed_cost_le (M : FiniteModel4) :
    (checkAx49Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) :=
  checkThreeThingsWorldsImpCosted_cost_le M _ _ _

def overlapWitnessCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun z =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.part z x w) 1) fun _ =>
      Complexity.Costed.tick (M.part z y w) 1

theorem overlapWitnessCosted_value (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (overlapWitnessCosted M x y w).value =
      anyThings M (fun z => M.part z x w && M.part z y w) := by
  unfold overlapWitnessCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

theorem overlapWitnessCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (overlapWitnessCosted M x y w).cost ≤ M.thingCount * 5 := by
  unfold overlapWitnessCosted
  apply anyThingsEvalCosted_cost_le M _ 3
  intro z
  cases h : M.part z x w <;> simp [Complexity.Costed.andThen]

def checkAx50Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (Complexity.Costed.tick (M.overlap x y w) 1) fun _ =>
        overlapWitnessCosted M x y w

def checkAx50 (M : FiniteModel4) : Bool := (checkAx50Costed M).value

theorem checkAx50_eq_legacy (M : FiniteModel4) :
    checkAx50 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (M.overlap x y w)
        (anyThings M (fun z => M.part z x w && M.part z y w))))) := by
  unfold checkAx50 checkAx50Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value, Complexity.Costed.tick_value,
    overlapWitnessCosted_value]
  cases hl : M.overlap x y w <;>
    cases hr : anyThings M (fun z => M.part z x w && M.part z y w) <;>
      simp [iffB]

theorem checkAx50Costed_cost_le (M : FiniteModel4) :
    (checkAx50Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 5 + 5) + 2) + 2) := by
  unfold checkAx50Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (M.thingCount * 5 + 5) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 5 + 5))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * 5 + 3)
  intro w
  have hz := overlapWitnessCosted_cost_le M x y w
  cases h : M.overlap x y w <;>
    simp [Complexity.Costed.iff] <;> omega

def supplementationWitnessCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun z =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.part z y w) 1) fun _ =>
      (Complexity.Costed.tick (M.overlap z x w) 1).not

theorem supplementationWitnessCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (supplementationWitnessCosted M x y w).value =
      anyThings M (fun z => M.part z y w && !(M.overlap z x w)) := by
  unfold supplementationWitnessCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

theorem supplementationWitnessCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (supplementationWitnessCosted M x y w).cost ≤ M.thingCount * 6 := by
  unfold supplementationWitnessCosted
  apply anyThingsEvalCosted_cost_le M _ 4
  intro z
  cases h : M.part z y w <;>
    simp [Complexity.Costed.andThen, Complexity.Costed.not]

def checkAx51Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.not (Complexity.Costed.tick (M.part y x w) 1)) fun _ =>
        supplementationWitnessCosted M x y w

def checkAx51 (M : FiniteModel4) : Bool := (checkAx51Costed M).value

theorem checkAx51_eq_legacy (M : FiniteModel4) :
    checkAx51 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (!(M.part y x w))
        (anyThings M (fun z => M.part z y w && !(M.overlap z x w)))))) := by
  unfold checkAx51 checkAx51Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, supplementationWitnessCosted_value,
    impliesB]

theorem checkAx51Costed_cost_le (M : FiniteModel4) :
    (checkAx51Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 6 + 6) + 2) + 2) := by
  unfold checkAx51Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (M.thingCount * 6 + 6) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 6 + 6))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * 6 + 4)
  intro w
  have hz := supplementationWitnessCosted_cost_le M x y w
  cases h : M.part y x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def checkAx52Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (Complexity.Costed.tick (M.properPart x y w) 1) fun _ =>
        Complexity.Costed.andThen (Complexity.Costed.tick (M.part x y w) 1) fun _ =>
          (Complexity.Costed.tick (M.part y x w) 1).not

def checkAx52 (M : FiniteModel4) : Bool := (checkAx52Costed M).value

theorem checkAx52_eq_legacy (M : FiniteModel4) :
    checkAx52 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (M.properPart x y w)
        (M.part x y w && !(M.part y x w))))) := by
  unfold checkAx52 checkAx52Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value, Complexity.Costed.tick_value,
    Complexity.Costed.andThen_value, Complexity.Costed.not_value]
  cases hl : M.properPart x y w <;>
    cases hp : M.part x y w <;> cases hr : M.part y x w <;> simp [iffB]

theorem checkAx52Costed_cost_le (M : FiniteModel4) :
    (checkAx52Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 9 + 2) + 2) := by
  unfold checkAx52Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * 9 + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 9)
  intro y
  apply allWorldsEvalCosted_cost_le M _ 7
  intro w
  cases hp : M.properPart x y w <;> cases hxy : M.part x y w <;>
    simp [Complexity.Costed.iff, Complexity.Costed.andThen,
      Complexity.Costed.not]

def genericFunctionalWitnessCosted (M : FiniteModel4) (x y' : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y =>
    Complexity.Costed.andThen (Complexity.Costed.tick (decide (y ≠ x)) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y y' w) 1) fun _ =>
        Complexity.Costed.tick (M.functionsAs y y' w) 1

theorem genericFunctionalWitnessCosted_value (M : FiniteModel4)
    (x y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (genericFunctionalWitnessCosted M x y' w).value = anyThings M (fun y =>
      decide (y ≠ x) && M.inst y y' w && M.functionsAs y y' w) := by
  unfold genericFunctionalWitnessCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value, Bool.and_assoc]

theorem genericFunctionalWitnessCosted_cost_le (M : FiniteModel4)
    (x y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (genericFunctionalWitnessCosted M x y' w).cost ≤ M.thingCount * 7 := by
  unfold genericFunctionalWitnessCosted
  apply anyThingsEvalCosted_cost_le M _ 5
  intro y
  cases hn : decide (y ≠ x) <;> cases hi : M.inst y y' w <;>
    simp [Complexity.Costed.andThen]

def genericFunctionalDependenceCosted
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    Complexity.Costed.implies
      (Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x x' w) 1) fun _ =>
        Complexity.Costed.tick (M.functionsAs x x' w) 1) fun _ =>
      genericFunctionalWitnessCosted M x y' w

def genericFunctionalDependenceB
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (genericFunctionalDependenceCosted M x' y' w).value

theorem genericFunctionalDependenceB_eq_legacy (M : FiniteModel4)
    (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    genericFunctionalDependenceB M x' y' w = allThings M (fun x =>
      impliesB (M.inst x x' w && M.functionsAs x x' w)
        (anyThings M (fun y =>
          decide (y ≠ x) && M.inst y y' w && M.functionsAs y y' w))) := by
  unfold genericFunctionalDependenceB genericFunctionalDependenceCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    genericFunctionalWitnessCosted_value, impliesB]

def genericFunctionalDependenceBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 7 + 7)

theorem genericFunctionalDependenceCosted_cost_le (M : FiniteModel4)
    (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (genericFunctionalDependenceCosted M x' y' w).cost ≤
      genericFunctionalDependenceBound M := by
  unfold genericFunctionalDependenceCosted genericFunctionalDependenceBound
  apply allThingsEvalCosted_cost_le M _ (M.thingCount * 7 + 5)
  intro x
  have hw := genericFunctionalWitnessCosted_cost_le M x y' w
  cases hi : M.inst x x' w <;> cases hf : M.functionsAs x x' w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not] ; omega

def individualFunctionalDependenceCosted
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen (genericFunctionalDependenceCosted M x' y' w) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x x' w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y y' w) 1) fun _ =>
        Complexity.Costed.implies
          (Complexity.Costed.tick (M.functionsAs x x' w) 1) fun _ =>
          Complexity.Costed.tick (M.functionsAs y y' w) 1

def individualFunctionalDependenceB
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (individualFunctionalDependenceCosted M x x' y y' w).value

theorem individualFunctionalDependenceB_eq_legacy (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    individualFunctionalDependenceB M x x' y y' w =
      (genericFunctionalDependenceB M x' y' w &&
        M.inst x x' w && M.inst y y' w &&
          impliesB (M.functionsAs x x' w) (M.functionsAs y y' w)) := by
  unfold individualFunctionalDependenceB individualFunctionalDependenceCosted
    genericFunctionalDependenceB
  simp only [Complexity.Costed.andThen_value, Complexity.Costed.implies_value,
    Complexity.Costed.tick_value]
  cases hg : (genericFunctionalDependenceCosted M x' y' w).value <;>
    cases hix : M.inst x x' w <;> cases hiy : M.inst y y' w <;>
      cases hf : M.functionsAs x x' w <;> cases hfy : M.functionsAs y y' w <;>
        simp [impliesB]

def individualFunctionalDependenceBound (M : FiniteModel4) : Nat :=
  genericFunctionalDependenceBound M + 9

theorem individualFunctionalDependenceCosted_cost_le (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (individualFunctionalDependenceCosted M x x' y y' w).cost ≤
      individualFunctionalDependenceBound M := by
  have hg := genericFunctionalDependenceCosted_cost_le M x' y' w
  unfold individualFunctionalDependenceCosted individualFunctionalDependenceBound
  cases hgv : (genericFunctionalDependenceCosted M x' y' w).value <;>
    cases hix : M.inst x x' w <;> cases hiy : M.inst y y' w <;>
      cases hf : M.functionsAs x x' w <;>
        simp [Complexity.Costed.andThen, Complexity.Costed.implies,
          Complexity.Costed.orElse, Complexity.Costed.not, hgv] <;> omega

def checkAx53Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x' => allThingsEvalCosted M fun y' =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (genericFunctionalDependenceCosted M x' y' w) fun _ =>
        genericFunctionalDependenceCosted M x' y' w

def checkAx53 (M : FiniteModel4) : Bool := (checkAx53Costed M).value

theorem checkAx53_eq_legacy (M : FiniteModel4) :
    checkAx53 M = allThings M (fun x' => allThings M (fun y' =>
      allWorlds M (fun w => iffB (genericFunctionalDependenceB M x' y' w)
        (genericFunctionalDependenceB M x' y' w)))) := by
  unfold checkAx53 checkAx53Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x'
  rw [allThingsEvalCosted_value]; congr 1; funext y'
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value]
  unfold genericFunctionalDependenceB
  simp [iffB]

theorem checkAx53Costed_cost_le (M : FiniteModel4) :
    (checkAx53Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * genericFunctionalDependenceBound M + 4) + 2) + 2) := by
  unfold checkAx53Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (2 * genericFunctionalDependenceBound M + 4) + 2))
  intro x'
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * genericFunctionalDependenceBound M + 4))
  intro y'
  apply allWorldsEvalCosted_cost_le M _
    (2 * genericFunctionalDependenceBound M + 2)
  intro w
  have hl := genericFunctionalDependenceCosted_cost_le M x' y' w
  have hr := genericFunctionalDependenceCosted_cost_le M x' y' w
  cases h : (genericFunctionalDependenceCosted M x' y' w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def checkAx54Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun x' =>
    allThingsEvalCosted M fun y => allThingsEvalCosted M fun y' =>
      allWorldsEvalCosted M fun w =>
        Complexity.Costed.iff
          (individualFunctionalDependenceCosted M x x' y y' w) fun _ =>
          individualFunctionalDependenceCosted M x x' y y' w

def checkAx54 (M : FiniteModel4) : Bool := (checkAx54Costed M).value

theorem checkAx54_eq_legacy (M : FiniteModel4) :
    checkAx54 M = allThings M (fun x => allThings M (fun x' =>
      allThings M (fun y => allThings M (fun y' => allWorlds M (fun w =>
        iffB (individualFunctionalDependenceB M x x' y y' w)
          (individualFunctionalDependenceB M x x' y y' w)))))) := by
  unfold checkAx54 checkAx54Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext x'
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext y'
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value]
  unfold individualFunctionalDependenceB
  simp [iffB]

theorem checkAx54Costed_cost_le (M : FiniteModel4) :
    (checkAx54Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (2 * individualFunctionalDependenceBound M + 4) + 2) + 2) +
        2) + 2) := by
  unfold checkAx54Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.thingCount *
      (M.worldCount * (2 * individualFunctionalDependenceBound M + 4) + 2) + 2) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount *
      (M.worldCount * (2 * individualFunctionalDependenceBound M + 4) + 2) + 2))
  intro x'
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (2 * individualFunctionalDependenceBound M + 4) + 2))
  intro y
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * individualFunctionalDependenceBound M + 4))
  intro y'
  apply allWorldsEvalCosted_cost_le M _
    (2 * individualFunctionalDependenceBound M + 2)
  intro w
  have hl := individualFunctionalDependenceCosted_cost_le M x x' y y' w
  have hr := individualFunctionalDependenceCosted_cost_le M x x' y y' w
  cases h : (individualFunctionalDependenceCosted M x x' y y' w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def functionalComponentCosted (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.properPart x y w) 1) fun _ =>
    individualFunctionalDependenceCosted M x x' y y' w

theorem functionalComponentCosted_value (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (functionalComponentCosted M x x' y y' w).value =
      (M.properPart x y w && individualFunctionalDependenceB M x x' y y' w) := by
  simp [functionalComponentCosted, Complexity.Costed.andThen_value,
    individualFunctionalDependenceB]

def functionalComponentBound (M : FiniteModel4) : Nat :=
  individualFunctionalDependenceBound M + 2

theorem functionalComponentCosted_cost_le (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (functionalComponentCosted M x x' y y' w).cost ≤ functionalComponentBound M := by
  have hi := individualFunctionalDependenceCosted_cost_le M x x' y y' w
  cases hp : M.properPart x y w <;>
    simp [functionalComponentCosted, functionalComponentBound,
      Complexity.Costed.andThen, hp] ; omega

def checkAx55Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun x' =>
    allThingsEvalCosted M fun y => allThingsEvalCosted M fun y' =>
      allWorldsEvalCosted M fun w =>
        Complexity.Costed.iff (functionalComponentCosted M x x' y y' w) fun _ =>
          functionalComponentCosted M x x' y y' w

def checkAx55 (M : FiniteModel4) : Bool := (checkAx55Costed M).value

theorem checkAx55_eq_legacy (M : FiniteModel4) :
    checkAx55 M = allThings M (fun x => allThings M (fun x' =>
      allThings M (fun y => allThings M (fun y' => allWorlds M (fun w =>
        iffB (M.properPart x y w && individualFunctionalDependenceB M x x' y y' w)
          (M.properPart x y w &&
            individualFunctionalDependenceB M x x' y y' w)))))) := by
  unfold checkAx55 checkAx55Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext x'
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext y'
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value, functionalComponentCosted_value]
  cases hp : M.properPart x y w <;>
    cases hi : individualFunctionalDependenceB M x x' y y' w <;> simp [iffB]

theorem checkAx55Costed_cost_le (M : FiniteModel4) :
    (checkAx55Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (2 * functionalComponentBound M + 4) + 2) + 2) + 2) + 2) := by
  unfold checkAx55Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.thingCount *
      (M.worldCount * (2 * functionalComponentBound M + 4) + 2) + 2) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount *
      (M.worldCount * (2 * functionalComponentBound M + 4) + 2) + 2))
  intro x'
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (2 * functionalComponentBound M + 4) + 2))
  intro y
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * functionalComponentBound M + 4))
  intro y'
  apply allWorldsEvalCosted_cost_le M _ (2 * functionalComponentBound M + 2)
  intro w
  have hl := functionalComponentCosted_cost_le M x x' y y' w
  have hr := functionalComponentCosted_cost_le M x x' y y' w
  cases h : (functionalComponentCosted M x x' y y' w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def constitutedSortAgreementCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.iff (Complexity.Costed.tick (M.endurant x w) 1) fun _ =>
      Complexity.Costed.tick (M.endurant y w) 1) fun _ =>
    Complexity.Costed.iff (Complexity.Costed.tick (M.perdurant x w) 1) fun _ =>
      Complexity.Costed.tick (M.perdurant y w) 1

theorem constitutedSortAgreementCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (constitutedSortAgreementCosted M x y w).value =
      (iffB (M.endurant x w) (M.endurant y w) &&
        iffB (M.perdurant x w) (M.perdurant y w)) := by
  unfold constitutedSortAgreementCosted
  rw [Complexity.Costed.andThen_value, Complexity.Costed.iff_value,
    Complexity.Costed.iff_value]
  cases M.endurant x w <;> cases M.endurant y w <;>
    cases M.perdurant x w <;> cases M.perdurant y w <;> decide

theorem constitutedSortAgreementCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (constitutedSortAgreementCosted M x y w).cost ≤ 9 := by
  unfold constitutedSortAgreementCosted
  cases he : M.endurant x w <;> cases hey : M.endurant y w <;>
    cases hp : M.perdurant x w <;>
      simp [Complexity.Costed.andThen, Complexity.Costed.iff]

def checkAx56Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (M.constitutedBy x y w) 1) fun _ =>
        constitutedSortAgreementCosted M x y w

def checkAx56 (M : FiniteModel4) : Bool := (checkAx56Costed M).value

theorem checkAx56_eq_legacy (M : FiniteModel4) :
    checkAx56 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (M.constitutedBy x y w)
        (iffB (M.endurant x w) (M.endurant y w) &&
          iffB (M.perdurant x w) (M.perdurant y w))))) := by
  unfold checkAx56 checkAx56Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, constitutedSortAgreementCosted_value,
    impliesB]

theorem checkAx56Costed_cost_le (M : FiniteModel4) :
    (checkAx56Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 14 + 2) + 2) := by
  unfold checkAx56Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * 14 + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 14)
  intro y
  apply allWorldsEvalCosted_cost_le M _ 12
  intro w
  have hc := constitutedSortAgreementCosted_cost_le M x y w
  cases h : M.constitutedBy x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def constitutedKindsAntecedentCosted (M : FiniteModel4)
    (x y x' y' : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.constitutedBy x y w) 1) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x x' w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y y' w) 1) fun _ =>
        Complexity.Costed.andThen (Complexity.Costed.tick (M.kind x' w) 1) fun _ =>
          Complexity.Costed.tick (M.kind y' w) 1

theorem constitutedKindsAntecedentCosted_value (M : FiniteModel4)
    (x y x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (constitutedKindsAntecedentCosted M x y x' y' w).value =
      (M.constitutedBy x y w && M.inst x x' w && M.inst y y' w &&
        M.kind x' w && M.kind y' w) := by
  unfold constitutedKindsAntecedentCosted
  simp [Complexity.Costed.andThen_value, Bool.and_assoc]

theorem constitutedKindsAntecedentCosted_cost_le (M : FiniteModel4)
    (x y x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (constitutedKindsAntecedentCosted M x y x' y' w).cost ≤ 9 := by
  unfold constitutedKindsAntecedentCosted
  cases h1 : M.constitutedBy x y w <;> cases h2 : M.inst x x' w <;>
    cases h3 : M.inst y y' w <;> cases h4 : M.kind x' w <;>
      simp [Complexity.Costed.andThen]

def checkAx57Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allThingsEvalCosted M fun x' => allThingsEvalCosted M fun y' =>
      allWorldsEvalCosted M fun w =>
        Complexity.Costed.implies (constitutedKindsAntecedentCosted M x y x' y' w)
          fun _ => Complexity.Costed.tick (decide (x' ≠ y')) 1

def checkAx57 (M : FiniteModel4) : Bool := (checkAx57Costed M).value

theorem checkAx57_eq_legacy (M : FiniteModel4) :
    checkAx57 M = allThings M (fun x => allThings M (fun y =>
      allThings M (fun x' => allThings M (fun y' => allWorlds M (fun w =>
        impliesB (M.constitutedBy x y w && M.inst x x' w && M.inst y y' w &&
          M.kind x' w && M.kind y' w) (decide (x' ≠ y'))))))) := by
  unfold checkAx57 checkAx57Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext x'
  rw [allThingsEvalCosted_value]; congr 1; funext y'
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, constitutedKindsAntecedentCosted_value,
    impliesB]

theorem checkAx57Costed_cost_le (M : FiniteModel4) :
    (checkAx57Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 14 + 2) + 2) + 2) + 2) := by
  unfold checkAx57Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.thingCount * (M.worldCount * 14 + 2) + 2) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.worldCount * 14 + 2) + 2))
  intro y
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * 14 + 2))
  intro x'
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 14)
  intro y'
  apply allWorldsEvalCosted_cost_le M _ 12
  intro w
  have ha := constitutedKindsAntecedentCosted_cost_le M x y x' y' w
  cases h : (constitutedKindsAntecedentCosted M x y x' y' w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def constitutionalWitnessCosted (M : FiniteModel4) (x y' : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y y' w) 1) fun _ =>
      Complexity.Costed.tick (M.constitutedBy x y w) 1

theorem constitutionalWitnessCosted_value (M : FiniteModel4)
    (x y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (constitutionalWitnessCosted M x y' w).value =
      anyThings M (fun y => M.inst y y' w && M.constitutedBy x y w) := by
  unfold constitutionalWitnessCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

theorem constitutionalWitnessCosted_cost_le (M : FiniteModel4)
    (x y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (constitutionalWitnessCosted M x y' w).cost ≤ M.thingCount * 5 := by
  unfold constitutionalWitnessCosted
  apply anyThingsEvalCosted_cost_le M _ 3
  intro y
  cases h : M.inst y y' w <;> simp [Complexity.Costed.andThen]

def genericConstitutionalDependenceCosted
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.inst x x' w) 1) fun _ =>
      constitutionalWitnessCosted M x y' w

def genericConstitutionalDependenceB
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (genericConstitutionalDependenceCosted M x' y' w).value

theorem genericConstitutionalDependenceB_eq_legacy (M : FiniteModel4)
    (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    genericConstitutionalDependenceB M x' y' w = allThings M (fun x =>
      impliesB (M.inst x x' w)
        (anyThings M (fun y => M.inst y y' w && M.constitutedBy x y w))) := by
  unfold genericConstitutionalDependenceB genericConstitutionalDependenceCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, constitutionalWitnessCosted_value, impliesB]

def genericConstitutionalDependenceBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 5 + 5)

theorem genericConstitutionalDependenceCosted_cost_le (M : FiniteModel4)
    (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (genericConstitutionalDependenceCosted M x' y' w).cost ≤
      genericConstitutionalDependenceBound M := by
  unfold genericConstitutionalDependenceCosted genericConstitutionalDependenceBound
  apply allThingsEvalCosted_cost_le M _ (M.thingCount * 5 + 3)
  intro x
  have hw := constitutionalWitnessCosted_cost_le M x y' w
  cases h : M.inst x x' w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def constitutionCosted
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x x' w) 1) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y y' w) 1) fun _ =>
      Complexity.Costed.andThen (genericConstitutionalDependenceCosted M x' y' w) fun _ =>
        Complexity.Costed.tick (M.constitutedBy x y w) 1

def constitutionB
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (constitutionCosted M x x' y y' w).value

theorem constitutionB_eq_legacy (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    constitutionB M x x' y y' w =
      (M.inst x x' w && M.inst y y' w &&
        genericConstitutionalDependenceB M x' y' w && M.constitutedBy x y w) := by
  unfold constitutionB constitutionCosted genericConstitutionalDependenceB
  simp [Complexity.Costed.andThen_value, Bool.and_assoc]

def constitutionBound (M : FiniteModel4) : Nat :=
  genericConstitutionalDependenceBound M + 6

theorem constitutionCosted_cost_le (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    (constitutionCosted M x x' y y' w).cost ≤ constitutionBound M := by
  have hg := genericConstitutionalDependenceCosted_cost_le M x' y' w
  unfold constitutionCosted constitutionBound
  cases hix : M.inst x x' w <;> cases hiy : M.inst y y' w <;>
    cases hgv : (genericConstitutionalDependenceCosted M x' y' w).value <;>
      simp [Complexity.Costed.andThen, hgv] <;> omega

def checkAx58Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x' => allThingsEvalCosted M fun y' =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (genericConstitutionalDependenceCosted M x' y' w) fun _ =>
        genericConstitutionalDependenceCosted M x' y' w

def checkAx58 (M : FiniteModel4) : Bool := (checkAx58Costed M).value

theorem checkAx58_eq_legacy (M : FiniteModel4) :
    checkAx58 M = allThings M (fun x' => allThings M (fun y' =>
      allWorlds M (fun w => iffB (genericConstitutionalDependenceB M x' y' w)
        (genericConstitutionalDependenceB M x' y' w)))) := by
  unfold checkAx58 checkAx58Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x'
  rw [allThingsEvalCosted_value]; congr 1; funext y'
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value]
  unfold genericConstitutionalDependenceB
  simp [iffB]

theorem checkAx58Costed_cost_le (M : FiniteModel4) :
    (checkAx58Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * genericConstitutionalDependenceBound M + 4) + 2) + 2) := by
  unfold checkAx58Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (2 * genericConstitutionalDependenceBound M + 4) + 2))
  intro x'
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * genericConstitutionalDependenceBound M + 4))
  intro y'
  apply allWorldsEvalCosted_cost_le M _
    (2 * genericConstitutionalDependenceBound M + 2)
  intro w
  have hl := genericConstitutionalDependenceCosted_cost_le M x' y' w
  have hr := genericConstitutionalDependenceCosted_cost_le M x' y' w
  cases h : (genericConstitutionalDependenceCosted M x' y' w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def checkAx59Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun x' =>
    allThingsEvalCosted M fun y => allThingsEvalCosted M fun y' =>
      allWorldsEvalCosted M fun w =>
        Complexity.Costed.iff (constitutionCosted M x x' y y' w) fun _ =>
          constitutionCosted M x x' y y' w

def checkAx59 (M : FiniteModel4) : Bool := (checkAx59Costed M).value

theorem checkAx59_eq_legacy (M : FiniteModel4) :
    checkAx59 M = allThings M (fun x => allThings M (fun x' =>
      allThings M (fun y => allThings M (fun y' => allWorlds M (fun w =>
        iffB (constitutionB M x x' y y' w) (constitutionB M x x' y y' w)))))) := by
  unfold checkAx59 checkAx59Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext x'
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext y'
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value]
  unfold constitutionB
  simp [iffB]

theorem checkAx59Costed_cost_le (M : FiniteModel4) :
    (checkAx59Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (2 * constitutionBound M + 4) + 2) + 2) + 2) + 2) := by
  unfold checkAx59Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount * (M.thingCount *
      (M.worldCount * (2 * constitutionBound M + 4) + 2) + 2) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.thingCount *
      (M.worldCount * (2 * constitutionBound M + 4) + 2) + 2))
  intro x'
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (2 * constitutionBound M + 4) + 2))
  intro y
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * constitutionBound M + 4))
  intro y'
  apply allWorldsEvalCosted_cost_le M _ (2 * constitutionBound M + 2)
  intro w
  have hl := constitutionCosted_cost_le M x x' y y' w
  have hr := constitutionCosted_cost_le M x x' y y' w
  cases h : (constitutionCosted M x x' y y' w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def constitutionPersistenceCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) : Complexity.Costed Bool :=
  allWorldsEvalCosted M fun v =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.ex x v) 1) fun _ =>
      Complexity.Costed.tick (M.constitutedBy x y v) 1

theorem constitutionPersistenceCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) :
    (constitutionPersistenceCosted M x y).value =
      allWorlds M (fun v => impliesB (M.ex x v) (M.constitutedBy x y v)) := by
  unfold constitutionPersistenceCosted
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem constitutionPersistenceCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) :
    (constitutionPersistenceCosted M x y).cost ≤ M.worldCount * 6 := by
  unfold constitutionPersistenceCosted
  apply allWorldsEvalCosted_cost_le M _ 4
  intro v
  cases h : M.ex x v <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def checkAx60Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.andThen (Complexity.Costed.tick (M.perdurant x w) 1) fun _ =>
          Complexity.Costed.tick (M.constitutedBy x y w) 1) fun _ =>
        constitutionPersistenceCosted M x y

def checkAx60 (M : FiniteModel4) : Bool := (checkAx60Costed M).value

theorem checkAx60_eq_legacy (M : FiniteModel4) :
    checkAx60 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (M.perdurant x w && M.constitutedBy x y w)
        (allWorlds M (fun v => impliesB (M.ex x v) (M.constitutedBy x y v)))))) := by
  unfold checkAx60 checkAx60Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    constitutionPersistenceCosted_value, impliesB]

theorem checkAx60Costed_cost_le (M : FiniteModel4) :
    (checkAx60Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.worldCount * 6 + 7) + 2) + 2) := by
  unfold checkAx60Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (M.worldCount * 6 + 7) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.worldCount * 6 + 7))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (M.worldCount * 6 + 5)
  intro w
  have hp := constitutionPersistenceCosted_cost_le M x y
  cases hper : M.perdurant x w <;> cases hc : M.constitutedBy x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not] ; omega

def checkAx61Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (M.constitutedBy x y w) 1) fun _ =>
        (Complexity.Costed.tick (M.constitutedBy y x w) 1).not

def checkAx61 (M : FiniteModel4) : Bool := (checkAx61Costed M).value

theorem checkAx61_eq_legacy (M : FiniteModel4) :
    checkAx61 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w =>
        impliesB (M.constitutedBy x y w) (!(M.constitutedBy y x w))))) := by
  unfold checkAx61 checkAx61Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem checkAx61Costed_cost_le (M : FiniteModel4) :
    (checkAx61Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 7 + 2) + 2) := by
  unfold checkAx61Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * 7 + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 7)
  intro y
  apply allWorldsEvalCosted_cost_le M _ 5
  intro w
  cases h : M.constitutedBy x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def checkAx62Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun _x => allWorldsEvalCosted M fun _w =>
    Complexity.Costed.pure true

def checkAx62 (M : FiniteModel4) : Bool := (checkAx62Costed M).value

theorem checkAx62_eq_legacy (M : FiniteModel4) :
  checkAx62 M = allThings M (fun _x => allWorlds M (fun _w => true)) := by
  unfold checkAx62 checkAx62Costed
  rw [allThingsEvalCosted_value]
  congr 1
  funext x
  rw [allWorldsEvalCosted_value]
  simp

theorem checkAx62Costed_cost_le (M : FiniteModel4) :
    (checkAx62Costed M).cost ≤ M.thingCount * (M.worldCount * 2 + 2) := by
  unfold checkAx62Costed
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * 2)
  intro x
  apply allWorldsEvalCosted_cost_le M _ 0
  intro w
  simp

def existentialDependenceCosted
    (M : FiniteModel4) (x y : Fin M.thingCount) (_w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  allWorldsEvalCosted M fun v =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.ex x v) 1) fun _ =>
      Complexity.Costed.tick (M.ex y v) 1

def existentialDependenceB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (existentialDependenceCosted M x y w).value

theorem existentialDependenceB_eq_legacy (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    existentialDependenceB M x y w =
      allWorlds M (fun v => impliesB (M.ex x v) (M.ex y v)) := by
  unfold existentialDependenceB existentialDependenceCosted
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

def existentialDependenceBound (M : FiniteModel4) : Nat := M.worldCount * 6

theorem existentialDependenceCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (existentialDependenceCosted M x y w).cost ≤ existentialDependenceBound M := by
  unfold existentialDependenceCosted existentialDependenceBound
  apply allWorldsEvalCosted_cost_le M _ 4
  intro v
  cases h : M.ex x v <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def existentialIndependenceCosted
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen (existentialDependenceCosted M x y w).not fun _ =>
    (existentialDependenceCosted M y x w).not

def existentialIndependenceB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (existentialIndependenceCosted M x y w).value

theorem existentialIndependenceB_eq_legacy (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    existentialIndependenceB M x y w =
      (!(existentialDependenceB M x y w) &&
        !(existentialDependenceB M y x w)) := by
  unfold existentialIndependenceB existentialIndependenceCosted existentialDependenceB
  simp [Complexity.Costed.andThen_value]

def existentialIndependenceBound (M : FiniteModel4) : Nat :=
  2 * existentialDependenceBound M + 3

theorem existentialIndependenceCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (existentialIndependenceCosted M x y w).cost ≤
      existentialIndependenceBound M := by
  have hxy := existentialDependenceCosted_cost_le M x y w
  have hyx := existentialDependenceCosted_cost_le M y x w
  cases h : (existentialDependenceCosted M x y w).value <;>
    simp [existentialIndependenceCosted, existentialIndependenceBound,
      Complexity.Costed.andThen, Complexity.Costed.not, h] <;> omega

def checkAx63Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (existentialDependenceCosted M x y w) fun _ =>
        existentialDependenceCosted M x y w

def checkAx63 (M : FiniteModel4) : Bool := (checkAx63Costed M).value

theorem checkAx63_eq_legacy (M : FiniteModel4) :
    checkAx63 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (existentialDependenceB M x y w)
        (existentialDependenceB M x y w)))) := by
  unfold checkAx63 checkAx63Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value]
  unfold existentialDependenceB
  simp [iffB]

theorem checkAx63Costed_cost_le (M : FiniteModel4) :
    (checkAx63Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * existentialDependenceBound M + 4) + 2) + 2) := by
  unfold checkAx63Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (2 * existentialDependenceBound M + 4) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * existentialDependenceBound M + 4))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (2 * existentialDependenceBound M + 2)
  intro w
  have hl := existentialDependenceCosted_cost_le M x y w
  have hr := existentialDependenceCosted_cost_le M x y w
  cases h : (existentialDependenceCosted M x y w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def checkAx64Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (existentialIndependenceCosted M x y w) fun _ =>
        existentialIndependenceCosted M x y w

def checkAx64 (M : FiniteModel4) : Bool := (checkAx64Costed M).value

theorem checkAx64_eq_legacy (M : FiniteModel4) :
    checkAx64 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (existentialIndependenceB M x y w)
        (existentialIndependenceB M x y w)))) := by
  unfold checkAx64 checkAx64Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value]
  unfold existentialIndependenceB
  simp [iffB]

theorem checkAx64Costed_cost_le (M : FiniteModel4) :
    (checkAx64Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * existentialIndependenceBound M + 4) + 2) + 2) := by
  unfold checkAx64Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (2 * existentialIndependenceBound M + 4) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * existentialIndependenceBound M + 4))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (2 * existentialIndependenceBound M + 2)
  intro w
  have hl := existentialIndependenceCosted_cost_le M x y w
  have hr := existentialIndependenceCosted_cost_le M x y w
  cases h : (existentialIndependenceCosted M x y w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def checkAx65Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.inheresIn x y w) 1) fun _ =>
        existentialDependenceCosted M x y w

def checkAx65 (M : FiniteModel4) : Bool := (checkAx65Costed M).value

theorem checkAx65_eq_legacy (M : FiniteModel4) :
    checkAx65 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (M.inheresIn x y w)
        (existentialDependenceB M x y w)))) := by
  unfold checkAx65 checkAx65Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, existentialDependenceB, impliesB]

theorem checkAx65Costed_cost_le (M : FiniteModel4) :
    (checkAx65Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (existentialDependenceBound M + 5) + 2) + 2) := by
  unfold checkAx65Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (existentialDependenceBound M + 5) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (existentialDependenceBound M + 5))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (existentialDependenceBound M + 3)
  intro w
  have hd := existentialDependenceCosted_cost_le M x y w
  cases h : M.inheresIn x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def ax66ConsequentCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.moment x w) 1) fun _ =>
    Complexity.Costed.orElse (typeBCosted M y w) fun _ =>
      Complexity.Costed.tick (M.concreteIndividual y w) 1

theorem ax66ConsequentCosted_value (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax66ConsequentCosted M x y w).value =
      (M.moment x w && (typeB M y w || M.concreteIndividual y w)) := by
  simp [ax66ConsequentCosted, Complexity.Costed.andThen_value,
    Complexity.Costed.orElse_value, typeBCosted_value]

theorem ax66ConsequentCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax66ConsequentCosted M x y w).cost ≤
      M.worldCount * (M.thingCount * 3 + 2) + 4 := by
  have ht := typeBCosted_cost_le M y w
  cases hm : M.moment x w <;> cases hty : typeB M y w <;>
    simp [ax66ConsequentCosted, Complexity.Costed.andThen,
      Complexity.Costed.orElse, typeBCosted_value, hm, hty] <;> omega

def checkAx66Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.inheresIn x y w) 1) fun _ =>
        ax66ConsequentCosted M x y w

def checkAx66 (M : FiniteModel4) : Bool := (checkAx66Costed M).value

theorem checkAx66_eq_legacy (M : FiniteModel4) :
    checkAx66 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (M.inheresIn x y w)
        (M.moment x w && (typeB M y w || M.concreteIndividual y w))))) := by
  unfold checkAx66 checkAx66Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax66ConsequentCosted_value, impliesB]

theorem checkAx66Costed_cost_le (M : FiniteModel4) :
    (checkAx66Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 9) + 2) + 2) := by
  unfold checkAx66Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 9) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 9))
  intro y
  apply allWorldsEvalCosted_cost_le M _
    (M.worldCount * (M.thingCount * 3 + 2) + 7)
  intro w
  have hc := ax66ConsequentCosted_cost_le M x y w
  cases h : M.inheresIn x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def checkAx67Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkThreeThingsWorldsImpCosted M
    (fun x y _ w => M.inheresIn x y w) (fun x _ z w => M.inheresIn x z w)
    (fun _ y z _ => decide (y = z))

def checkAx67 (M : FiniteModel4) : Bool := (checkAx67Costed M).value

theorem checkAx67_eq_legacy (M : FiniteModel4) :
    checkAx67 M = allThings M (fun x => allThings M (fun y =>
      allThings M (fun z => allWorlds M (fun w =>
        impliesB (M.inheresIn x y w && M.inheresIn x z w) (decide (y = z)))))) :=
  checkThreeThingsWorldsImpCosted_value M _ _ _

theorem checkAx67Costed_cost_le (M : FiniteModel4) :
    (checkAx67Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) :=
  checkThreeThingsWorldsImpCosted_cost_le M _ _ _

/-!
Axiom 68 is the first checker whose executable cost has two visibly distinct
phases: verified Warshall closure construction and short-circuiting formula
evaluation over the resulting matrices.  Keeping both phases in one counted
core follows the cost-aware semantics discipline of Niu et al. (POPL 2022),
while reusing one proved executable as the production definition follows the
verified-DSL methodology exemplified by de Moura's `RadixExperiment`.  These
are complementary guarantees: the former justifies the bound; the latter
justifies that the bound applies to the checker we actually run.
-/

def checkAx68WithClosuresCosted (M : FiniteModel4)
    (closures : Vector (Complexity.BoolMatrix M.thingCount) M.worldCount) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M fun m =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.moment m w) 1) fun _ =>
        existsUniqueUltimateBearerWarshallCosted M closures m w

theorem checkAx68WithClosuresCosted_value (M : FiniteModel4) (closures) :
    (checkAx68WithClosuresCosted M closures).value =
      allThings M (fun m => allWorlds M (fun w =>
        impliesB (M.moment m w)
          (existsUniqueUltimateBearerWarshallB M closures m w))) := by
  unfold checkAx68WithClosuresCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext m
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, existsUniqueUltimateBearerWarshallB,
    impliesB]

def checkAx68EvaluationBound (M : FiniteModel4) : Nat :=
  M.thingCount *
    (M.worldCount * (ultimateBearerUniquenessBound M + 5) + 2)

theorem checkAx68WithClosuresCosted_cost_le (M : FiniteModel4) (closures) :
    (checkAx68WithClosuresCosted M closures).cost ≤ checkAx68EvaluationBound M := by
  unfold checkAx68WithClosuresCosted checkAx68EvaluationBound
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (ultimateBearerUniquenessBound M + 5))
  intro m
  apply allWorldsEvalCosted_cost_le M _ (ultimateBearerUniquenessBound M + 3)
  intro w
  have hu := existsUniqueUltimateBearerWarshallCosted_cost_le M closures m w
  cases h : M.moment m w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def checkAx68Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.Costed.bind (inherenceMatricesCosted M) fun closures =>
    checkAx68WithClosuresCosted M closures

def checkAx68 (M : FiniteModel4) : Bool := (checkAx68Costed M).value

theorem checkAx68_eq_warshall (M : FiniteModel4) :
    checkAx68 M = checkAx68Warshall M := by
  unfold checkAx68 checkAx68Costed
  rw [Complexity.Costed.bind_value, checkAx68WithClosuresCosted_value]
  rfl

def checkAx68CostBound (M : FiniteModel4) : Nat :=
  M.worldCount * (7 * M.thingCount ^ 3 + 5 * M.thingCount ^ 2) +
    checkAx68EvaluationBound M

theorem checkAx68Costed_cost_le (M : FiniteModel4) :
    (checkAx68Costed M).cost ≤ checkAx68CostBound M := by
  unfold checkAx68Costed checkAx68CostBound
  rw [Complexity.Costed.bind_cost, inherenceMatricesCosted_cost]
  exact Nat.add_le_add_left
    (checkAx68WithClosuresCosted_cost_le M (inherenceMatricesCosted M).value) _

/-!
External dependence was formerly computed by an opaque `decide` over nested
quantifiers.  The following executable exposes those quantifiers and their
short-circuit order.  This is essential for the explicit-input machine model:
the theorem charges every inspected `ex` and `inheresIn` table cell.
-/

def existenceDifferenceCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) : Complexity.Costed Bool :=
  anyWorldsEvalCosted M fun w =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.ex x w) 1) fun _ =>
      (Complexity.Costed.tick (M.ex y w) 1).not

theorem existenceDifferenceCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) :
    (existenceDifferenceCosted M x y).value =
      anyWorlds M (fun w => M.ex x w && !(M.ex y w)) := by
  unfold existenceDifferenceCosted
  rw [anyWorldsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

def existenceDifferenceBound (M : FiniteModel4) : Nat := M.worldCount * 6

theorem existenceDifferenceCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) :
    (existenceDifferenceCosted M x y).cost ≤ existenceDifferenceBound M := by
  unfold existenceDifferenceCosted existenceDifferenceBound
  apply anyWorldsEvalCosted_cost_le M _ 4
  intro w
  cases h : M.ex x w <;>
    simp [Complexity.Costed.andThen, Complexity.Costed.not]

def externalSeparationCosted (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.implies (Complexity.Costed.tick (M.inheresIn x z w) 1) fun _ =>
    Complexity.Costed.andThen (existenceDifferenceCosted M y z) fun _ =>
      existenceDifferenceCosted M z y

theorem externalSeparationCosted_value (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (externalSeparationCosted M x y z w).value =
      impliesB (M.inheresIn x z w)
        (anyWorlds M (fun v => M.ex y v && !(M.ex z v)) &&
          anyWorlds M (fun v => M.ex z v && !(M.ex y v))) := by
  simp [externalSeparationCosted, Complexity.Costed.implies_value,
    Complexity.Costed.andThen_value, existenceDifferenceCosted_value, impliesB]

def externalSeparationBound (M : FiniteModel4) : Nat :=
  2 * existenceDifferenceBound M + 4

theorem externalSeparationCosted_cost_le (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (externalSeparationCosted M x y z w).cost ≤ externalSeparationBound M := by
  have hyz := existenceDifferenceCosted_cost_le M y z
  have hzy := existenceDifferenceCosted_cost_le M z y
  cases hi : M.inheresIn x z w <;>
    cases hd : (existenceDifferenceCosted M y z).value <;>
      simp [externalSeparationCosted, externalSeparationBound,
        Complexity.Costed.implies, Complexity.Costed.orElse,
        Complexity.Costed.andThen, Complexity.Costed.not, hi, hd] <;> omega

def externallyDependentCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (existentialDependenceCosted M x y w) fun _ =>
    allThingsEvalCosted M fun z => externalSeparationCosted M x y z w

theorem externallyDependentCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (externallyDependentCosted M x y w).value = externallyDependentB M x y w := by
  apply Bool.eq_iff_iff.mpr
  unfold externallyDependentCosted externallyDependentB
  rw [Complexity.Costed.andThen_value]
  change (existentialDependenceB M x y w &&
      (allThingsEvalCosted M fun z => externalSeparationCosted M x y z w).value) =
      true ↔ _
  rw [existentialDependenceB_eq_legacy]
  rw [allThingsEvalCosted_value, decide_eq_true_iff]
  simp [externalSeparationCosted_value, allWorlds_eq_true_iff,
    allThings_eq_true_iff, anyWorlds_eq_true_iff, impliesB]
  grind

def externallyDependentBound (M : FiniteModel4) : Nat :=
  existentialDependenceBound M + 1 +
    M.thingCount * (externalSeparationBound M + 2)

theorem externallyDependentCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (externallyDependentCosted M x y w).cost ≤ externallyDependentBound M := by
  have hd := existentialDependenceCosted_cost_le M x y w
  have hs : (allThingsEvalCosted M fun z =>
      externalSeparationCosted M x y z w).cost ≤
      M.thingCount * (externalSeparationBound M + 2) := by
    apply allThingsEvalCosted_cost_le M _ (externalSeparationBound M)
    intro z
    exact externalSeparationCosted_cost_le M x y z w
  cases h : (existentialDependenceCosted M x y w).value <;>
    simp [externallyDependentCosted, externallyDependentBound,
      Complexity.Costed.andThen, h] <;> omega

def checkAx69Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (externallyDependentCosted M x y w) fun _ =>
        externallyDependentCosted M x y w

def checkAx69 (M : FiniteModel4) : Bool := (checkAx69Costed M).value

theorem checkAx69_eq_legacy (M : FiniteModel4) :
    checkAx69 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (externallyDependentB M x y w)
        (externallyDependentB M x y w)))) := by
  unfold checkAx69 checkAx69Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.iff_value, externallyDependentCosted_value, iffB]

theorem checkAx69Costed_cost_le (M : FiniteModel4) :
    (checkAx69Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (2 * externallyDependentBound M + 4) + 2) + 2) := by
  unfold checkAx69Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (2 * externallyDependentBound M + 4) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * externallyDependentBound M + 4))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (2 * externallyDependentBound M + 2)
  intro w
  have h₁ := externallyDependentCosted_cost_le M x y w
  have h₂ := externallyDependentCosted_cost_le M x y w
  cases h : (externallyDependentCosted M x y w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def externallyDependentModeCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.mode x w) 1) fun _ =>
    anyThingsEvalCosted M fun y => externallyDependentCosted M x y w

theorem externallyDependentModeCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (externallyDependentModeCosted M x w).value = externallyDependentModeB M x w := by
  apply Bool.eq_iff_iff.mpr
  unfold externallyDependentModeCosted externallyDependentModeB
  rw [Complexity.Costed.andThen_value, anyThingsEvalCosted_value,
    decide_eq_true_iff]
  simp [anyThings_eq_true_iff, externallyDependentCosted_value]
  intro _hm
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [externallyDependentB] using hy
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [externallyDependentB] using hy

def externallyDependentModeBound (M : FiniteModel4) : Nat :=
  2 + M.thingCount * (externallyDependentBound M + 2)

theorem externallyDependentModeCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (externallyDependentModeCosted M x w).cost ≤ externallyDependentModeBound M := by
  have hs : (anyThingsEvalCosted M fun y => externallyDependentCosted M x y w).cost ≤
      M.thingCount * (externallyDependentBound M + 2) := by
    apply anyThingsEvalCosted_cost_le M _ (externallyDependentBound M)
    intro y
    exact externallyDependentCosted_cost_le M x y w
  cases h : M.mode x w <;>
    simp [externallyDependentModeCosted, externallyDependentModeBound,
      Complexity.Costed.andThen, h] ; omega

def checkAx70Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (externallyDependentModeCosted M x w) fun _ =>
      externallyDependentModeCosted M x w

def checkAx70 (M : FiniteModel4) : Bool := (checkAx70Costed M).value

theorem checkAx70_eq_legacy (M : FiniteModel4) :
    checkAx70 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (externallyDependentModeB M x w) (externallyDependentModeB M x w))) := by
  unfold checkAx70 checkAx70Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.iff_value, externallyDependentModeCosted_value, iffB]

theorem checkAx70Costed_cost_le (M : FiniteModel4) :
    (checkAx70Costed M).cost ≤ M.thingCount *
      (M.worldCount * (2 * externallyDependentModeBound M + 4) + 2) := by
  unfold checkAx70Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * externallyDependentModeBound M + 4))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (2 * externallyDependentModeBound M + 2)
  intro w
  have h₁ := externallyDependentModeCosted_cost_le M x w
  have h₂ := externallyDependentModeCosted_cost_le M x w
  cases h : (externallyDependentModeCosted M x w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def ax71ConsequentCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.orElse (externallyDependentModeCosted M x w) fun _ =>
      Complexity.Costed.tick (M.relator x w) 1) fun _ =>
    Complexity.Costed.tick (M.perdurant y w) 1

theorem ax71ConsequentCosted_value (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax71ConsequentCosted M x y w).value =
      ((externallyDependentModeB M x w || M.relator x w) && M.perdurant y w) := by
  simp [ax71ConsequentCosted, Complexity.Costed.andThen_value,
    Complexity.Costed.orElse_value, externallyDependentModeCosted_value]

theorem ax71ConsequentCosted_cost_le (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax71ConsequentCosted M x y w).cost ≤ externallyDependentModeBound M + 4 := by
  have hm := externallyDependentModeCosted_cost_le M x w
  cases he : (externallyDependentModeCosted M x w).value <;>
    cases hr : M.relator x w <;>
      simp [ax71ConsequentCosted, Complexity.Costed.andThen,
        Complexity.Costed.orElse, he, hr] <;> omega

def checkAx71Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.foundedBy x y w) 1) fun _ =>
        ax71ConsequentCosted M x y w

def checkAx71 (M : FiniteModel4) : Bool := (checkAx71Costed M).value

theorem checkAx71_eq_legacy (M : FiniteModel4) :
    checkAx71 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (M.foundedBy x y w)
        ((externallyDependentModeB M x w || M.relator x w) && M.perdurant y w)))) := by
  unfold checkAx71 checkAx71Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax71ConsequentCosted_value, impliesB]

theorem checkAx71Costed_cost_le (M : FiniteModel4) :
    (checkAx71Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (externallyDependentModeBound M + 9) + 2) + 2) := by
  unfold checkAx71Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (externallyDependentModeBound M + 9) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (externallyDependentModeBound M + 9))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (externallyDependentModeBound M + 7)
  intro w
  have hc := ax71ConsequentCosted_cost_le M x y w
  cases hf : M.foundedBy x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def foundedByUniqueForCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun z =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.foundedBy x z w) 1) fun _ =>
      Complexity.Costed.tick (decide (z = y)) 1

theorem foundedByUniqueForCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (foundedByUniqueForCosted M x y w).value =
      allThings M (fun z => impliesB (M.foundedBy x z w) (decide (z = y))) := by
  unfold foundedByUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem foundedByUniqueForCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (foundedByUniqueForCosted M x y w).cost ≤ M.thingCount * 6 := by
  unfold foundedByUniqueForCosted
  apply allThingsEvalCosted_cost_le M _ 4
  intro z
  cases h : M.foundedBy x z w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def foundedByWitnessCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.foundedBy x y w) 1) fun _ =>
    foundedByUniqueForCosted M x y w

theorem foundedByWitnessCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (foundedByWitnessCosted M x y w).value =
      (M.foundedBy x y w &&
        allThings M (fun z => impliesB (M.foundedBy x z w) (decide (z = y)))) := by
  simp [foundedByWitnessCosted, Complexity.Costed.andThen_value,
    foundedByUniqueForCosted_value]

theorem foundedByWitnessCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (foundedByWitnessCosted M x y w).cost ≤ M.thingCount * 6 + 2 := by
  have hu := foundedByUniqueForCosted_cost_le M x y w
  cases h : M.foundedBy x y w <;>
    simp [foundedByWitnessCosted, Complexity.Costed.andThen, h] ; omega

def existsUniqueFoundedByCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y => foundedByWitnessCosted M x y w

theorem existsUniqueFoundedByCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueFoundedByCosted M x w).value = existsUniqueFoundedByB M x w := by
  apply Bool.eq_iff_iff.mpr
  unfold existsUniqueFoundedByCosted existsUniqueFoundedByB
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [foundedByWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

def existsUniqueFoundedByBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 6 + 4)

theorem existsUniqueFoundedByCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueFoundedByCosted M x w).cost ≤ existsUniqueFoundedByBound M := by
  unfold existsUniqueFoundedByCosted existsUniqueFoundedByBound
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 6 + 2)
  intro y
  exact foundedByWitnessCosted_cost_le M x y w

def checkAx72Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.implies (externallyDependentModeCosted M x w) fun _ =>
      existsUniqueFoundedByCosted M x w

def checkAx72 (M : FiniteModel4) : Bool := (checkAx72Costed M).value

theorem checkAx72_eq_legacy (M : FiniteModel4) :
    checkAx72 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (externallyDependentModeB M x w) (existsUniqueFoundedByB M x w))) := by
  unfold checkAx72 checkAx72Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, externallyDependentModeCosted_value,
    existsUniqueFoundedByCosted_value, impliesB]

theorem checkAx72Costed_cost_le (M : FiniteModel4) :
    (checkAx72Costed M).cost ≤ M.thingCount *
      (M.worldCount * (externallyDependentModeBound M +
        existsUniqueFoundedByBound M + 4) + 2) := by
  unfold checkAx72Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (externallyDependentModeBound M +
      existsUniqueFoundedByBound M + 4))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (externallyDependentModeBound M + existsUniqueFoundedByBound M + 2)
  intro w
  have hm := externallyDependentModeCosted_cost_le M x w
  have hu := existsUniqueFoundedByCosted_cost_le M x w
  cases h : (externallyDependentModeCosted M x w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def sameFoundationCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun u =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.foundedBy x u w) 1) fun _ =>
      Complexity.Costed.tick (M.foundedBy y u w) 1

theorem sameFoundationCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (sameFoundationCosted M x y w).value = sameFoundationB M x y w := by
  unfold sameFoundationCosted sameFoundationB
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

def sameFoundationBound (M : FiniteModel4) : Nat := M.thingCount * 5

theorem sameFoundationCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (sameFoundationCosted M x y w).cost ≤ sameFoundationBound M := by
  unfold sameFoundationCosted sameFoundationBound
  apply anyThingsEvalCosted_cost_le M _ 3
  intro u
  cases h : M.foundedBy x u w <;>
    simp [Complexity.Costed.andThen]

def ax73ClassificationCosted (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen (externallyDependentModeCosted M z w) fun _ =>
      Complexity.Costed.tick (M.inheresIn z y w) 1) fun _ =>
    sameFoundationCosted M z x w

theorem ax73ClassificationCosted_value (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax73ClassificationCosted M x y z w).value =
      (externallyDependentModeB M z w && M.inheresIn z y w &&
        sameFoundationB M z x w) := by
  simp [ax73ClassificationCosted, Complexity.Costed.andThen_value,
    externallyDependentModeCosted_value, sameFoundationCosted_value]

def ax73ClassificationBound (M : FiniteModel4) : Nat :=
  externallyDependentModeBound M + sameFoundationBound M + 3

theorem ax73ClassificationCosted_cost_le (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax73ClassificationCosted M x y z w).cost ≤ ax73ClassificationBound M := by
  have hm := externallyDependentModeCosted_cost_le M z w
  have hs := sameFoundationCosted_cost_le M z x w
  cases he : (externallyDependentModeCosted M z w).value <;>
    cases hi : M.inheresIn z y w <;>
      simp [ax73ClassificationCosted, ax73ClassificationBound,
        Complexity.Costed.andThen, he, hi] <;> omega

def ax73PartsCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun z =>
    Complexity.Costed.iff (Complexity.Costed.tick (M.part z x w) 1) fun _ =>
      ax73ClassificationCosted M x y z w

theorem ax73PartsCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax73PartsCosted M x y w).value = allThings M (fun z =>
      iffB (M.part z x w) (externallyDependentModeB M z w &&
        M.inheresIn z y w && sameFoundationB M z x w)) := by
  unfold ax73PartsCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext z
  rw [Complexity.Costed.iff_value, ax73ClassificationCosted_value]
  cases hp : M.part z x w <;>
    cases hc : (externallyDependentModeB M z w && M.inheresIn z y w &&
      sameFoundationB M z x w) <;> rfl

def ax73PartsBound (M : FiniteModel4) : Nat :=
  M.thingCount * (ax73ClassificationBound M + 5)

theorem ax73PartsCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax73PartsCosted M x y w).cost ≤ ax73PartsBound M := by
  unfold ax73PartsCosted ax73PartsBound
  apply allThingsEvalCosted_cost_le M _ (ax73ClassificationBound M + 3)
  intro z
  have hc := ax73ClassificationCosted_cost_le M x y z w
  cases hp : M.part z x w <;>
    simp [Complexity.Costed.iff] <;> omega

def checkAx73Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (Complexity.Costed.tick (M.quaIndividualOf x y w) 1) fun _ =>
        ax73PartsCosted M x y w

def checkAx73 (M : FiniteModel4) : Bool := (checkAx73Costed M).value

theorem checkAx73_eq_legacy (M : FiniteModel4) :
    checkAx73 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (M.quaIndividualOf x y w)
        (allThings M fun z => iffB (M.part z x w)
          (externallyDependentModeB M z w && M.inheresIn z y w &&
            sameFoundationB M z x w))))) := by
  unfold checkAx73 checkAx73Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  congr 1
  funext w
  rw [Complexity.Costed.iff_value, ax73PartsCosted_value]
  cases hq : M.quaIndividualOf x y w <;>
    cases hp : (allThings M fun z => iffB (M.part z x w)
      (externallyDependentModeB M z w && M.inheresIn z y w &&
        sameFoundationB M z x w)) <;> rfl

theorem checkAx73Costed_cost_le (M : FiniteModel4) :
    (checkAx73Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (ax73PartsBound M + 5) + 2) + 2) := by
  unfold checkAx73Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (ax73PartsBound M + 5) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (ax73PartsBound M + 5))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (ax73PartsBound M + 3)
  intro w
  have hp := ax73PartsCosted_cost_le M x y w
  cases hq : M.quaIndividualOf x y w <;>
    simp [Complexity.Costed.iff] <;> omega

def checkAx77Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.relator x w) 1) fun _ =>
      existsUniqueFoundedByCosted M x w

def checkAx77 (M : FiniteModel4) : Bool := (checkAx77Costed M).value

theorem checkAx77_eq_legacy (M : FiniteModel4) :
    checkAx77 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.relator x w) (existsUniqueFoundedByB M x w))) := by
  unfold checkAx77 checkAx77Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, existsUniqueFoundedByCosted_value, impliesB]

theorem checkAx77Costed_cost_le (M : FiniteModel4) :
    (checkAx77Costed M).cost ≤ M.thingCount *
      (M.worldCount * (existsUniqueFoundedByBound M + 5) + 2) := by
  unfold checkAx77Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (existsUniqueFoundedByBound M + 5))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (existsUniqueFoundedByBound M + 3)
  intro w
  have hu := existsUniqueFoundedByCosted_cost_le M x w
  cases h : M.relator x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def quaIndividualExistsCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y => Complexity.Costed.tick (M.quaIndividualOf x y w) 1

theorem quaIndividualExistsCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (quaIndividualExistsCosted M x w).value =
      anyThings M (fun y => M.quaIndividualOf x y w) := by
  unfold quaIndividualExistsCosted
  rw [anyThingsEvalCosted_value]
  rfl

def quaIndividualExistsBound (M : FiniteModel4) : Nat := M.thingCount * 3

theorem quaIndividualExistsCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (quaIndividualExistsCosted M x w).cost ≤ quaIndividualExistsBound M := by
  unfold quaIndividualExistsCosted quaIndividualExistsBound
  apply anyThingsEvalCosted_cost_le M _ 1
  intro y
  simp

def checkAx74Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (quaIndividualExistsCosted M x w) fun _ =>
      quaIndividualExistsCosted M x w

def checkAx74 (M : FiniteModel4) : Bool := (checkAx74Costed M).value

theorem checkAx74_eq_legacy (M : FiniteModel4) :
    checkAx74 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (anyThings M fun y => M.quaIndividualOf x y w)
        (anyThings M fun y => M.quaIndividualOf x y w))) := by
  unfold checkAx74 checkAx74Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.iff_value, quaIndividualExistsCosted_value, iffB]

theorem checkAx74Costed_cost_le (M : FiniteModel4) :
    (checkAx74Costed M).cost ≤ M.thingCount *
      (M.worldCount * (2 * quaIndividualExistsBound M + 4) + 2) := by
  unfold checkAx74Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (2 * quaIndividualExistsBound M + 4))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (2 * quaIndividualExistsBound M + 2)
  intro w
  have h₁ := quaIndividualExistsCosted_cost_le M x w
  have h₂ := quaIndividualExistsCosted_cost_le M x w
  cases h : (quaIndividualExistsCosted M x w).value <;>
    simp [Complexity.Costed.iff, h] <;> omega

def checkAx75Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.implies (quaIndividualExistsCosted M x w) fun _ =>
      externallyDependentModeCosted M x w

def checkAx75 (M : FiniteModel4) : Bool := (checkAx75Costed M).value

theorem checkAx75_eq_legacy (M : FiniteModel4) :
    checkAx75 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (anyThings M fun y => M.quaIndividualOf x y w)
        (externallyDependentModeB M x w))) := by
  unfold checkAx75 checkAx75Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, quaIndividualExistsCosted_value,
    externallyDependentModeCosted_value, impliesB]

theorem checkAx75Costed_cost_le (M : FiniteModel4) :
    (checkAx75Costed M).cost ≤ M.thingCount *
      (M.worldCount * (quaIndividualExistsBound M +
        externallyDependentModeBound M + 4) + 2) := by
  unfold checkAx75Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (quaIndividualExistsBound M +
      externallyDependentModeBound M + 4))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (quaIndividualExistsBound M + externallyDependentModeBound M + 2)
  intro w
  have hq := quaIndividualExistsCosted_cost_le M x w
  have hm := externallyDependentModeCosted_cost_le M x w
  cases h : (quaIndividualExistsCosted M x w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def checkAx76Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkThreeThingsWorldsImpCosted M
    (fun x y _ w => M.quaIndividualOf x y w)
    (fun x _ y' w => M.quaIndividualOf x y' w)
    (fun _ y y' _ => decide (y = y'))

def checkAx76 (M : FiniteModel4) : Bool := (checkAx76Costed M).value

theorem checkAx76_eq_legacy (M : FiniteModel4) :
    checkAx76 M = allThings M (fun x => allThings M (fun y =>
      allThings M (fun y' => allWorlds M (fun w =>
        impliesB (M.quaIndividualOf x y w && M.quaIndividualOf x y' w)
          (decide (y = y')))))) :=
  checkThreeThingsWorldsImpCosted_value M _ _ _

theorem checkAx76Costed_cost_le (M : FiniteModel4) :
    (checkAx76Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) :=
  checkThreeThingsWorldsImpCosted_cost_le M _ _ _

def checkAx78Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.andThen (Complexity.Costed.tick (M.relator x w) 1) fun _ =>
          Complexity.Costed.tick (M.part y x w) 1) fun _ =>
        sameFoundationCosted M x y w

def checkAx78 (M : FiniteModel4) : Bool := (checkAx78Costed M).value

theorem checkAx78_eq_legacy (M : FiniteModel4) :
    checkAx78 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (M.relator x w && M.part y x w)
        (sameFoundationB M x y w)))) := by
  unfold checkAx78 checkAx78Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    sameFoundationCosted_value, impliesB]

theorem checkAx78Costed_cost_le (M : FiniteModel4) :
    (checkAx78Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (sameFoundationBound M + 7) + 2) + 2) := by
  unfold checkAx78Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (sameFoundationBound M + 7) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (sameFoundationBound M + 7))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (sameFoundationBound M + 5)
  intro w
  have hs := sameFoundationCosted_cost_le M x y w
  cases hr : M.relator x w <;> cases hp : M.part y x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not] ; omega

def boxExImpCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  existentialDependenceCosted M x y w

theorem boxExImpCosted_value (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (boxExImpCosted M x y w).value = boxExImpB M x y w := by
  change existentialDependenceB M x y w = boxExImpB M x y w
  apply Bool.eq_iff_iff.mpr
  rw [existentialDependenceB_eq_legacy]
  unfold boxExImpB
  rw [allWorlds_eq_true_iff, decide_eq_true_iff]
  simp [impliesB]
  grind

theorem boxExImpCosted_cost_le (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (boxExImpCosted M x y w).cost ≤ existentialDependenceBound M :=
  existentialDependenceCosted_cost_le M x y w

def properPartExistsCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y => Complexity.Costed.tick (M.properPart y x w) 1

theorem properPartExistsCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (properPartExistsCosted M x w).value =
      anyThings M (fun y => M.properPart y x w) := by
  unfold properPartExistsCosted
  rw [anyThingsEvalCosted_value]
  rfl

def properPartExistsBound (M : FiniteModel4) : Nat := M.thingCount * 3

theorem properPartExistsCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (properPartExistsCosted M x w).cost ≤ properPartExistsBound M := by
  unfold properPartExistsCosted properPartExistsBound
  apply anyThingsEvalCosted_cost_le M _ 1
  intro y
  simp

def ax79PairCompatibilityCosted (M : FiniteModel4)
    (y z : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (quaIndividualExistsCosted M y w) fun _ =>
    Complexity.Costed.andThen (quaIndividualExistsCosted M z w) fun _ =>
      Complexity.Costed.andThen (sameFoundationCosted M y z w) fun _ =>
        Complexity.Costed.andThen (boxExImpCosted M y z w) fun _ =>
          boxExImpCosted M z y w

theorem ax79PairCompatibilityCosted_value (M : FiniteModel4)
    (y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79PairCompatibilityCosted M y z w).value =
      ((anyThings M fun q => M.quaIndividualOf y q w) &&
        (anyThings M fun q => M.quaIndividualOf z q w) &&
        sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w) := by
  simp [ax79PairCompatibilityCosted, Complexity.Costed.andThen_value,
    quaIndividualExistsCosted_value, sameFoundationCosted_value,
    boxExImpCosted_value, Bool.and_assoc]

def ax79PairCompatibilityBound (M : FiniteModel4) : Nat :=
  2 * quaIndividualExistsBound M + sameFoundationBound M +
    2 * existentialDependenceBound M + 4

theorem ax79PairCompatibilityCosted_cost_le (M : FiniteModel4)
    (y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79PairCompatibilityCosted M y z w).cost ≤ ax79PairCompatibilityBound M := by
  have hqy := quaIndividualExistsCosted_cost_le M y w
  have hqz := quaIndividualExistsCosted_cost_le M z w
  have hs := sameFoundationCosted_cost_le M y z w
  have hyz := boxExImpCosted_cost_le M y z w
  have hzy := boxExImpCosted_cost_le M z y w
  cases hqyV : (quaIndividualExistsCosted M y w).value <;>
    cases hqzV : (quaIndividualExistsCosted M z w).value <;>
      cases hsV : (sameFoundationCosted M y z w).value <;>
        cases hyzV : (boxExImpCosted M y z w).value <;>
          simp [ax79PairCompatibilityCosted, ax79PairCompatibilityBound,
            Complexity.Costed.andThen, hqyV, hqzV, hsV, hyzV] <;> omega

def ax79PairConditionCosted (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.implies
    (Complexity.Costed.andThen (Complexity.Costed.tick (M.properPart y x w) 1) fun _ =>
      Complexity.Costed.tick (M.properPart z x w) 1) fun _ =>
    ax79PairCompatibilityCosted M y z w

theorem ax79PairConditionCosted_value (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79PairConditionCosted M x y z w).value =
      impliesB (M.properPart y x w && M.properPart z x w)
        ((anyThings M fun q => M.quaIndividualOf y q w) &&
          (anyThings M fun q => M.quaIndividualOf z q w) &&
          sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w) := by
  simp [ax79PairConditionCosted, Complexity.Costed.implies_value,
    Complexity.Costed.andThen_value, ax79PairCompatibilityCosted_value, impliesB]

def ax79PairConditionBound (M : FiniteModel4) : Nat :=
  ax79PairCompatibilityBound M + 5

theorem ax79PairConditionCosted_cost_le (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79PairConditionCosted M x y z w).cost ≤ ax79PairConditionBound M := by
  have ha : (Complexity.Costed.andThen
      (Complexity.Costed.tick (M.properPart y x w) 1) fun _ =>
        Complexity.Costed.tick (M.properPart z x w) 1).cost ≤ 3 := by
    apply Complexity.Costed.andThen_cost_le _ _ 1 1 <;> simp
  have hc := ax79PairCompatibilityCosted_cost_le M y z w
  cases hy : M.properPart y x w <;> cases hz : M.properPart z x w <;>
    simp [ax79PairConditionCosted, ax79PairConditionBound,
      Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not, hy, hz] ; omega

def ax79PairwiseCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun y => allThingsEvalCosted M fun z =>
    ax79PairConditionCosted M x y z w

theorem ax79PairwiseCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79PairwiseCosted M x w).value = allThings M (fun y => allThings M fun z =>
      impliesB (M.properPart y x w && M.properPart z x w)
        ((anyThings M fun q => M.quaIndividualOf y q w) &&
          (anyThings M fun q => M.quaIndividualOf z q w) &&
          sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w)) := by
  unfold ax79PairwiseCosted
  rw [allThingsEvalCosted_value]
  congr 1; funext y
  rw [allThingsEvalCosted_value]
  simp [ax79PairConditionCosted_value]

def ax79PairwiseBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * (ax79PairConditionBound M + 2) + 2)

theorem ax79PairwiseCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79PairwiseCosted M x w).cost ≤ ax79PairwiseBound M := by
  unfold ax79PairwiseCosted ax79PairwiseBound
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (ax79PairConditionBound M + 2))
  intro y
  apply allThingsEvalCosted_cost_le M _ (ax79PairConditionBound M)
  intro z
  exact ax79PairConditionCosted_cost_le M x y z w

def ax79ClosurePremiseCosted (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.properPart y x w) 1) fun _ =>
    Complexity.Costed.andThen (quaIndividualExistsCosted M z w) fun _ =>
      Complexity.Costed.andThen (sameFoundationCosted M y z w) fun _ =>
        Complexity.Costed.andThen (boxExImpCosted M y z w) fun _ =>
          boxExImpCosted M z y w

theorem ax79ClosurePremiseCosted_value (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79ClosurePremiseCosted M x y z w).value =
      (M.properPart y x w &&
        (anyThings M fun q => M.quaIndividualOf z q w) &&
        sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w) := by
  simp [ax79ClosurePremiseCosted, Complexity.Costed.andThen_value,
    quaIndividualExistsCosted_value, sameFoundationCosted_value,
    boxExImpCosted_value, Bool.and_assoc]

def ax79ClosurePremiseBound (M : FiniteModel4) : Nat :=
  quaIndividualExistsBound M + sameFoundationBound M +
    2 * existentialDependenceBound M + 5

theorem ax79ClosurePremiseCosted_cost_le (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79ClosurePremiseCosted M x y z w).cost ≤ ax79ClosurePremiseBound M := by
  have hq := quaIndividualExistsCosted_cost_le M z w
  have hs := sameFoundationCosted_cost_le M y z w
  have hyz := boxExImpCosted_cost_le M y z w
  have hzy := boxExImpCosted_cost_le M z y w
  cases hpV : M.properPart y x w <;>
    cases hqV : (quaIndividualExistsCosted M z w).value <;>
      cases hsV : (sameFoundationCosted M y z w).value <;>
        cases hyzV : (boxExImpCosted M y z w).value <;>
          simp [ax79ClosurePremiseCosted, ax79ClosurePremiseBound,
            Complexity.Costed.andThen, hpV, hqV, hsV, hyzV] <;> omega

def ax79ClosureConditionCosted (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.implies (ax79ClosurePremiseCosted M x y z w) fun _ =>
    Complexity.Costed.tick (M.properPart z x w) 1

theorem ax79ClosureConditionCosted_value (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79ClosureConditionCosted M x y z w).value =
      impliesB
        (M.properPart y x w &&
          (anyThings M fun q => M.quaIndividualOf z q w) &&
          sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w)
        (M.properPart z x w) := by
  simp [ax79ClosureConditionCosted, Complexity.Costed.implies_value,
    ax79ClosurePremiseCosted_value, impliesB]

def ax79ClosureConditionBound (M : FiniteModel4) : Nat :=
  ax79ClosurePremiseBound M + 3

theorem ax79ClosureConditionCosted_cost_le (M : FiniteModel4)
    (x y z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79ClosureConditionCosted M x y z w).cost ≤ ax79ClosureConditionBound M := by
  have hp := ax79ClosurePremiseCosted_cost_le M x y z w
  cases h : (ax79ClosurePremiseCosted M x y z w).value <;>
    simp [ax79ClosureConditionCosted, ax79ClosureConditionBound,
      Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def ax79ClosureCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun y => allThingsEvalCosted M fun z =>
    ax79ClosureConditionCosted M x y z w

theorem ax79ClosureCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79ClosureCosted M x w).value = allThings M (fun y => allThings M fun z =>
      impliesB
        (M.properPart y x w &&
          (anyThings M fun q => M.quaIndividualOf z q w) &&
          sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w)
        (M.properPart z x w)) := by
  unfold ax79ClosureCosted
  rw [allThingsEvalCosted_value]
  congr 1; funext y
  rw [allThingsEvalCosted_value]
  simp [ax79ClosureConditionCosted_value]

def ax79ClosureBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * (ax79ClosureConditionBound M + 2) + 2)

theorem ax79ClosureCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79ClosureCosted M x w).cost ≤ ax79ClosureBound M := by
  unfold ax79ClosureCosted ax79ClosureBound
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (ax79ClosureConditionBound M + 2))
  intro y
  apply allThingsEvalCosted_cost_le M _ (ax79ClosureConditionBound M)
  intro z
  exact ax79ClosureConditionCosted_cost_le M x y z w

def ax79CharacterizationCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (properPartExistsCosted M x w) fun _ =>
    Complexity.Costed.andThen (ax79PairwiseCosted M x w) fun _ =>
      ax79ClosureCosted M x w

theorem ax79CharacterizationCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79CharacterizationCosted M x w).value =
      ((anyThings M fun y => M.properPart y x w) &&
        (allThings M fun y => allThings M fun z =>
          impliesB (M.properPart y x w && M.properPart z x w)
            ((anyThings M fun q => M.quaIndividualOf y q w) &&
              (anyThings M fun q => M.quaIndividualOf z q w) &&
              sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w)) &&
        (allThings M fun y => allThings M fun z =>
          impliesB
            (M.properPart y x w &&
              (anyThings M fun q => M.quaIndividualOf z q w) &&
              sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w)
            (M.properPart z x w))) := by
  simp [ax79CharacterizationCosted, Complexity.Costed.andThen_value,
    properPartExistsCosted_value, ax79PairwiseCosted_value,
    ax79ClosureCosted_value, Bool.and_assoc]

def ax79CharacterizationBound (M : FiniteModel4) : Nat :=
  properPartExistsBound M + ax79PairwiseBound M + ax79ClosureBound M + 2

theorem ax79CharacterizationCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax79CharacterizationCosted M x w).cost ≤ ax79CharacterizationBound M := by
  have he := properPartExistsCosted_cost_le M x w
  have hp := ax79PairwiseCosted_cost_le M x w
  have hc := ax79ClosureCosted_cost_le M x w
  cases heV : (properPartExistsCosted M x w).value <;>
    cases hpV : (ax79PairwiseCosted M x w).value <;>
      simp [ax79CharacterizationCosted, ax79CharacterizationBound,
        Complexity.Costed.andThen, heV, hpV] <;> omega

def checkAx79Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (Complexity.Costed.tick (M.relator x w) 1) fun _ =>
      ax79CharacterizationCosted M x w

def checkAx79 (M : FiniteModel4) : Bool := (checkAx79Costed M).value

theorem checkAx79_eq_legacy (M : FiniteModel4) :
    checkAx79 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (M.relator x w)
        ((anyThings M fun y => M.properPart y x w) &&
          (allThings M fun y => allThings M fun z =>
            impliesB (M.properPart y x w && M.properPart z x w)
              ((anyThings M fun q => M.quaIndividualOf y q w) &&
                (anyThings M fun q => M.quaIndividualOf z q w) &&
                sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w)) &&
          (allThings M fun y => allThings M fun z =>
            impliesB
              (M.properPart y x w &&
                (anyThings M fun q => M.quaIndividualOf z q w) &&
                sameFoundationB M y z w && boxExImpB M y z w && boxExImpB M z y w)
              (M.properPart z x w))))) := by
  unfold checkAx79 checkAx79Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  congr 1
  funext w
  rw [Complexity.Costed.iff_value, ax79CharacterizationCosted_value]
  cases hr : M.relator x w <;>
    cases hc : (ax79CharacterizationCosted M x w).value <;>
      simp [iffB]

theorem checkAx79Costed_cost_le (M : FiniteModel4) :
    (checkAx79Costed M).cost ≤ M.thingCount *
      (M.worldCount * (ax79CharacterizationBound M + 5) + 2) := by
  unfold checkAx79Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (ax79CharacterizationBound M + 5))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (ax79CharacterizationBound M + 3)
  intro w
  have hc := ax79CharacterizationCosted_cost_le M x w
  cases h : M.relator x w <;>
    simp [Complexity.Costed.iff] <;> omega

def mediationWitnessCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun z =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.quaIndividualOf z y w) 1) fun _ =>
      Complexity.Costed.tick (M.part z x w) 1

theorem mediationWitnessCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (mediationWitnessCosted M x y w).value =
      anyThings M (fun z => M.quaIndividualOf z y w && M.part z x w) := by
  unfold mediationWitnessCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

def mediationWitnessBound (M : FiniteModel4) : Nat := M.thingCount * 5

theorem mediationWitnessCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (mediationWitnessCosted M x y w).cost ≤ mediationWitnessBound M := by
  unfold mediationWitnessCosted mediationWitnessBound
  apply anyThingsEvalCosted_cost_le M _ 3
  intro z
  cases h : M.quaIndividualOf z y w <;>
    simp [Complexity.Costed.andThen]

def ax80CharacterizationCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen (Complexity.Costed.tick (M.relator x w) 1) fun _ =>
      Complexity.Costed.tick (M.endurant y w) 1) fun _ =>
    mediationWitnessCosted M x y w

theorem ax80CharacterizationCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax80CharacterizationCosted M x y w).value =
      (M.relator x w && M.endurant y w &&
        anyThings M (fun z => M.quaIndividualOf z y w && M.part z x w)) := by
  simp [ax80CharacterizationCosted, Complexity.Costed.andThen_value,
    mediationWitnessCosted_value]

def ax80CharacterizationBound (M : FiniteModel4) : Nat :=
  mediationWitnessBound M + 4

theorem ax80CharacterizationCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax80CharacterizationCosted M x y w).cost ≤ ax80CharacterizationBound M := by
  have hw := mediationWitnessCosted_cost_le M x y w
  cases hr : M.relator x w <;> cases he : M.endurant y w <;>
    simp [ax80CharacterizationCosted, ax80CharacterizationBound,
      Complexity.Costed.andThen, hr, he] ; omega

def checkAx80Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (Complexity.Costed.tick (M.mediates x y w) 1) fun _ =>
        ax80CharacterizationCosted M x y w

def checkAx80 (M : FiniteModel4) : Bool := (checkAx80Costed M).value

theorem checkAx80_eq_legacy (M : FiniteModel4) :
    checkAx80 M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => iffB (M.mediates x y w)
        (M.relator x w && M.endurant y w &&
          anyThings M fun z => M.quaIndividualOf z y w && M.part z x w)))) := by
  unfold checkAx80 checkAx80Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  congr 1
  funext w
  rw [Complexity.Costed.iff_value, ax80CharacterizationCosted_value]
  cases hm : M.mediates x y w <;>
    cases hc : (M.relator x w && M.endurant y w &&
      anyThings M fun z => M.quaIndividualOf z y w && M.part z x w) <;> rfl

theorem checkAx80Costed_cost_le (M : FiniteModel4) :
    (checkAx80Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (ax80CharacterizationBound M + 5) + 2) + 2) := by
  unfold checkAx80Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (ax80CharacterizationBound M + 5) + 2))
  intro x
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (ax80CharacterizationBound M + 5))
  intro y
  apply allWorldsEvalCosted_cost_le M _ (ax80CharacterizationBound M + 3)
  intro w
  have hc := ax80CharacterizationCosted_cost_le M x y w
  cases hm : M.mediates x y w <;>
    simp [Complexity.Costed.iff] <;> omega

def checkAxQuaIndividualOfEndurantCosted (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.quaIndividualOf x y w) 1) fun _ =>
        Complexity.Costed.tick (M.endurant y w) 1

def checkAxQuaIndividualOfEndurant (M : FiniteModel4) : Bool :=
  (checkAxQuaIndividualOfEndurantCosted M).value

theorem checkAxQuaIndividualOfEndurant_eq_legacy (M : FiniteModel4) :
    checkAxQuaIndividualOfEndurant M = allThings M (fun x => allThings M (fun y =>
      allWorlds M (fun w => impliesB (M.quaIndividualOf x y w) (M.endurant y w)))) := by
  unfold checkAxQuaIndividualOfEndurant checkAxQuaIndividualOfEndurantCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.implies_value]
  rfl

theorem checkAxQuaIndividualOfEndurantCosted_cost_le (M : FiniteModel4) :
    (checkAxQuaIndividualOfEndurantCosted M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 6 + 2) + 2) := by
  unfold checkAxQuaIndividualOfEndurantCosted
  apply allThingsEvalCosted_cost_le M _ _; intro x
  apply allThingsEvalCosted_cost_le M _ _; intro y
  apply allWorldsEvalCosted_cost_le M _ 4; intro w
  cases hq : M.quaIndividualOf x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse, Complexity.Costed.not]

def instInheresUniqueForCosted (M : FiniteModel4)
    (z t y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun y' =>
    Complexity.Costed.implies
      (Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y' t w) 1) fun _ =>
        Complexity.Costed.tick (M.inheresIn z y' w) 1) fun _ =>
      Complexity.Costed.tick (decide (y' = y)) 1

theorem instInheresUniqueForCosted_value (M : FiniteModel4)
    (z t y : Fin M.thingCount) (w : Fin M.worldCount) :
    (instInheresUniqueForCosted M z t y w).value = allThings M (fun y' =>
      impliesB (M.inst y' t w && M.inheresIn z y' w) (decide (y' = y))) := by
  unfold instInheresUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value, impliesB]

theorem instInheresUniqueForCosted_cost_le (M : FiniteModel4)
    (z t y : Fin M.thingCount) (w : Fin M.worldCount) :
    (instInheresUniqueForCosted M z t y w).cost ≤ M.thingCount * 8 := by
  unfold instInheresUniqueForCosted
  apply allThingsEvalCosted_cost_le M _ 6
  intro y'
  cases hi : M.inst y' t w <;> cases hh : M.inheresIn z y' w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not]

def instInheresWitnessCosted (M : FiniteModel4)
    (z t y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y t w) 1) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inheresIn z y w) 1) fun _ =>
      instInheresUniqueForCosted M z t y w

theorem instInheresWitnessCosted_value (M : FiniteModel4)
    (z t y : Fin M.thingCount) (w : Fin M.worldCount) :
    (instInheresWitnessCosted M z t y w).value =
      (M.inst y t w && M.inheresIn z y w && allThings M (fun y' =>
        impliesB (M.inst y' t w && M.inheresIn z y' w) (decide (y' = y)))) := by
  simp [instInheresWitnessCosted, Complexity.Costed.andThen_value,
    instInheresUniqueForCosted_value, Bool.and_assoc]

theorem instInheresWitnessCosted_cost_le (M : FiniteModel4)
    (z t y : Fin M.thingCount) (w : Fin M.worldCount) :
    (instInheresWitnessCosted M z t y w).cost ≤ M.thingCount * 8 + 4 := by
  have hu := instInheresUniqueForCosted_cost_le M z t y w
  cases hi : M.inst y t w <;> cases hh : M.inheresIn z y w <;>
    simp [instInheresWitnessCosted, Complexity.Costed.andThen, hi, hh] ; omega

def existsUniqueInstInheresCosted (M : FiniteModel4)
    (z t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y => instInheresWitnessCosted M z t y w

theorem existsUniqueInstInheresCosted_value (M : FiniteModel4)
    (z t : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueInstInheresCosted M z t w).value = existsUniqueInstInheresB M z t w := by
  apply Bool.eq_iff_iff.mpr
  unfold existsUniqueInstInheresCosted existsUniqueInstInheresB
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [instInheresWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

def existsUniqueInstInheresBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 8 + 6)

theorem existsUniqueInstInheresCosted_cost_le (M : FiniteModel4)
    (z t : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueInstInheresCosted M z t w).cost ≤ existsUniqueInstInheresBound M := by
  unfold existsUniqueInstInheresCosted existsUniqueInstInheresBound
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 8 + 4)
  intro y
  exact instInheresWitnessCosted_cost_le M z t y w

def ax82InstancesCosted (M : FiniteModel4)
    (t q : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.inst x q w) 1) fun _ =>
      existsUniqueInstInheresCosted M x t w

theorem ax82InstancesCosted_value (M : FiniteModel4)
    (t q : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax82InstancesCosted M t q w).value = allThings M (fun x =>
      impliesB (M.inst x q w) (existsUniqueInstInheresB M x t w)) := by
  unfold ax82InstancesCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, existsUniqueInstInheresCosted_value,
    impliesB]

def ax82InstancesBound (M : FiniteModel4) : Nat :=
  M.thingCount * (existsUniqueInstInheresBound M + 5)

theorem ax82InstancesCosted_cost_le (M : FiniteModel4)
    (t q : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax82InstancesCosted M t q w).cost ≤ ax82InstancesBound M := by
  unfold ax82InstancesCosted ax82InstancesBound
  apply allThingsEvalCosted_cost_le M _ (existsUniqueInstInheresBound M + 3)
  intro x
  have hu := existsUniqueInstInheresCosted_cost_le M x t w
  cases h : M.inst x q w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def ax81MomentWitnessCosted (M : FiniteModel4)
    (m x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.inst y m w) 1) fun _ =>
      Complexity.Costed.tick (M.inheresIn y x w) 1

theorem ax81MomentWitnessCosted_value (M : FiniteModel4)
    (m x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax81MomentWitnessCosted M m x w).value =
      anyThings M (fun y => M.inst y m w && M.inheresIn y x w) := by
  unfold ax81MomentWitnessCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

def ax81MomentWitnessBound (M : FiniteModel4) : Nat := M.thingCount * 5

theorem ax81MomentWitnessCosted_cost_le (M : FiniteModel4)
    (m x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax81MomentWitnessCosted M m x w).cost ≤ ax81MomentWitnessBound M := by
  unfold ax81MomentWitnessCosted ax81MomentWitnessBound
  apply anyThingsEvalCosted_cost_le M _ 3
  intro y
  cases h : M.inst y m w <;> simp [Complexity.Costed.andThen]

def ax81TypeInstancesCosted (M : FiniteModel4)
    (t m : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.inst x t w) 1) fun _ =>
      ax81MomentWitnessCosted M m x w

theorem ax81TypeInstancesCosted_value (M : FiniteModel4)
    (t m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax81TypeInstancesCosted M t m w).value = allThings M (fun x =>
      impliesB (M.inst x t w)
        (anyThings M fun y => M.inst y m w && M.inheresIn y x w)) := by
  unfold ax81TypeInstancesCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax81MomentWitnessCosted_value, impliesB]

def ax81TypeInstancesBound (M : FiniteModel4) : Nat :=
  M.thingCount * (ax81MomentWitnessBound M + 5)

theorem ax81TypeInstancesCosted_cost_le (M : FiniteModel4)
    (t m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax81TypeInstancesCosted M t m w).cost ≤ ax81TypeInstancesBound M := by
  unfold ax81TypeInstancesCosted ax81TypeInstancesBound
  apply allThingsEvalCosted_cost_le M _ (ax81MomentWitnessBound M + 3)
  intro x
  have hw := ax81MomentWitnessCosted_cost_le M m x w
  cases h : M.inst x t w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def ax81ConsequentCosted (M : FiniteModel4)
    (t m : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.endurantType t w) 1) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.momentType m w) 1) fun _ =>
      Complexity.Costed.andThen (ax81TypeInstancesCosted M t m w) fun _ =>
        ax82InstancesCosted M t m w

theorem ax81ConsequentCosted_value (M : FiniteModel4)
    (t m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax81ConsequentCosted M t m w).value =
      (M.endurantType t w && M.momentType m w &&
        (allThings M fun x => impliesB (M.inst x t w)
          (anyThings M fun y => M.inst y m w && M.inheresIn y x w)) &&
        (allThings M fun z => impliesB (M.inst z m w)
          (existsUniqueInstInheresB M z t w))) := by
  simp [ax81ConsequentCosted, Complexity.Costed.andThen_value,
    ax81TypeInstancesCosted_value, ax82InstancesCosted_value, Bool.and_assoc]

def ax81ConsequentBound (M : FiniteModel4) : Nat :=
  ax81TypeInstancesBound M + ax82InstancesBound M + 5

theorem ax81ConsequentCosted_cost_le (M : FiniteModel4)
    (t m : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax81ConsequentCosted M t m w).cost ≤ ax81ConsequentBound M := by
  have ht := ax81TypeInstancesCosted_cost_le M t m w
  have hm := ax82InstancesCosted_cost_le M t m w
  cases he : M.endurantType t w <;> cases hmo : M.momentType m w <;>
    cases hi : (ax81TypeInstancesCosted M t m w).value <;>
      simp [ax81ConsequentCosted, ax81ConsequentBound,
        Complexity.Costed.andThen, he, hmo, hi] <;> omega

def checkAx81Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allThingsEvalCosted M fun m =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.tick (M.characterization t m w) 1) fun _ =>
        ax81ConsequentCosted M t m w

def checkAx81 (M : FiniteModel4) : Bool := (checkAx81Costed M).value

theorem checkAx81_eq_legacy (M : FiniteModel4) :
    checkAx81 M = allThings M (fun t => allThings M (fun m =>
      allWorlds M (fun w => impliesB (M.characterization t m w)
        (M.endurantType t w && M.momentType m w &&
          (allThings M fun x => impliesB (M.inst x t w)
            (anyThings M fun y => M.inst y m w && M.inheresIn y x w)) &&
          (allThings M fun z => impliesB (M.inst z m w)
            (existsUniqueInstInheresB M z t w)))))) := by
  unfold checkAx81 checkAx81Costed
  rw [allThingsEvalCosted_value]; congr 1; funext t
  rw [allThingsEvalCosted_value]; congr 1; funext m
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax81ConsequentCosted_value, impliesB]

theorem checkAx81Costed_cost_le (M : FiniteModel4) :
    (checkAx81Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (ax81ConsequentBound M + 5) + 2) + 2) := by
  unfold checkAx81Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (ax81ConsequentBound M + 5) + 2))
  intro t
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (ax81ConsequentBound M + 5))
  intro m
  apply allWorldsEvalCosted_cost_le M _ (ax81ConsequentBound M + 3)
  intro w
  have hc := ax81ConsequentCosted_cost_le M t m w
  cases h : M.characterization t m w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def checkAx82Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allThingsEvalCosted M fun q =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.andThen (Complexity.Costed.tick (M.characterization t q w) 1)
          fun _ => Complexity.Costed.tick (M.qualityType q w) 1) fun _ =>
        ax82InstancesCosted M t q w

def checkAx82 (M : FiniteModel4) : Bool := (checkAx82Costed M).value

theorem checkAx82_eq_legacy (M : FiniteModel4) :
    checkAx82 M = allThings M (fun t => allThings M (fun q =>
      allWorlds M (fun w => impliesB (M.characterization t q w && M.qualityType q w)
        (allThings M fun x => impliesB (M.inst x q w)
          (existsUniqueInstInheresB M x t w))))) := by
  unfold checkAx82 checkAx82Costed
  rw [allThingsEvalCosted_value]; congr 1; funext t
  rw [allThingsEvalCosted_value]; congr 1; funext q
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    ax82InstancesCosted_value, impliesB]

theorem checkAx82Costed_cost_le (M : FiniteModel4) :
    (checkAx82Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (ax82InstancesBound M + 7) + 2) + 2) := by
  unfold checkAx82Costed
  apply allThingsEvalCosted_cost_le M _
    (M.thingCount * (M.worldCount * (ax82InstancesBound M + 7) + 2))
  intro t
  apply allThingsEvalCosted_cost_le M _ (M.worldCount * (ax82InstancesBound M + 7))
  intro q
  apply allWorldsEvalCosted_cost_le M _ (ax82InstancesBound M + 5)
  intro w
  have hi := ax82InstancesCosted_cost_le M t q w
  cases hc : M.characterization t q w <;> cases hq : M.qualityType q w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not] ; omega

def checkAx83Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableImplicationCosted M M.quale M.abstractIndividual

def checkAx83 (M : FiniteModel4) : Bool := (checkAx83Costed M).value

theorem checkAx83_eq_legacy (M : FiniteModel4) :
    checkAx83 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.quale x w) (M.abstractIndividual x w))) :=
  checkUnaryTableImplicationCosted_value M M.quale M.abstractIndividual

theorem checkAx83Costed_cost_le (M : FiniteModel4) :
    (checkAx83Costed M).cost ≤ M.thingCount * (M.worldCount * 6 + 2) :=
  checkUnaryTableImplicationCosted_cost_le M M.quale M.abstractIndividual

def checkAx84Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableImplicationCosted M M.set_ M.abstractIndividual

def checkAx84 (M : FiniteModel4) : Bool := (checkAx84Costed M).value

theorem checkAx84_eq_legacy (M : FiniteModel4) :
    checkAx84 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.set_ x w) (M.abstractIndividual x w))) :=
  checkUnaryTableImplicationCosted_value M M.set_ M.abstractIndividual

theorem checkAx84Costed_cost_le (M : FiniteModel4) :
    (checkAx84Costed M).cost ≤ M.thingCount * (M.worldCount * 6 + 2) :=
  checkUnaryTableImplicationCosted_cost_le M M.set_ M.abstractIndividual

def checkAx85Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkWorldFirstDisjointCosted M M.quale M.set_

def checkAx85 (M : FiniteModel4) : Bool := (checkAx85Costed M).value

theorem checkAx85_eq_legacy (M : FiniteModel4) :
    checkAx85 M = allWorlds M (fun w => allThings M (fun x =>
      !(M.quale x w && M.set_ x w))) :=
  checkWorldFirstDisjointCosted_value M M.quale M.set_

theorem checkAx85Costed_cost_le (M : FiniteModel4) :
    (checkAx85Costed M).cost ≤ M.worldCount * (M.thingCount * 6 + 2) :=
  checkWorldFirstDisjointCosted_cost_le M M.quale M.set_

def qualityStructureCandidateCosted (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.qualityType t w) 1) fun _ =>
    Complexity.Costed.tick (M.associatedWith x t w) 1

theorem qualityStructureCandidateCosted_value (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureCandidateCosted M x t w).value =
      (M.qualityType t w && M.associatedWith x t w) := by
  simp [qualityStructureCandidateCosted, Complexity.Costed.andThen_value]

theorem qualityStructureCandidateCosted_cost_le (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureCandidateCosted M x t w).cost ≤ 3 := by
  cases h : M.qualityType t w <;>
    simp [qualityStructureCandidateCosted, Complexity.Costed.andThen, h]

def qualityStructureUniqueForCosted (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t' =>
    Complexity.Costed.implies (qualityStructureCandidateCosted M x t' w) fun _ =>
      Complexity.Costed.tick (decide (t' = t)) 1

theorem qualityStructureUniqueForCosted_value (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureUniqueForCosted M x t w).value = allThings M (fun t' =>
      impliesB (M.qualityType t' w && M.associatedWith x t' w) (decide (t' = t))) := by
  unfold qualityStructureUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, qualityStructureCandidateCosted_value, impliesB]

theorem qualityStructureUniqueForCosted_cost_le (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureUniqueForCosted M x t w).cost ≤ M.thingCount * 8 := by
  unfold qualityStructureUniqueForCosted
  apply allThingsEvalCosted_cost_le M _ 6
  intro t'
  have hc := qualityStructureCandidateCosted_cost_le M x t' w
  cases h : (qualityStructureCandidateCosted M x t' w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def qualityStructureWitnessCosted (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityStructureCandidateCosted M x t w) fun _ =>
    qualityStructureUniqueForCosted M x t w

theorem qualityStructureWitnessCosted_value (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureWitnessCosted M x t w).value =
      ((M.qualityType t w && M.associatedWith x t w) && allThings M (fun t' =>
        impliesB (M.qualityType t' w && M.associatedWith x t' w) (decide (t' = t)))) := by
  simp [qualityStructureWitnessCosted, Complexity.Costed.andThen_value,
    qualityStructureCandidateCosted_value, qualityStructureUniqueForCosted_value]

theorem qualityStructureWitnessCosted_cost_le (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureWitnessCosted M x t w).cost ≤ M.thingCount * 8 + 4 := by
  have hc := qualityStructureCandidateCosted_cost_le M x t w
  have hu := qualityStructureUniqueForCosted_cost_le M x t w
  cases h : (qualityStructureCandidateCosted M x t w).value <;>
    simp [qualityStructureWitnessCosted, Complexity.Costed.andThen, h] <;> omega

def qualityStructureCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun t => qualityStructureWitnessCosted M x t w

theorem qualityStructureCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureCosted M x w).value = qualityStructureB M x w := by
  apply Bool.eq_iff_iff.mpr
  unfold qualityStructureCosted qualityStructureB
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [qualityStructureWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

def qualityStructureBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 8 + 6)

theorem qualityStructureCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureCosted M x w).cost ≤ qualityStructureBound M := by
  unfold qualityStructureCosted qualityStructureBound
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 8 + 4)
  intro t
  exact qualityStructureWitnessCosted_cost_le M x t w

def nonEmptySetCosted (M : FiniteModel4)
    (s : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun x => Complexity.Costed.tick (M.memberOf x s w) 1

theorem nonEmptySetCosted_value (M : FiniteModel4)
    (s : Fin M.thingCount) (w : Fin M.worldCount) :
    (nonEmptySetCosted M s w).value = nonEmptySetB M s w := by
  unfold nonEmptySetCosted nonEmptySetB
  rw [anyThingsEvalCosted_value]
  rfl

def nonEmptySetBound (M : FiniteModel4) : Nat := M.thingCount * 3

theorem nonEmptySetCosted_cost_le (M : FiniteModel4)
    (s : Fin M.thingCount) (w : Fin M.worldCount) :
    (nonEmptySetCosted M s w).cost ≤ nonEmptySetBound M := by
  unfold nonEmptySetCosted nonEmptySetBound
  apply anyThingsEvalCosted_cost_le M _ 1
  intro x
  simp

def ax86ConsequentCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.set_ x w) 1) fun _ =>
    nonEmptySetCosted M x w

theorem ax86ConsequentCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax86ConsequentCosted M x w).value = (M.set_ x w && nonEmptySetB M x w) := by
  simp [ax86ConsequentCosted, Complexity.Costed.andThen_value, nonEmptySetCosted_value]

def checkAx86Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.implies (qualityStructureCosted M x w) fun _ =>
      ax86ConsequentCosted M x w

def checkAx86 (M : FiniteModel4) : Bool := (checkAx86Costed M).value

theorem checkAx86_eq_legacy (M : FiniteModel4) :
    checkAx86 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (qualityStructureB M x w) (M.set_ x w && nonEmptySetB M x w))) := by
  unfold checkAx86 checkAx86Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, qualityStructureCosted_value,
    ax86ConsequentCosted_value, impliesB]

theorem checkAx86Costed_cost_le (M : FiniteModel4) :
    (checkAx86Costed M).cost ≤ M.thingCount *
      (M.worldCount * (qualityStructureBound M + nonEmptySetBound M + 6) + 2) := by
  unfold checkAx86Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (qualityStructureBound M + nonEmptySetBound M + 6))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (qualityStructureBound M + nonEmptySetBound M + 4)
  intro w
  have hq := qualityStructureCosted_cost_le M x w
  have hn := nonEmptySetCosted_cost_le M x w
  cases hqs : (qualityStructureCosted M x w).value <;> cases hs : M.set_ x w <;>
    simp [ax86ConsequentCosted, Complexity.Costed.implies,
      Complexity.Costed.orElse, Complexity.Costed.andThen,
      Complexity.Costed.not, hqs, hs] <;> omega

def qualityStructureMemberCandidateCosted (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityStructureCosted M s w) fun _ =>
    Complexity.Costed.tick (M.memberOf x s w) 1

theorem qualityStructureMemberCandidateCosted_value (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureMemberCandidateCosted M x s w).value =
      (qualityStructureB M s w && M.memberOf x s w) := by
  simp [qualityStructureMemberCandidateCosted, Complexity.Costed.andThen_value,
    qualityStructureCosted_value]

theorem qualityStructureMemberCandidateCosted_cost_le (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureMemberCandidateCosted M x s w).cost ≤ qualityStructureBound M + 2 := by
  have hq := qualityStructureCosted_cost_le M s w
  cases h : (qualityStructureCosted M s w).value <;>
    simp [qualityStructureMemberCandidateCosted, Complexity.Costed.andThen, h] <;> omega

def qualityStructureMemberUniqueForCosted (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun s' =>
    Complexity.Costed.implies (qualityStructureMemberCandidateCosted M x s' w) fun _ =>
      Complexity.Costed.tick (decide (s' = s)) 1

def qualityStructureMemberUniqueForBound (M : FiniteModel4) : Nat :=
  M.thingCount * (qualityStructureBound M + 7)

theorem qualityStructureMemberUniqueForCosted_value (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureMemberUniqueForCosted M x s w).value = allThings M (fun s' =>
      impliesB (qualityStructureB M s' w && M.memberOf x s' w) (decide (s' = s))) := by
  unfold qualityStructureMemberUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value,
    qualityStructureMemberCandidateCosted_value, impliesB]

theorem qualityStructureMemberUniqueForCosted_cost_le (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureMemberUniqueForCosted M x s w).cost ≤
      qualityStructureMemberUniqueForBound M := by
  unfold qualityStructureMemberUniqueForCosted qualityStructureMemberUniqueForBound
  apply allThingsEvalCosted_cost_le M _ (qualityStructureBound M + 5)
  intro s'
  have hc := qualityStructureMemberCandidateCosted_cost_le M x s' w
  cases h : (qualityStructureMemberCandidateCosted M x s' w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def qualityStructureMemberWitnessCosted (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityStructureMemberCandidateCosted M x s w) fun _ =>
    qualityStructureMemberUniqueForCosted M x s w

theorem qualityStructureMemberWitnessCosted_value (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureMemberWitnessCosted M x s w).value =
      ((qualityStructureB M s w && M.memberOf x s w) && allThings M (fun s' =>
        impliesB (qualityStructureB M s' w && M.memberOf x s' w) (decide (s' = s)))) := by
  simp [qualityStructureMemberWitnessCosted, Complexity.Costed.andThen_value,
    qualityStructureMemberCandidateCosted_value,
    qualityStructureMemberUniqueForCosted_value]

theorem qualityStructureMemberWitnessCosted_cost_le (M : FiniteModel4)
    (x s : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureMemberWitnessCosted M x s w).cost ≤
      qualityStructureBound M + qualityStructureMemberUniqueForBound M + 3 := by
  have hc := qualityStructureMemberCandidateCosted_cost_le M x s w
  have hu := qualityStructureMemberUniqueForCosted_cost_le M x s w
  cases h : (qualityStructureMemberCandidateCosted M x s w).value <;>
    simp [qualityStructureMemberWitnessCosted, Complexity.Costed.andThen, h] <;> omega

def existsUniqueQualityStructureMemberCosted (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun s => qualityStructureMemberWitnessCosted M x s w

def existsUniqueQualityStructureMemberBound (M : FiniteModel4) : Nat :=
  M.thingCount * (qualityStructureBound M +
    qualityStructureMemberUniqueForBound M + 5)

theorem existsUniqueQualityStructureMemberCosted_value (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueQualityStructureMemberCosted M x w).value =
      existsUniqueQualityStructureMemberB M x w := by
  apply Bool.eq_iff_iff.mpr
  unfold existsUniqueQualityStructureMemberCosted existsUniqueQualityStructureMemberB
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [qualityStructureMemberWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

theorem existsUniqueQualityStructureMemberCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueQualityStructureMemberCosted M x w).cost ≤
      existsUniqueQualityStructureMemberBound M := by
  unfold existsUniqueQualityStructureMemberCosted existsUniqueQualityStructureMemberBound
  apply anyThingsEvalCosted_cost_le M _
    (qualityStructureBound M + qualityStructureMemberUniqueForBound M + 3)
  intro s
  exact qualityStructureMemberWitnessCosted_cost_le M x s w

def checkAx87Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (Complexity.Costed.tick (M.quale x w) 1) fun _ =>
      existsUniqueQualityStructureMemberCosted M x w

def checkAx87 (M : FiniteModel4) : Bool := (checkAx87Costed M).value

theorem checkAx87_eq_legacy (M : FiniteModel4) :
    checkAx87 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (M.quale x w) (existsUniqueQualityStructureMemberB M x w))) := by
  unfold checkAx87 checkAx87Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  congr 1
  funext w
  rw [Complexity.Costed.iff_value,
    existsUniqueQualityStructureMemberCosted_value]
  cases hq : M.quale x w <;>
    cases hu : existsUniqueQualityStructureMemberB M x w <;> rfl

theorem checkAx87Costed_cost_le (M : FiniteModel4) :
    (checkAx87Costed M).cost ≤ M.thingCount *
      (M.worldCount * (existsUniqueQualityStructureMemberBound M + 5) + 2) := by
  unfold checkAx87Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (existsUniqueQualityStructureMemberBound M + 5))
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (existsUniqueQualityStructureMemberBound M + 3)
  intro w
  have hu := existsUniqueQualityStructureMemberCosted_cost_le M x w
  cases h : M.quale x w <;> simp [Complexity.Costed.iff] <;> omega

def checkAx88Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (qualityStructureCosted M x w) fun _ =>
      Complexity.Costed.orElse (Complexity.Costed.tick (M.qualityDomain x w) 1) fun _ =>
        Complexity.Costed.tick (M.qualityDimension x w) 1

def checkAx88 (M : FiniteModel4) : Bool := (checkAx88Costed M).value

theorem checkAx88_eq_legacy (M : FiniteModel4) :
    checkAx88 M = allThings M (fun x => allWorlds M (fun w =>
      iffB (qualityStructureB M x w)
        (M.qualityDomain x w || M.qualityDimension x w))) := by
  unfold checkAx88 checkAx88Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  congr 1
  funext w
  rw [Complexity.Costed.iff_value, Complexity.Costed.orElse_value,
    qualityStructureCosted_value]
  simp only [Complexity.Costed.tick_value]
  cases hq : qualityStructureB M x w <;>
    cases hd : (M.qualityDomain x w || M.qualityDimension x w) <;> rfl

theorem checkAx88Costed_cost_le (M : FiniteModel4) :
    (checkAx88Costed M).cost ≤ M.thingCount *
      (M.worldCount * (qualityStructureBound M + 7) + 2) := by
  unfold checkAx88Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (qualityStructureBound M + 7))
  intro x
  apply allWorldsEvalCosted_cost_le M _ (qualityStructureBound M + 5)
  intro w
  have hq := qualityStructureCosted_cost_le M x w
  cases hs : (qualityStructureCosted M x w).value <;>
    cases hd : M.qualityDomain x w <;>
      simp [Complexity.Costed.iff, Complexity.Costed.orElse, hs] <;> omega

def checkAx89Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkUnaryTableDisjointCosted M M.qualityDomain M.qualityDimension

def checkAx89 (M : FiniteModel4) : Bool := (checkAx89Costed M).value

theorem checkAx89_eq_legacy (M : FiniteModel4) :
    checkAx89 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (M.qualityDomain x w) (!(M.qualityDimension x w)))) :=
  checkUnaryTableDisjointCosted_value M M.qualityDomain M.qualityDimension

theorem checkAx89Costed_cost_le (M : FiniteModel4) :
    (checkAx89Costed M).cost ≤ M.thingCount * (M.worldCount * 7 + 2) :=
  checkUnaryTableDisjointCosted_cost_le M M.qualityDomain M.qualityDimension

/-!
Axiom 90 is the first quality-space law whose consequent performs two complete
membership scans.  We expose both scans instead of assigning a cost to the
already-decided `properSubsetB`.  This is the same executable-interpreter
discipline used throughout this file: the production value is the erasure of
the instrumented computation (cf. RadixExperiment), while the compositional
cost accounting follows Niu et al. and Haslbeck.  See
`docs/dsl/complexity.md` for the distinct roles of those references.
-/

def properSubsetContainedCosted (M : FiniteModel4) (s t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x =>
    Complexity.Costed.implies
      (Complexity.Costed.tick (M.memberOf x s w) 1) fun _ =>
      Complexity.Costed.tick (M.memberOf x t w) 1

def properSubsetDifferenceCosted (M : FiniteModel4) (s t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun x =>
    Complexity.Costed.andThen
      (Complexity.Costed.tick (M.memberOf x t w) 1) fun _ =>
      (Complexity.Costed.tick (M.memberOf x s w) 1).not

def properSubsetCosted (M : FiniteModel4) (s t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (properSubsetContainedCosted M s t w) fun _ =>
    properSubsetDifferenceCosted M s t w

theorem properSubsetCosted_value (M : FiniteModel4) (s t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (properSubsetCosted M s t w).value = properSubsetB M s t w := by
  unfold properSubsetCosted properSubsetContainedCosted properSubsetDifferenceCosted
    properSubsetB
  rw [Complexity.Costed.andThen_value, allThingsEvalCosted_value,
    anyThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value, impliesB]

theorem properSubsetContainedCosted_cost_le (M : FiniteModel4)
    (s t : Fin M.thingCount) (w : Fin M.worldCount) :
    (properSubsetContainedCosted M s t w).cost ≤ M.thingCount * 6 := by
  unfold properSubsetContainedCosted
  apply allThingsEvalCosted_cost_le M _ 4
  intro x
  cases h : M.memberOf x s w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

theorem properSubsetDifferenceCosted_cost_le (M : FiniteModel4)
    (s t : Fin M.thingCount) (w : Fin M.worldCount) :
    (properSubsetDifferenceCosted M s t w).cost ≤ M.thingCount * 6 := by
  unfold properSubsetDifferenceCosted
  apply anyThingsEvalCosted_cost_le M _ 4
  intro x
  cases h : M.memberOf x t w <;>
    simp [Complexity.Costed.andThen, Complexity.Costed.not]

theorem properSubsetCosted_cost_le (M : FiniteModel4) (s t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (properSubsetCosted M s t w).cost ≤ 12 * M.thingCount + 1 := by
  have hc := properSubsetContainedCosted_cost_le M s t w
  have hd := properSubsetDifferenceCosted_cost_le M s t w
  cases h : (properSubsetContainedCosted M s t w).value <;>
    simp [properSubsetCosted, Complexity.Costed.andThen, h] <;> omega

def ax90AntecedentCosted (M : FiniteModel4) (s t s' t' : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.associatedWith s t w) 1) fun _ =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.associatedWith s' t' w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.sub t' t w) 1) fun _ =>
        (Complexity.Costed.tick (M.sub t t' w) 1).not

theorem ax90AntecedentCosted_value (M : FiniteModel4) (s t s' t' : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax90AntecedentCosted M s t s' t' w).value =
      (M.associatedWith s t w && M.associatedWith s' t' w &&
        (M.sub t' t w && !(M.sub t t' w))) := by
  simp [ax90AntecedentCosted, Complexity.Costed.andThen_value, Bool.and_assoc]

theorem ax90AntecedentCosted_cost_le (M : FiniteModel4)
    (s t s' t' : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax90AntecedentCosted M s t s' t' w).cost ≤ 8 := by
  unfold ax90AntecedentCosted
  cases h₁ : M.associatedWith s t w <;>
    cases h₂ : M.associatedWith s' t' w <;>
      cases h₃ : M.sub t' t w <;>
        simp [Complexity.Costed.andThen, Complexity.Costed.not]

def checkAx90Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun s =>
    allThingsEvalCosted M fun t =>
      allThingsEvalCosted M fun s' =>
        allThingsEvalCosted M fun t' =>
          allWorldsEvalCosted M fun w =>
            Complexity.Costed.implies (ax90AntecedentCosted M s t s' t' w) fun _ =>
              properSubsetCosted M s' s w

def checkAx90 (M : FiniteModel4) : Bool := (checkAx90Costed M).value

theorem checkAx90_eq_legacy (M : FiniteModel4) :
    checkAx90 M = allThings M (fun s => allThings M (fun t =>
      allThings M (fun s' => allThings M (fun t' => allWorlds M (fun w =>
        impliesB (M.associatedWith s t w && M.associatedWith s' t' w &&
          (M.sub t' t w && !(M.sub t t' w))) (properSubsetB M s' s w)))))) := by
  unfold checkAx90 checkAx90Costed
  rw [allThingsEvalCosted_value]; congr 1; funext s
  rw [allThingsEvalCosted_value]; congr 1; funext t
  rw [allThingsEvalCosted_value]; congr 1; funext s'
  rw [allThingsEvalCosted_value]; congr 1; funext t'
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  simp [Complexity.Costed.implies_value, ax90AntecedentCosted_value,
    properSubsetCosted_value, impliesB]

def checkAx90Bound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * (M.thingCount * (M.thingCount *
    (M.worldCount * (12 * M.thingCount + 13) + 2) + 2) + 2) + 2)

theorem checkAx90Costed_cost_le (M : FiniteModel4) :
    (checkAx90Costed M).cost ≤ checkAx90Bound M := by
  unfold checkAx90Costed checkAx90Bound
  apply allThingsEvalCosted_cost_le M _ _
  intro s
  apply allThingsEvalCosted_cost_le M _ _
  intro t
  apply allThingsEvalCosted_cost_le M _ _
  intro s'
  apply allThingsEvalCosted_cost_le M _ _
  intro t'
  apply allWorldsEvalCosted_cost_le M _ (12 * M.thingCount + 11)
  intro w
  have h := Complexity.Costed.implies_cost_le _
    (fun _ => properSubsetCosted M s' s w) 8 (12 * M.thingCount + 1)
    (ax90AntecedentCosted_cost_le M s t s' t' w)
    (properSubsetCosted_cost_le M s' s w)
  omega

def qualityStructureForTypeCandidateCosted (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityStructureCosted M x w) fun _ =>
    Complexity.Costed.tick (M.associatedWith x t w) 1

theorem qualityStructureForTypeCandidateCosted_value (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureForTypeCandidateCosted M t x w).value =
      (qualityStructureB M x w && M.associatedWith x t w) := by
  simp [qualityStructureForTypeCandidateCosted, Complexity.Costed.andThen_value,
    qualityStructureCosted_value]

theorem qualityStructureForTypeCandidateCosted_cost_le (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureForTypeCandidateCosted M t x w).cost ≤ qualityStructureBound M + 2 := by
  have hq := qualityStructureCosted_cost_le M x w
  cases h : (qualityStructureCosted M x w).value <;>
    simp [qualityStructureForTypeCandidateCosted, Complexity.Costed.andThen, h] <;> omega

def qualityStructureForTypeUniqueCosted (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x' =>
    Complexity.Costed.implies (qualityStructureForTypeCandidateCosted M t x' w) fun _ =>
      Complexity.Costed.tick (decide (x' = x)) 1

def qualityStructureForTypeUniqueBound (M : FiniteModel4) : Nat :=
  M.thingCount * (qualityStructureBound M + 7)

theorem qualityStructureForTypeUniqueCosted_value (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureForTypeUniqueCosted M t x w).value = allThings M (fun x' =>
      impliesB (qualityStructureB M x' w && M.associatedWith x' t w)
        (decide (x' = x))) := by
  unfold qualityStructureForTypeUniqueCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value,
    qualityStructureForTypeCandidateCosted_value, impliesB]

theorem qualityStructureForTypeUniqueCosted_cost_le (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureForTypeUniqueCosted M t x w).cost ≤
      qualityStructureForTypeUniqueBound M := by
  unfold qualityStructureForTypeUniqueCosted qualityStructureForTypeUniqueBound
  apply allThingsEvalCosted_cost_le M _ (qualityStructureBound M + 5)
  intro x'
  have hc := qualityStructureForTypeCandidateCosted_cost_le M t x' w
  cases h : (qualityStructureForTypeCandidateCosted M t x' w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def qualityStructureForTypeWitnessCosted (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityStructureForTypeCandidateCosted M t x w) fun _ =>
    qualityStructureForTypeUniqueCosted M t x w

theorem qualityStructureForTypeWitnessCosted_value (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureForTypeWitnessCosted M t x w).value =
      ((qualityStructureB M x w && M.associatedWith x t w) &&
        allThings M (fun x' => impliesB
          (qualityStructureB M x' w && M.associatedWith x' t w) (decide (x' = x)))) := by
  simp [qualityStructureForTypeWitnessCosted, Complexity.Costed.andThen_value,
    qualityStructureForTypeCandidateCosted_value,
    qualityStructureForTypeUniqueCosted_value]

theorem qualityStructureForTypeWitnessCosted_cost_le (M : FiniteModel4)
    (t x : Fin M.thingCount) (w : Fin M.worldCount) :
    (qualityStructureForTypeWitnessCosted M t x w).cost ≤
      qualityStructureBound M + qualityStructureForTypeUniqueBound M + 3 := by
  have hc := qualityStructureForTypeCandidateCosted_cost_le M t x w
  have hu := qualityStructureForTypeUniqueCosted_cost_le M t x w
  cases h : (qualityStructureForTypeCandidateCosted M t x w).value <;>
    simp [qualityStructureForTypeWitnessCosted, Complexity.Costed.andThen, h] <;> omega

def existsUniqueQualityStructureForTypeCosted (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun x => qualityStructureForTypeWitnessCosted M t x w

def existsUniqueQualityStructureForTypeBound (M : FiniteModel4) : Nat :=
  M.thingCount * (qualityStructureBound M +
    qualityStructureForTypeUniqueBound M + 5)

theorem existsUniqueQualityStructureForTypeCosted_value (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueQualityStructureForTypeCosted M t w).value = decide
      (∃ x : Fin M.thingCount,
        (qualityStructureB M x w = true ∧ M.associatedWith x t w = true) ∧
          ∀ x' : Fin M.thingCount,
            qualityStructureB M x' w = true ∧ M.associatedWith x' t w = true → x' = x) := by
  apply Bool.eq_iff_iff.mpr
  unfold existsUniqueQualityStructureForTypeCosted
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [qualityStructureForTypeWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

theorem existsUniqueQualityStructureForTypeCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueQualityStructureForTypeCosted M t w).cost ≤
      existsUniqueQualityStructureForTypeBound M := by
  unfold existsUniqueQualityStructureForTypeCosted existsUniqueQualityStructureForTypeBound
  apply anyThingsEvalCosted_cost_le M _
    (qualityStructureBound M + qualityStructureForTypeUniqueBound M + 3)
  intro x
  exact qualityStructureForTypeWitnessCosted_cost_le M t x w

def ax91ConsequentCosted (M : FiniteModel4) (t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.intrinsicMomentType t w) 1) fun _ =>
    existsUniqueQualityStructureForTypeCosted M t w

def checkAx91Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun t => allWorldsEvalCosted M fun w =>
    Complexity.Costed.iff (Complexity.Costed.tick (M.qualityType t w) 1) fun _ =>
      ax91ConsequentCosted M t w

def checkAx91 (M : FiniteModel4) : Bool := (checkAx91Costed M).value

theorem checkAx91_eq_legacy (M : FiniteModel4) :
    checkAx91 M = allThings M (fun t => allWorlds M (fun w =>
      iffB (M.qualityType t w)
        (M.intrinsicMomentType t w && decide
          (∃ x : Fin M.thingCount,
            (qualityStructureB M x w = true ∧ M.associatedWith x t w = true) ∧
              ∀ x' : Fin M.thingCount,
                qualityStructureB M x' w = true ∧ M.associatedWith x' t w = true →
                  x' = x)))) := by
  unfold checkAx91 checkAx91Costed ax91ConsequentCosted
  rw [allThingsEvalCosted_value]; congr 1; funext t
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value, Complexity.Costed.andThen_value,
    existsUniqueQualityStructureForTypeCosted_value]
  simp only [Complexity.Costed.tick_value]
  cases hq : M.qualityType t w <;> cases hi : M.intrinsicMomentType t w <;>
    cases he : decide (∃ x : Fin M.thingCount,
      (qualityStructureB M x w = true ∧ M.associatedWith x t w = true) ∧
        ∀ x' : Fin M.thingCount,
          qualityStructureB M x' w = true ∧ M.associatedWith x' t w = true → x' = x) <;> rfl

theorem checkAx91Costed_cost_le (M : FiniteModel4) :
    (checkAx91Costed M).cost ≤ M.thingCount *
      (M.worldCount * (existsUniqueQualityStructureForTypeBound M + 7) + 2) := by
  unfold checkAx91Costed
  apply allThingsEvalCosted_cost_le M _
    (M.worldCount * (existsUniqueQualityStructureForTypeBound M + 7))
  intro t
  apply allWorldsEvalCosted_cost_le M _
    (existsUniqueQualityStructureForTypeBound M + 5)
  intro w
  have he := existsUniqueQualityStructureForTypeCosted_cost_le M t w
  cases hq : M.qualityType t w <;> cases hi : M.intrinsicMomentType t w <;>
    simp [ax91ConsequentCosted, Complexity.Costed.iff,
      Complexity.Costed.andThen, hi] <;> omega

def ax92ConsequentCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityBCosted M x w) fun _ =>
    Complexity.Costed.tick (M.quale y w) 1

def checkAx92Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.hasValue x y w) 1) fun _ =>
        ax92ConsequentCosted M x y w

def checkAx92 (M : FiniteModel4) : Bool := (checkAx92Costed M).value

theorem checkAx92_eq_legacy (M : FiniteModel4) :
    checkAx92 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      impliesB (M.hasValue x y w) (qualityB M x w && M.quale y w)))) := by
  unfold checkAx92 checkAx92Costed ax92ConsequentCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    qualityB, impliesB]

def qualityBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 8 + 6)

theorem checkAx92Costed_cost_le (M : FiniteModel4) :
    (checkAx92Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (qualityBound M + 7) + 2) + 2) := by
  unfold checkAx92Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allWorldsEvalCosted_cost_le M _ (qualityBound M + 5)
  intro w
  have hq := qualityBCosted_cost_le M x w
  unfold qualityBound
  cases hh : M.hasValue x y w <;> cases hqb : (qualityBCosted M x w).value <;>
    simp [ax92ConsequentCosted, Complexity.Costed.implies,
      Complexity.Costed.orElse, Complexity.Costed.andThen,
      Complexity.Costed.not, hqb] <;> omega

def hasValueUniqueForCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun y' =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.hasValue x y' w) 1) fun _ =>
      Complexity.Costed.tick (decide (y' = y)) 1

theorem hasValueUniqueForCosted_value (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (hasValueUniqueForCosted M x y w).value = allThings M (fun y' =>
      impliesB (M.hasValue x y' w) (decide (y' = y))) := by
  unfold hasValueUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem hasValueUniqueForCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (hasValueUniqueForCosted M x y w).cost ≤ M.thingCount * 6 := by
  unfold hasValueUniqueForCosted
  apply allThingsEvalCosted_cost_le M _ 4
  intro y'
  cases h : M.hasValue x y' w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def hasValueWitnessCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.hasValue x y w) 1) fun _ =>
    hasValueUniqueForCosted M x y w

theorem hasValueWitnessCosted_value (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (hasValueWitnessCosted M x y w).value =
      (M.hasValue x y w && allThings M (fun y' =>
        impliesB (M.hasValue x y' w) (decide (y' = y)))) := by
  simp [hasValueWitnessCosted, Complexity.Costed.andThen_value,
    hasValueUniqueForCosted_value]

theorem hasValueWitnessCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (hasValueWitnessCosted M x y w).cost ≤ M.thingCount * 6 + 2 := by
  have hu := hasValueUniqueForCosted_cost_le M x y w
  cases h : M.hasValue x y w <;>
    simp [hasValueWitnessCosted, Complexity.Costed.andThen, h] ; omega

def existsUniqueHasValueCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun y => hasValueWitnessCosted M x y w

def existsUniqueHasValueBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 6 + 4)

theorem existsUniqueHasValueCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (existsUniqueHasValueCosted M x w).value = existsUniqueHasValueB M x w := by
  apply Bool.eq_iff_iff.mpr
  unfold existsUniqueHasValueCosted existsUniqueHasValueB
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [hasValueWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

theorem existsUniqueHasValueCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueHasValueCosted M x w).cost ≤ existsUniqueHasValueBound M := by
  unfold existsUniqueHasValueCosted existsUniqueHasValueBound
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 6 + 2)
  intro y
  exact hasValueWitnessCosted_cost_le M x y w

def checkAx93Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.implies (qualityBCosted M x w) fun _ =>
      existsUniqueHasValueCosted M x w

def checkAx93 (M : FiniteModel4) : Bool := (checkAx93Costed M).value

theorem checkAx93_eq_legacy (M : FiniteModel4) :
    checkAx93 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (qualityB M x w) (existsUniqueHasValueB M x w))) := by
  unfold checkAx93 checkAx93Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, existsUniqueHasValueCosted_value,
    qualityB, impliesB]

theorem checkAx93Costed_cost_le (M : FiniteModel4) :
    (checkAx93Costed M).cost ≤ M.thingCount *
      (M.worldCount * (qualityBound M + existsUniqueHasValueBound M + 4) + 2) := by
  unfold checkAx93Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (qualityBound M + existsUniqueHasValueBound M + 2)
  intro w
  have hq := qualityBCosted_cost_le M x w
  have he := existsUniqueHasValueCosted_cost_le M x w
  unfold qualityBound at *
  cases h : (qualityBCosted M x w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def ax94WitnessCandidateCosted (M : FiniteModel4)
    (x y t s : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen (Complexity.Costed.tick (M.inst x t w) 1) fun _ =>
      Complexity.Costed.tick (M.associatedWith s t w) 1) fun _ =>
    Complexity.Costed.tick (M.memberOf y s w) 1

theorem ax94WitnessCandidateCosted_value (M : FiniteModel4)
    (x y t s : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax94WitnessCandidateCosted M x y t s w).value =
      (M.inst x t w && M.associatedWith s t w && M.memberOf y s w) := by
  simp [ax94WitnessCandidateCosted, Complexity.Costed.andThen_value]

theorem ax94WitnessCandidateCosted_cost_le (M : FiniteModel4)
    (x y t s : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax94WitnessCandidateCosted M x y t s w).cost ≤ 5 := by
  unfold ax94WitnessCandidateCosted
  cases hi : M.inst x t w <;> cases ha : M.associatedWith s t w <;>
    simp [Complexity.Costed.andThen]

def ax94WitnessCosted (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun t => anyThingsEvalCosted M fun s =>
    ax94WitnessCandidateCosted M x y t s w

def ax94WitnessBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 7 + 2)

theorem ax94WitnessCosted_value (M : FiniteModel4) (x y : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax94WitnessCosted M x y w).value = anyThings M (fun t => anyThings M (fun s =>
      M.inst x t w && M.associatedWith s t w && M.memberOf y s w)) := by
  unfold ax94WitnessCosted
  rw [anyThingsEvalCosted_value]; congr 1; funext t
  rw [anyThingsEvalCosted_value]
  simp [ax94WitnessCandidateCosted_value]

theorem ax94WitnessCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax94WitnessCosted M x y w).cost ≤ ax94WitnessBound M := by
  unfold ax94WitnessCosted ax94WitnessBound
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 7)
  intro t
  apply anyThingsEvalCosted_cost_le M _ 5
  intro s
  exact ax94WitnessCandidateCosted_cost_le M x y t s w

def checkAx94Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.hasValue x y w) 1) fun _ =>
        ax94WitnessCosted M x y w

def checkAx94 (M : FiniteModel4) : Bool := (checkAx94Costed M).value

theorem checkAx94_eq_legacy (M : FiniteModel4) :
    checkAx94 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      impliesB (M.hasValue x y w) (anyThings M (fun t => anyThings M (fun s =>
        M.inst x t w && M.associatedWith s t w && M.memberOf y s w)))))) := by
  unfold checkAx94 checkAx94Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax94WitnessCosted_value, impliesB]

theorem checkAx94Costed_cost_le (M : FiniteModel4) :
    (checkAx94Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (ax94WitnessBound M + 5) + 2) + 2) := by
  unfold checkAx94Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allWorldsEvalCosted_cost_le M _ (ax94WitnessBound M + 3)
  intro w
  have hw := ax94WitnessCosted_cost_le M x y w
  cases h : M.hasValue x y w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

/-!
The simple/complex quality predicates below retain the production
evaluation order, including the repeated quality computation inside
`complexQualityB`.  A cache could reduce that work, but it would need its own
construction charge and equivalence theorem; the present result therefore
describes what is concretely computed today.
-/

def noInheringThingsCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun y =>
    (Complexity.Costed.tick (M.inheresIn y x w) 1).not

theorem noInheringThingsCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (noInheringThingsCosted M x w).value =
      allThings M (fun y => !(M.inheresIn y x w)) := by
  unfold noInheringThingsCosted
  rw [allThingsEvalCosted_value]
  rfl

theorem noInheringThingsCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (noInheringThingsCosted M x w).cost ≤ M.thingCount * 4 := by
  unfold noInheringThingsCosted
  apply allThingsEvalCosted_cost_le M _ 2
  intro y
  simp

def simpleQualityCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityBCosted M x w) fun _ =>
    noInheringThingsCosted M x w

def simpleQualityBound (M : FiniteModel4) : Nat :=
  qualityBound M + M.thingCount * 4 + 1

theorem simpleQualityCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (simpleQualityCosted M x w).value = simpleQualityB M x w := by
  unfold simpleQualityCosted simpleQualityB qualityB
  rw [Complexity.Costed.andThen_value, noInheringThingsCosted_value]

theorem simpleQualityCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (simpleQualityCosted M x w).cost ≤ simpleQualityBound M := by
  have hq := qualityBCosted_cost_le M x w
  have hn := noInheringThingsCosted_cost_le M x w
  unfold simpleQualityBound qualityBound
  cases h : (qualityBCosted M x w).value <;>
    simp [simpleQualityCosted, Complexity.Costed.andThen, h] <;> omega

def complexQualityCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (qualityBCosted M x w) fun _ =>
    (simpleQualityCosted M x w).not

def complexQualityBound (M : FiniteModel4) : Nat :=
  qualityBound M + simpleQualityBound M + 2

theorem complexQualityCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (complexQualityCosted M x w).value = complexQualityB M x w := by
  unfold complexQualityCosted complexQualityB qualityB
  rw [Complexity.Costed.andThen_value, Complexity.Costed.not_value,
    simpleQualityCosted_value]

theorem complexQualityCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (complexQualityCosted M x w).cost ≤ complexQualityBound M := by
  have hq := qualityBCosted_cost_le M x w
  have hs := simpleQualityCosted_cost_le M x w
  unfold complexQualityBound qualityBound
  cases h : (qualityBCosted M x w).value <;>
    simp [complexQualityCosted, Complexity.Costed.andThen,
      Complexity.Costed.not, h] <;> omega

def simpleQualityTypeCosted (M : FiniteModel4) (t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.qualityType t w) 1) fun _ =>
    allThingsEvalCosted M fun x =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.inst x t w) 1) fun _ =>
        simpleQualityCosted M x w

def simpleQualityTypeBound (M : FiniteModel4) : Nat :=
  M.thingCount * (simpleQualityBound M + 5) + 2

theorem simpleQualityTypeCosted_value (M : FiniteModel4) (t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (simpleQualityTypeCosted M t w).value = simpleQualityTypeB M t w := by
  unfold simpleQualityTypeCosted simpleQualityTypeB
  rw [Complexity.Costed.andThen_value, allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, simpleQualityCosted_value, impliesB]

theorem simpleQualityTypeCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (simpleQualityTypeCosted M t w).cost ≤ simpleQualityTypeBound M := by
  unfold simpleQualityTypeCosted simpleQualityTypeBound
  cases hq : M.qualityType t w
  · simp [Complexity.Costed.andThen]
  · simp only [Complexity.Costed.andThen, Complexity.Costed.tick_value,
      Complexity.Costed.tick_cost, ↓reduceIte]
    have hall : (allThingsEvalCosted M fun x =>
        Complexity.Costed.implies (Complexity.Costed.tick (M.inst x t w) 1) fun _ =>
          simpleQualityCosted M x w).cost ≤
        M.thingCount * (simpleQualityBound M + 5) := by
      apply allThingsEvalCosted_cost_le M _ (simpleQualityBound M + 3)
      intro x
      have hs := simpleQualityCosted_cost_le M x w
      cases hi : M.inst x t w <;>
        simp [Complexity.Costed.implies, Complexity.Costed.orElse,
          Complexity.Costed.not] ; omega
    omega

def checkAx95Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.associatedWith x y w) 1) fun _ =>
        Complexity.Costed.iff (Complexity.Costed.tick (M.qualityDimension x w) 1) fun _ =>
          simpleQualityTypeCosted M y w

def checkAx95 (M : FiniteModel4) : Bool := (checkAx95Costed M).value

theorem checkAx95_eq_legacy (M : FiniteModel4) :
    checkAx95 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      impliesB (M.associatedWith x y w)
        (iffB (M.qualityDimension x w) (simpleQualityTypeB M y w))))) := by
  unfold checkAx95 checkAx95Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.implies_value, Complexity.Costed.iff_value,
    simpleQualityTypeCosted_value]
  cases ha : M.associatedWith x y w <;> cases hd : M.qualityDimension x w <;>
    cases hs : simpleQualityTypeB M y w <;> rfl

theorem checkAx95Costed_cost_le (M : FiniteModel4) :
    (checkAx95Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (simpleQualityTypeBound M + 8) + 2) + 2) := by
  unfold checkAx95Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allWorldsEvalCosted_cost_le M _ (simpleQualityTypeBound M + 6)
  intro w
  have hs := simpleQualityTypeCosted_cost_le M y w
  cases ha : M.associatedWith x y w <;> cases hd : M.qualityDimension x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.iff, Complexity.Costed.not] <;> omega

def complexQualityTypeCosted (M : FiniteModel4) (t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.qualityType t w) 1) fun _ =>
    allThingsEvalCosted M fun x =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.inst x t w) 1) fun _ =>
        complexQualityCosted M x w

def complexQualityTypeBound (M : FiniteModel4) : Nat :=
  M.thingCount * (complexQualityBound M + 5) + 2

theorem complexQualityTypeCosted_value (M : FiniteModel4) (t : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (complexQualityTypeCosted M t w).value = complexQualityTypeB M t w := by
  unfold complexQualityTypeCosted complexQualityTypeB
  rw [Complexity.Costed.andThen_value, allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, complexQualityCosted_value, impliesB]

theorem complexQualityTypeCosted_cost_le (M : FiniteModel4)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (complexQualityTypeCosted M t w).cost ≤ complexQualityTypeBound M := by
  unfold complexQualityTypeCosted complexQualityTypeBound
  cases hq : M.qualityType t w
  · simp [Complexity.Costed.andThen]
  · simp only [Complexity.Costed.andThen, Complexity.Costed.tick_value,
      Complexity.Costed.tick_cost, ↓reduceIte]
    have hall : (allThingsEvalCosted M fun x =>
        Complexity.Costed.implies (Complexity.Costed.tick (M.inst x t w) 1) fun _ =>
          complexQualityCosted M x w).cost ≤
        M.thingCount * (complexQualityBound M + 5) := by
      apply allThingsEvalCosted_cost_le M _ (complexQualityBound M + 3)
      intro x
      have hc := complexQualityCosted_cost_le M x w
      cases hi : M.inst x t w <;>
        simp [Complexity.Costed.implies, Complexity.Costed.orElse,
          Complexity.Costed.not] ; omega
    omega

def checkAx96Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.associatedWith x y w) 1) fun _ =>
        Complexity.Costed.iff (Complexity.Costed.tick (M.qualityDomain x w) 1) fun _ =>
          complexQualityTypeCosted M y w

def checkAx96 (M : FiniteModel4) : Bool := (checkAx96Costed M).value

theorem checkAx96_eq_legacy (M : FiniteModel4) :
    checkAx96 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      impliesB (M.associatedWith x y w)
        (iffB (M.qualityDomain x w) (complexQualityTypeB M y w))))) := by
  unfold checkAx96 checkAx96Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.implies_value, Complexity.Costed.iff_value,
    complexQualityTypeCosted_value]
  cases ha : M.associatedWith x y w <;> cases hd : M.qualityDomain x w <;>
    cases hc : complexQualityTypeB M y w <;> rfl

theorem checkAx96Costed_cost_le (M : FiniteModel4) :
    (checkAx96Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (complexQualityTypeBound M + 8) + 2) + 2) := by
  unfold checkAx96Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allWorldsEvalCosted_cost_le M _ (complexQualityTypeBound M + 6)
  intro w
  have hc := complexQualityTypeCosted_cost_le M y w
  cases ha : M.associatedWith x y w <;> cases hd : M.qualityDomain x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.iff, Complexity.Costed.not] <;> omega

def ax97AntecedentCosted (M : FiniteModel4)
    (x y z Y Z : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen
      (Complexity.Costed.andThen
        (Complexity.Costed.andThen
          (Complexity.Costed.andThen (complexQualityCosted M x w) fun _ =>
            Complexity.Costed.tick (M.inst y Y w) 1) fun _ =>
          Complexity.Costed.tick (M.inst z Z w) 1) fun _ =>
        Complexity.Costed.tick (M.inheresIn y x w) 1) fun _ =>
      Complexity.Costed.tick (M.inheresIn z x w) 1) fun _ =>
    Complexity.Costed.tick (decide (Y = Z)) 1

theorem ax97AntecedentCosted_value (M : FiniteModel4)
    (x y z Y Z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax97AntecedentCosted M x y z Y Z w).value =
      (complexQualityB M x w && M.inst y Y w && M.inst z Z w &&
        M.inheresIn y x w && M.inheresIn z x w && decide (Y = Z)) := by
  simp [ax97AntecedentCosted, Complexity.Costed.andThen_value,
    complexQualityCosted_value]

theorem ax97AntecedentCosted_cost_le (M : FiniteModel4)
    (x y z Y Z : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax97AntecedentCosted M x y z Y Z w).cost ≤ complexQualityBound M + 10 := by
  have hc := complexQualityCosted_cost_le M x w
  cases hq : (complexQualityCosted M x w).value <;>
    cases hy : M.inst y Y w <;> cases hz : M.inst z Z w <;>
      cases hiy : M.inheresIn y x w <;> cases hiz : M.inheresIn z x w <;>
        simp [ax97AntecedentCosted, Complexity.Costed.andThen,
          hq, hy, hz, hiy, hiz] <;> omega

def checkAx97Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allThingsEvalCosted M fun z => allThingsEvalCosted M fun Y =>
      allThingsEvalCosted M fun Z => allWorldsEvalCosted M fun w =>
        Complexity.Costed.implies (ax97AntecedentCosted M x y z Y Z w) fun _ =>
          Complexity.Costed.tick (decide (y = z)) 1

def checkAx97 (M : FiniteModel4) : Bool := (checkAx97Costed M).value

theorem checkAx97_eq_legacy (M : FiniteModel4) :
    checkAx97 M = allThings M (fun x => allThings M (fun y => allThings M (fun z =>
      allThings M (fun Y => allThings M (fun Z => allWorlds M (fun w =>
        impliesB (complexQualityB M x w && M.inst y Y w && M.inst z Z w &&
          M.inheresIn y x w && M.inheresIn z x w && decide (Y = Z))
          (decide (y = z)))))))) := by
  unfold checkAx97 checkAx97Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext z
  rw [allThingsEvalCosted_value]; congr 1; funext Y
  rw [allThingsEvalCosted_value]; congr 1; funext Z
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, ax97AntecedentCosted_value, impliesB]

def checkAx97Bound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * (M.thingCount * (M.thingCount * (M.thingCount *
    (M.worldCount * (complexQualityBound M + 15) + 2) + 2) + 2) + 2) + 2)

theorem checkAx97Costed_cost_le (M : FiniteModel4) :
    (checkAx97Costed M).cost ≤ checkAx97Bound M := by
  unfold checkAx97Costed checkAx97Bound
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allThingsEvalCosted_cost_le M _ _
  intro z
  apply allThingsEvalCosted_cost_le M _ _
  intro Y
  apply allThingsEvalCosted_cost_le M _ _
  intro Z
  apply allWorldsEvalCosted_cost_le M _ (complexQualityBound M + 13)
  intro w
  have h := Complexity.Costed.implies_cost_le
    (ax97AntecedentCosted M x y z Y Z w)
    (fun _ => Complexity.Costed.tick (decide (y = z)) 1)
    (complexQualityBound M + 10) 1
    (ax97AntecedentCosted_cost_le M x y z Y Z w) (by simp)
  omega

def ax98PartsCosted (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun y =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.inheresIn y x w) 1) fun _ =>
      simpleQualityCosted M y w

def ax98PartsBound (M : FiniteModel4) : Nat :=
  M.thingCount * (simpleQualityBound M + 5)

theorem ax98PartsCosted_value (M : FiniteModel4) (x : Fin M.thingCount)
    (w : Fin M.worldCount) :
    (ax98PartsCosted M x w).value = allThings M (fun y =>
      impliesB (M.inheresIn y x w) (simpleQualityB M y w)) := by
  unfold ax98PartsCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, simpleQualityCosted_value, impliesB]

theorem ax98PartsCosted_cost_le (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax98PartsCosted M x w).cost ≤ ax98PartsBound M := by
  unfold ax98PartsCosted ax98PartsBound
  apply allThingsEvalCosted_cost_le M _ (simpleQualityBound M + 3)
  intro y
  have hs := simpleQualityCosted_cost_le M y w
  cases hi : M.inheresIn y x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def checkAx98Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allWorldsEvalCosted M fun w =>
    Complexity.Costed.implies (complexQualityCosted M x w) fun _ =>
      ax98PartsCosted M x w

def checkAx98 (M : FiniteModel4) : Bool := (checkAx98Costed M).value

theorem checkAx98_eq_legacy (M : FiniteModel4) :
    checkAx98 M = allThings M (fun x => allWorlds M (fun w =>
      impliesB (complexQualityB M x w) (allThings M (fun y =>
        impliesB (M.inheresIn y x w) (simpleQualityB M y w))))) := by
  unfold checkAx98 checkAx98Costed
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, complexQualityCosted_value,
    ax98PartsCosted_value, impliesB]

theorem checkAx98Costed_cost_le (M : FiniteModel4) :
    (checkAx98Costed M).cost ≤ M.thingCount *
      (M.worldCount * (complexQualityBound M + ax98PartsBound M + 4) + 2) := by
  unfold checkAx98Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allWorldsEvalCosted_cost_le M _
    (complexQualityBound M + ax98PartsBound M + 2)
  intro w
  have hc := complexQualityCosted_cost_le M x w
  have hp := ax98PartsCosted_cost_le M x w
  cases h : (complexQualityCosted M x w).value <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, h] <;> omega

def productFamilyDimensions
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount) :
    Fin pf.dimensionThings.size → Fin thingCount :=
  fun i => pf.dimensionThings[i]

def productFamilyTypes
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount) :
  Fin pf.dimensionThings.size → Fin thingCount :=
  fun i =>
    let hidx : i.val < pf.typeThings.size := by
      rw [← pf.sameSize]
      exact i.isLt
    pf.typeThings[i.val]'hidx

def productFamilyWitnessProp
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Prop :=
  pf.domain = x ∧ pf.qualityType = t ∧ pf.world = w ∧
    (∀ p : Fin M.thingCount,
      M.memberOf p x w = true →
        ∀ i : Fin pf.dimensionThings.size,
          M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w = true) ∧
    (∀ i : Fin pf.dimensionThings.size,
      M.associatedWith (productFamilyDimensions pf i) (productFamilyTypes pf i) w = true ∧
        M.characterization t (productFamilyTypes pf i) w = true) ∧
    (∀ u : Fin M.thingCount,
      M.characterization t u w = true →
        ∃ i : Fin pf.dimensionThings.size, u = productFamilyTypes pf i)

def allProductFamilyIndices
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount)
    (p : Fin pf.dimensionThings.size → Bool) : Bool :=
  decide (∀ i : Fin pf.dimensionThings.size, p i = true)

def anyProductFamilyIndices
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount)
    (p : Fin pf.dimensionThings.size → Bool) : Bool :=
  decide (∃ i : Fin pf.dimensionThings.size, p i = true)

def anyProductFamilyWitness
    (M : FiniteModel4)
    (p : (pf : ProductFamilyWitness M.thingCount M.worldCount) → Bool) : Bool :=
  decide (∃ i : Fin M.productFamilies.size, p (M.productFamilies[i]) = true)

def productFamilyEntryB
    (M : FiniteModel4) (x t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  anyProductFamilyWitness M fun pf =>
    decide (pf.domain = x ∧ pf.qualityType = t ∧ pf.world = w)

def checkAx99WitnessEntriesPresent (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun t =>
      allWorlds M fun w =>
        impliesB
          (M.qualityDomain x w && M.associatedWith x t w)
          (productFamilyEntryB M x t w)

def productFamilyWitnessB
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide (pf.domain = x) && decide (pf.qualityType = t) && decide (pf.world = w) &&
    (allThings M fun p =>
      impliesB (M.memberOf p x w)
        (allProductFamilyIndices pf fun i =>
          M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w)) &&
    (allProductFamilyIndices pf fun i =>
      M.associatedWith (productFamilyDimensions pf i) (productFamilyTypes pf i) w &&
        M.characterization t (productFamilyTypes pf i) w) &&
    (allThings M fun u =>
      impliesB (M.characterization t u w)
        (anyProductFamilyIndices pf fun i => decide (u = productFamilyTypes pf i)))

def productFamilyProjectionRowsCosted
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun p =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.memberOf p x w) 1) fun _ =>
      allFinEvalCosted pf.dimensionThings.size fun i =>
        /- One dimension-array read, one tuple-projection lookup, and one
        membership-table lookup. -/
        Complexity.Costed.tick
          (M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w) 3

def productFamilyAssociationRowsCosted
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allFinEvalCosted pf.dimensionThings.size fun i =>
    Complexity.Costed.andThen
      /- Dimension and type array reads plus the association lookup. -/
      (Complexity.Costed.tick
        (M.associatedWith (productFamilyDimensions pf i) (productFamilyTypes pf i) w) 3)
      fun _ =>
        /- The source expression reads the type slot again for characterization. -/
        Complexity.Costed.tick (M.characterization t (productFamilyTypes pf i) w) 2

def productFamilyCoverageRowsCosted
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun u =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.characterization t u w) 1) fun _ =>
      anyFinEvalCosted pf.dimensionThings.size fun i =>
        Complexity.Costed.tick (decide (u = productFamilyTypes pf i)) 2

theorem productFamilyProjectionRowsCosted_value
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyProjectionRowsCosted M pf x w).value = allThings M (fun p =>
      impliesB (M.memberOf p x w) (allProductFamilyIndices pf fun i =>
        M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w)) := by
  unfold productFamilyProjectionRowsCosted
  rw [allThingsEvalCosted_value]
  congr 1
  funext p
  simp [Complexity.Costed.implies_value, allFinEvalCosted_value,
    allProductFamilyIndices, impliesB]
  rfl

theorem productFamilyAssociationRowsCosted_value
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyAssociationRowsCosted M pf t w).value =
      allProductFamilyIndices pf (fun i =>
        M.associatedWith (productFamilyDimensions pf i) (productFamilyTypes pf i) w &&
          M.characterization t (productFamilyTypes pf i) w) := by
  unfold productFamilyAssociationRowsCosted allProductFamilyIndices
  rw [allFinEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

theorem productFamilyCoverageRowsCosted_value
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyCoverageRowsCosted M pf t w).value = allThings M (fun u =>
      impliesB (M.characterization t u w) (anyProductFamilyIndices pf fun i =>
        decide (u = productFamilyTypes pf i))) := by
  unfold productFamilyCoverageRowsCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, anyFinEvalCosted_value,
    anyProductFamilyIndices, impliesB]

theorem productFamilyProjectionRowsCosted_cost_le
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyProjectionRowsCosted M pf x w).cost ≤
      M.thingCount * (5 * pf.dimensionThings.size + 5) := by
  unfold productFamilyProjectionRowsCosted
  apply allThingsEvalCosted_cost_le M _ (5 * pf.dimensionThings.size + 3)
  intro p
  have hi : (allFinEvalCosted pf.dimensionThings.size fun i =>
      Complexity.Costed.tick
        (M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w) 3).cost ≤
      pf.dimensionThings.size * 5 := by
    apply allFinEvalCosted_cost_le _ _ 3
    intro i
    simp
  cases h : M.memberOf p x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

theorem productFamilyAssociationRowsCosted_cost_le
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyAssociationRowsCosted M pf t w).cost ≤
      pf.dimensionThings.size * 8 := by
  unfold productFamilyAssociationRowsCosted
  apply allFinEvalCosted_cost_le _ _ 6
  intro i
  cases h : M.associatedWith (productFamilyDimensions pf i)
      (productFamilyTypes pf i) w <;>
    simp [Complexity.Costed.andThen]

theorem productFamilyCoverageRowsCosted_cost_le
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyCoverageRowsCosted M pf t w).cost ≤
      M.thingCount * (4 * pf.dimensionThings.size + 5) := by
  unfold productFamilyCoverageRowsCosted
  apply allThingsEvalCosted_cost_le M _ (4 * pf.dimensionThings.size + 3)
  intro u
  have hi : (anyFinEvalCosted pf.dimensionThings.size fun i =>
      Complexity.Costed.tick (decide (u = productFamilyTypes pf i)) 2).cost ≤
      pf.dimensionThings.size * 4 := by
    apply anyFinEvalCosted_cost_le _ _ 2
    intro i
    simp
  cases h : M.characterization t u w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not] ; omega

def productFamilyHeaderCosted
    (pf : ProductFamilyWitness thingCount worldCount)
    (x t : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen (Complexity.Costed.tick (decide (pf.domain = x)) 1) fun _ =>
      Complexity.Costed.tick (decide (pf.qualityType = t)) 1) fun _ =>
    Complexity.Costed.tick (decide (pf.world = w)) 1

def productFamilyWitnessCosted
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen
      (Complexity.Costed.andThen (productFamilyHeaderCosted pf x t w) fun _ =>
        productFamilyProjectionRowsCosted M pf x w) fun _ =>
      productFamilyAssociationRowsCosted M pf t w) fun _ =>
    productFamilyCoverageRowsCosted M pf t w

def productFamilyWitnessBound
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount) : Nat :=
  8 + M.thingCount * (5 * pf.dimensionThings.size + 5) +
    pf.dimensionThings.size * 8 +
    M.thingCount * (4 * pf.dimensionThings.size + 5)

theorem productFamilyWitnessCosted_value
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyWitnessCosted M pf x t w).value = productFamilyWitnessB M pf x t w := by
  unfold productFamilyWitnessCosted productFamilyHeaderCosted productFamilyWitnessB
  simp [Complexity.Costed.andThen_value,
    productFamilyProjectionRowsCosted_value,
    productFamilyAssociationRowsCosted_value,
    productFamilyCoverageRowsCosted_value]

theorem productFamilyWitnessCosted_cost_le
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilyWitnessCosted M pf x t w).cost ≤ productFamilyWitnessBound M pf := by
  have hp := productFamilyProjectionRowsCosted_cost_le M pf x w
  have ha := productFamilyAssociationRowsCosted_cost_le M pf t w
  have hc := productFamilyCoverageRowsCosted_cost_le M pf t w
  unfold productFamilyWitnessBound productFamilyWitnessCosted productFamilyHeaderCosted
  cases h₁ : decide (pf.domain = x) <;> cases h₂ : decide (pf.qualityType = t) <;>
    cases h₃ : decide (pf.world = w) <;>
      cases h₄ : (productFamilyProjectionRowsCosted M pf x w).value <;>
        cases h₅ : (productFamilyAssociationRowsCosted M pf t w).value <;>
          simp [Complexity.Costed.andThen, h₄, h₅] <;> omega

def ax99Finite (M : FiniteModel4) : Prop :=
  ∀ (x t : Fin M.thingCount) (w : Fin M.worldCount),
    (M.qualityDomain x w = true ∧ M.associatedWith x t w = true) →
      ∃ i : Fin M.productFamilies.size,
        productFamilyWitnessProp M (M.productFamilies[i]) x t w

def productFamilySearchCosted (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyFinEvalCosted M.productFamilies.size fun i =>
    productFamilyWitnessCosted M M.productFamilies[i] x t w

def productFamilySearchBound (M : FiniteModel4) : Nat :=
  ((List.finRange M.productFamilies.size).map fun i =>
    productFamilyWitnessBound M M.productFamilies[i] + 2).sum

theorem productFamilySearchCosted_value (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilySearchCosted M x t w).value =
      anyProductFamilyWitness M (fun pf => productFamilyWitnessB M pf x t w) := by
  unfold productFamilySearchCosted anyProductFamilyWitness
  rw [anyFinEvalCosted_value]
  simp [productFamilyWitnessCosted_value]

theorem productFamilySearchCosted_cost_le (M : FiniteModel4)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    (productFamilySearchCosted M x t w).cost ≤ productFamilySearchBound M := by
  unfold productFamilySearchCosted productFamilySearchBound
  apply anyFinEvalCosted_cost_le_sum
  intro i
  exact productFamilyWitnessCosted_cost_le M M.productFamilies[i] x t w

def ax99AntecedentCosted (M : FiniteModel4) (x t : Fin M.thingCount)
    (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.qualityDomain x w) 1) fun _ =>
    Complexity.Costed.tick (M.associatedWith x t w) 1

def checkAx99Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun t =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (ax99AntecedentCosted M x t w) fun _ =>
        productFamilySearchCosted M x t w

def checkAx99 (M : FiniteModel4) : Bool := (checkAx99Costed M).value

theorem checkAx99_eq_legacy (M : FiniteModel4) :
    checkAx99 M = allThings M (fun x => allThings M (fun t => allWorlds M (fun w =>
      impliesB (M.qualityDomain x w && M.associatedWith x t w)
        (anyProductFamilyWitness M fun pf => productFamilyWitnessB M pf x t w)))) := by
  unfold checkAx99 checkAx99Costed ax99AntecedentCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext t
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    productFamilySearchCosted_value, impliesB]

theorem checkAx99Costed_cost_le (M : FiniteModel4) :
    (checkAx99Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (productFamilySearchBound M + 7) + 2) + 2) := by
  unfold checkAx99Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro t
  apply allWorldsEvalCosted_cost_le M _ (productFamilySearchBound M + 5)
  intro w
  have hs := productFamilySearchCosted_cost_le M x t w
  cases hd : M.qualityDomain x w <;> cases ha : M.associatedWith x t w <;>
    simp [ax99AntecedentCosted, Complexity.Costed.andThen,
      Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, hd, ha] ; omega

def commonQualityStructureCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun z =>
    Complexity.Costed.andThen (Complexity.Costed.tick (M.memberOf x z w) 1) fun _ =>
      Complexity.Costed.tick (M.memberOf y z w) 1

theorem commonQualityStructureCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (commonQualityStructureCosted M x y w).value =
      anyThings M (fun z => M.memberOf x z w && M.memberOf y z w) := by
  unfold commonQualityStructureCosted
  rw [anyThingsEvalCosted_value]
  simp [Complexity.Costed.andThen_value]

theorem commonQualityStructureCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (commonQualityStructureCosted M x y w).cost ≤ M.thingCount * 5 := by
  unfold commonQualityStructureCosted
  apply anyThingsEvalCosted_cost_le M _ 3
  intro z
  cases h : M.memberOf x z w <;>
    simp [Complexity.Costed.andThen]

def ax100ConsequentCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen (Complexity.Costed.tick (M.quale x w) 1) fun _ =>
      Complexity.Costed.tick (M.quale y w) 1) fun _ =>
    commonQualityStructureCosted M x y w

def checkAx100Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allThingsEvalCosted M fun r => allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.distance x y r w) 1) fun _ =>
        ax100ConsequentCosted M x y w

def checkAx100 (M : FiniteModel4) : Bool := (checkAx100Costed M).value

theorem checkAx100_eq_legacy (M : FiniteModel4) :
    checkAx100 M = allThings M (fun x => allThings M (fun y => allThings M (fun r =>
      allWorlds M (fun w => impliesB (M.distance x y r w)
        (M.quale x w && M.quale y w && anyThings M (fun z =>
          M.memberOf x z w && M.memberOf y z w)))))) := by
  unfold checkAx100 checkAx100Costed ax100ConsequentCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext r
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    commonQualityStructureCosted_value, impliesB]

theorem checkAx100Costed_cost_le (M : FiniteModel4) :
    (checkAx100Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * (5 * M.thingCount + 9) + 2) + 2) + 2) := by
  unfold checkAx100Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allThingsEvalCosted_cost_le M _ _
  intro r
  apply allWorldsEvalCosted_cost_le M _ (5 * M.thingCount + 7)
  intro w
  have hc := commonQualityStructureCosted_cost_le M x y w
  cases hd : M.distance x y r w <;> cases hx : M.quale x w <;>
    cases hy : M.quale y w <;>
      simp [ax100ConsequentCosted, Complexity.Costed.implies,
        Complexity.Costed.orElse, Complexity.Costed.andThen,
        Complexity.Costed.not, hx, hy] ; omega

def distanceUniqueForCosted (M : FiniteModel4)
    (x y r : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun r' =>
    Complexity.Costed.implies (Complexity.Costed.tick (M.distance x y r' w) 1) fun _ =>
      Complexity.Costed.tick (decide (r' = r)) 1

theorem distanceUniqueForCosted_value (M : FiniteModel4)
    (x y r : Fin M.thingCount) (w : Fin M.worldCount) :
    (distanceUniqueForCosted M x y r w).value = allThings M (fun r' =>
      impliesB (M.distance x y r' w) (decide (r' = r))) := by
  unfold distanceUniqueForCosted
  rw [allThingsEvalCosted_value]
  simp [Complexity.Costed.implies_value, impliesB]

theorem distanceUniqueForCosted_cost_le (M : FiniteModel4)
    (x y r : Fin M.thingCount) (w : Fin M.worldCount) :
    (distanceUniqueForCosted M x y r w).cost ≤ M.thingCount * 6 := by
  unfold distanceUniqueForCosted
  apply allThingsEvalCosted_cost_le M _ 4
  intro r'
  cases h : M.distance x y r' w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def distanceWitnessCosted (M : FiniteModel4)
    (x y r : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.distance x y r w) 1) fun _ =>
    distanceUniqueForCosted M x y r w

theorem distanceWitnessCosted_value (M : FiniteModel4)
    (x y r : Fin M.thingCount) (w : Fin M.worldCount) :
    (distanceWitnessCosted M x y r w).value =
      (M.distance x y r w && allThings M (fun r' =>
        impliesB (M.distance x y r' w) (decide (r' = r)))) := by
  simp [distanceWitnessCosted, Complexity.Costed.andThen_value,
    distanceUniqueForCosted_value]

theorem distanceWitnessCosted_cost_le (M : FiniteModel4)
    (x y r : Fin M.thingCount) (w : Fin M.worldCount) :
    (distanceWitnessCosted M x y r w).cost ≤ M.thingCount * 6 + 2 := by
  have hu := distanceUniqueForCosted_cost_le M x y r w
  cases h : M.distance x y r w <;>
    simp [distanceWitnessCosted, Complexity.Costed.andThen, h] ; omega

def existsUniqueDistanceCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  anyThingsEvalCosted M fun r => distanceWitnessCosted M x y r w

def existsUniqueDistanceBound (M : FiniteModel4) : Nat :=
  M.thingCount * (M.thingCount * 6 + 4)

theorem existsUniqueDistanceCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueDistanceCosted M x y w).value = decide
      (∃ r : Fin M.thingCount,
        M.distance x y r w = true ∧
          ∀ r' : Fin M.thingCount, M.distance x y r' w = true → r' = r) := by
  apply Bool.eq_iff_iff.mpr
  unfold existsUniqueDistanceCosted
  rw [anyThingsEvalCosted_value, anyThings_eq_true_iff, decide_eq_true_iff]
  simp [distanceWitnessCosted_value, allThings_eq_true_iff, impliesB]
  grind

theorem existsUniqueDistanceCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (existsUniqueDistanceCosted M x y w).cost ≤ existsUniqueDistanceBound M := by
  unfold existsUniqueDistanceCosted existsUniqueDistanceBound
  apply anyThingsEvalCosted_cost_le M _ (M.thingCount * 6 + 2)
  intro r
  exact distanceWitnessCosted_cost_le M x y r w

def ax101AntecedentCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen (Complexity.Costed.tick (M.quale x w) 1) fun _ =>
    Complexity.Costed.tick (M.quale y w) 1

def checkAx101Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (ax101AntecedentCosted M x y w) fun _ =>
        existsUniqueDistanceCosted M x y w

def checkAx101 (M : FiniteModel4) : Bool := (checkAx101Costed M).value

theorem checkAx101_eq_legacy (M : FiniteModel4) :
    checkAx101 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      impliesB (M.quale x w && M.quale y w) (decide
        (∃ r : Fin M.thingCount, M.distance x y r w = true ∧
          ∀ r' : Fin M.thingCount, M.distance x y r' w = true → r' = r))))) := by
  unfold checkAx101 checkAx101Costed ax101AntecedentCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value,
    existsUniqueDistanceCosted_value, impliesB]

theorem checkAx101Costed_cost_le (M : FiniteModel4) :
    (checkAx101Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (existsUniqueDistanceBound M + 7) + 2) + 2) := by
  unfold checkAx101Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allWorldsEvalCosted_cost_le M _ (existsUniqueDistanceBound M + 5)
  intro w
  have he := existsUniqueDistanceCosted_cost_le M x y w
  cases hx : M.quale x w <;> cases hy : M.quale y w <;>
    simp [ax101AntecedentCosted, Complexity.Costed.andThen,
      Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, hx, hy] ; omega

def checkBinaryRelationToUnaryPairCosted (M : FiniteModel4)
    (relation : Fin M.thingCount → Fin M.thingCount → Fin M.worldCount → Bool)
    (left right : Fin M.thingCount → Fin M.worldCount → Bool) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (relation x y w) 1) fun _ =>
        Complexity.Costed.andThen (Complexity.Costed.tick (left x w) 1) fun _ =>
          Complexity.Costed.tick (right y w) 1

theorem checkBinaryRelationToUnaryPairCosted_value (M : FiniteModel4)
    (relation left right) :
    (checkBinaryRelationToUnaryPairCosted M relation left right).value =
      allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
        impliesB (relation x y w) (left x w && right y w)))) := by
  unfold checkBinaryRelationToUnaryPairCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]
  simp [Complexity.Costed.implies_value, Complexity.Costed.andThen_value, impliesB]

theorem checkBinaryRelationToUnaryPairCosted_cost_le (M : FiniteModel4)
    (relation left right) :
    (checkBinaryRelationToUnaryPairCosted M relation left right).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) := by
  unfold checkBinaryRelationToUnaryPairCosted
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allWorldsEvalCosted_cost_le M _ 6
  intro w
  cases hr : relation x y w <;> cases hl : left x w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.andThen, Complexity.Costed.not]

def checkAx102Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkBinaryRelationToUnaryPairCosted M M.manifests M.perdurant M.endurant

def checkAx102 (M : FiniteModel4) : Bool := (checkAx102Costed M).value

theorem checkAx102_eq_legacy (M : FiniteModel4) :
    checkAx102 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      impliesB (M.manifests x y w) (M.perdurant x w && M.endurant y w)))) :=
  checkBinaryRelationToUnaryPairCosted_value M M.manifests M.perdurant M.endurant

theorem checkAx102Costed_cost_le (M : FiniteModel4) :
    (checkAx102Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  checkBinaryRelationToUnaryPairCosted_cost_le M M.manifests M.perdurant M.endurant

def ax103OverlapRowsCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun z =>
    Complexity.Costed.iff (Complexity.Costed.tick (M.overlap z x w) 1) fun _ =>
      Complexity.Costed.andThen (Complexity.Costed.tick (M.perdurant z w) 1) fun _ =>
        Complexity.Costed.tick (M.manifests z y w) 1

theorem ax103OverlapRowsCosted_value (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax103OverlapRowsCosted M x y w).value = allThings M (fun z =>
      iffB (M.overlap z x w) (M.perdurant z w && M.manifests z y w)) := by
  unfold ax103OverlapRowsCosted
  rw [allThingsEvalCosted_value]; congr 1; funext z
  rw [Complexity.Costed.iff_value, Complexity.Costed.andThen_value]
  cases ho : M.overlap z x w <;> cases hp : M.perdurant z w <;>
    cases hm : M.manifests z y w <;> rfl

theorem ax103OverlapRowsCosted_cost_le (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    (ax103OverlapRowsCosted M x y w).cost ≤ M.thingCount * 8 := by
  unfold ax103OverlapRowsCosted
  apply allThingsEvalCosted_cost_le M _ 6
  intro z
  cases ho : M.overlap z x w <;> cases hp : M.perdurant z w <;>
    simp [Complexity.Costed.iff, Complexity.Costed.andThen]

def ax103ConsequentCosted (M : FiniteModel4)
    (x y : Fin M.thingCount) (w : Fin M.worldCount) : Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen (Complexity.Costed.tick (M.perdurant x w) 1) fun _ =>
      Complexity.Costed.tick (M.endurant y w) 1) fun _ =>
    ax103OverlapRowsCosted M x y w

def checkAx103Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allWorldsEvalCosted M fun w =>
      Complexity.Costed.iff (Complexity.Costed.tick (M.lifeOf x y w) 1) fun _ =>
        ax103ConsequentCosted M x y w

def checkAx103 (M : FiniteModel4) : Bool := (checkAx103Costed M).value

theorem checkAx103_eq_legacy (M : FiniteModel4) :
    checkAx103 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      iffB (M.lifeOf x y w) (M.perdurant x w && M.endurant y w && allThings M (fun z =>
        iffB (M.overlap z x w) (M.perdurant z w && M.manifests z y w)))))) := by
  unfold checkAx103 checkAx103Costed ax103ConsequentCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.iff_value, Complexity.Costed.andThen_value,
    Complexity.Costed.andThen_value, ax103OverlapRowsCosted_value]
  cases hl : M.lifeOf x y w <;> cases hp : M.perdurant x w <;>
    cases he : M.endurant y w <;> cases hr : ax103OverlapRowsCosted M x y w |>.value <;>
      simp [iffB]

theorem checkAx103Costed_cost_le (M : FiniteModel4) :
    (checkAx103Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 8 + 9) + 2) + 2) := by
  unfold checkAx103Costed
  apply allThingsEvalCosted_cost_le M _ _
  intro x
  apply allThingsEvalCosted_cost_le M _ _
  intro y
  apply allWorldsEvalCosted_cost_le M _ (M.thingCount * 8 + 7)
  intro w
  have hr := ax103OverlapRowsCosted_cost_le M x y w
  cases hl : M.lifeOf x y w <;> cases hp : M.perdurant x w <;>
    cases he : M.endurant y w <;>
      simp [ax103ConsequentCosted, Complexity.Costed.iff,
        Complexity.Costed.andThen, hp, he] <;> omega

def checkAx104Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  checkBinaryRelationToUnaryPairCosted M M.meet M.perdurant M.perdurant

def checkAx104 (M : FiniteModel4) : Bool := (checkAx104Costed M).value

theorem checkAx104_eq_legacy (M : FiniteModel4) :
    checkAx104 M = allThings M (fun x => allThings M (fun y => allWorlds M (fun w =>
      impliesB (M.meet x y w) (M.perdurant x w && M.perdurant y w)))) :=
  checkBinaryRelationToUnaryPairCosted_value M M.meet M.perdurant M.perdurant

theorem checkAx104Costed_cost_le (M : FiniteModel4) :
    (checkAx104Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  checkBinaryRelationToUnaryPairCosted_cost_le M M.meet M.perdurant M.perdurant

def checkAx105Costed (_M : FiniteModel4) : Complexity.Costed Bool := .pure true
def checkAx105 (M : FiniteModel4) : Bool := (checkAx105Costed M).value
theorem checkAx105Costed_cost (M : FiniteModel4) : (checkAx105Costed M).cost = 0 := rfl
theorem checkAx105Costed_cost_le (M : FiniteModel4) : (checkAx105Costed M).cost ≤ 0 :=
  Nat.le_of_eq (checkAx105Costed_cost M)

def checkAx106Costed (_M : FiniteModel4) : Complexity.Costed Bool := .pure true
def checkAx106 (M : FiniteModel4) : Bool := (checkAx106Costed M).value
theorem checkAx106Costed_cost (M : FiniteModel4) : (checkAx106Costed M).cost = 0 := rfl
theorem checkAx106Costed_cost_le (M : FiniteModel4) : (checkAx106Costed M).cost ≤ 0 :=
  Nat.le_of_eq (checkAx106Costed_cost M)

def checkAx107Costed (_M : FiniteModel4) : Complexity.Costed Bool := .pure true
def checkAx107 (M : FiniteModel4) : Bool := (checkAx107Costed M).value
theorem checkAx107Costed_cost (M : FiniteModel4) : (checkAx107Costed M).cost = 0 := rfl
theorem checkAx107Costed_cost_le (M : FiniteModel4) : (checkAx107Costed M).cost ≤ 0 :=
  Nat.le_of_eq (checkAx107Costed_cost M)

def checkAx108Costed (_M : FiniteModel4) : Complexity.Costed Bool := .pure true
def checkAx108 (M : FiniteModel4) : Bool := (checkAx108Costed M).value
theorem checkAx108Costed_cost (M : FiniteModel4) : (checkAx108Costed M).cost = 0 := rfl
theorem checkAx108Costed_cost_le (M : FiniteModel4) : (checkAx108Costed M).cost ≤ 0 :=
  Nat.le_of_eq (checkAx108Costed_cost M)

def checkAxDistanceIdentityCosted (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allThingsEvalCosted M fun r => allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies
        (Complexity.Costed.andThen (Complexity.Costed.tick (decide (x = y)) 1) fun _ =>
          Complexity.Costed.tick (M.distance x y r w) 1) fun _ =>
        Complexity.Costed.tick (M.distanceZero r w) 1

def checkAxDistanceIdentity (M : FiniteModel4) : Bool :=
  (checkAxDistanceIdentityCosted M).value

theorem checkAxDistanceIdentity_eq_legacy (M : FiniteModel4) :
    checkAxDistanceIdentity M = allThings M (fun x => allThings M (fun y =>
      allThings M (fun r => allWorlds M (fun w =>
        impliesB (decide (x = y) && M.distance x y r w) (M.distanceZero r w))))) := by
  unfold checkAxDistanceIdentity checkAxDistanceIdentityCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext r
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.implies_value, Complexity.Costed.andThen_value]
  rfl

theorem checkAxDistanceIdentityCosted_cost_le (M : FiniteModel4) :
    (checkAxDistanceIdentityCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) := by
  unfold checkAxDistanceIdentityCosted
  apply allThingsEvalCosted_cost_le M _ _; intro x
  apply allThingsEvalCosted_cost_le M _ _; intro y
  apply allThingsEvalCosted_cost_le M _ _; intro r
  apply allWorldsEvalCosted_cost_le M _ 6; intro w
  cases heq : decide (x = y) <;> cases hd : M.distance x y r w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not, Complexity.Costed.andThen]

def checkAxDistanceSymmetryCosted (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allThingsEvalCosted M fun r => allWorldsEvalCosted M fun w =>
      Complexity.Costed.implies (Complexity.Costed.tick (M.distance x y r w) 1) fun _ =>
        Complexity.Costed.tick (M.distance y x r w) 1

def checkAxDistanceSymmetry (M : FiniteModel4) : Bool :=
  (checkAxDistanceSymmetryCosted M).value

theorem checkAxDistanceSymmetry_eq_legacy (M : FiniteModel4) :
    checkAxDistanceSymmetry M = allThings M (fun x => allThings M (fun y =>
      allThings M (fun r => allWorlds M (fun w =>
        impliesB (M.distance x y r w) (M.distance y x r w))))) := by
  unfold checkAxDistanceSymmetry checkAxDistanceSymmetryCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext r
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.implies_value]
  rfl

theorem checkAxDistanceSymmetryCosted_cost_le (M : FiniteModel4) :
    (checkAxDistanceSymmetryCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 6 + 2) + 2) + 2) := by
  unfold checkAxDistanceSymmetryCosted
  apply allThingsEvalCosted_cost_le M _ _; intro x
  apply allThingsEvalCosted_cost_le M _ _; intro y
  apply allThingsEvalCosted_cost_le M _ _; intro r
  apply allWorldsEvalCosted_cost_le M _ 4; intro w
  cases hd : M.distance x y r w <;>
    simp [Complexity.Costed.implies, Complexity.Costed.orElse,
      Complexity.Costed.not]

def distanceTriangleAntecedentCosted (M : FiniteModel4)
    (x y z r0 r1 r2 s : Fin M.thingCount) (w : Fin M.worldCount) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.andThen
      (Complexity.Costed.andThen (Complexity.Costed.tick (M.distance x y r0 w) 1) fun _ =>
        Complexity.Costed.tick (M.distance y z r1 w) 1) fun _ =>
      Complexity.Costed.tick (M.distance x z r2 w) 1) fun _ =>
    Complexity.Costed.tick (M.distanceSum r0 r1 s w) 1

def checkAxDistanceTriangleCosted (M : FiniteModel4) : Complexity.Costed Bool :=
  allThingsEvalCosted M fun x => allThingsEvalCosted M fun y =>
    allThingsEvalCosted M fun z => allThingsEvalCosted M fun r0 =>
      allThingsEvalCosted M fun r1 => allThingsEvalCosted M fun r2 =>
        allThingsEvalCosted M fun s => allWorldsEvalCosted M fun w =>
          Complexity.Costed.implies
            (distanceTriangleAntecedentCosted M x y z r0 r1 r2 s w) fun _ =>
            Complexity.Costed.tick (M.distanceGreaterEq s r2 w) 1

def checkAxDistanceTriangle (M : FiniteModel4) : Bool :=
  (checkAxDistanceTriangleCosted M).value

theorem distanceTriangleAntecedentCosted_value (M : FiniteModel4)
    (x y z r0 r1 r2 s : Fin M.thingCount) (w : Fin M.worldCount) :
    (distanceTriangleAntecedentCosted M x y z r0 r1 r2 s w).value =
      (M.distance x y r0 w && M.distance y z r1 w &&
        M.distance x z r2 w && M.distanceSum r0 r1 s w) := by
  simp [distanceTriangleAntecedentCosted, Complexity.Costed.andThen_value]

theorem checkAxDistanceTriangle_eq_legacy (M : FiniteModel4) :
    checkAxDistanceTriangle M = allThings M (fun x => allThings M (fun y =>
      allThings M (fun z => allThings M (fun r0 => allThings M (fun r1 =>
        allThings M (fun r2 => allThings M (fun s => allWorlds M (fun w =>
          impliesB
            (M.distance x y r0 w && M.distance y z r1 w &&
              M.distance x z r2 w && M.distanceSum r0 r1 s w)
            (M.distanceGreaterEq s r2 w))))))))) := by
  unfold checkAxDistanceTriangle checkAxDistanceTriangleCosted
  rw [allThingsEvalCosted_value]; congr 1; funext x
  rw [allThingsEvalCosted_value]; congr 1; funext y
  rw [allThingsEvalCosted_value]; congr 1; funext z
  rw [allThingsEvalCosted_value]; congr 1; funext r0
  rw [allThingsEvalCosted_value]; congr 1; funext r1
  rw [allThingsEvalCosted_value]; congr 1; funext r2
  rw [allThingsEvalCosted_value]; congr 1; funext s
  rw [allWorldsEvalCosted_value]; congr 1; funext w
  rw [Complexity.Costed.implies_value, distanceTriangleAntecedentCosted_value]
  rfl

theorem distanceTriangleAntecedentCosted_cost_le (M : FiniteModel4)
    (x y z r0 r1 r2 s : Fin M.thingCount) (w : Fin M.worldCount) :
    (distanceTriangleAntecedentCosted M x y z r0 r1 r2 s w).cost ≤ 7 := by
  cases h0 : M.distance x y r0 w <;> cases h1 : M.distance y z r1 w <;>
    cases h2 : M.distance x z r2 w <;>
      simp [distanceTriangleAntecedentCosted, Complexity.Costed.andThen, h0, h1, h2]

theorem checkAxDistanceTriangleCosted_cost_le (M : FiniteModel4) :
    (checkAxDistanceTriangleCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.thingCount * (M.thingCount *
        (M.thingCount * (M.thingCount * (M.worldCount * 12 + 2) + 2) + 2) + 2) + 2) + 2) + 2) := by
  unfold checkAxDistanceTriangleCosted
  apply allThingsEvalCosted_cost_le M _ _; intro x
  apply allThingsEvalCosted_cost_le M _ _; intro y
  apply allThingsEvalCosted_cost_le M _ _; intro z
  apply allThingsEvalCosted_cost_le M _ _; intro r0
  apply allThingsEvalCosted_cost_le M _ _; intro r1
  apply allThingsEvalCosted_cost_le M _ _; intro r2
  apply allThingsEvalCosted_cost_le M _ _; intro s
  apply allWorldsEvalCosted_cost_le M _ 10; intro w
  apply Complexity.Costed.implies_cost_le _ _ 7 1
  · exact distanceTriangleAntecedentCosted_cost_le M x y z r0 r1 r2 s w
  · simp


def checkAxioms4Checks (M : FiniteModel4) : List Bool := [
  checkAx1 M, checkAx2 M, checkAx3 M, checkAx4 M, checkAx5 M,
  checkAx6 M, checkAx7 M, checkAx8 M, checkAx9 M, checkAx10 M,
  checkAx11 M, checkAx12 M, checkAx13 M, checkAx14 M, checkAx15 M,
  checkAx16 M, checkAx17 M, checkAx18 M, checkAx19 M, checkAx20 M,
  checkAx21 M, checkAx22 M, checkAx23 M, checkAx24 M, checkAx25 M,
  checkAx26 M, checkAx27 M, checkAx28 M, checkAx29 M, checkAx30 M,
  checkAx31 M, checkAx32 M, checkAx33 M, checkAxInstEndurant M,
  checkAxSubKindSortal M, checkAxNonSortalUp M, checkAxKindStable M,
  checkAx34 M, checkAx35 M, checkAx36 M, checkAx37 M, checkAx38 M,
  checkAx39 M, checkAx40 M, checkAx41 M, checkAx42 M, checkAx43 M,
  checkAx44 M, checkAx45 M, checkAx46 M,
  checkAx47 M, checkAx48 M, checkAx49 M, checkAx50 M,
  checkAx51 M, checkAx52 M,
  checkAx53 M, checkAx54 M, checkAx55 M,
  checkAx56 M, checkAx57 M, checkAx58 M, checkAx59 M, checkAx60 M,
  checkAx61 M, checkAx62 M, checkAx63 M, checkAx64 M,
  checkAx65 M, checkAx66 M, checkAx67 M, checkAx68 M,
  checkAx69 M, checkAx70 M, checkAx71 M, checkAx72 M, checkAx73 M,
  checkAx74 M, checkAx75 M, checkAx76 M, checkAx77 M, checkAx78 M,
  checkAx79 M, checkAx80 M, checkAxQuaIndividualOfEndurant M,
  checkAx81 M, checkAx82 M,
  checkAx83 M, checkAx84 M, checkAx85 M, checkAx86 M, checkAx87 M,
  checkAx88 M, checkAx89 M, checkAx90 M, checkAx91 M, checkAx92 M,
  checkAx93 M, checkAx94 M, checkAx95 M, checkAx96 M, checkAx97 M,
  checkAx98 M, checkAx99 M, checkAx100 M, checkAx101 M,
  checkAxDistanceIdentity M, checkAxDistanceSymmetry M, checkAxDistanceTriangle M,
  checkAx102 M, checkAx103 M, checkAx104 M,
  checkAx105 M, checkAx106 M, checkAx107 M, checkAx108 M
]

/-- The same fixed registry, now pairing every computation with its concrete
per-entry theorem. The bound field is inferred from that theorem, so the final
sum retains the actual heterogeneous formulas rather than a global maximum. -/
def checkAxioms4BoundedRegistry (M : FiniteModel4) : Array Complexity.BoundedCheck := #[
  .of (fun _ => checkAx1Costed M) (checkAx1Costed_cost_le M),
  .of (fun _ => checkAx2Costed M) (checkAx2Costed_cost_le M),
  .of (fun _ => checkAx3Costed M) (checkAx3Costed_cost_le M),
  .of (fun _ => checkAx4Costed M) (checkAx4Costed_cost_le M),
  .of (fun _ => checkAx5Costed M) (checkAx5Costed_cost_le M),
  .of (fun _ => checkAx6Costed M) (checkAx6Costed_cost_le M),
  .of (fun _ => checkAx7Costed M) (checkAx7Costed_cost_le M),
  .of (fun _ => checkAx8Costed M) (checkAx8Costed_cost_le M),
  .of (fun _ => checkAx9Costed M) (checkAx9Costed_cost_le M),
  .of (fun _ => checkAx10Costed M) (checkAx10Costed_cost_le M),
  .of (fun _ => checkAx11Costed M) (checkAx11Costed_cost_le M),
  .of (fun _ => checkAx12Costed M) (checkAx12Costed_cost_le M),
  .of (fun _ => checkAx13Costed M) (checkAx13Costed_cost_le M),
  .of (fun _ => checkAx14Costed M) (checkAx14Costed_cost_le M),
  .of (fun _ => checkAx15Costed M) (checkAx15Costed_cost_le M),
  .of (fun _ => checkAx16Costed M) (checkAx16Costed_cost_le M),
  .of (fun _ => checkAx17Costed M) (checkAx17Costed_cost_le M),
  .of (fun _ => checkAx18Costed M) (checkAx18Costed_cost_le M),
  .of (fun _ => checkAx19Costed M) (checkAx19Costed_cost_le M),
  .of (fun _ => checkAx20Costed M) (checkAx20Costed_cost_le M),
  .of (fun _ => checkAx21Costed M) (checkAx21Costed_cost_le M),
  .of (fun _ => checkAx22Costed M) (checkAx22Costed_cost_le M),
  .of (fun _ => checkAx23Costed M) (checkAx23Costed_cost_le M),
  .of (fun _ => checkAx24Costed M) (checkAx24Costed_cost_le M),
  .of (fun _ => checkAx25Costed M) (checkAx25Costed_cost_le M),
  .of (fun _ => checkAx26Costed M) (checkAx26Costed_cost_le M),
  .of (fun _ => checkAx27Costed M) (checkAx27Costed_cost_le M),
  .of (fun _ => checkAx28Costed M) (checkAx28Costed_cost_le M),
  .of (fun _ => checkAx29Costed M) (checkAx29Costed_cost_le M),
  .of (fun _ => checkAx30Costed M) (checkAx30Costed_cost_le M),
  .of (fun _ => checkAx31Costed M) (checkAx31Costed_cost_le M),
  .of (fun _ => checkAx32Costed M) (checkAx32Costed_cost_le M),
  .of (fun _ => checkAx33Costed M) (checkAx33Costed_cost_le M),
  .of (fun _ => checkAxInstEndurantCosted M) (checkAxInstEndurantCosted_cost_le M),
  .of (fun _ => checkAxSubKindSortalCosted M) (checkAxSubKindSortalCosted_cost_le M),
  .of (fun _ => checkAxNonSortalUpCosted M) (checkAxNonSortalUpCosted_cost_le M),
  .of (fun _ => checkAxKindStableCosted M) (checkAxKindStableCosted_cost_le M),
  .of (fun _ => checkAx34Costed M) (checkAx34Costed_cost_le M),
  .of (fun _ => checkAx35Costed M) (checkAx35Costed_cost_le M),
  .of (fun _ => checkAx36Costed M) (checkAx36Costed_cost_le M),
  .of (fun _ => checkAx37Costed M) (checkAx37Costed_cost_le M),
  .of (fun _ => checkAx38Costed M) (checkAx38Costed_cost_le M),
  .of (fun _ => checkAx39Costed M) (checkAx39Costed_cost_le M),
  .of (fun _ => checkAx40Costed M) (checkAx40Costed_cost_le M),
  .of (fun _ => checkAx41Costed M) (checkAx41Costed_cost_le M),
  .of (fun _ => checkAx42Costed M) (checkAx42Costed_cost_le M),
  .of (fun _ => checkAx43Costed M) (checkAx43Costed_cost_le M),
  .of (fun _ => checkAx44Costed M) (checkAx44Costed_cost_le M),
  .of (fun _ => checkAx45Costed M) (checkAx45Costed_cost_le M),
  .of (fun _ => checkAx46Costed M) (checkAx46Costed_cost_le M),
  .of (fun _ => checkAx47Costed M) (checkAx47Costed_cost_le M),
  .of (fun _ => checkAx48Costed M) (checkAx48Costed_cost_le M),
  .of (fun _ => checkAx49Costed M) (checkAx49Costed_cost_le M),
  .of (fun _ => checkAx50Costed M) (checkAx50Costed_cost_le M),
  .of (fun _ => checkAx51Costed M) (checkAx51Costed_cost_le M),
  .of (fun _ => checkAx52Costed M) (checkAx52Costed_cost_le M),
  .of (fun _ => checkAx53Costed M) (checkAx53Costed_cost_le M),
  .of (fun _ => checkAx54Costed M) (checkAx54Costed_cost_le M),
  .of (fun _ => checkAx55Costed M) (checkAx55Costed_cost_le M),
  .of (fun _ => checkAx56Costed M) (checkAx56Costed_cost_le M),
  .of (fun _ => checkAx57Costed M) (checkAx57Costed_cost_le M),
  .of (fun _ => checkAx58Costed M) (checkAx58Costed_cost_le M),
  .of (fun _ => checkAx59Costed M) (checkAx59Costed_cost_le M),
  .of (fun _ => checkAx60Costed M) (checkAx60Costed_cost_le M),
  .of (fun _ => checkAx61Costed M) (checkAx61Costed_cost_le M),
  .of (fun _ => checkAx62Costed M) (checkAx62Costed_cost_le M),
  .of (fun _ => checkAx63Costed M) (checkAx63Costed_cost_le M),
  .of (fun _ => checkAx64Costed M) (checkAx64Costed_cost_le M),
  .of (fun _ => checkAx65Costed M) (checkAx65Costed_cost_le M),
  .of (fun _ => checkAx66Costed M) (checkAx66Costed_cost_le M),
  .of (fun _ => checkAx67Costed M) (checkAx67Costed_cost_le M),
  .of (fun _ => checkAx68Costed M) (checkAx68Costed_cost_le M),
  .of (fun _ => checkAx69Costed M) (checkAx69Costed_cost_le M),
  .of (fun _ => checkAx70Costed M) (checkAx70Costed_cost_le M),
  .of (fun _ => checkAx71Costed M) (checkAx71Costed_cost_le M),
  .of (fun _ => checkAx72Costed M) (checkAx72Costed_cost_le M),
  .of (fun _ => checkAx73Costed M) (checkAx73Costed_cost_le M),
  .of (fun _ => checkAx74Costed M) (checkAx74Costed_cost_le M),
  .of (fun _ => checkAx75Costed M) (checkAx75Costed_cost_le M),
  .of (fun _ => checkAx76Costed M) (checkAx76Costed_cost_le M),
  .of (fun _ => checkAx77Costed M) (checkAx77Costed_cost_le M),
  .of (fun _ => checkAx78Costed M) (checkAx78Costed_cost_le M),
  .of (fun _ => checkAx79Costed M) (checkAx79Costed_cost_le M),
  .of (fun _ => checkAx80Costed M) (checkAx80Costed_cost_le M),
  .of (fun _ => checkAxQuaIndividualOfEndurantCosted M)
    (checkAxQuaIndividualOfEndurantCosted_cost_le M),
  .of (fun _ => checkAx81Costed M) (checkAx81Costed_cost_le M),
  .of (fun _ => checkAx82Costed M) (checkAx82Costed_cost_le M),
  .of (fun _ => checkAx83Costed M) (checkAx83Costed_cost_le M),
  .of (fun _ => checkAx84Costed M) (checkAx84Costed_cost_le M),
  .of (fun _ => checkAx85Costed M) (checkAx85Costed_cost_le M),
  .of (fun _ => checkAx86Costed M) (checkAx86Costed_cost_le M),
  .of (fun _ => checkAx87Costed M) (checkAx87Costed_cost_le M),
  .of (fun _ => checkAx88Costed M) (checkAx88Costed_cost_le M),
  .of (fun _ => checkAx89Costed M) (checkAx89Costed_cost_le M),
  .of (fun _ => checkAx90Costed M) (checkAx90Costed_cost_le M),
  .of (fun _ => checkAx91Costed M) (checkAx91Costed_cost_le M),
  .of (fun _ => checkAx92Costed M) (checkAx92Costed_cost_le M),
  .of (fun _ => checkAx93Costed M) (checkAx93Costed_cost_le M),
  .of (fun _ => checkAx94Costed M) (checkAx94Costed_cost_le M),
  .of (fun _ => checkAx95Costed M) (checkAx95Costed_cost_le M),
  .of (fun _ => checkAx96Costed M) (checkAx96Costed_cost_le M),
  .of (fun _ => checkAx97Costed M) (checkAx97Costed_cost_le M),
  .of (fun _ => checkAx98Costed M) (checkAx98Costed_cost_le M),
  .of (fun _ => checkAx99Costed M) (checkAx99Costed_cost_le M),
  .of (fun _ => checkAx100Costed M) (checkAx100Costed_cost_le M),
  .of (fun _ => checkAx101Costed M) (checkAx101Costed_cost_le M),
  .of (fun _ => checkAxDistanceIdentityCosted M) (checkAxDistanceIdentityCosted_cost_le M),
  .of (fun _ => checkAxDistanceSymmetryCosted M) (checkAxDistanceSymmetryCosted_cost_le M),
  .of (fun _ => checkAxDistanceTriangleCosted M) (checkAxDistanceTriangleCosted_cost_le M),
  .of (fun _ => checkAx102Costed M) (checkAx102Costed_cost_le M),
  .of (fun _ => checkAx103Costed M) (checkAx103Costed_cost_le M),
  .of (fun _ => checkAx104Costed M) (checkAx104Costed_cost_le M),
  .of (fun _ => checkAx105Costed M) (checkAx105Costed_cost_le M),
  .of (fun _ => checkAx106Costed M) (checkAx106Costed_cost_le M),
  .of (fun _ => checkAx107Costed M) (checkAx107Costed_cost_le M),
  .of (fun _ => checkAx108Costed M) (checkAx108Costed_cost_le M)
]

def checkAxioms4OperationalBound (M : FiniteModel4) : Nat :=
  Complexity.boundedRegistryCostBound (checkAxioms4BoundedRegistry M)

def checkAxioms4Costed (M : FiniteModel4) : Complexity.Costed Bool :=
  Complexity.checkBoundedRegistryCosted (checkAxioms4BoundedRegistry M)

def checkAxioms4 (M : FiniteModel4) : Bool := (checkAxioms4Costed M).value

theorem checkAxioms4BoundedRegistry_size (M : FiniteModel4) :
    (checkAxioms4BoundedRegistry M).size = 116 := by rfl

theorem checkAxioms4BoundedRegistry_values (M : FiniteModel4) :
    (checkAxioms4BoundedRegistry M).toList.map
      (fun check => (check.run ()).value) = checkAxioms4Checks M := by rfl

theorem checkAxioms4Costed_cost_le (M : FiniteModel4) :
    (checkAxioms4Costed M).cost ≤ checkAxioms4OperationalBound M := by
  exact Complexity.checkBoundedRegistryCosted_cost_le (checkAxioms4BoundedRegistry M)

theorem checkAxioms4_eq_legacy (M : FiniteModel4) :
    checkAxioms4 M = (checkAxioms4Checks M).all id := by
  rw [checkAxioms4, checkAxioms4Costed, Complexity.checkBoundedRegistryCosted_value]
  have h := congrArg (fun xs : List Bool => xs.all id)
    (checkAxioms4BoundedRegistry_values M)
  simpa only [List.all_map, Function.comp_def, id_eq] using h

end Checker
end LeanUfo.UFO.DSL
