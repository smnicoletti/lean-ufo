import LeanUfo.UFO.DSL.Complexity

/-!
# Checker/table cost correspondence regressions

Exact tests distinguish skipped and executed right-hand reads. The general
tests compare entire counted computations, so equal answers with incorrect
costs cannot satisfy them. Fixture tables use the verified compiler constructor.
-/

namespace LeanUfo.Test.Complexity.Queries

open LeanUfo.UFO.DSL LeanUfo.UFO.DSL.Complexity
open LeanUfo.UFO.DSL.Complexity.Production

/-! ## Closure edge accounting

Two vertices have two off-diagonal edge queries. Raising each query charge
from one to eleven adds twenty operations. Pivot work depends on the resulting
matrix: the empty graph costs 108, and the complete graph costs 92.
The singleton fixture assigns a huge diagonal query cost to detect accidental
evaluation of a query that reflexivity must skip.
-/

example : (warshallMatrixEvalCosted 0 (fun _ _ => Costed.tick false 11)).cost = 0 := by
  native_decide

example : (warshallMatrixEvalCosted 1
    (fun _ _ => Costed.tick false 1000000)).cost = 14 := by native_decide

example : (warshallMatrixEvalCosted 2 (fun _ _ => Costed.tick false 11)).cost = 108 := by
  native_decide

example : (warshallMatrixEvalCosted 2 (fun _ _ => Costed.tick true 11)).cost = 92 := by
  native_decide

example : (warshallMatrixEvalCosted 2 (fun _ _ => Costed.tick false 11)).value.toArray =
    #[#v[true, false], #v[false, true]] := by native_decide

example : (warshallMatrixEvalCosted 2 (fun _ _ => Costed.tick true 11)).value.toArray =
    #[#v[true, true], #v[true, true]] := by native_decide

private def closureEdgeAst (forward backward : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 2,
    facts := (if forward then #[.binary .inheresIn 0 1 0] else #[]) ++
      (if backward then #[.binary .inheresIn 1 0 0] else #[]) }

private def closureEdgeModel (forward backward : Bool) : FiniteModel4 :=
  compileVerifiedModel (closureEdgeAst forward backward)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases forward <;> cases backward <;> decide)

-- World-vector construction adds two operations to its matrix cost.
example : (Checker.inherenceMatricesCosted (closureEdgeModel false false)).cost = 110 := by
  native_decide
example : (Checker.inherenceMatricesCosted (closureEdgeModel true false)).cost = 102 := by
  native_decide
example : (Checker.inherenceMatricesCosted (closureEdgeModel false true)).cost = 102 := by
  native_decide
example : (Checker.inherenceMatricesCosted (closureEdgeModel true true)).cost = 94 := by
  native_decide

example (edge : Fin n → Fin n → Costed Bool) (bound : Nat)
    (h : ∀ i j, (edge i j).cost ≤ bound) :
    (warshallMatrixEvalCosted n edge).cost ≤
      10 * n ^ 3 + (bound + 6) * n ^ 2 + 3 * n :=
  warshallMatrixEvalCosted_cost_le n edge bound h

/-! ## Bearer selection

The source moment is thing zero. Things one and two are possible bearers.
The first-witness and last-witness fixtures differ by one rejected candidate,
which costs nineteen operations. Two witnesses make uniqueness fail.
-/

private def bearerAst (classified first last : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if classified then #[.unary .moment 0 0] else #[]) ++
      (if first then #[.binary .inheresIn 0 1 0] else #[]) ++
      (if last then #[.binary .inheresIn 0 2 0] else #[]) }

private def bearerModel (classified first last : Bool) : FiniteModel4 :=
  compileVerifiedModel (bearerAst classified first last)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases classified <;> cases first <;> cases last <;> decide)

-- A false outer premise skips the entire witness search.
example : Checker.checkAx68Costed (bearerModel false false false) = ⟨true, 43⟩ := by
  native_decide
example : Checker.checkAx68Costed (bearerModel false true true) = ⟨true, 43⟩ := by
  native_decide

example : Checker.checkAx68Costed (bearerModel true false false) = ⟨false, 66⟩ := by
  native_decide
example : Checker.checkAx68Costed (bearerModel true true false) = ⟨true, 130⟩ := by
  native_decide
example : Checker.checkAx68Costed (bearerModel true false true) = ⟨true, 149⟩ := by
  native_decide
example : Checker.checkAx68Costed (bearerModel true true true) = ⟨false, 157⟩ := by
  native_decide

-- A candidate classified as a moment skips even an expensive reachability call.
example :
    let M := bearerModel true false false
    Checker.ultimateBearerOfCosted M (fun _ _ _ => Costed.tick true 1000000)
      (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 10⟩ := by native_decide

example :
    let M := bearerModel true false false
    Checker.ultimateBearerOfCosted M (fun _ _ _ => Costed.tick false 6)
      (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 16⟩ := by native_decide
example :
    let M := bearerModel true false false
    Checker.ultimateBearerOfCosted M (fun _ _ _ => Costed.tick true 6)
      (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 16⟩ := by native_decide

private def ast (left right : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := (if left then #[.unary .endurant 0 0] else #[]) ++
      (if right then #[.unary .concreteIndividual 0 0] else #[]) }

private def model (left right : Bool) : FiniteModel4 :=
  compileVerifiedModel (ast left right) (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by cases left <;> cases right <;> decide)

-- A false premise costs 8+2, plus two operations for each of the two loops.
example : Checker.checkAx11Costed (model false false) = ⟨true, 14⟩ := by native_decide
example : Checker.checkAx11Costed (model false true) = ⟨true, 14⟩ := by native_decide
-- Executing the right lookup adds eight operations, regardless of its answer.
example : Checker.checkAx11Costed (model true false) = ⟨false, 22⟩ := by native_decide
example : Checker.checkAx11Costed (model true true) = ⟨true, 22⟩ := by native_decide

example : Checker.checkUnaryTableDisjointCosted (model false false)
    (model false false).endurant (model false false).concreteIndividual = ⟨true, 14⟩ :=
  by native_decide
-- Disjointness adds one negation only when it executes the right lookup.
example : Checker.checkUnaryTableDisjointCosted (model true false)
    (model true false).endurant (model true false).concreteIndividual = ⟨true, 23⟩ :=
  by native_decide
example : Checker.checkUnaryTableDisjointCosted (model true true)
    (model true true).endurant (model true true).concreteIndividual = ⟨false, 23⟩ :=
  by native_decide

example (tables : FactTables) (field : UnaryField) {W T : Nat} (x : Fin T) (w : Fin W) :
    Costed.tick (tables.unaryTypedTableDense field x w) 8 =
      tables.unaryTypedTableCosted field x w :=
  unaryTableBlock_eq_counted tables field x w

-- Missing cells still perform all eight operations and return false.
example : (FactTables.unaryTypedTableCosted {} .endurant (0 : Fin 1) (0 : Fin 1)) =
    ⟨false, 8⟩ := by native_decide

private def worldOrderAst : ModelAST :=
  { worldCount := 2, thingCount := 2, facts := #[.unary .endurant 0 1] }
private def thingOrderAst : ModelAST :=
  { worldCount := 2, thingCount := 2, facts := #[.unary .endurant 1 0] }

-- World 0 skips the right lookup. World 1 fails: (10+2)+(18+2)+2=34.
example : Checker.checkAx11Costed
    (compileVerifiedModel worldOrderAst (by decide) (by decide) (by decide)) =
      ⟨false, 34⟩ := by native_decide
-- Thing 0 passes both worlds (26). Thing 1 fails in its first world (22).
example : Checker.checkAx11Costed
    (compileVerifiedModel thingOrderAst (by decide) (by decide) (by decide)) =
      ⟨false, 48⟩ := by native_decide

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    Checker.checkAx11Costed M =
      allFinCosted source.things.size (fun x => allFinCosted source.worlds.size (fun w =>
        Costed.implies (compiled.tables.unaryTypedTableCosted .endurant x w)
          (fun _ => compiled.tables.unaryTypedTableCosted .concreteIndividual x w))) :=
  compiledAx11_eq_countedTables compiled.tables source.worlds.size source.things.size hw ht
    (compileModelSource_ok_lookups_agree source compiled success)
    (compileModelSource_ok_inherenceCacheValid source compiled success)
    (compileModelSource_ok_tableDimensions source compiled success).1
    (compileModelSource_ok_tableDimensions source compiled success).2

private def classificationAst (a b c d : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := (if a then #[.unary .kind 0 0] else #[]) ++
      (if b then #[.unary .subKind 0 0] else #[]) ++
      (if c then #[.unary .rigid 0 0] else #[]) ++
      (if d then #[.unary .sortal 0 0] else #[]) }

private def classificationModel (a b c d : Bool) : FiniteModel4 :=
  compileVerifiedModel (classificationAst a b c d)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by cases a <;> cases b <;> cases c <;> cases d <;> decide)

-- All truth assignments use actual compiled fields. The expected formulas
-- count eight per visited lookup and four for the two finite loops.
example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c =>
      let M := classificationModel a b c false
      Checker.checkUnaryIffAndCosted M M.kind M.subKind M.rigid ==
        ⟨a == (b && c), 22 + (if b then 8 else 0) + (if a then 0 else 1)⟩))) = true :=
  by native_decide

-- The second conjunct's negation runs only after a true first conjunct.
example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c =>
      let M := classificationModel a b c false
      Checker.checkUnaryIffAndNotCosted M M.kind M.subKind M.rigid ==
        ⟨a == (b && !c), 22 + (if b then 9 else 0) + (if a then 0 else 1)⟩))) = true :=
  by native_decide

example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c => (#[false, true]).all (fun d =>
      let M := classificationModel a b c d
      Checker.checkAx26Costed M ==
        ⟨(a || b) == (c && d),
          23 + (if a then 0 else 8) + (if c then 8 else 0) + (if a || b then 0 else 1)⟩)))) = true :=
  by native_decide

example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    let M := classificationModel a b false false
    Checker.checkAx25Costed M == ⟨!(a && b), 14 + (if a then 8 else 0)⟩)) = true :=
  by native_decide

example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c =>
      let M := classificationModel a b c false
      Checker.checkUnaryIffOrSingleCosted M M.kind M.subKind M.rigid ==
        ⟨(a || b) == c, 22 + (if a then 0 else 8) + (if a || b then 0 else 1)⟩))) = true :=
  by native_decide

-- Each skipped disjunct saves its read, and skipping the inner disjunction
-- also saves its branch. Equivalence always evaluates its right operand.
example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c => (#[false, true]).all (fun d =>
      let M := classificationModel a b c d
      Checker.checkUnaryIffThreeOrSingleCosted M M.kind M.subKind M.rigid M.sortal ==
        ⟨(a || b || c) == d,
          22 + (if a then 0 else 9 + (if b then 0 else 8)) +
            (if a || b || c then 0 else 1)⟩)))) = true := by native_decide

private def worldFirstAst : ModelAST :=
  { worldCount := 2, thingCount := 3,
    facts := #[.unary .kind 2 0, .unary .subKind 2 0] }

-- World-first order reaches the conflict after two skipped right-hand reads:
-- 12+12+20+2=46. Thing-first order would visit the other world between things.
example : Checker.checkAx25Costed
    (compileVerifiedModel worldFirstAst (by decide) (by decide) (by decide)) =
      ⟨false, 46⟩ := by native_decide

private def firstKindAst : ModelAST :=
  { worldCount := 1, thingCount := 1, facts := #[.unary .objectKind 0 0] }
private def lastKindAst : ModelAST :=
  { worldCount := 1, thingCount := 1, facts := #[.unary .qualityKind 0 0] }

-- A false/false equivalence costs 23. Each registry entry adds three.
example : Checker.checkAx45Costed (model false false) = ⟨true, 156⟩ := by native_decide
-- A true/false mismatch costs 22. The first entry therefore stops at 25.
example : Checker.checkAx45Costed
    (compileVerifiedModel firstKindAst (by decide) (by decide) (by decide)) =
      ⟨false, 25⟩ := by native_decide
-- The last entry runs after five successful entries: 5*26+25=155.
example : Checker.checkAx45Costed
    (compileVerifiedModel lastKindAst (by decide) (by decide) (by decide)) =
      ⟨false, 155⟩ := by native_decide

/-! Binary and ternary queries retain exact costs even when optional reads
return their default. The general equalities also cover nonempty raw tables. -/

example (tables : FactTables) (field : BinaryField) {W T : Nat}
    (x y : Fin T) (w : Fin W) :
    Costed.tick (tables.binaryTypedTableDense field x y w) 11 =
      tables.binaryTypedTableCosted field x y w :=
  binaryTableBlock_eq_counted tables field x y w

example (tables : FactTables) (field : TernaryField) {W T : Nat}
    (x y z : Fin T) (w : Fin W) :
    Costed.tick (tables.ternaryTypedTableDense field x y z w) 14 =
      tables.ternaryTypedTableCosted field x y z w :=
  ternaryTableBlock_eq_counted tables field x y z w

example : FactTables.binaryTypedTableCosted {} .manifests
    (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) = ⟨false, 11⟩ := by native_decide
example : FactTables.ternaryTypedTableCosted {} .distance
    (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) = ⟨false, 14⟩ := by native_decide

private def binaryPairAst (relation left right : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := (if relation then #[.binary .manifests 0 0 0, .binary .meet 0 0 0] else #[]) ++
      (if left then #[.unary .perdurant 0 0] else #[]) ++
      (if right then #[.unary .endurant 0 0] else #[]) }

private def binaryPairModel (relation left right : Bool) : FiniteModel4 :=
  compileVerifiedModel (binaryPairAst relation left right)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by cases relation <;> cases left <;> cases right <;> decide)

-- Three loops add six. The relation and implication add thirteen; a visited
-- pair adds nine for its first read/branch and eight for its second read.
example : (#[false, true]).all (fun r => (#[false, true]).all (fun a =>
    (#[false, true]).all (fun b =>
      Checker.checkAx102Costed (binaryPairModel r a b) ==
        ⟨!r || (a && b), 19 + (if r then 9 + (if a then 8 else 0) else 0)⟩))) = true :=
  by native_decide

example : (#[false, true]).all (fun r => (#[false, true]).all (fun a =>
    Checker.checkAx104Costed (binaryPairModel r a false) ==
      ⟨!r || a, 19 + (if r then 9 + (if a then 8 else 0) else 0)⟩)) = true :=
  by native_decide

private def distanceAst (distance zero sum greater : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := (if distance then #[.ternary .distance 0 0 0 0] else #[]) ++
      (if zero then #[.unary .distanceZero 0 0] else #[]) ++
      (if sum then #[.ternary .distanceSum 0 0 0 0] else #[]) ++
      (if greater then #[.binary .distanceGreaterEq 0 0 0] else #[]) }

private def distanceModel (distance zero sum greater : Bool) : FiniteModel4 :=
  compileVerifiedModel (distanceAst distance zero sum greater)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by cases distance <;> cases zero <;> cases sum <;> cases greater <;> decide)

-- Four loops add eight. Identity always reads distance at this equal pair,
-- but reads distanceZero only after a true distance result.
example : (#[false, true]).all (fun d => (#[false, true]).all (fun z =>
    Checker.checkAxDistanceIdentityCosted (distanceModel d z false false) ==
      ⟨!d || z, 26 + (if d then 8 else 0)⟩)) = true := by native_decide

example : (#[false, true]).all (fun d =>
    Checker.checkAxDistanceSymmetryCosted (distanceModel d false false false) ==
      ⟨true, 24 + (if d then 14 else 0)⟩) = true := by native_decide

-- A false first distance skips three reads, but all three enclosing
-- conjunction tests still run. The eight loops add sixteen.
example : (#[false, true]).all (fun d => (#[false, true]).all (fun s =>
    (#[false, true]).all (fun g =>
      Checker.checkAxDistanceTriangleCosted (distanceModel d false s g) ==
        ⟨!d || !s || g, 35 + (if d then 42 + (if s then 11 else 0) else 0)⟩))) = true :=
  by native_decide

private def asymmetricDistanceAst (reverse : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 2,
    facts := if reverse then #[.ternary .distance 1 0 0 0]
      else #[.ternary .distance 0 1 0 0] }

private def asymmetricDistanceModel (reverse : Bool) : FiniteModel4 :=
  compileVerifiedModel (asymmetricDistanceAst reverse)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases reverse <;> decide)

-- Symmetry reaches (0,1,0) after one complete y-row: 42+36+2=80.
-- Reversing the fact adds one complete x-row before the failure: 86+38=124.
example : Checker.checkAxDistanceSymmetryCosted (asymmetricDistanceModel false) =
    ⟨false, 80⟩ := by native_decide
example : Checker.checkAxDistanceSymmetryCosted (asymmetricDistanceModel true) =
    ⟨false, 124⟩ := by native_decide

-- Identity skips unequal pairs before their distance reads. Each x-row has
-- one equal y-row (46), one unequal y-row (18), and its outer charge (2).
example : Checker.checkAxDistanceIdentityCosted (asymmetricDistanceModel false) =
    ⟨true, 132⟩ := by native_decide

private def triangleAst (a b c d : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if a then #[.ternary .distance 0 1 0 0] else #[]) ++
      (if b then #[.ternary .distance 1 2 1 0] else #[]) ++
      (if c then #[.ternary .distance 0 2 2 0] else #[]) ++
      (if d then #[.ternary .distanceSum 0 1 0 0] else #[]) }

private def triangleModel (a b c d : Bool) : FiniteModel4 :=
  compileVerifiedModel (triangleAst a b c d)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases a <;> cases b <;> cases c <;> cases d <;> decide)

-- Independent coordinates exercise all four reads, so a repeated one-cell
-- lookup cannot conceal a field/index mix-up. There are always three branches.
example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c => (#[false, true]).all (fun d =>
      Checker.distanceTriangleAntecedentCosted (triangleModel a b c d)
        (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3)
        (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 1) ==
          ⟨a && b && c && d, 17 + (if a then 14 + (if b then
            14 + (if c then 14 else 0) else 0) else 0)⟩)))) = true := by native_decide

/-! ## Instantiation scans and first-block checks

The two-world fixtures separate the current world from the searched worlds.
Each visited assignment runs its shared predicate once, even for a tautology.
-/

private def instantiationAst (first last : Bool) : ModelAST :=
  { worldCount := 2, thingCount := 2,
    facts := (if first then #[.binary .inst 0 0 0] else #[]) ++
      (if last then #[.binary .inst 1 0 1] else #[]) }

private def instantiationModel (first last : Bool) : FiniteModel4 :=
  compileVerifiedModel (instantiationAst first last)
    (by change 0 < 2; decide) (by change 0 < 2; decide)
    (by cases first <;> cases last <;> decide)

-- A visited thing costs 11+2. Each world adds two: 2*(2*13+2)=56.
example : Checker.typeBCosted (instantiationModel false false)
    (0 : Fin 2) (0 : Fin 2) = ⟨false, 56⟩ := by native_decide
example : Checker.typeBCosted (instantiationModel true false)
    (0 : Fin 2) (0 : Fin 2) = ⟨true, 15⟩ := by native_decide
example : Checker.typeBCosted (instantiationModel false true)
    (0 : Fin 2) (0 : Fin 2) = ⟨true, 56⟩ := by native_decide
-- The current-world argument does not change the search or its cost.
example : Checker.typeBCosted (instantiationModel true false)
    (0 : Fin 2) (1 : Fin 2) = ⟨true, 15⟩ := by native_decide
example : Checker.typeBCosted (instantiationModel true true)
    (0 : Fin 2) (0 : Fin 2) = ⟨true, 15⟩ := by native_decide
example : Checker.individualBCosted (instantiationModel false false)
    (0 : Fin 2) (0 : Fin 2) = ⟨true, 57⟩ := by native_decide
example : Checker.individualBCosted (instantiationModel true false)
    (0 : Fin 2) (0 : Fin 2) = ⟨false, 16⟩ := by native_decide

-- Negation runs once per visited world. A witness ends the outer scan too.
example : Checker.noInstancesEveryWorldCosted (instantiationModel false false)
    (0 : Fin 2) = ⟨true, 58⟩ := by native_decide
example : Checker.noInstancesEveryWorldCosted (instantiationModel true false)
    (0 : Fin 2) = ⟨false, 16⟩ := by native_decide
example : Checker.noInstancesEveryWorldCosted (instantiationModel false true)
    (0 : Fin 2) = ⟨false, 58⟩ := by native_decide

-- Axiom 1 shares the type scan within each thing/world pair.
-- With no facts, four pairs cost 4*(56+2), plus twelve loop operations.
example : Checker.checkAx1Costed (instantiationModel false false) =
    ⟨true, 244⟩ := by native_decide
example : Checker.checkAx1Costed (instantiationModel true false) =
    ⟨true, 160⟩ := by native_decide
example : Checker.checkAx1Costed (instantiationModel false true) =
    ⟨true, 242⟩ := by native_decide
example : Checker.checkAx2Costed (instantiationModel false false) =
    ⟨true, 476⟩ := by native_decide
example : Checker.checkAx2Costed (instantiationModel true false) =
    ⟨true, 312⟩ := by native_decide
example : Checker.checkAx2Costed (instantiationModel false true) =
    ⟨true, 478⟩ := by native_decide

-- Reversing subsumption changes which instance column is read first.
example : Checker.instSubsumptionCosted (instantiationModel true false)
    (0 : Fin 2) (1 : Fin 2) = ⟨false, 28⟩ := by native_decide
example : Checker.instSubsumptionCosted (instantiationModel true false)
    (1 : Fin 2) (0 : Fin 2) = ⟨true, 64⟩ := by native_decide
example : Checker.instSubsumptionCosted (instantiationModel true false)
    (0 : Fin 2) (0 : Fin 2) = ⟨true, 75⟩ := by native_decide

-- A missing type skips the remaining type and subsumption tests.
example : Checker.subDefBCosted (instantiationModel true false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) = ⟨false, 73⟩ := by native_decide
example : Checker.subDefBCosted (instantiationModel true false)
    (1 : Fin 2) (0 : Fin 2) (0 : Fin 2) = ⟨false, 57⟩ := by native_decide
example : Checker.subDefBCosted (instantiationModel true false)
    (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) = ⟨true, 107⟩ := by native_decide

example : Checker.checkAx3Costed (instantiationModel false false) =
    ⟨true, 132⟩ := by native_decide
example : Checker.checkAx3Costed (instantiationModel true false) =
    ⟨true, 148⟩ := by native_decide
example : Checker.checkAx3Costed (instantiationModel false true) =
    ⟨true, 246⟩ := by native_decide
example : Checker.checkAx4Costed (instantiationModel true false) =
    ⟨false, 48⟩ := by native_decide
example : Checker.checkAx4Costed (instantiationModel false false) =
    ⟨true, 988⟩ := by native_decide
example : Checker.checkAx5Costed (instantiationModel true false) =
    ⟨false, 126⟩ := by native_decide
example : Checker.checkAx5Costed (instantiationModel false false) =
    ⟨true, 588⟩ := by native_decide
example : Checker.checkAx6Costed (instantiationModel true false) =
    ⟨false, 116⟩ := by native_decide

private def specializationAst (lower : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := #[.binary .inst 2 2 0] ++
      (if lower then #[.binary .sub 2 0 0, .binary .sub 2 1 0]
        else #[.binary .sub 0 2 0, .binary .sub 1 2 0]) }

private def specializationModel (lower : Bool) : FiniteModel4 :=
  compileVerifiedModel (specializationAst lower)
    (by change 0 < 1; decide) (by change 0 < 3; decide) (by cases lower <;> decide)

-- A matching last candidate costs 14+14+37=65. Upper success skips lower;
-- lower success pays 42 for the failed upper scan, then 1+65.
example : Checker.ax6ConsequentCosted (specializationModel false)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 1) = ⟨true, 66⟩ := by native_decide
example : Checker.ax6ConsequentCosted (specializationModel true)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 1) = ⟨true, 108⟩ := by native_decide

private def upperWitnessAst (a b c : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if a then #[.binary .sub 0 2 0] else #[]) ++
      (if b then #[.binary .sub 1 2 0] else #[]) ++
      (if c then #[.binary .inst 2 2 0] else #[]) }

private def upperWitnessModel (a b c : Bool) : FiniteModel4 :=
  compileVerifiedModel (upperWitnessAst a b c)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases a <;> cases b <;> cases c <;> decide)

example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c =>
      Checker.ax6WitnessCosted (upperWitnessModel a b c)
        (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 1) ==
          ⟨a && b && c, 42 + (if a then 12 + (if b then 11 else 0) else 0)⟩))) = true :=
  by native_decide

private def typeClassificationAst (isType left right : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := (if isType then #[.binary .inst 0 0 0] else #[]) ++
      (if left then #[.unary .concreteIndividual 0 0, .unary .endurantType 0 0] else #[]) ++
      (if right then #[.unary .abstractIndividual 0 0, .unary .perdurantType 0 0] else #[]) }

private def typeClassificationModel (isType left right : Bool) : FiniteModel4 :=
  compileVerifiedModel (typeClassificationAst isType left right)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by cases isType <;> cases left <;> cases right <;> decide)

-- A one-cell type scan costs 15, and its complement costs 16. Implications
-- skip those scans after a false unary read. Equivalence reads both sides.
example : (#[false, true]).all (fun d => (#[false, true]).all (fun a =>
    (#[false, true]).all (fun b =>
      let M := typeClassificationModel d a b
      #[Checker.checkAx7Costed M, Checker.checkAx8Costed M, Checker.checkAx10Costed M,
        Checker.checkAx15Costed M, Checker.checkAx16Costed M] ==
      #[⟨!a || !d, 14 + (if a then 16 else 0)⟩,
        ⟨!b || !d, 14 + (if b then 16 else 0)⟩,
        ⟨(!d) == (a || b), 30 + (if a then 0 else 8) + (if d then 1 else 0)⟩,
        ⟨!a || d, 14 + (if a then 15 else 0)⟩,
        ⟨!b || d, 14 + (if b then 15 else 0)⟩]))) = true := by native_decide

private def modalAst (first last marked : Bool) : ModelAST :=
  { worldCount := 2, thingCount := 1,
    facts := #[.unary .endurantType 0 0, .unary .endurantType 0 1] ++
      (if first then #[.binary .inst 0 0 0] else #[]) ++
      (if last then #[.binary .inst 0 0 1] else #[]) ++
      (if marked then #[.unary .rigid 0 0, .unary .rigid 0 1,
        .unary .antiRigid 0 0, .unary .antiRigid 0 1] else #[]) }

private def modalModel (first last marked : Bool) : FiniteModel4 :=
  compileVerifiedModel (modalAst first last marked)
    (by change 0 < 2; decide) (by change 0 < 1; decide)
    (by cases first <;> cases last <;> cases marked <;> decide)

-- Each visited world costs 13, or 14 when the read is negated.
example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    let M := modalModel a b false
    #[Checker.instanceSomeWorldCosted M (0 : Fin 1) (0 : Fin 1),
      Checker.instanceAllWorldsCosted M (0 : Fin 1) (0 : Fin 1),
      Checker.instanceAbsentSomeWorldCosted M (0 : Fin 1) (0 : Fin 1)] ==
    #[⟨a || b, if a then 13 else 26⟩,
      ⟨a && b, if a then 26 else 13⟩,
      ⟨!a || !b, if a then 28 else 14⟩])) = true := by native_decide

-- The one-thing implication adds four operations, including its loop.
-- Rigidity scans every world only after finding a possible instance.
example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    let M := modalModel a b false
    #[Checker.rigidInstancesCosted M (0 : Fin 1),
      Checker.antiRigidInstancesCosted M (0 : Fin 1)] ==
    #[⟨a == b, if a || b then 43 else 30⟩,
      ⟨!(a && b), if a then 45 else if b then 44 else 30⟩])) = true := by native_decide

-- An absent instance satisfies rigidity. Each successful outer world costs
-- 20 plus the inner scan; the outer thing loop adds two.
example : Checker.checkAx18Costed (modalModel false false true) =
    ⟨true, 102⟩ := by native_decide
example : Checker.checkAx18Costed (modalModel true false false) =
    ⟨true, 130⟩ := by native_decide
example : Checker.checkAx18Costed (modalModel true false true) =
    ⟨false, 65⟩ := by native_decide
example : Checker.checkAx19Costed (modalModel true false true) =
    ⟨true, 132⟩ := by native_decide
example : Checker.checkAx19Costed (modalModel true true false) =
    ⟨true, 134⟩ := by native_decide
example : Checker.checkAx20Costed (modalModel false false true) =
    ⟨true, 64⟩ := by native_decide
example : Checker.checkAx20Costed (modalModel false false false) =
    ⟨false, 42⟩ := by native_decide

private def kindAst (other : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 2,
    facts := #[.unary .endurant 0 0, .unary .endurantType 1 0,
      .unary .sortal 1 0, .unary .kind 1 0, .binary .inst 0 1 0] ++
      (if other then #[.unary .kind 0 0, .binary .inst 0 0 0] else #[]) }

private def kindModel (other : Bool) : FiniteModel4 :=
  compileVerifiedModel (kindAst other)
    (by change 0 < 1; decide) (by change 0 < 2; decide) (by cases other <;> decide)

-- An earlier matching kind saves the eleven-operation rejected candidate.
example : Checker.checkAx21Costed (kindModel false) = ⟨true, 63⟩ := by native_decide
example : Checker.checkAx21Costed (kindModel true) = ⟨true, 52⟩ := by native_decide
example : Checker.ax23KindWitnessCosted (kindModel false) (1 : Fin 2) (0 : Fin 1) =
    ⟨true, 65⟩ := by native_decide
example : Checker.ax23KindWitnessCosted (kindModel true) (1 : Fin 2) (0 : Fin 1) =
    ⟨true, 54⟩ := by native_decide

-- Testing the same kind still pays the disequality comparison. A different
-- first kind ends the search before the second candidate.
example : Checker.ax22AlternativeCosted (kindModel false)
    (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) =
    ⟨false, 22⟩ := by native_decide
example : Checker.ax22CounterexampleCosted (kindModel false) (1 : Fin 2) (0 : Fin 2) =
    ⟨false, 37⟩ := by native_decide
example : Checker.ax22CounterexampleCosted (kindModel true) (1 : Fin 2) (0 : Fin 2) =
    ⟨true, 26⟩ := by native_decide
example : (Checker.checkAx22Costed (kindModel false)).value = true := by native_decide
example : (Checker.checkAx22Costed (kindModel true)).value = false := by native_decide
example : (Checker.checkAx23Costed (kindModel false)).value = true := by native_decide
example : (Checker.checkAx23Costed (kindModel true)).value = true := by native_decide

private def crossWorldKindAst : ModelAST :=
  { worldCount := 2, thingCount := 2,
    facts := #[.unary .kind 0 0, .binary .inst 0 0 0,
      .unary .kind 1 1, .binary .inst 0 1 1] }

private def crossWorldKindModel : FiniteModel4 :=
  compileVerifiedModel crossWorldKindAst (by decide) (by decide) (by decide)

-- Each world costs 37. The second world reveals the conflicting kind.
example : Checker.ax22CounterexampleCosted crossWorldKindModel (0 : Fin 2) (0 : Fin 2) =
    ⟨true, 74⟩ := by native_decide
example : Checker.checkAx22Costed crossWorldKindModel =
    ⟨false, 103⟩ := by native_decide

private def nonSortalAst (a b c : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 2,
    facts := (if a then #[.unary .nonSortal 0 0] else #[]) ++
      (if b then #[.binary .sub 0 1 0] else #[]) ++
      (if c then #[.unary .nonSortal 1 0] else #[]) }

private def nonSortalModel (a b c : Bool) : FiniteModel4 :=
  compileVerifiedModel (nonSortalAst a b c)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases a <;> cases b <;> cases c <;> decide)

-- The failed (0,1) pair follows a vacuous (0,0) pair. Later pairs are skipped.
example : Checker.checkAxNonSortalUpCosted (nonSortalModel true true false) =
    ⟨false, 62⟩ := by native_decide

private def qualityAst (k0 k1 i0 i1 : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 2,
    facts := (if k0 then #[.unary .qualityKind 0 0] else #[]) ++
      (if k1 then #[.unary .qualityKind 1 0] else #[]) ++
      (if i0 then #[.binary .inst 0 0 0] else #[]) ++
      (if i1 then #[.binary .inst 0 1 0] else #[]) }

private def qualityModel (k0 k1 i0 i1 : Bool) : FiniteModel4 :=
  compileVerifiedModel (qualityAst k0 k1 i0 i1)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases k0 <;> cases k1 <;> cases i0 <;> cases i1 <;> decide)

-- A failed kind read costs nine. Otherwise the candidate costs twenty.
-- Each rejected outer candidate adds three for its conjunction and loop.
-- A unique first match costs 23+25+(c1+4). A unique last match costs
-- (c0+3)+23+(c0+4)+25. Two matches cost (23+25+25)+(23+25)=121.
example : (#[false, true]).all (fun k0 => (#[false, true]).all (fun k1 =>
    (#[false, true]).all (fun i0 => (#[false, true]).all (fun i1 =>
      let c0 := if k0 then 20 else 9
      let c1 := if k1 then 20 else 9
      let v0 := k0 && i0
      let v1 := k1 && i1
      let expectedCost := if v0 then (if v1 then 121 else c1 + 52)
        else if v1 then 2 * c0 + 55 else c0 + c1 + 6
      Checker.qualityBCosted (qualityModel k0 k1 i0 i1) (0 : Fin 2) (0 : Fin 1) ==
        ⟨v0 != v1, expectedCost⟩)))) = true := by native_decide

example : Checker.qualityBCosted (qualityModel false false false false)
    (0 : Fin 2) (0 : Fin 1) = ⟨false, 24⟩ := by native_decide
example : Checker.qualityBCosted (qualityModel true false true false)
    (0 : Fin 2) (0 : Fin 1) = ⟨true, 61⟩ := by native_decide
example : Checker.qualityBCosted (qualityModel false true false true)
    (0 : Fin 2) (0 : Fin 1) = ⟨true, 73⟩ := by native_decide
example : Checker.qualityBCosted (qualityModel true true true true)
    (0 : Fin 2) (0 : Fin 1) = ⟨false, 121⟩ := by native_decide

private def qualityClassificationAst (hasInstance mode intrinsic : Bool) : ModelAST :=
  { (qualityAst false true false hasInstance) with
    facts := (qualityAst false true false hasInstance).facts ++
      (if mode then #[.unary .mode 0 0] else #[]) ++
      (if intrinsic then #[.unary .intrinsicMoment 0 0] else #[]) }

private def qualityClassificationModel (hasInstance mode intrinsic : Bool) : FiniteModel4 :=
  compileVerifiedModel (qualityClassificationAst hasInstance mode intrinsic)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases hasInstance <;> cases mode <;> cases intrinsic <;> decide)

-- Axiom 42 skips quality after a true mode read. The second thing has no
-- instance and costs 58; a failed first thing skips it.
example : Checker.checkAx42Costed (qualityClassificationModel true false true) =
    ⟨true, 153⟩ := by native_decide
example : Checker.checkAx42Costed (qualityClassificationModel true true true) =
    ⟨true, 80⟩ := by native_decide
example : Checker.checkAx42Costed (qualityClassificationModel true false false) =
    ⟨false, 95⟩ := by native_decide
example : Checker.checkAx42Costed (qualityClassificationModel true true false) =
    ⟨false, 22⟩ := by native_decide
example : Checker.checkAx42Costed (qualityClassificationModel false false false) =
    ⟨true, 116⟩ := by native_decide

-- Axiom 43 uses the opposite short-circuit condition: false mode skips quality.
example : Checker.checkAx43Costed (qualityClassificationModel true false false) =
    ⟨true, 26⟩ := by native_decide
example : Checker.checkAx43Costed (qualityClassificationModel true true false) =
    ⟨false, 87⟩ := by native_decide
example : Checker.checkAx43Costed (qualityClassificationModel false true false) =
    ⟨true, 61⟩ := by native_decide

private def qualityOrderAst : ModelAST :=
  { worldCount := 2, thingCount := 2,
    facts := #[.unary .qualityKind 1 0, .unary .qualityKind 1 1,
      .binary .inst 0 1 1, .binary .inst 1 1 0,
      .unary .mode 0 1, .unary .mode 1 0] }

private def qualityOrderModel : FiniteModel4 :=
  compileVerifiedModel qualityOrderAst (by decide) (by decide) (by decide)

-- Axiom 42 visits (thing 0, world 0), then fails in world 1: 56+20+2.
-- Axiom 43 visits both things in world 0 and fails at thing 1: 12+85+2.
example : Checker.checkAx42Costed qualityOrderModel = ⟨false, 78⟩ := by native_decide
example : Checker.checkAx43Costed qualityOrderModel = ⟨false, 99⟩ := by native_decide

private def allTypeFamiliesAst (first last : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := #[.binary .inst 0 0 0, .unary .qualityKind 0 0,
      .unary .perdurantType 0 0, .unary .substantialType 0 0,
      .unary .momentType 0 0, .unary .objectType 0 0,
      .unary .collectiveType 0 0, .unary .quantityType 0 0,
      .unary .relatorType 0 0, .unary .modeType 0 0,
      .unary .endurant 0 0, .unary .perdurant 0 0,
      .unary .substantial 0 0, .unary .moment 0 0,
      .unary .object 0 0, .unary .collective 0 0,
      .unary .quantity 0 0, .unary .relator 0 0, .unary .mode 0 0] ++
      (if first then #[.unary .endurantType 0 0] else #[]) ++
      (if last then #[.unary .qualityType 0 0] else #[]) }

private def allTypeFamiliesModel (first last : Bool) : FiniteModel4 :=
  compileVerifiedModel (allTypeFamiliesAst first last)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by cases first <;> cases last <;> decide)

-- These fixtures isolate axiom 44; they do not satisfy the whole UFO registry.
-- A direct family costs 54. The quality family substitutes a 48-operation
-- leaf for an eight-operation read, so it costs 94.
example : Checker.typeByInstancesCosted (allTypeFamiliesModel true true)
    (allTypeFamiliesModel true true).endurantType
    (allTypeFamiliesModel true true).endurant = ⟨true, 54⟩ := by native_decide
example : Checker.checkAx44QualityCosted (allTypeFamiliesModel true true) =
    ⟨true, 94⟩ := by native_decide

-- Registry overhead is three per visited family: 9*(54+3)+(94+3)=610.
-- A false left side of equivalence adds one negation.
example : Checker.checkAx44Costed (allTypeFamiliesModel true true) =
    ⟨true, 610⟩ := by native_decide
example : Checker.checkAx44Costed (allTypeFamiliesModel false true) =
    ⟨false, 58⟩ := by native_decide
example : Checker.checkAx44Costed (allTypeFamiliesModel true false) =
    ⟨false, 611⟩ := by native_decide

-- With no instances, each family skips its leaf scan and costs 30+3.
example : Checker.checkAx44Costed (model false false) =
    ⟨true, 330⟩ := by native_decide

private def specificKindAst (field : UnaryField) (hasInstance : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := #[.unary .endurant 0 0, .unary field 0 0] ++
      (if hasInstance then #[.binary .inst 0 0 0] else #[]) }

private def specificKindModel (field : UnaryField) (hasInstance : Bool) : FiniteModel4 :=
  compileVerifiedModel (specificKindAst field hasInstance)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by
      cases hasInstance <;>
        simp [explicitModelWellBounded, specificKindAst, factWellBounded])

-- The first five disjunction positions cost nine each. The last has no
-- following branch test, so all six reads cost 53.
example : (#[UnaryField.objectKind, .collectiveKind, .quantityKind,
    .relatorKind, .modeKind, .qualityKind]).map (fun field =>
      (Checker.specificEndurantKindCosted (specificKindModel field true)
        (0 : Fin 1) (0 : Fin 1)).cost) = #[9, 18, 27, 36, 45, 53] := by native_decide

-- Instantiation and the nested loops add thirty to the selected kind cost.
example : (#[UnaryField.objectKind, .collectiveKind, .quantityKind,
    .relatorKind, .modeKind, .qualityKind]).map (fun field =>
      Checker.checkAx46Costed (specificKindModel field true)) =
    #[⟨true, 39⟩, ⟨true, 48⟩, ⟨true, 57⟩,
      ⟨true, 66⟩, ⟨true, 75⟩, ⟨true, 83⟩] := by native_decide
example : Checker.checkAx46Costed (specificKindModel .qualityKind false) =
    ⟨false, 83⟩ := by native_decide
-- A generic kind does not satisfy the six-field classification. No instance
-- read follows its failed classification scan.
example : Checker.checkAx46Costed (specificKindModel .kind true) =
    ⟨false, 72⟩ := by native_decide

private def laterKindAst (hasInstance : Bool) : ModelAST :=
  { worldCount := 2, thingCount := 1,
    facts := #[.unary .endurant 0 0, .unary .qualityKind 0 1] ++
      (if hasInstance then #[.binary .inst 0 0 1] else #[]) }

private def laterKindModel (hasInstance : Bool) : FiniteModel4 :=
  compileVerifiedModel (laterKindAst hasInstance)
    (by change 0 < 2; decide) (by change 0 < 1; decide)
    (by cases hasInstance <;> decide)

-- The witness search visits both worlds: 58+69. Failure skips the final
-- outer-world check, saving twelve operations.
example : Checker.checkAx46Costed (laterKindModel true) =
    ⟨true, 153⟩ := by native_decide
example : Checker.checkAx46Costed (laterKindModel false) =
    ⟨false, 141⟩ := by native_decide

private def partAst (forward backward overlapping properForward properBackward : Bool) :
    ModelAST :=
  { worldCount := 1, thingCount := 2,
    facts := (if forward then #[.binary .part 0 1 0] else #[]) ++
      (if backward then #[.binary .part 1 0 0] else #[]) ++
      (if overlapping then #[.binary .overlap 0 1 0, .binary .overlap 1 0 0] else #[]) ++
      (if properForward then #[.binary .properPart 0 1 0] else #[]) ++
      (if properBackward then #[.binary .properPart 1 0 0] else #[]) }

private def partModel (forward backward overlapping properForward properBackward : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (partAst forward backward overlapping properForward properBackward)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases forward <;> cases backward <;> cases overlapping <;>
      cases properForward <;> cases properBackward <;> decide)

-- The generic block preserves arbitrary relation answers, even on the
-- diagonal. Only the compiled-model theorem identifies its guard behavior.
example : Checker.reflexiveBinaryQueryCosted
    (fun (_ _ : Fin 1) (_ : Fin 1) => false) 0 0 0 = ⟨false, 2⟩ := by native_decide
example : Checker.reflexiveBinaryQueryCosted
    (partModel false false false false false).part (0 : Fin 2) (0 : Fin 2) (0 : Fin 1) =
    ⟨true, 2⟩ := by native_decide
example : Checker.reflexiveBinaryQueryCosted
    (partModel false false false false false).part (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) =
    ⟨false, 13⟩ := by native_decide
example : Checker.reflexiveBinaryQueryCosted
    (partModel true false false false false).part (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) =
    ⟨true, 13⟩ := by native_decide
example : Checker.reflexiveBinaryQueryCosted
    (partModel true false false false false).overlap (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) =
    ⟨false, 13⟩ := by native_decide

-- Reflexivity performs two equality/branch operations plus two per world
-- and two per thing. Antisymmetry stops at the first unequal mutual pair.
example : Checker.checkAx47Costed (partModel false false false false false) =
    ⟨true, 12⟩ := by native_decide
example : Checker.checkAx48Costed (partModel false false false false false) =
    ⟨true, 68⟩ := by native_decide
example : Checker.checkAx48Costed (partModel true false false false false) =
    ⟨true, 81⟩ := by native_decide
example : Checker.checkAx48Costed (partModel true true false false false) =
    ⟨false, 48⟩ := by native_decide

-- All two-thing reflexive relations are transitive, but execute different
-- numbers of table reads. The eight triples add 44 loop operations.
example : Checker.checkAx49Costed (partModel false false false false false) =
    ⟨true, 162⟩ := by native_decide
example : Checker.checkAx49Costed (partModel true false false false false) =
    ⟨true, 203⟩ := by native_decide
example : Checker.checkAx49Costed (partModel true true false false false) =
    ⟨true, 248⟩ := by native_decide

private def partChainAst : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := #[.binary .part 0 1 0, .binary .part 1 2 0] }

-- The first failed triple is (0,1,2). The preceding y=0 block costs 72;
-- the y=1 block costs 116, and the outer loop adds two.
example : Checker.checkAx49Costed
    (compileVerifiedModel partChainAst (by decide) (by decide) (by decide)) =
    ⟨false, 190⟩ := by native_decide

-- Without cross edges, the two off-diagonal common-part searches cost 34.
-- Adding (0,1) finds a common part but conflicts with the absent overlap fact.
example : Checker.checkAx50Costed (partModel false false false false false) =
    ⟨true, 154⟩ := by native_decide
example : Checker.checkAx50Costed (partModel true false false false false) =
    ⟨false, 53⟩ := by native_decide

-- Supplementation searches for a part that does not overlap the other thing.
example : Checker.checkAx51Costed (partModel false false false false false) =
    ⟨true, 116⟩ := by native_decide
example : Checker.checkAx51Costed (partModel true false true false false) =
    ⟨false, 69⟩ := by native_decide

-- Proper-part facts are separate from the reflexive part interpretation.
example : Checker.checkAx52Costed (partModel false false false false false) =
    ⟨true, 112⟩ := by native_decide
example : Checker.checkAx52Costed (partModel true false false true false) =
    ⟨true, 125⟩ := by native_decide
example : Checker.checkAx52Costed (partModel true false false false false) =
    ⟨false, 70⟩ := by native_decide
example : Checker.checkAx52Costed (partModel true true false false false) =
    ⟨true, 140⟩ := by native_decide

example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun p => (#[false, true]).all (fun q =>
      (Checker.checkAx52Costed (partModel a b false p q)).value ==
        ((p == (a && !b)) && (q == (b && !a))))))) = true := by native_decide

private def functionalAst
    (hasSource sourceWorks early late targetWorks hasPart : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if hasSource then #[.binary .inst 0 0 0] else #[]) ++
      (if sourceWorks then #[.binary .functionsAs 0 0 0] else #[]) ++
      (if early then #[.binary .inst 1 1 0] else #[]) ++
      (if late then #[.binary .inst 2 1 0] else #[]) ++
      (if targetWorks then
        #[.binary .functionsAs 1 1 0, .binary .functionsAs 2 1 0] else #[]) ++
      (if hasPart then #[.binary .properPart 0 1 0] else #[]) }

private def functionalModel
    (hasSource sourceWorks early late targetWorks hasPart : Bool) : FiniteModel4 :=
  compileVerifiedModel (functionalAst hasSource sourceWorks early late targetWorks hasPart)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by
      cases hasSource <;> cases sourceWorks <;> cases early <;> cases late <;>
        cases targetWorks <;> cases hasPart <;> decide)

-- An excluded self costs four with loop overhead. A distinct candidate costs
-- sixteen after a failed instance read, or twenty-seven after both reads.
example : Checker.genericFunctionalWitnessCosted
    (functionalModel true true false false true false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 36⟩ := by native_decide
example : Checker.genericFunctionalWitnessCosted
    (functionalModel true true true false true false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 31⟩ := by native_decide
example : Checker.genericFunctionalWitnessCosted
    (functionalModel true true false true true false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 47⟩ := by native_decide
example : Checker.genericFunctionalWitnessCosted
    (functionalModel true true true false false false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 47⟩ := by native_decide
example : Checker.genericFunctionalWitnessCosted
    (functionalModel true true true false true false) (2 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 43⟩ := by native_decide

-- A missing source instance skips functions-as and the witness search.
-- A present instance that does not function adds eleven for functions-as.
example : Checker.genericFunctionalDependenceCosted
    (functionalModel false true true true true false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 48⟩ := by native_decide
example : Checker.genericFunctionalDependenceCosted
    (functionalModel true false false false false false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 59⟩ := by native_decide
-- A failed witness stops at the first source. A successful witness continues
-- through the remaining two source candidates, costing another 32.
example : Checker.genericFunctionalDependenceCosted
    (functionalModel true true false false true false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 63⟩ := by native_decide
example : Checker.genericFunctionalDependenceCosted
    (functionalModel true true true false true false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 90⟩ := by native_decide
example : Checker.genericFunctionalDependenceCosted
    (functionalModel true true false true true false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 106⟩ := by native_decide
example : Checker.genericFunctionalDependenceCosted
    (functionalModel true true true false false false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 74⟩ := by native_decide
example : Checker.genericFunctionalDependenceCosted
    (functionalModel true true true true false false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 85⟩ := by native_decide

-- The generic result controls whether individual instance queries execute.
-- A false functions-as premise skips its target query.
example : Checker.individualFunctionalDependenceCosted
    (functionalModel false true true true true false) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 61⟩ := by native_decide
example : Checker.individualFunctionalDependenceCosted
    (functionalModel true false false false false false) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 84⟩ := by native_decide
example : Checker.individualFunctionalDependenceCosted
    (functionalModel true false true false true false) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 97⟩ := by native_decide
example : Checker.individualFunctionalDependenceCosted
    (functionalModel true true true false true false) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 139⟩ := by native_decide
example : Checker.individualFunctionalDependenceCosted
    (functionalModel true true false false true false) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 64⟩ := by native_decide
example : Checker.individualFunctionalDependenceCosted
    (functionalModel true true false true true false) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 131⟩ := by native_decide

-- Proper part is a separate guard, evaluated before either dependence search.
example : Checker.functionalComponentCosted
    (functionalModel true true true false true false) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 12⟩ := by native_decide
example : Checker.functionalComponentCosted
    (functionalModel true true true false true true) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 151⟩ := by native_decide
example : Checker.functionalComponentCosted
    (functionalModel true true false false true true) (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 76⟩ := by native_decide

example : (#[false, true]).all (fun source => (#[false, true]).all (fun sourceWorks =>
    (#[false, true]).all (fun early => (#[false, true]).all (fun late =>
      (#[false, true]).all (fun targetWorks =>
        (Checker.genericFunctionalDependenceCosted
          (functionalModel source sourceWorks early late targetWorks false) (0 : Fin 3) (1 : Fin 3) (0 : Fin 1)).value ==
            (!source || !sourceWorks || ((early || late) && targetWorks))))))) = true :=
  by native_decide

private def functionalTwoWorldAst : ModelAST :=
  { functionalAst true true true false true true with worldCount := 2 }

-- All facts are in world zero. The second world cannot borrow its witnesses.
example : Checker.genericFunctionalDependenceCosted
    (compileVerifiedModel functionalTwoWorldAst (by decide) (by decide) (by decide))
      (0 : Fin 3) (1 : Fin 3) (1 : Fin 2) = ⟨true, 48⟩ := by native_decide

private def oneFunctionalAst (hasInstance works hasPart : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := (if hasInstance then #[.binary .inst 0 0 0] else #[]) ++
      (if works then #[.binary .functionsAs 0 0 0] else #[]) ++
      (if hasPart then #[.binary .properPart 0 0 0] else #[]) }

private def oneFunctionalModel (hasInstance works hasPart : Bool) : FiniteModel4 :=
  compileVerifiedModel (oneFunctionalAst hasInstance works hasPart)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by cases hasInstance <;> cases works <;> cases hasPart <;> decide)

-- Each definition check binds its shared search once. Equivalence adds one
-- operation for a true answer, or two for a false one.
-- Three loops add six to axiom 53; five loops add ten to axioms 54 and 55.
example : Checker.checkAx53Costed (oneFunctionalModel false false false) =
    ⟨true, 23⟩ := by native_decide
example : Checker.checkAx54Costed (oneFunctionalModel false false false) =
    ⟨true, 41⟩ := by native_decide
example : Checker.checkAx55Costed (oneFunctionalModel false false false) =
    ⟨true, 24⟩ := by native_decide
example : Checker.checkAx53Costed (oneFunctionalModel true true true) =
    ⟨true, 39⟩ := by native_decide
example : Checker.checkAx54Costed (oneFunctionalModel true true true) =
    ⟨true, 44⟩ := by native_decide
example : Checker.checkAx55Costed (oneFunctionalModel true true true) =
    ⟨true, 56⟩ := by native_decide
example : Checker.checkAx53Costed (oneFunctionalModel true false true) =
    ⟨true, 34⟩ := by native_decide
example : Checker.checkAx54Costed (oneFunctionalModel true false true) =
    ⟨true, 76⟩ := by native_decide
example : Checker.checkAx55Costed (oneFunctionalModel true false true) =
    ⟨true, 88⟩ := by native_decide

private def constitutionAst (hasInstance linked endurant perdurant kind existsHere : Bool) :
    ModelAST :=
  { worldCount := 1, thingCount := 1,
    facts := (if hasInstance then #[.binary .inst 0 0 0] else #[]) ++
      (if linked then #[.binary .constitutedBy 0 0 0] else #[]) ++
      (if endurant then #[.unary .endurant 0 0] else #[]) ++
      (if perdurant then #[.unary .perdurant 0 0] else #[]) ++
      (if kind then #[.unary .kind 0 0] else #[]) ++
      (if existsHere then #[.unary .ex 0 0] else #[]) }

private def constitutionModel (hasInstance linked endurant perdurant kind existsHere : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (constitutionAst hasInstance linked endurant perdurant kind existsHere)
    (by change 0 < 1; decide) (by change 0 < 1; decide)
    (by
      cases hasInstance <;> cases linked <;> cases endurant <;> cases perdurant <;>
        cases kind <;> cases existsHere <;> decide)

-- False left operands add a negation to classification equivalence.
-- The two equivalences and their conjunction cost 37, 36, or 35 here.
example : Checker.checkAx56Costed (constitutionModel false false false false false false) =
    ⟨true, 19⟩ := by native_decide
example : Checker.checkAx56Costed (constitutionModel false true false false false false) =
    ⟨true, 56⟩ := by native_decide
example : Checker.checkAx56Costed (constitutionModel false true true false false false) =
    ⟨true, 55⟩ := by native_decide
example : Checker.checkAx56Costed (constitutionModel false true true true false false) =
    ⟨true, 54⟩ := by native_decide

-- The kind condition tests constitution, two instances, and two kinds in order.
example : Checker.checkAx57Costed (constitutionModel false false false false false false) =
    ⟨true, 24⟩ := by native_decide
example : Checker.checkAx57Costed (constitutionModel false true false false false false) =
    ⟨true, 36⟩ := by native_decide
example : Checker.checkAx57Costed (constitutionModel true true false false false false) =
    ⟨true, 57⟩ := by native_decide
example : Checker.checkAx57Costed (constitutionModel true true false false true false) =
    ⟨false, 66⟩ := by native_decide

-- Both equivalence operands reuse one search result, including false results.
example : Checker.checkAx58Costed (constitutionModel false false false false false false) =
    ⟨true, 22⟩ := by native_decide
example : Checker.checkAx58Costed (constitutionModel true false false false false false) =
    ⟨true, 48⟩ := by native_decide
example : Checker.checkAx58Costed (constitutionModel true true false false false false) =
    ⟨true, 47⟩ := by native_decide
example : Checker.checkAx59Costed (constitutionModel false false false false false false) =
    ⟨true, 24⟩ := by native_decide
example : Checker.checkAx59Costed (constitutionModel true false false false false false) =
    ⟨true, 77⟩ := by native_decide
example : Checker.checkAx59Costed (constitutionModel true true false false false false) =
    ⟨true, 87⟩ := by native_decide

-- Persistence scans run only after both the perdurant and constitution reads pass.
example : Checker.checkAx60Costed (constitutionModel false true false false false true) =
    ⟨true, 17⟩ := by native_decide
example : Checker.checkAx60Costed (constitutionModel false false false true false true) =
    ⟨true, 28⟩ := by native_decide
example : Checker.checkAx60Costed (constitutionModel false true false true false false) =
    ⟨true, 40⟩ := by native_decide
example : Checker.checkAx60Costed (constitutionModel false true false true false true) =
    ⟨true, 51⟩ := by native_decide
example : Checker.checkAx61Costed (constitutionModel false false false false false false) =
    ⟨true, 19⟩ := by native_decide
example : Checker.checkAx61Costed (constitutionModel false true false false false false) =
    ⟨false, 31⟩ := by native_decide
example : Checker.checkAx62Costed (constitutionModel true true true true true true) =
    ⟨true, 4⟩ := by native_decide

private def constitutionSortAst (leftEnd rightEnd leftPer rightPer : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 2, facts :=
    #[.binary .constitutedBy 0 1 0] ++
      (if leftEnd then #[.unary .endurant 0 0] else #[]) ++
      (if rightEnd then #[.unary .endurant 1 0] else #[]) ++
      (if leftPer then #[.unary .perdurant 0 0] else #[]) ++
      (if rightPer then #[.unary .perdurant 1 0] else #[]) }

private def constitutionSortModel (leftEnd rightEnd leftPer rightPer : Bool) : FiniteModel4 :=
  compileVerifiedModel (constitutionSortAst leftEnd rightEnd leftPer rightPer)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases leftEnd <;> cases rightEnd <;> cases leftPer <;> cases rightPer <;> decide)

example : Checker.checkAx56Costed (constitutionSortModel false false false false) =
    ⟨true, 109⟩ := by native_decide
-- An endurant mismatch skips both perdurant reads.
example : Checker.checkAx56Costed (constitutionSortModel true false true true) =
    ⟨false, 54⟩ := by native_decide
example : Checker.checkAx56Costed (constitutionSortModel false true true true) =
    ⟨false, 55⟩ := by native_decide
example : Checker.checkAx56Costed (constitutionSortModel false false true false) =
    ⟨false, 72⟩ := by native_decide
example : Checker.checkAx56Costed (constitutionSortModel true true true true) =
    ⟨true, 107⟩ := by native_decide
example : (#[false, true]).all (fun a => (#[false, true]).all (fun b =>
    (#[false, true]).all (fun c => (#[false, true]).all (fun d =>
      (Checker.checkAx56Costed (constitutionSortModel a b c d)).value ==
        ((a == b) && (c == d)))))) = true := by native_decide

-- A single directed constitution passes asymmetry; the reverse is absent.
example : Checker.checkAx61Costed (constitutionSortModel false false false false) =
    ⟨true, 84⟩ := by native_decide

private def constitutionWitnessAst (early late linked : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3, facts := #[.binary .inst 0 0 0] ++
    (if early then #[.binary .inst 1 1 0] else #[]) ++
    (if late then #[.binary .inst 2 1 0] else #[]) ++
    (if linked then
      #[.binary .constitutedBy 0 1 0, .binary .constitutedBy 0 2 0] else #[]) }

private def constitutionWitnessModel (early late linked : Bool) : FiniteModel4 :=
  compileVerifiedModel (constitutionWitnessAst early late linked)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases early <;> cases late <;> cases linked <;> decide)

-- A failed instance costs fourteen per candidate with loop overhead.
-- An executed constitution read raises the candidate cost to twenty-five.
example : Checker.constitutionalWitnessCosted (constitutionWitnessModel false false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 42⟩ := by native_decide
example : Checker.constitutionalWitnessCosted (constitutionWitnessModel true false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 39⟩ := by native_decide
example : Checker.constitutionalWitnessCosted (constitutionWitnessModel false true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 53⟩ := by native_decide
example : Checker.constitutionalWitnessCosted (constitutionWitnessModel true false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 53⟩ := by native_decide
example : Checker.genericConstitutionalDependenceCosted
    (constitutionWitnessModel false false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 57⟩ := by native_decide
example : Checker.genericConstitutionalDependenceCosted
    (constitutionWitnessModel true false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 84⟩ := by native_decide
example : Checker.genericConstitutionalDependenceCosted
    (constitutionWitnessModel false true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 98⟩ := by native_decide
-- Unlike individual functional dependence, constitution tests both instances
-- before the generic search. A missing second instance stops at cost 24.
example : Checker.constitutionCosted (constitutionWitnessModel false true true)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 24⟩ := by native_decide
example : Checker.constitutionCosted (constitutionWitnessModel true false true)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨true, 120⟩ := by native_decide
example : Checker.constitutionCosted (constitutionWitnessModel true false false)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
      ⟨false, 93⟩ := by native_decide

private def persistenceAst (existsLater linkedLater : Bool) : ModelAST :=
  { worldCount := 2, thingCount := 2, facts :=
    #[.unary .perdurant 0 0, .unary .ex 0 0, .binary .constitutedBy 0 1 0] ++
      (if existsLater then #[.unary .ex 0 1] else #[]) ++
      (if linkedLater then #[.binary .constitutedBy 0 1 1] else #[]) }

private def persistenceModel (existsLater linkedLater : Bool) : FiniteModel4 :=
  compileVerifiedModel (persistenceAst existsLater linkedLater)
    (by change 0 < 2; decide) (by change 0 < 2; decide)
    (by cases existsLater <;> cases linkedLater <;> decide)

example : Checker.constitutionPersistenceCosted (persistenceModel false false)
    (0 : Fin 2) (1 : Fin 2) = ⟨true, 35⟩ := by native_decide
example : Checker.constitutionPersistenceCosted (persistenceModel true false)
    (0 : Fin 2) (1 : Fin 2) = ⟨false, 46⟩ := by native_decide
example : Checker.constitutionPersistenceCosted (persistenceModel true true)
    (0 : Fin 2) (1 : Fin 2) = ⟨true, 46⟩ := by native_decide
example : Checker.checkAx60Costed (persistenceModel false false) =
    ⟨true, 173⟩ := by native_decide
example : Checker.checkAx60Costed (persistenceModel true false) =
    ⟨false, 113⟩ := by native_decide
example : Checker.checkAx60Costed (persistenceModel true true) =
    ⟨true, 184⟩ := by native_decide
-- Axiom 62 still visits both domains, even though every body is true.
example : Checker.checkAx62Costed (persistenceModel true true) =
    ⟨true, 12⟩ := by native_decide

/-! ## Existence across worlds and inherence

An existence implication costs twelve operations when its premise is false,
or twenty when it reads the consequent. Each count includes the world loop.
The fixtures keep world zero first, even when the caller supplies world one.
-/

private def existenceAst (x0 y0 x1 y1 : Bool) : ModelAST :=
  { worldCount := 2, thingCount := 2,
    facts := (if x0 then #[.unary .ex 0 0] else #[]) ++
      (if y0 then #[.unary .ex 1 0] else #[]) ++
      (if x1 then #[.unary .ex 0 1] else #[]) ++
      (if y1 then #[.unary .ex 1 1] else #[]) }

private def existenceModel (x0 y0 x1 y1 : Bool) : FiniteModel4 :=
  compileVerifiedModel (existenceAst x0 y0 x1 y1)
    (by change 0 < 2; decide) (by change 0 < 2; decide)
    (by cases x0 <;> cases y0 <;> cases x1 <;> cases y1 <;> decide)

example : Checker.existentialDependenceCosted (existenceModel false false false false)
    (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = ⟨true, 24⟩ := by native_decide
example : Checker.existentialDependenceCosted (existenceModel true false false false)
    (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = ⟨false, 20⟩ := by native_decide
example : Checker.existentialDependenceCosted (existenceModel false false true false)
    (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = ⟨false, 32⟩ := by native_decide
example : Checker.existentialDependenceCosted (existenceModel true true true true)
    (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = ⟨true, 40⟩ := by native_decide
example : Checker.existentialDependenceCosted (existenceModel true false false true)
    (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = ⟨false, 20⟩ := by native_decide
example : Checker.existentialDependenceCosted (existenceModel false true true false)
    (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = ⟨false, 32⟩ := by native_decide

example : Checker.existentialIndependenceCosted (existenceModel false false false false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) = ⟨false, 26⟩ := by native_decide
example : Checker.existentialIndependenceCosted (existenceModel true true true true)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) = ⟨false, 42⟩ := by native_decide
example : Checker.existentialIndependenceCosted (existenceModel true false false true)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) = ⟨true, 55⟩ := by native_decide
example : Checker.existentialIndependenceCosted (existenceModel false true true false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) = ⟨true, 55⟩ := by native_decide

-- A true shared answer needs one comparison branch; a false one also needs
-- negation. Each axiom-63 body here costs D+1 for search cost D. The eight
-- assignments add eight comparison operations and 28 loop operations.
example : Checker.checkAx63Costed (existenceModel false false false false) = ⟨true, 228⟩ := by
  native_decide
example : Checker.checkAx63Costed (existenceModel true true true true) = ⟨true, 356⟩ := by
  native_decide
example : Checker.checkAx64Costed (existenceModel false false false false) = ⟨true, 252⟩ := by
  native_decide
example : Checker.checkAx64Costed (existenceModel true true true true) = ⟨true, 380⟩ := by
  native_decide
example : Checker.checkAx65Costed (existenceModel false false false false) = ⟨true, 132⟩ := by
  native_decide
example : Checker.checkAx66Costed (existenceModel false false false false) = ⟨true, 132⟩ := by
  native_decide
example : Checker.checkAx67Costed (existenceModel false false false false) = ⟨true, 284⟩ := by
  native_decide

/-- Exhaust all sixteen existence patterns. Independence requires a witness
world in each direction, rather than only failure of one implication. -/
example :
    ([false, true].all fun x0 => [false, true].all fun y0 =>
      [false, true].all fun x1 => [false, true].all fun y1 =>
        let M := existenceModel x0 y0 x1 y1
        (Checker.existentialDependenceCosted M (0 : Fin 2) (1 : Fin 2) (0 : Fin 2)).value ==
          ((!x0 || y0) && (!x1 || y1)) &&
        (Checker.existentialIndependenceCosted M (0 : Fin 2) (1 : Fin 2) (0 : Fin 2)).value ==
          (((x0 && !y0) || (x1 && !y1)) && ((y0 && !x0) || (y1 && !x1)))) = true := by
  native_decide

/-- One inherence edge exercises the implication consequent. A second edge
at (0,0) gives axiom 67 two different bearers. Existence, moment classification,
concrete classification, and instantiation occupy separate table fields. -/
private def inherenceAst (existsX existsY isMoment concrete hasInstance doubleBearer : Bool) :
    ModelAST :=
  { worldCount := 1, thingCount := 2,
    facts := #[.binary .inheresIn 0 1 0] ++
      (if doubleBearer then #[.binary .inheresIn 0 0 0] else #[]) ++
      (if existsX then #[.unary .ex 0 0] else #[]) ++
      (if existsY then #[.unary .ex 1 0] else #[]) ++
      (if isMoment then #[.unary .moment 0 0] else #[]) ++
      (if concrete then #[.unary .concreteIndividual 1 0] else #[]) ++
      (if hasInstance then #[.binary .inst 0 1 0] else #[]) }

private def inherenceModel (existsX existsY isMoment concrete hasInstance doubleBearer : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (inherenceAst existsX existsY isMoment concrete hasInstance doubleBearer)
    (by change 0 < 1; decide) (by change 0 < 2; decide)
    (by cases existsX <;> cases existsY <;> cases isMoment <;> cases concrete <;>
      cases hasInstance <;> cases doubleBearer <;> decide)

example : Checker.ax66ConsequentCosted (inherenceModel false false false true true false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = ⟨false, 9⟩ := by native_decide
example : Checker.ax66ConsequentCosted (inherenceModel false false true false true false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = ⟨true, 25⟩ := by native_decide
example : Checker.ax66ConsequentCosted (inherenceModel false false true true true false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = ⟨true, 25⟩ := by native_decide
example : Checker.ax66ConsequentCosted (inherenceModel false false true false false false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = ⟨false, 46⟩ := by native_decide
example : Checker.ax66ConsequentCosted (inherenceModel false false true true false false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = ⟨true, 46⟩ := by native_decide
example : Checker.checkAx65Costed (inherenceModel false false false false false false) =
    ⟨true, 84⟩ := by native_decide
example : Checker.checkAx65Costed (inherenceModel true false false false false false) =
    ⟨false, 56⟩ := by native_decide
example : Checker.checkAx65Costed (inherenceModel true true false false false false) =
    ⟨true, 92⟩ := by native_decide
example : Checker.checkAx66Costed (inherenceModel false false false false false false) =
    ⟨false, 45⟩ := by native_decide
example : Checker.checkAx66Costed (inherenceModel false false true false false false) =
    ⟨false, 82⟩ := by native_decide
example : Checker.checkAx66Costed (inherenceModel false false true true false false) =
    ⟨true, 118⟩ := by native_decide
example : Checker.checkAx66Costed (inherenceModel false false true false true false) =
    ⟨true, 97⟩ := by native_decide
example : Checker.checkAx67Costed (inherenceModel false false false false false false) =
    ⟨true, 179⟩ := by native_decide
example : Checker.checkAx67Costed (inherenceModel false false false false false true) =
    ⟨false, 64⟩ := by native_decide

-- Shared consumers must retain the corrected existence-scan cost.
example : Checker.externallyDependentCosted
    (inherenceModel true false false false false false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = ⟨false, 21⟩ := by native_decide

example : Checker.boxExImpCosted (inherenceModel true false false false false false)
    (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = ⟨false, 20⟩ := by native_decide

/-! ## External dependence

A difference scan costs eleven operations when the left existence test fails,
or twenty when both cells are read, including the world loop. A false inherence
premise costs thirteen operations and skips both separation scans.
-/

example : Checker.existenceDifferenceCosted (existenceModel false false false false)
    (0 : Fin 2) (1 : Fin 2) = ⟨false, 22⟩ := by native_decide
example : Checker.existenceDifferenceCosted (existenceModel true false false false)
    (0 : Fin 2) (1 : Fin 2) = ⟨true, 20⟩ := by native_decide
example : Checker.existenceDifferenceCosted (existenceModel false false true false)
    (0 : Fin 2) (1 : Fin 2) = ⟨true, 31⟩ := by native_decide
example : Checker.existenceDifferenceCosted (existenceModel true true true true)
    (0 : Fin 2) (1 : Fin 2) = ⟨false, 40⟩ := by native_decide

example : ∀ x0 y0 x1 y1 : Bool,
    (Checker.existenceDifferenceCosted (existenceModel x0 y0 x1 y1)
      (0 : Fin 2) (1 : Fin 2)).value = ((x0 && !y0) || (x1 && !y1)) := by
  native_decide

-- Three worlds separate the common existence premise from the two independent
-- separation witnesses. Bearer 2 is visited after two false inherence premises.
private def externalAst (hasBearer yOnly zOnly isMode : Bool) : ModelAST :=
  { worldCount := 3, thingCount := 3,
    facts := #[.unary .ex 0 0, .unary .ex 1 0, .unary .ex 2 0] ++
      (if hasBearer then #[.binary .inheresIn 0 2 0] else #[]) ++
      (if yOnly then #[.unary .ex 1 1] else #[]) ++
      (if zOnly then #[.unary .ex 2 2] else #[]) ++
      (if isMode then #[.unary .mode 0 0] else #[]) }

private def externalModel (hasBearer yOnly zOnly isMode : Bool) : FiniteModel4 :=
  compileVerifiedModel (externalAst hasBearer yOnly zOnly isMode)
    (by change 0 < 3; decide) (by change 0 < 3; decide)
    (by cases hasBearer <;> cases yOnly <;> cases zOnly <;> cases isMode <;> decide)

example : Checker.externalSeparationCosted (externalModel false true true true)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) = ⟨true, 13⟩ := by native_decide
example : Checker.externalSeparationCosted (externalModel true false true true)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) = ⟨false, 56⟩ := by native_decide
example : Checker.externalSeparationCosted (externalModel true true false true)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) = ⟨false, 96⟩ := by native_decide
example : Checker.externalSeparationCosted (externalModel true true true true)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) = ⟨true, 105⟩ := by native_decide

example : Checker.externallyDependentCosted (externalModel false true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) = ⟨true, 90⟩ := by native_decide
example : Checker.externallyDependentCosted (externalModel true false true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) = ⟨false, 133⟩ := by native_decide
example : Checker.externallyDependentCosted (externalModel true true false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) = ⟨false, 173⟩ := by native_decide
example : Checker.externallyDependentCosted (externalModel true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) = ⟨true, 182⟩ := by native_decide

example : Checker.externallyDependentModeCosted (externalModel true true true false)
    (0 : Fin 3) (0 : Fin 3) = ⟨false, 9⟩ := by native_decide
example : Checker.externallyDependentModeCosted (externalModel false true true true)
    (0 : Fin 3) (0 : Fin 3) = ⟨true, 101⟩ := by native_decide
example : Checker.externallyDependentModeCosted (externalModel true true true true)
    (0 : Fin 3) (0 : Fin 3) = ⟨true, 328⟩ := by native_decide
example : Checker.externallyDependentModeCosted (externalModel true false true true)
    (0 : Fin 3) (0 : Fin 3) = ⟨false, 423⟩ := by native_decide

example : ∀ hasBearer yOnly zOnly isMode : Bool,
    let M := externalModel hasBearer yOnly zOnly isMode
    (Checker.externallyDependentCosted M (0 : Fin 3) (1 : Fin 3) (0 : Fin 3)).value =
      (!hasBearer || (yOnly && zOnly)) := by native_decide

-- With no edges or modes, axiom 69 evaluates the shared dependence predicate
-- once. Axiom 70 skips every dependence search after its mode test.
example : Checker.checkAx69Costed (existenceModel false false false false) =
    ⟨true, 476⟩ := by native_decide
example : Checker.checkAx70Costed (existenceModel false false false false) =
    ⟨true, 56⟩ := by native_decide

/-! ## Foundation witnesses and qua-individuals

A candidate without a foundation edge costs fourteen operations, including the
outer search step, and skips uniqueness. For three things, a unique first
foundation costs sixty operations; a unique last foundation costs eighty-eight.
Part tests include the two-operation reflexive branch.
-/

private def foundationAst (first last isMode isRelator firstEvent lastEvent : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if first then #[.binary .foundedBy 0 0 0] else #[]) ++
      (if last then #[.binary .foundedBy 0 2 0] else #[]) ++
      (if isMode then #[.unary .mode 0 0] else #[]) ++
      (if isRelator then #[.unary .relator 0 0] else #[]) ++
      (if firstEvent then #[.unary .perdurant 0 0] else #[]) ++
      (if lastEvent then #[.unary .perdurant 2 0] else #[]) }

private def foundationModel (first last isMode isRelator firstEvent lastEvent : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (foundationAst first last isMode isRelator firstEvent lastEvent)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases isMode <;> cases isRelator <;>
      cases firstEvent <;> cases lastEvent <;> decide)

example : Checker.existsUniqueFoundedByCosted (foundationModel false false false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 42⟩ := by native_decide

example : Checker.existsUniqueFoundedByCosted (foundationModel true false false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 60⟩ := by native_decide

example : Checker.existsUniqueFoundedByCosted (foundationModel false true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 88⟩ := by native_decide

example : Checker.existsUniqueFoundedByCosted (foundationModel true true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 105⟩ := by native_decide

example : Checker.sameFoundationCosted (foundationModel false false false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 42⟩ := by native_decide

example : Checker.sameFoundationCosted (foundationModel true false false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 25⟩ := by native_decide

example : Checker.sameFoundationCosted (foundationModel false true false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 53⟩ := by native_decide

example : Checker.sameFoundationCosted (foundationModel true false false false false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 53⟩ := by native_decide

example : Checker.ax71ConsequentCosted (foundationModel true false false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 19⟩ := by native_decide

example : Checker.ax71ConsequentCosted (foundationModel true false false true false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 27⟩ := by native_decide

example : Checker.ax71ConsequentCosted (foundationModel true false false true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 27⟩ := by native_decide

example : Checker.ax71ConsequentCosted (foundationModel true false true false true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 79⟩ := by native_decide

example : Checker.checkAx71Costed (foundationModel false false false false false false) =
    ⟨true, 159⟩ := by native_decide

example : Checker.checkAx71Costed (foundationModel true false false false false false) =
    ⟨false, 38⟩ := by native_decide

example : Checker.checkAx71Costed (foundationModel true false false true false false) =
    ⟨false, 46⟩ := by native_decide

example : Checker.checkAx71Costed (foundationModel true false false true true false) =
    ⟨true, 186⟩ := by native_decide

example : Checker.checkAx71Costed (foundationModel true false true false true false) =
    ⟨true, 238⟩ := by native_decide

example : Checker.checkAx72Costed (foundationModel false false false false false false) =
    ⟨true, 45⟩ := by native_decide

example : Checker.checkAx72Costed (foundationModel false false true false false false) =
    ⟨false, 117⟩ := by native_decide

example : Checker.checkAx72Costed (foundationModel true false true false false false) =
    ⟨true, 165⟩ := by native_decide

example : Checker.checkAx72Costed (foundationModel false true true false false false) =
    ⟨true, 193⟩ := by native_decide

example : Checker.checkAx72Costed (foundationModel true true true false false false) =
    ⟨false, 180⟩ := by native_decide

example : Checker.checkAx77Costed (foundationModel false false false false false false) =
    ⟨true, 42⟩ := by native_decide

example : Checker.checkAx77Costed (foundationModel false false false true false false) =
    ⟨false, 56⟩ := by native_decide

example : Checker.checkAx77Costed (foundationModel true false false true false false) =
    ⟨true, 102⟩ := by native_decide

example : Checker.checkAx77Costed (foundationModel false true false true false false) =
    ⟨true, 130⟩ := by native_decide

example : Checker.checkAx77Costed (foundationModel true true false true false false) =
    ⟨false, 119⟩ := by native_decide

example : Checker.checkAx78Costed (foundationModel false false false false false false) =
    ⟨true, 141⟩ := by native_decide

example : Checker.checkAx78Costed (foundationModel false false false true false false) =
    ⟨false, 61⟩ := by native_decide

example : Checker.checkAx78Costed (foundationModel true false false true false false) =
    ⟨true, 194⟩ := by native_decide

example : Checker.checkAx78Costed (foundationModel false true false true false false) =
    ⟨true, 222⟩ := by native_decide

example : ∀ first last : Bool,
    (Checker.existsUniqueFoundedByCosted
      (foundationModel first last false false false false)
      (0 : Fin 3) (0 : Fin 1)).value = (first != last) := by native_decide

private def quaAst (first last isMode : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if first then #[.binary .quaIndividualOf 0 0 0] else #[]) ++
      (if last then #[.binary .quaIndividualOf 0 2 0] else #[]) ++
      (if isMode then #[.unary .mode 0 0] else #[]) }

private def quaModel (first last isMode : Bool) : FiniteModel4 :=
  compileVerifiedModel (quaAst first last isMode)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases isMode <;> decide)

example : Checker.quaIndividualExistsCosted (quaModel false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 39⟩ := by native_decide

example : Checker.quaIndividualExistsCosted (quaModel true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 13⟩ := by native_decide

example : Checker.quaIndividualExistsCosted (quaModel false true false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 39⟩ := by native_decide

-- Each inner part/classification equivalence fails at the reflexive part.
-- The outer equivalence compares that false result with a false qua edge,
-- succeeds, and continues. The three rows cost 101, 185, and 269 operations.
example : Checker.checkAx73Costed (quaModel false false false) =
    ⟨true, 555⟩ := by native_decide

example : Checker.checkAx74Costed (quaModel false false false) =
    ⟨true, 135⟩ := by native_decide

example : Checker.checkAx74Costed (quaModel true false false) =
    ⟨true, 108⟩ := by native_decide

example : Checker.checkAx74Costed (quaModel false true false) =
    ⟨true, 134⟩ := by native_decide

example : Checker.checkAx75Costed (quaModel false false false) =
    ⟨true, 135⟩ := by native_decide

example : Checker.checkAx75Costed (quaModel true false false) =
    ⟨false, 28⟩ := by native_decide

example : Checker.checkAx75Costed (quaModel true false true) =
    ⟨true, 178⟩ := by native_decide

example : Checker.checkAx75Costed (quaModel false true true) =
    ⟨true, 204⟩ := by native_decide

example : Checker.checkAx76Costed (quaModel false false false) =
    ⟨true, 510⟩ := by native_decide

example : Checker.checkAx76Costed (quaModel true false false) =
    ⟨true, 544⟩ := by native_decide

example : Checker.checkAx76Costed (quaModel false true false) =
    ⟨true, 544⟩ := by native_decide

example : Checker.checkAx76Costed (quaModel true true false) =
    ⟨false, 93⟩ := by native_decide

-- The common foundation affects classification but not the external-dependence
-- search. This isolates the final search after a successful mode and bearer test.
private def foundationClassificationAst (hasFoundation : Bool) : ModelAST :=
  let ast := externalAst true true true true
  { ast with facts := ast.facts ++
      (if hasFoundation then #[.binary .foundedBy 0 2 0] else #[]) }

private def foundationClassificationModel (hasFoundation : Bool) : FiniteModel4 :=
  compileVerifiedModel (foundationClassificationAst hasFoundation)
    (by change 0 < 3; decide) (by change 0 < 3; decide)
    (by cases hasFoundation <;> decide)

example : Checker.ax73ClassificationCosted (externalModel true true true false)
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) =
    ⟨false, 11⟩ := by native_decide

example : Checker.ax73ClassificationCosted (externalModel false true true true)
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) =
    ⟨false, 114⟩ := by native_decide

example : Checker.ax73ClassificationCosted (foundationClassificationModel false)
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) =
    ⟨false, 383⟩ := by native_decide

example : Checker.ax73ClassificationCosted (foundationClassificationModel true)
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) =
    ⟨true, 394⟩ := by native_decide

example : Checker.ax73PartsCosted (foundationClassificationModel false)
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) =
    ⟨false, 388⟩ := by native_decide

example : Checker.ax73PartsCosted (foundationClassificationModel true)
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) =
    ⟨true, 455⟩ := by native_decide

/-! ## Relators and characterization witnesses

These fixtures isolate the searches from the full UFO registry. Each model is
compiled to proved dense tables, but need not satisfy all UFO axioms. Exact
counts distinguish a skipped search from a searched domain with no witness.
-/

private def relatorPartsAst (first last qualifiedFirst extraCandidate isRelator : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if first then #[.binary .properPart 1 0 0] else #[]) ++
      (if last then #[.binary .properPart 2 0 0] else #[]) ++
      (if qualifiedFirst then #[.binary .quaIndividualOf 1 0 0, .binary .foundedBy 1 0 0] else #[]) ++
      (if extraCandidate then #[.binary .quaIndividualOf 2 0 0, .binary .foundedBy 2 0 0] else #[]) ++
      (if isRelator then #[.unary .relator 0 0] else #[]) }

private def relatorPartsModel (first last qualifiedFirst extraCandidate isRelator : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (relatorPartsAst first last qualifiedFirst extraCandidate isRelator)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases qualifiedFirst <;>
      cases extraCandidate <;> cases isRelator <;> decide)

example : Checker.properPartExistsCosted (relatorPartsModel false false true false true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 39⟩ := by native_decide

example : Checker.properPartExistsCosted (relatorPartsModel true false true false true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 26⟩ := by native_decide

example : Checker.properPartExistsCosted (relatorPartsModel false true true false true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 39⟩ := by native_decide

example : Checker.ax79PairConditionCosted (relatorPartsModel false false true false true)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 1) =
    ⟨true, 14⟩ := by native_decide

example : Checker.ax79PairConditionCosted (relatorPartsModel true false true false true)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 1) =
    ⟨true, 25⟩ := by native_decide

example : Checker.ax79PairConditionCosted (relatorPartsModel true false false false true)
    (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 65⟩ := by native_decide

example : Checker.ax79PairCompatibilityCosted (relatorPartsModel true false true false true)
    (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 79⟩ := by native_decide

example : Checker.ax79PairwiseCosted (relatorPartsModel true false true false true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 262⟩ := by native_decide

example : Checker.ax79ClosureCosted (relatorPartsModel true false true false true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 306⟩ := by native_decide

example : Checker.ax79CharacterizationCosted (relatorPartsModel true false true false true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 596⟩ := by native_decide

example : Checker.ax79CharacterizationCosted (relatorPartsModel true false false false true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 174⟩ := by native_decide

example : Checker.ax79ClosureCosted (relatorPartsModel true false true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 292⟩ := by native_decide

example : Checker.ax79CharacterizationCosted (relatorPartsModel true false true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 582⟩ := by native_decide

example : Checker.checkAx79Costed (relatorPartsModel true false true false true) =
    ⟨true, 717⟩ := by native_decide

example : Checker.checkAx79Costed (relatorPartsModel true false true false false) =
    ⟨false, 610⟩ := by native_decide

example : Checker.checkAx79Costed (relatorPartsModel false false true false true) =
    ⟨false, 53⟩ := by native_decide

example : Checker.checkAx79Costed (relatorPartsModel true false false false true) =
    ⟨false, 187⟩ := by native_decide

example : Checker.checkAx79Costed (relatorPartsModel true false true true true) =
    ⟨false, 595⟩ := by native_decide

private def mediationAst (self first last hasParts isRelator isEndurant claimed : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if self then #[.binary .quaIndividualOf 0 1 0] else #[]) ++
      (if first then #[.binary .quaIndividualOf 1 1 0] else #[]) ++
      (if last then #[.binary .quaIndividualOf 2 1 0] else #[]) ++
      (if hasParts then #[.binary .part 1 0 0, .binary .part 2 0 0] else #[]) ++
      (if isRelator then #[.unary .relator 0 0] else #[]) ++
      (if isEndurant then #[.unary .endurant 1 0] else #[]) ++
      (if claimed then #[.binary .mediates 0 1 0] else #[]) }

private def mediationModel (self first last hasParts isRelator isEndurant claimed : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (mediationAst self first last hasParts isRelator isEndurant claimed)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases self <;> cases first <;> cases last <;> cases hasParts <;>
      cases isRelator <;> cases isEndurant <;> cases claimed <;> decide)

example : Checker.mediationWitnessCosted (mediationModel false false false true true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 42⟩ := by native_decide

example : Checker.mediationWitnessCosted (mediationModel true false false false true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 16⟩ := by native_decide

example : Checker.mediationWitnessCosted (mediationModel false true false true true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 41⟩ := by native_decide

example : Checker.mediationWitnessCosted (mediationModel false false true true true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 55⟩ := by native_decide

example : Checker.mediationWitnessCosted (mediationModel false true false false true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 55⟩ := by native_decide

example : Checker.ax80CharacterizationCosted (mediationModel false false false false false true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 10⟩ := by native_decide

example : Checker.ax80CharacterizationCosted (mediationModel false false false false true false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 18⟩ := by native_decide

example : Checker.ax80CharacterizationCosted (mediationModel false false false true true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 60⟩ := by native_decide

example : Checker.ax80CharacterizationCosted (mediationModel false true false true true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 59⟩ := by native_decide

example : Checker.ax80CharacterizationCosted (mediationModel true false false false true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 34⟩ := by native_decide

example : Checker.checkAx80Costed (mediationModel false false false false false true false) =
    ⟨true, 249⟩ := by native_decide

example : Checker.checkAx80Costed (mediationModel false true false true true true false) =
    ⟨false, 113⟩ := by native_decide

example : Checker.checkAx80Costed (mediationModel false true false true true true true) =
    ⟨true, 313⟩ := by native_decide

example : Checker.checkAxQuaIndividualOfEndurantCosted (mediationModel false false false true true true false) =
    ⟨true, 159⟩ := by native_decide

example : Checker.checkAxQuaIndividualOfEndurantCosted (mediationModel false true false true true false false) =
    ⟨false, 97⟩ := by native_decide

example : Checker.checkAxQuaIndividualOfEndurantCosted (mediationModel false true false true true true false) =
    ⟨true, 167⟩ := by native_decide

-- Type 0 has optional bearer instances 0 and 2. Type 1 has moment instance 1.
-- The characterization edge is fixed, so missing types or witnesses expose
-- the corresponding branch rather than skipping the whole axiom premise.
private def characterizationWitnessAst
    (first last hasMoment firstEdge lastEdge typed : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := #[.binary .characterization 0 1 0] ++
      (if first then #[.binary .inst 0 0 0] else #[]) ++
      (if last then #[.binary .inst 2 0 0] else #[]) ++
      (if hasMoment then #[.binary .inst 1 1 0] else #[]) ++
      (if firstEdge then #[.binary .inheresIn 1 0 0] else #[]) ++
      (if lastEdge then #[.binary .inheresIn 1 2 0] else #[]) ++
      (if typed then #[.unary .endurantType 0 0, .unary .momentType 1 0,
        .unary .qualityType 1 0] else #[]) }

private def characterizationWitnessModel
    (first last hasMoment firstEdge lastEdge typed : Bool) : FiniteModel4 :=
  compileVerifiedModel (characterizationWitnessAst first last hasMoment firstEdge lastEdge typed)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases hasMoment <;>
      cases firstEdge <;> cases lastEdge <;> cases typed <;> decide)

example : Checker.existsUniqueInstInheresCosted (characterizationWitnessModel false false true true true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 42⟩ := by native_decide

example : Checker.existsUniqueInstInheresCosted (characterizationWitnessModel true false true true true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 86⟩ := by native_decide

example : Checker.existsUniqueInstInheresCosted (characterizationWitnessModel false true true true true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 114⟩ := by native_decide

example : Checker.existsUniqueInstInheresCosted (characterizationWitnessModel true true true true true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 166⟩ := by native_decide

example : Checker.existsUniqueInstInheresCosted (characterizationWitnessModel true false true false true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 54⟩ := by native_decide

example : Checker.ax81MomentWitnessCosted (characterizationWitnessModel true false true true true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 39⟩ := by native_decide

example : Checker.ax81MomentWitnessCosted (characterizationWitnessModel true false false true true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 42⟩ := by native_decide

example : Checker.ax81MomentWitnessCosted (characterizationWitnessModel true false true false true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 53⟩ := by native_decide

example : Checker.ax81TypeInstancesCosted (characterizationWitnessModel true false true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 84⟩ := by native_decide

example : Checker.ax81TypeInstancesCosted (characterizationWitnessModel false true true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 84⟩ := by native_decide

example : Checker.ax81TypeInstancesCosted (characterizationWitnessModel true false false true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 57⟩ := by native_decide

example : Checker.ax81TypeInstancesCosted (characterizationWitnessModel true true true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 123⟩ := by native_decide

example : Checker.ax82InstancesCosted (characterizationWitnessModel true false true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 131⟩ := by native_decide

example : Checker.ax82InstancesCosted (characterizationWitnessModel false true true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 159⟩ := by native_decide

example : Checker.ax82InstancesCosted (characterizationWitnessModel false false true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 72⟩ := by native_decide

example : Checker.ax82InstancesCosted (characterizationWitnessModel true true true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 196⟩ := by native_decide

example : Checker.ax81ConsequentCosted (characterizationWitnessModel true false true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 234⟩ := by native_decide

example : Checker.ax81ConsequentCosted (characterizationWitnessModel true false false true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 76⟩ := by native_decide

example : Checker.ax81ConsequentCosted (characterizationWitnessModel false false true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 136⟩ := by native_decide

example : Checker.ax81ConsequentCosted (characterizationWitnessModel true true true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 338⟩ := by native_decide

example : Checker.ax81ConsequentCosted (characterizationWitnessModel true false true true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 9⟩ := by native_decide

example : Checker.checkAx81Costed (characterizationWitnessModel true false true true true true) =
    ⟨true, 393⟩ := by native_decide

example : Checker.checkAx81Costed (characterizationWitnessModel true false false true true true) =
    ⟨false, 112⟩ := by native_decide

example : Checker.checkAx81Costed (characterizationWitnessModel false false true true true true) =
    ⟨false, 172⟩ := by native_decide

example : Checker.checkAx81Costed (characterizationWitnessModel true true true true true true) =
    ⟨false, 374⟩ := by native_decide

example : Checker.checkAx81Costed (characterizationWitnessModel true false true true true false) =
    ⟨false, 45⟩ := by native_decide

example : Checker.checkAx82Costed (characterizationWitnessModel true false true true true true) =
    ⟨true, 307⟩ := by native_decide

example : Checker.checkAx82Costed (characterizationWitnessModel true false false true true true) =
    ⟨true, 221⟩ := by native_decide

example : Checker.checkAx82Costed (characterizationWitnessModel false false true true true true) =
    ⟨false, 118⟩ := by native_decide

example : Checker.checkAx82Costed (characterizationWitnessModel true true true true true true) =
    ⟨false, 242⟩ := by native_decide

example : Checker.checkAx82Costed (characterizationWitnessModel true false true true true false) =
    ⟨true, 176⟩ := by native_decide

example : ∀ first last firstEdge lastEdge : Bool,
    (Checker.existsUniqueInstInheresCosted
      (characterizationWitnessModel first last true firstEdge lastEdge true)
      (1 : Fin 3) (0 : Fin 3) (0 : Fin 1)).value =
      ((first && firstEdge) != (last && lastEdge)) := by native_decide

/-! ## Nested quality-structure searches and proper subset

A structure must have exactly one associated quality type. A containing
structure or a structure for a type must also be unique, so those queries repeat
the first search. These exact counts include that repeated work.
-/

private def qualityStructureAst (first last isSet nonempty domain dimension : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if first then #[.unary .qualityType 0 0, .binary .associatedWith 0 0 0] else #[]) ++
      (if last then #[.unary .qualityType 2 0, .binary .associatedWith 0 2 0] else #[]) ++
      (if isSet then #[.unary .set_ 0 0] else #[]) ++
      (if nonempty then #[.binary .memberOf 0 0 0] else #[]) ++
      (if domain then #[.unary .qualityDomain 0 0] else #[]) ++
      (if dimension then #[.unary .qualityDimension 0 0] else #[]) }

private def qualityStructureModel (first last isSet nonempty domain dimension : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (qualityStructureAst first last isSet nonempty domain dimension)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases isSet <;> cases nonempty <;>
      cases domain <;> cases dimension <;> decide)

example : Checker.qualityStructureCosted (qualityStructureModel false false false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 36⟩ := by native_decide

example : Checker.qualityStructureCosted (qualityStructureModel true false false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 74⟩ := by native_decide

example : Checker.qualityStructureCosted (qualityStructureModel false true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 98⟩ := by native_decide

example : Checker.qualityStructureCosted (qualityStructureModel true true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 146⟩ := by native_decide

example : Checker.qualityStructureCandidateCosted (qualityStructureModel false false false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 9⟩ := by native_decide

example : Checker.qualityStructureCandidateCosted (qualityStructureModel true false false false false false)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 20⟩ := by native_decide

example : Checker.nonEmptySetCosted (qualityStructureModel false false false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 39⟩ := by native_decide

example : Checker.nonEmptySetCosted (qualityStructureModel false false false true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 13⟩ := by native_decide

example : Checker.checkAx86Costed (qualityStructureModel false false false false false false) =
    ⟨true, 126⟩ := by native_decide

example : Checker.checkAx86Costed (qualityStructureModel true false false false false false) =
    ⟨false, 89⟩ := by native_decide

example : Checker.checkAx86Costed (qualityStructureModel true false true false false false) =
    ⟨false, 128⟩ := by native_decide

example : Checker.checkAx86Costed (qualityStructureModel true false true true false false) =
    ⟨true, 208⟩ := by native_decide

example : Checker.checkAx86Costed (qualityStructureModel false true true true false false) =
    ⟨true, 232⟩ := by native_decide

example : Checker.checkAx86Costed (qualityStructureModel true true false false false false) =
    ⟨true, 280⟩ := by native_decide

example : Checker.checkAx88Costed (qualityStructureModel false false false false false false) =
    ⟨true, 177⟩ := by native_decide

example : Checker.checkAx88Costed (qualityStructureModel true false false false true false) =
    ⟨true, 228⟩ := by native_decide

example : Checker.checkAx88Costed (qualityStructureModel true false false false false true) =
    ⟨true, 236⟩ := by native_decide

example : Checker.checkAx88Costed (qualityStructureModel true false false false false false) =
    ⟨false, 96⟩ := by native_decide

example : Checker.checkAx88Costed (qualityStructureModel true true false false true false) =
    ⟨false, 161⟩ := by native_decide

example : Checker.checkAx87Costed (qualityStructureModel false false false false false false) =
    ⟨true, 402⟩ := by native_decide

example : ∀ first last : Bool,
    (Checker.qualityStructureCosted
      (qualityStructureModel first last false false false false)
      (0 : Fin 3) (0 : Fin 1)).value = (first != last) := by native_decide

-- Structures 0 and 2 share quality type 0. Membership and type association
-- therefore exercise the same nesting depth through different binary fields.
private def qualityMembershipAst (first last members intrinsic quale : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := #[.unary .qualityType 0 0] ++
      (if first then #[.binary .associatedWith 0 0 0] else #[]) ++
      (if last then #[.binary .associatedWith 2 0 0] else #[]) ++
      (if members then #[.binary .memberOf 0 0 0, .binary .memberOf 0 2 0] else #[]) ++
      (if intrinsic then #[.unary .intrinsicMomentType 0 0] else #[]) ++
      (if quale then #[.unary .quale 0 0] else #[]) }

private def qualityMembershipModel (first last members intrinsic quale : Bool) : FiniteModel4 :=
  compileVerifiedModel (qualityMembershipAst first last members intrinsic quale)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases members <;> cases intrinsic <;> cases quale <;> decide)

example : Checker.existsUniqueQualityStructureMemberCosted (qualityMembershipModel false false true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 153⟩ := by native_decide

example : Checker.existsUniqueQualityStructureForTypeCosted (qualityMembershipModel false false true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 153⟩ := by native_decide

example : Checker.existsUniqueQualityStructureMemberCosted (qualityMembershipModel true false true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 284⟩ := by native_decide

example : Checker.existsUniqueQualityStructureForTypeCosted (qualityMembershipModel true false true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 284⟩ := by native_decide

example : Checker.existsUniqueQualityStructureMemberCosted (qualityMembershipModel false true true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 386⟩ := by native_decide

example : Checker.existsUniqueQualityStructureForTypeCosted (qualityMembershipModel false true true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 386⟩ := by native_decide

example : Checker.existsUniqueQualityStructureMemberCosted (qualityMembershipModel true true true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 554⟩ := by native_decide

example : Checker.existsUniqueQualityStructureForTypeCosted (qualityMembershipModel true true true true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 554⟩ := by native_decide

example : Checker.existsUniqueQualityStructureMemberCosted (qualityMembershipModel true false false true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 191⟩ := by native_decide

example : Checker.checkAx87Costed (qualityMembershipModel true false true true true) =
    ⟨true, 707⟩ := by native_decide

example : Checker.checkAx87Costed (qualityMembershipModel true false true true false) =
    ⟨false, 298⟩ := by native_decide

example : Checker.checkAx87Costed (qualityMembershipModel true false false true true) =
    ⟨false, 204⟩ := by native_decide

example : Checker.checkAx91Costed (qualityMembershipModel false false true true true) =
    ⟨false, 175⟩ := by native_decide

example : Checker.checkAx91Costed (qualityMembershipModel true false true true true) =
    ⟨true, 352⟩ := by native_decide

example : Checker.checkAx91Costed (qualityMembershipModel false true true true true) =
    ⟨true, 454⟩ := by native_decide

example : Checker.checkAx91Costed (qualityMembershipModel true true true true true) =
    ⟨false, 576⟩ := by native_decide

example : Checker.checkAx91Costed (qualityMembershipModel true false true false true) =
    ⟨false, 22⟩ := by native_decide

example : ∀ first last members : Bool,
    (Checker.existsUniqueQualityStructureMemberCosted
      (qualityMembershipModel first last members false false)
      (0 : Fin 3) (0 : Fin 1)).value = (members && (first != last)) := by native_decide

private def subsetAst (s0 t0 s2 t2 : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if s0 then #[.binary .memberOf 0 0 0] else #[]) ++
      (if t0 then #[.binary .memberOf 0 1 0] else #[]) ++
      (if s2 then #[.binary .memberOf 2 0 0] else #[]) ++
      (if t2 then #[.binary .memberOf 2 1 0] else #[]) }

private def subsetModel (s0 t0 s2 t2 : Bool) : FiniteModel4 :=
  compileVerifiedModel (subsetAst s0 t0 s2 t2)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases s0 <;> cases t0 <;> cases s2 <;> cases t2 <;> decide)

example : Checker.properSubsetCosted (subsetModel false false false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 88⟩ := by native_decide

example : Checker.properSubsetCosted (subsetModel true false false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 27⟩ := by native_decide

example : Checker.properSubsetCosted (subsetModel false true false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 72⟩ := by native_decide

example : Checker.properSubsetCosted (subsetModel false false false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 100⟩ := by native_decide

example : Checker.properSubsetCosted (subsetModel true true false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 111⟩ := by native_decide

example : Checker.properSubsetCosted (subsetModel true true false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 123⟩ := by native_decide

example : Checker.properSubsetCosted (subsetModel false false true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 57⟩ := by native_decide

example : Checker.checkAx90Costed (subsetModel false false false false) =
    ⟨true, 1536⟩ := by native_decide

example : ∀ s0 t0 s2 t2 : Bool,
    (Checker.properSubsetCosted (subsetModel s0 t0 s2 t2)
      (0 : Fin 3) (1 : Fin 3) (0 : Fin 1)).value =
      (((!s0 || t0) && (!s2 || t2)) && ((t0 && !s0) || (t2 && !s2))) := by native_decide

private def qualityInclusionAst (first second subtype reverse hasDifference : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if first then #[.binary .associatedWith 0 0 0] else #[]) ++
      (if second then #[.binary .associatedWith 1 1 0] else #[]) ++
      (if subtype then #[.binary .sub 1 0 0] else #[]) ++
      (if reverse then #[.binary .sub 0 1 0] else #[]) ++
      (if hasDifference then #[.binary .memberOf 0 0 0] else #[]) }

private def qualityInclusionModel (first second subtype reverse hasDifference : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (qualityInclusionAst first second subtype reverse hasDifference)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases second <;> cases subtype <;> cases reverse <;>
      cases hasDifference <;> decide)

example : Checker.ax90AntecedentCosted (qualityInclusionModel false false false false false)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 12⟩ := by native_decide

example : Checker.ax90AntecedentCosted (qualityInclusionModel true false false false false)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 24⟩ := by native_decide

example : Checker.ax90AntecedentCosted (qualityInclusionModel true true false false false)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 36⟩ := by native_decide

example : Checker.ax90AntecedentCosted (qualityInclusionModel true true true false false)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨true, 48⟩ := by native_decide

example : Checker.ax90AntecedentCosted (qualityInclusionModel true true true true false)
    (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 48⟩ := by native_decide

example : ∀ hasDifference : Bool,
    (Checker.checkAx90Costed
      (qualityInclusionModel true true true false hasDifference)).value =
      hasDifference := by native_decide

-- Both subtype directions make the strict-subtype premise false, so no
-- containment or difference query is needed.
example : (Checker.checkAx90Costed
    (qualityInclusionModel true true true true false)).value = true := by native_decide

/-! ## Quality values and their type/space witnesses

On three things, a value query costs eleven. The uniqueness scan costs
fifteen per absent competitor and sixteen per present competitor, including
the loop. An absent outer candidate costs fourteen. Thus no value costs 42,
a unique first value 60, a unique last value 88, and two values 105.
-/

private def qualityValueAst (first last quality quale : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if first then #[.binary .hasValue 0 0 0] else #[]) ++
      (if last then #[.binary .hasValue 0 2 0] else #[]) ++
      (if quality then #[.unary .qualityKind 0 0, .binary .inst 0 0 0] else #[]) ++
      (if quale then #[.unary .quale 0 0, .unary .quale 2 0] else #[]) }

private def qualityValueModel (first last quality quale : Bool) : FiniteModel4 :=
  compileVerifiedModel (qualityValueAst first last quality quale)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases quality <;> cases quale <;> decide)

example : ∀ first last quality quale : Bool,
    Checker.existsUniqueHasValueCosted (qualityValueModel first last quality quale)
      (0 : Fin 3) (0 : Fin 1) =
      ⟨first != last, if first then (if last then 105 else 60)
        else if last then 88 else 42⟩ := by native_decide

example : ∀ first last quality quale : Bool,
    (Checker.checkAx92Costed (qualityValueModel first last quality quale)).value =
      (!(first || last) || (quality && quale)) := by native_decide

example : ∀ first last quality quale : Bool,
    (Checker.checkAx93Costed (qualityValueModel first last quality quale)).value =
      (!quality || (first != last)) := by native_decide

example : Checker.hasValueUniqueForCosted (qualityValueModel false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 45⟩ := by native_decide

example : Checker.hasValueUniqueForCosted (qualityValueModel true false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 46⟩ := by native_decide

example : Checker.hasValueUniqueForCosted (qualityValueModel true false false false)
    (0 : Fin 3) (2 : Fin 3) (0 : Fin 1) =
    ⟨false, 16⟩ := by native_decide

example : Checker.hasValueUniqueForCosted (qualityValueModel false true false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 46⟩ := by native_decide

example : Checker.hasValueUniqueForCosted (qualityValueModel true true false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 47⟩ := by native_decide

example : Checker.checkAx92Costed (qualityValueModel false false false false) =
    ⟨true, 159⟩ := by native_decide

example : Checker.checkAx92Costed (qualityValueModel true false false false) =
    ⟨false, 56⟩ := by native_decide

example : Checker.checkAx92Costed (qualityValueModel true false true false) =
    ⟨false, 102⟩ := by native_decide

example : Checker.checkAx92Costed (qualityValueModel true false true true) =
    ⟨true, 242⟩ := by native_decide

example : Checker.checkAx92Costed (qualityValueModel false true true true) =
    ⟨true, 242⟩ := by native_decide

example : Checker.checkAx92Costed (qualityValueModel true true true true) =
    ⟨true, 325⟩ := by native_decide

example : Checker.checkAx93Costed (qualityValueModel false false false false) =
    ⟨true, 126⟩ := by native_decide

example : Checker.checkAx93Costed (qualityValueModel false false true false) =
    ⟨false, 122⟩ := by native_decide

example : Checker.checkAx93Costed (qualityValueModel true false true false) =
    ⟨true, 246⟩ := by native_decide

example : Checker.checkAx93Costed (qualityValueModel false true true false) =
    ⟨true, 274⟩ := by native_decide

example : Checker.checkAx93Costed (qualityValueModel true true true false) =
    ⟨false, 185⟩ := by native_decide

-- Duplicate source facts do not create a second value. The compiled field
-- still stores one Boolean cell and the counted search follows the same path.
private def duplicateQualityValueAst : ModelAST :=
  let ast := qualityValueAst true false true true
  { ast with facts := ast.facts ++ ast.facts }

private def duplicateQualityValueModel : FiniteModel4 :=
  compileVerifiedModel duplicateQualityValueAst
    (by decide) (by decide) (by decide)

example : Checker.existsUniqueHasValueCosted duplicateQualityValueModel
    (0 : Fin 3) (0 : Fin 1) = ⟨true, 60⟩ := by native_decide

/- A failed instantiation still costs thirteen in axiom 94: eleven for the
read and two conjunction branches. A failed association costs 24; a visited
membership read costs 35. The two nested loops add two per visited index. -/
private def qualityValueWitnessAst (first last associated member value : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if first then #[.binary .inst 0 0 0] else #[]) ++
      (if last then #[.binary .inst 0 2 0] else #[]) ++
      (if associated then
        #[.binary .associatedWith 0 0 0, .binary .associatedWith 2 2 0] else #[]) ++
      (if member then #[.binary .memberOf 0 0 0, .binary .memberOf 0 2 0] else #[]) ++
      (if value then #[.binary .hasValue 0 0 0] else #[]) }

private def qualityValueWitnessModel (first last associated member value : Bool) : FiniteModel4 :=
  compileVerifiedModel (qualityValueWitnessAst first last associated member value)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases first <;> cases last <;> cases associated <;> cases member <;>
      cases value <;> decide)

example : ∀ first last associated member value : Bool,
    (Checker.ax94WitnessCosted
      (qualityValueWitnessModel first last associated member value)
      (0 : Fin 3) (0 : Fin 3) (0 : Fin 1)).value =
      ((first || last) && associated && member) := by native_decide

example : ∀ first last associated member value : Bool,
    (Checker.checkAx94Costed
      (qualityValueWitnessModel first last associated member value)).value =
      (!value || ((first || last) && associated && member)) := by native_decide

example : Checker.ax94WitnessCandidateCosted (qualityValueWitnessModel false false true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 13⟩ := by native_decide

example : Checker.ax94WitnessCandidateCosted (qualityValueWitnessModel true false false true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 24⟩ := by native_decide

example : Checker.ax94WitnessCandidateCosted (qualityValueWitnessModel true false true false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 35⟩ := by native_decide

example : Checker.ax94WitnessCandidateCosted (qualityValueWitnessModel true false true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 35⟩ := by native_decide

example : Checker.ax94WitnessCosted (qualityValueWitnessModel false false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 141⟩ := by native_decide

example : Checker.ax94WitnessCosted (qualityValueWitnessModel true false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 174⟩ := by native_decide

example : Checker.ax94WitnessCosted (qualityValueWitnessModel true false true false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 185⟩ := by native_decide

example : Checker.ax94WitnessCosted (qualityValueWitnessModel true false true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 39⟩ := by native_decide

example : Checker.ax94WitnessCosted (qualityValueWitnessModel false true true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 185⟩ := by native_decide

example : Checker.ax94WitnessCosted (qualityValueWitnessModel true true true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 39⟩ := by native_decide

example : Checker.checkAx94Costed (qualityValueWitnessModel false false false false false) =
    ⟨true, 159⟩ := by native_decide

example : Checker.checkAx94Costed (qualityValueWitnessModel false false false false true) =
    ⟨false, 160⟩ := by native_decide

example : Checker.checkAx94Costed (qualityValueWitnessModel true false false false true) =
    ⟨false, 193⟩ := by native_decide

example : Checker.checkAx94Costed (qualityValueWitnessModel true false true false true) =
    ⟨false, 204⟩ := by native_decide

example : Checker.checkAx94Costed (qualityValueWitnessModel true false true true true) =
    ⟨true, 198⟩ := by native_decide

example : Checker.checkAx94Costed (qualityValueWitnessModel false true true true true) =
    ⟨true, 344⟩ := by native_decide

/-! ## Simple and complex qualities

The parent quality is thing zero. Inhering children are things one and two.
Each visited inherence test costs fourteen with negation and loop overhead.
Thus no child and a last child both cost 42; the first child costs 28.
A quality search costs 74. The complex predicate repeats that source search.
-/

private def qualityPartsAst (quality first last childQualities childEdges : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if quality then #[.unary .qualityKind 0 0, .binary .inst 0 0 0] else #[]) ++
      (if first then #[.binary .inheresIn 1 0 0] else #[]) ++
      (if last then #[.binary .inheresIn 2 0 0] else #[]) ++
      (if childQualities then #[.binary .inst 1 0 0, .binary .inst 2 0 0] else #[]) ++
      (if childEdges then #[.binary .inheresIn 0 1 0, .binary .inheresIn 0 2 0] else #[]) }

private def qualityPartsModel (quality first last childQualities childEdges : Bool) : FiniteModel4 :=
  compileVerifiedModel (qualityPartsAst quality first last childQualities childEdges)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases quality <;> cases first <;> cases last <;> cases childQualities <;>
      cases childEdges <;> decide)

example : ∀ quality first last childQualities childEdges : Bool,
    (Checker.simpleQualityCosted (qualityPartsModel quality first last childQualities childEdges)
      (0 : Fin 3) (0 : Fin 1)).value = (quality && !(first || last)) := by native_decide

example : ∀ quality first last childQualities childEdges : Bool,
    (Checker.complexQualityCosted (qualityPartsModel quality first last childQualities childEdges)
      (0 : Fin 3) (0 : Fin 1)).value = (quality && (first || last)) := by native_decide

example : ∀ quality first last childQualities childEdges : Bool,
    (Checker.checkAx97Costed
      (qualityPartsModel quality first last childQualities childEdges)).value =
      !(quality && first && last && childQualities) := by native_decide

-- With reverse edges, each child contains the parent. Such a child is complex,
-- so axiom 98 rejects it when the parent is also complex.
example : ∀ quality first last childQualities childEdges : Bool,
    (Checker.checkAx98Costed
      (qualityPartsModel quality first last childQualities childEdges)).value =
      (!quality || !(first || last) || (childQualities && !childEdges)) := by native_decide

example : Checker.noInheringThingsCosted (qualityPartsModel true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 42⟩ := by native_decide

example : Checker.noInheringThingsCosted (qualityPartsModel true true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 28⟩ := by native_decide

example : Checker.noInheringThingsCosted (qualityPartsModel true false true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 42⟩ := by native_decide

example : Checker.noInheringThingsCosted (qualityPartsModel true true true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 28⟩ := by native_decide

example : Checker.simpleQualityCosted (qualityPartsModel false true true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 37⟩ := by native_decide

example : Checker.simpleQualityCosted (qualityPartsModel true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 117⟩ := by native_decide

example : Checker.simpleQualityCosted (qualityPartsModel true true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 103⟩ := by native_decide

example : Checker.simpleQualityCosted (qualityPartsModel true false true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 117⟩ := by native_decide

example : Checker.complexQualityCosted (qualityPartsModel false true true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 37⟩ := by native_decide

example : Checker.complexQualityCosted (qualityPartsModel true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 193⟩ := by native_decide

example : Checker.complexQualityCosted (qualityPartsModel true true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 179⟩ := by native_decide

example : Checker.complexQualityCosted (qualityPartsModel true false true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 193⟩ := by native_decide

example : Checker.ax98PartsCosted (qualityPartsModel true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 45⟩ := by native_decide

example : Checker.ax98PartsCosted (qualityPartsModel true true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 78⟩ := by native_decide

example : Checker.ax98PartsCosted (qualityPartsModel true false true false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 93⟩ := by native_decide

example : Checker.ax98PartsCosted (qualityPartsModel true true false true false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 162⟩ := by native_decide

example : Checker.ax98PartsCosted (qualityPartsModel true false true true false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 162⟩ := by native_decide

example : Checker.ax98PartsCosted (qualityPartsModel true true true true false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 279⟩ := by native_decide

example : Checker.ax98PartsCosted (qualityPartsModel true true false true true)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 119⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel false false false false false) =
    ⟨true, 129⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel true false false false false) =
    ⟨true, 307⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel true true false false false) =
    ⟨false, 263⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel true false true false false) =
    ⟨false, 292⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel true true false true false) =
    ⟨true, 745⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel true false true true false) =
    ⟨true, 759⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel true true true true false) =
    ⟨true, 862⟩ := by native_decide

example : Checker.checkAx98Costed (qualityPartsModel true true false true true) =
    ⟨false, 304⟩ := by native_decide

example : Checker.ax97AntecedentCosted (qualityPartsModel false true true true false)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 42⟩ := by native_decide

example : Checker.ax97AntecedentCosted (qualityPartsModel true false false true false)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 198⟩ := by native_decide

example : Checker.ax97AntecedentCosted (qualityPartsModel true true false false false)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 195⟩ := by native_decide

example : Checker.ax97AntecedentCosted (qualityPartsModel true true false true false)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 228⟩ := by native_decide

example : Checker.ax97AntecedentCosted (qualityPartsModel true false true true false)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 231⟩ := by native_decide

example : Checker.ax97AntecedentCosted (qualityPartsModel true true true true false)
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 229⟩ := by native_decide

example : Checker.checkAx97Costed (qualityPartsModel false false false false false) =
    ⟨true, 11904⟩ := by native_decide

/- Type zero has either no instances or the parent as its only instance.
The type guard costs nine. A vacuous three-thing instance scan adds 45.
The association selects the only nonvacuous whole-check assignment. -/
private def qualityTypeShapeAst (hasInstance child isType linked dimension domain : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := #[.unary .qualityKind 0 0] ++
      (if hasInstance then #[.binary .inst 0 0 0] else #[]) ++
      (if child then #[.binary .inheresIn 2 0 0] else #[]) ++
      (if isType then #[.unary .qualityType 0 0] else #[]) ++
      (if linked then #[.binary .associatedWith 0 0 0] else #[]) ++
      (if dimension then #[.unary .qualityDimension 0 0] else #[]) ++
      (if domain then #[.unary .qualityDomain 0 0] else #[]) }

private def qualityTypeShapeModel (hasInstance child isType linked dimension domain : Bool) : FiniteModel4 :=
  compileVerifiedModel (qualityTypeShapeAst hasInstance child isType linked dimension domain)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases hasInstance <;> cases child <;> cases isType <;> cases linked <;>
      cases dimension <;> cases domain <;> decide)

example : ∀ hasInstance child isType linked dimension domain : Bool,
    (Checker.checkAx95Costed
      (qualityTypeShapeModel hasInstance child isType linked dimension domain)).value =
      (!linked || (dimension == (isType && (!hasInstance || !child)))) := by native_decide

example : ∀ hasInstance child isType linked dimension domain : Bool,
    (Checker.checkAx96Costed
      (qualityTypeShapeModel hasInstance child isType linked dimension domain)).value =
      (!linked || (domain == (isType && (!hasInstance || child)))) := by native_decide

example : Checker.simpleQualityTypeCosted (qualityTypeShapeModel true true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 9⟩ := by native_decide

example : Checker.simpleQualityTypeCosted (qualityTypeShapeModel false false true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 54⟩ := by native_decide

example : Checker.simpleQualityTypeCosted (qualityTypeShapeModel true false true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 171⟩ := by native_decide

example : Checker.simpleQualityTypeCosted (qualityTypeShapeModel true true true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 141⟩ := by native_decide

example : Checker.complexQualityTypeCosted (qualityTypeShapeModel true true false false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 9⟩ := by native_decide

example : Checker.complexQualityTypeCosted (qualityTypeShapeModel false false true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 54⟩ := by native_decide

example : Checker.complexQualityTypeCosted (qualityTypeShapeModel true false true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 217⟩ := by native_decide

example : Checker.complexQualityTypeCosted (qualityTypeShapeModel true true true false false false)
    (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 247⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel true false true false true false) =
    ⟨true, 159⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel true false false true false false) =
    ⟨true, 178⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel true false false true true false) =
    ⟨false, 37⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel false false true true true false) =
    ⟨true, 222⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel false false true true false false) =
    ⟨false, 83⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel true false true true true false) =
    ⟨true, 339⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel true true true true true false) =
    ⟨false, 169⟩ := by native_decide

example : Checker.checkAx95Costed (qualityTypeShapeModel true true true true false false) =
    ⟨true, 310⟩ := by native_decide

example : Checker.checkAx96Costed (qualityTypeShapeModel true false true false false true) =
    ⟨true, 159⟩ := by native_decide

example : Checker.checkAx96Costed (qualityTypeShapeModel true false false true false false) =
    ⟨true, 178⟩ := by native_decide

example : Checker.checkAx96Costed (qualityTypeShapeModel true false false true false true) =
    ⟨false, 37⟩ := by native_decide

example : Checker.checkAx96Costed (qualityTypeShapeModel false false true true false true) =
    ⟨true, 222⟩ := by native_decide

example : Checker.checkAx96Costed (qualityTypeShapeModel true true true true false true) =
    ⟨true, 415⟩ := by native_decide

example : Checker.checkAx96Costed (qualityTypeShapeModel true false true true false true) =
    ⟨false, 245⟩ := by native_decide

example : Checker.checkAx96Costed (qualityTypeShapeModel true false true true false false) =
    ⟨true, 386⟩ := by native_decide

/-! ## Product-family projection and search

Three projection paths return tuple zero but cost two (slot outside the table),
nine (empty initialized cell), or eleven (stored self-projection). The family
has one dimension. Its projection row adds fourteen per slot to the projection
cost: a dimension read, membership read, and loop overhead.
-/

private def countedFamily : ProductFamilyWitness 3 1 :=
  { domain := 0, qualityType := 0, world := 0,
    dimensionThings := #[1], typeThings := #[2], sameSize := rfl }

private def familyCostAst (mode : Fin 4)
    (tupleMember componentMember associated characterized extraTarget : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    productFamilies := #[⟨0, 0, #[1], #[2]⟩],
    facts := #[.unary .qualityDomain 0 0, .binary .associatedWith 0 0 0] ++
      (match mode.val with
        | 0 => #[]
        | 1 => #[.tupleProjection 2 0 2 0]
        | 2 => #[.tupleProjection 0 0 0 0]
        | _ => #[.tupleProjection 0 0 1 0]) ++
      (if tupleMember then #[.binary .memberOf 0 0 0] else #[]) ++
      (if componentMember then #[.binary .memberOf 0 1 0, .binary .memberOf 1 1 0] else #[]) ++
      (if associated then #[.binary .associatedWith 1 2 0] else #[]) ++
      (if characterized then #[.binary .characterization 0 2 0] else #[]) ++
      (if extraTarget then #[.binary .characterization 0 1 0] else #[]) }

private def familyCostModel (mode : Fin 4)
    (tupleMember componentMember associated characterized extraTarget : Bool) : FiniteModel4 :=
  compileVerifiedModel (familyCostAst mode tupleMember componentMember associated characterized extraTarget)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by
      rcases mode with ⟨mode, bound⟩
      have hm : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 3 := by omega
      rcases hm with rfl | rfl | rfl | rfl <;>
      cases tupleMember <;> cases componentMember <;>
      cases associated <;> cases characterized <;> cases extraTarget <;>
      dsimp only [familyCostAst] <;> decide)

example (M : FiniteModel4) {n : Nat}
    (p : Fin M.thingCount) (i : Fin n) (w : Fin M.worldCount) :
    (M.tupleProjectionCosted p i w).value = M.tupleProjection p i w := rfl

example (M : FiniteModel4) {n : Nat}
    (p : Fin M.thingCount) (i : Fin n) (w : Fin M.worldCount) :
    (M.tupleProjectionCosted p i w).cost ≤ 11 := M.tupleProjectionCost_le p i w

example : ∀ mode : Fin 4, ∀ tupleMember componentMember associated characterized extraTarget : Bool,
    (Checker.productFamilyWitnessCosted
      (familyCostModel mode tupleMember componentMember associated characterized extraTarget)
      countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1)).value =
      ((!tupleMember || componentMember) && associated && characterized && !extraTarget) := by
  native_decide

example : ∀ mode : Fin 4, ∀ tupleMember componentMember associated characterized extraTarget : Bool,
    (Checker.checkAx99Costed
      (familyCostModel mode tupleMember componentMember associated characterized extraTarget)).value =
      ((!tupleMember || componentMember) && associated && characterized && !extraTarget) := by
  native_decide

example : (familyCostModel 0 false false false false false).tupleProjectionCosted
    (0 : Fin 3) (0 : Fin 1) (0 : Fin 1) =
    ⟨(0 : Fin 3), 2⟩ := by native_decide

example : (familyCostModel 1 false false false false false).tupleProjectionCosted
    (0 : Fin 3) (0 : Fin 1) (0 : Fin 1) =
    ⟨(0 : Fin 3), 9⟩ := by native_decide

example : (familyCostModel 2 false false false false false).tupleProjectionCosted
    (0 : Fin 3) (0 : Fin 1) (0 : Fin 1) =
    ⟨(0 : Fin 3), 11⟩ := by native_decide

example : (familyCostModel 3 false false false false false).tupleProjectionCosted
    (0 : Fin 3) (0 : Fin 1) (0 : Fin 1) =
    ⟨(1 : Fin 3), 11⟩ := by native_decide

example : (familyCostModel 3 false false false false false).tupleProjectionCosted
    (0 : Fin 3) (1 : Fin 2) (0 : Fin 1) =
    ⟨(0 : Fin 3), 2⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 0 false false false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 45⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 0 true true false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 61⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 1 true true false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 68⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 2 true true false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 70⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 3 true true false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 70⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 0 true false false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 31⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 1 true false false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 38⟩ := by native_decide

example : Checker.productFamilyProjectionRowsCosted (familyCostModel 3 true false false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 40⟩ := by native_decide

example : Checker.productFamilyAssociationRowsCosted (familyCostModel 0 false false false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 16⟩ := by native_decide

example : Checker.productFamilyAssociationRowsCosted (familyCostModel 0 false false true false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 28⟩ := by native_decide

example : Checker.productFamilyAssociationRowsCosted (familyCostModel 0 false false true true false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 28⟩ := by native_decide

example : Checker.productFamilyCoverageRowsCosted (familyCostModel 0 false false false false false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 45⟩ := by native_decide

example : Checker.productFamilyCoverageRowsCosted (familyCostModel 0 false false false true false)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 49⟩ := by native_decide

example : Checker.productFamilyCoverageRowsCosted (familyCostModel 0 false false false true true)
    countedFamily (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 34⟩ := by native_decide

-- Two-member scans count both projection calls. With one coordinate and
-- one-operation projections, a compared pair costs 23 when coordinates agree
-- and 22 when they differ. The first collision stops the outer scan.
example : Checker.productCoordinatesSeparateCosted 2 1
    (fun _ => Complexity.Costed.tick true 11)
    (fun _ _ => Complexity.Costed.tick (0 : Fin 2) 1) = ⟨false, 61⟩ := by
  native_decide

example : Checker.productCoordinatesSeparateCosted 2 1
    (fun _ => Complexity.Costed.tick true 11)
    (fun p _ => Complexity.Costed.tick p 1) = ⟨true, 120⟩ := by
  native_decide

-- Empty domains skip projection work. Zero coordinates still require
-- injectivity: at most one member can represent the empty tuple.
example : Checker.productCoordinatesSeparateCosted 2 0
    (fun _ => Complexity.Costed.tick false 11)
    (fun p _ => Complexity.Costed.tick p 1) = ⟨true, 30⟩ := by native_decide

example : Checker.productCoordinatesSeparateCosted 2 0
    (fun p => Complexity.Costed.tick (decide (p = 0)) 11)
    (fun p _ => Complexity.Costed.tick p 1) = ⟨true, 63⟩ := by native_decide

example : Checker.productCoordinatesSeparateCosted 2 0
    (fun _ => Complexity.Costed.tick true 11)
    (fun p _ => Complexity.Costed.tick p 1) = ⟨false, 51⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 0 false false false false false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 115⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 0 false false true false false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 127⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 0 false false true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 176⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 0 false false true true true)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 161⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 0 true true true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 247⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 1 true true true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 268⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 2 true true true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 274⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 3 true true true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 274⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 0 true false true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 40⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 1 true false true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 47⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 3 true false true true false)
    countedFamily (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 49⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 3 true true true true false)
    countedFamily (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 7⟩ := by native_decide

example : Checker.productFamilyWitnessCosted (familyCostModel 3 true true true true false)
    countedFamily (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) =
    ⟨false, 8⟩ := by native_decide

example : Checker.productFamilySearchCosted (familyCostModel 0 false false true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 179⟩ := by native_decide

example : Checker.productFamilySearchCosted (familyCostModel 0 true true true true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 250⟩ := by native_decide

example : Checker.productFamilySearchCosted (familyCostModel 0 false false false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 118⟩ := by native_decide

example : Checker.checkAx99Costed (familyCostModel 0 false false true true false) =
    ⟨true, 353⟩ := by native_decide

example : Checker.checkAx99Costed (familyCostModel 0 true true true true false) =
    ⟨true, 424⟩ := by native_decide

example : Checker.checkAx99Costed (familyCostModel 0 false false false false false) =
    ⟨false, 146⟩ := by native_decide

-- These models retain the compiled relation and projection operations while
-- varying only the supplied family array. Each visited family adds one array
-- read and two loop operations. A successful first entry skips the second.
private def familyOrderModel (firstValid secondValid : Bool) : FiniteModel4 :=
  let M := familyCostModel 0 false false true true false
  let wrong : ProductFamilyWitness 3 1 := { countedFamily with domain := (1 : Fin 3) }
  { M with productFamilies :=
      #[(if firstValid then countedFamily else wrong),
        (if secondValid then countedFamily else wrong)] }

example : Checker.productFamilySearchCosted (familyOrderModel true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 179⟩ := by native_decide

example : Checker.productFamilySearchCosted (familyOrderModel true true)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 179⟩ := by native_decide

example : Checker.productFamilySearchCosted (familyOrderModel false true)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨true, 189⟩ := by native_decide

example : Checker.productFamilySearchCosted (familyOrderModel false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) =
    ⟨false, 20⟩ := by native_decide

example : Checker.checkAx99Costed
    { familyCostModel 0 false false true true false with productFamilies := #[] } =
    ⟨false, 28⟩ := by native_decide

example : Checker.checkAx99Costed (familyOrderModel false true) =
    ⟨true, 363⟩ := by native_decide

-- Family arity is independent of the number of model things. Later slots
-- outside the projection table use the two-operation tuple fallback.
private def wideCountedFamily : ProductFamilyWitness 3 1 :=
  { countedFamily with
    dimensionThings := #[1, 1, 1, 1, 1]
    typeThings := #[2, 2, 2, 2, 2]
    sameSize := rfl }

example : Checker.productFamilyWitnessCosted
    (familyCostModel 0 false false true true false) wideCountedFamily
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 288⟩ := by native_decide

example : Checker.productFamilyWitnessCosted
    (familyCostModel 3 true true true true false) wideCountedFamily
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 478⟩ := by native_decide

example : Checker.productFamilyWitnessCosted
    (familyCostModel 0 true false true false false)
    { countedFamily with dimensionThings := #[], typeThings := #[], sameSize := rfl }
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 192⟩ := by native_decide

private def projectionWorldAst : ModelAST :=
  { worldCount := 2, thingCount := 3, facts := #[.tupleProjection 0 0 1 1] }

private def projectionWorldModel : FiniteModel4 :=
  compileVerifiedModel projectionWorldAst (by decide) (by decide) (by decide)

example : projectionWorldModel.tupleProjectionCosted
    (0 : Fin 3) (0 : Fin 1) (0 : Fin 2) = ⟨(0 : Fin 3), 9⟩ := by native_decide

example : projectionWorldModel.tupleProjectionCosted
    (0 : Fin 3) (0 : Fin 1) (1 : Fin 2) = ⟨(1 : Fin 3), 11⟩ := by native_decide

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    {n : Nat} (p : Fin source.things.size) (i : Fin n) (w : Fin source.worlds.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    M.tupleProjectionCosted p i w = compiled.tables.tupleProjectionTypedTableCosted p i.val w :=
  compiledProjection_eq_countedTable _ _ _ _ _ _ _ _ _ p i w

/-! ## Distance candidates and life-of equivalence

The distance fixture varies the first and last result independently of the
common membership witness. Exact tests account for every rejected candidate.
-/

private def distanceShapeAst (qx qy firstResult lastResult firstCommon lastCommon leftOnly : Bool) :
    ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if qx then #[.unary .quale 0 0] else #[]) ++
      (if qy then #[.unary .quale 1 0] else #[]) ++
      (if firstResult then #[.ternary .distance 0 1 0 0] else #[]) ++
      (if lastResult then #[.ternary .distance 0 1 2 0] else #[]) ++
      (if firstCommon then #[.binary .memberOf 0 0 0, .binary .memberOf 1 0 0] else #[]) ++
      (if lastCommon then #[.binary .memberOf 0 2 0, .binary .memberOf 1 2 0] else #[]) ++
      (if leftOnly then #[.binary .memberOf 0 1 0] else #[]) }

private def distanceShapeModel (qx qy firstResult lastResult firstCommon lastCommon leftOnly : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (distanceShapeAst qx qy firstResult lastResult firstCommon lastCommon leftOnly)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases qx <;> cases qy <;> cases firstResult <;> cases lastResult <;>
        cases firstCommon <;> cases lastCommon <;> cases leftOnly <;> decide)

example : ∀ qx qy firstResult lastResult firstCommon lastCommon leftOnly : Bool,
    (Checker.checkAx100Costed
      (distanceShapeModel qx qy firstResult lastResult firstCommon lastCommon leftOnly)).value =
      (!(firstResult || lastResult) || (qx && qy && (firstCommon || lastCommon))) := by
  native_decide

example : Checker.commonQualityStructureCosted (distanceShapeModel false false false false false false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 42⟩ := by native_decide

example : Checker.commonQualityStructureCosted (distanceShapeModel false false false false true false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 25⟩ := by native_decide

example : Checker.commonQualityStructureCosted (distanceShapeModel false false false false false true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 53⟩ := by native_decide

example : Checker.commonQualityStructureCosted (distanceShapeModel false false false false false false true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 53⟩ := by native_decide

example : Checker.commonQualityStructureCosted (distanceShapeModel false false false false false true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 64⟩ := by native_decide

example : Checker.commonQualityStructureCosted (distanceShapeModel false false false false true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 25⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel false false false false false false false) = ⟨true, 564⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel false false true false false false false) = ⟨false, 96⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel true false true false false false false) = ⟨false, 104⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel true true true false false false false) = ⟨false, 146⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel true true true false true false false) = ⟨true, 607⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel true true true false false true false) = ⟨true, 635⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel true true true true true false false) = ⟨true, 650⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel true true true true false true false) = ⟨true, 706⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel false false false true false false false) = ⟨false, 136⟩ := by native_decide

example : Checker.checkAx100Costed (distanceShapeModel true true false true false false false) = ⟨false, 186⟩ := by native_decide

example : Checker.existsUniqueDistanceCosted
    (distanceShapeModel false false true false false false false)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 51⟩ := by native_decide

private def distanceValueAst (classified first last : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if classified then #[.unary .quale 0 0] else #[]) ++
      (if first then #[.ternary .distance 0 0 0 0] else #[]) ++
      (if last then #[.ternary .distance 0 0 2 0] else #[]) }

private def distanceValueModel (classified first last : Bool) : FiniteModel4 :=
  compileVerifiedModel (distanceValueAst classified first last)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases classified <;> cases first <;> cases last <;> decide)

example : ∀ classified first last : Bool,
    (Checker.checkAx101Costed (distanceValueModel classified first last)).value =
      (!classified || (first != last)) := by native_decide

example : Checker.distanceUniqueForCosted (distanceValueModel false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 54⟩ := by native_decide

example : Checker.distanceUniqueForCosted (distanceValueModel false true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 55⟩ := by native_decide

example : Checker.distanceUniqueForCosted (distanceValueModel false true false)
    (0 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 1) = ⟨false, 19⟩ := by native_decide

example : Checker.distanceUniqueForCosted (distanceValueModel false false true)
    (0 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 1) = ⟨true, 55⟩ := by native_decide

example : Checker.distanceUniqueForCosted (distanceValueModel false false true)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 55⟩ := by native_decide

example : Checker.distanceUniqueForCosted (distanceValueModel false true true)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 56⟩ := by native_decide

example : Checker.existsUniqueDistanceCosted (distanceValueModel false false false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 51⟩ := by native_decide

example : Checker.existsUniqueDistanceCosted (distanceValueModel false true false)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 72⟩ := by native_decide

example : Checker.existsUniqueDistanceCosted (distanceValueModel false false true)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨true, 106⟩ := by native_decide

example : Checker.existsUniqueDistanceCosted (distanceValueModel false true true)
    (0 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 126⟩ := by native_decide

example : Checker.existsUniqueDistanceCosted (distanceValueModel false true true)
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 1) = ⟨false, 51⟩ := by native_decide

example : Checker.checkAx101Costed (distanceValueModel false false false) = ⟨true, 141⟩ := by native_decide

example : Checker.checkAx101Costed (distanceValueModel false true true) = ⟨true, 141⟩ := by native_decide

example : Checker.checkAx101Costed (distanceValueModel true false false) = ⟨false, 76⟩ := by native_decide

example : Checker.checkAx101Costed (distanceValueModel true true false) = ⟨true, 237⟩ := by native_decide

example : Checker.checkAx101Costed (distanceValueModel true false true) = ⟨true, 271⟩ := by native_decide

example : Checker.checkAx101Costed (distanceValueModel true true true) = ⟨false, 151⟩ := by native_decide

-- Thing zero is the candidate life, thing one the endurant, and thing two
-- a possible overlapping event. The overlap table is directed in this fixture.
private def lifeShapeAst (event owner life selfManifest overlap otherEvent otherManifest : Bool) :
    ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := (if event then #[.unary .perdurant 0 0] else #[]) ++
      (if owner then #[.unary .endurant 1 0] else #[]) ++
      (if life then #[.binary .lifeOf 0 1 0] else #[]) ++
      (if selfManifest then #[.binary .manifests 0 1 0] else #[]) ++
      (if overlap then #[.binary .overlap 2 0 0] else #[]) ++
      (if otherEvent then #[.unary .perdurant 2 0] else #[]) ++
      (if otherManifest then #[.binary .manifests 2 1 0] else #[]) }

private def lifeShapeModel (event owner life selfManifest overlap otherEvent otherManifest : Bool) :
    FiniteModel4 :=
  compileVerifiedModel (lifeShapeAst event owner life selfManifest overlap otherEvent otherManifest)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases event <;> cases owner <;> cases life <;> cases selfManifest <;>
        cases overlap <;> cases otherEvent <;> cases otherManifest <;> decide)

example : ∀ event owner life selfManifest overlap : Bool,
    (Checker.checkAx103Costed
      (lifeShapeModel event owner life selfManifest overlap false false)).value =
      (life == (event && owner && selfManifest && !overlap)) := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel false true false false false false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 14⟩ := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel true true false false false false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 25⟩ := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel true true false true false false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 77⟩ := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel true true false true true false false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 76⟩ := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel true true false true false true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 88⟩ := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel true true false true false true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 88⟩ := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel true true false true true true true)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨true, 87⟩ := by native_decide

example : Checker.ax103OverlapRowsCosted (lifeShapeModel true true false true true true false)
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 1) = ⟨false, 87⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel false false false false false false false) = ⟨true, 249⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true false false false false false false) = ⟨true, 273⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true true false false false false false) = ⟨true, 298⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true true false true false false false) = ⟨false, 149⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true true true true false false false) = ⟨true, 349⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true true true false false false false) = ⟨false, 96⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel false true true true false false false) = ⟨false, 55⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true false true true false false false) = ⟨false, 71⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true true false true true false false) = ⟨true, 349⟩ := by native_decide

example : Checker.checkAx103Costed (lifeShapeModel true true true true true false false) = ⟨false, 147⟩ := by native_decide

-- Definition checks are justified semantically for every finite model.
example (M : FiniteModel4) :
    Checker.checkAx105Costed M = ⟨true, 0⟩ ∧
    Checker.checkAx106Costed M = ⟨true, 0⟩ ∧
    Checker.checkAx107Costed M = ⟨true, 0⟩ ∧
    Checker.checkAx108Costed M = ⟨true, 0⟩ := definitionChecks_eq_pure M

example (M : FiniteModel4) : ax_a105 M.toUFOSignature4 :=
  Checker.checkAx105_sound M rfl

example : Checker.checkAx105Costed (lifeShapeModel true true true true false false false) =
    ⟨true, 0⟩ := by native_decide

example (M : FiniteModel4) : ax_a106 M.toUFOSignature4 :=
  Checker.checkAx106_sound M rfl

example : Checker.checkAx106Costed (lifeShapeModel true true true true false false false) =
    ⟨true, 0⟩ := by native_decide

example (M : FiniteModel4) : ax_a107 M.toUFOSignature4 :=
  Checker.checkAx107_sound M rfl

example : Checker.checkAx107Costed (lifeShapeModel true true true true false false false) =
    ⟨true, 0⟩ := by native_decide

example (M : FiniteModel4) : ax_a108 M.toUFOSignature4 :=
  Checker.checkAx108_sound M rfl

/-- Isolate the interpretation of (a108). These raw tables test the definition;
the cumulative anti-vacuity model separately proves full-package consistency.
Thing 0 instantiates category 1 and specializes target 2. -/
private def categorizationAst (reverse : Bool) : ModelAST :=
  { worldCount := 1, thingCount := 3,
    facts := #[.binary .inst 0 1 0, .binary .sub 0 2 0] ++
      (if reverse then #[.binary .sub 2 0 0] else #[]) }

private def categorizationModel (reverse : Bool) : FiniteModel4 :=
  compileVerifiedModel (categorizationAst reverse)
    (by change 0 < 1; decide) (by change 0 < 3; decide)
    (by cases reverse <;> decide)

example : (categorizationModel false).toUFOSignature4.Categorizes
    (1 : Fin 3) (2 : Fin 3) (0 : Fin 1) := by
  refine ⟨⟨(0 : Fin 1), (0 : Fin 3), by decide⟩, ?_⟩
  intro t
  change Fin 3 at t
  have ht : t = (0 : Fin 3) ∨ t = (1 : Fin 3) ∨ t = (2 : Fin 3) := by
    have := t.isLt
    change t.val < 3 at this
    omega
  rcases ht with rfl | rfl | rfl <;> decide

example : ¬ (categorizationModel true).toUFOSignature4.Categorizes
    (1 : Fin 3) (2 : Fin 3) (0 : Fin 1) := by
  intro h
  have hp := h.2 (0 : Fin 3) (by decide)
  exact hp.2 (by decide)

example : Checker.checkAx108Costed (lifeShapeModel true true true true false false false) =
    ⟨true, 0⟩ := by native_decide

end LeanUfo.Test.Complexity.Queries
