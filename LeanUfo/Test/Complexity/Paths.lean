import LeanUfo.UFO.DSL.Complexity

/-!
# Compiled diagnostic path regressions

A diamond supplies two routes to the same target. An extra edge makes a cycle,
and a fifth vertex is disconnected. Exact arrays check the deterministic route
selected by the descending-pivot Warshall loop. The general source theorem
connects every returned path to the produced finite model.
-/

namespace LeanUfo.Test.Complexity.Paths

open LeanUfo.UFO.DSL
open LeanUfo.UFO.DSL.Complexity

private def ast : ModelAST := {
  worldCount := 2
  thingCount := 5
  facts := #[.binary .inheresIn 0 1 0, .binary .inheresIn 0 2 0,
    .binary .inheresIn 1 3 0, .binary .inheresIn 2 3 0, .binary .inheresIn 3 0 0]
}

private def tables := compileExplicitModelAST ast

-- Each followed pointer costs eleven. The terminal vertex costs three;
-- selecting the world's row and initializing the path costs four.
example : tables.momentOfPathCosted 5 0 0 3 = ⟨some #[0, 2, 3], 29⟩ := by native_decide
example : tables.momentOfPathCosted 5 0 0 1 = ⟨some #[0, 1], 18⟩ := by native_decide
example : tables.momentOfPathCosted 5 0 0 0 = ⟨some #[0], 7⟩ := by native_decide
example : tables.momentOfPathCosted 5 0 0 4 = ⟨none, 13⟩ := by native_decide
example : tables.momentOfPathCosted 5 1 0 3 = ⟨none, 13⟩ := by native_decide
example : tables.momentOfPathCosted 5 2 0 3 = ⟨none, 2⟩ := by native_decide

example : FactTables.nextHopPathFromCosted tables.inherenceNextHops[0]! 5 0 3 1 =
    ⟨none, 14⟩ := by native_decide

example : FinitePath (fun x y => tables.binaryTypedTableDense .inheresIn x y (0 : Fin 2))
    (0 : Fin 5) 3 #[0, 2, 3] := by
  apply FactTables.inherenceCache_path_sound tables
    (compileExplicitModelAST_inherenceCacheValid ast) 2 5 rfl rfl
  native_decide

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    (start target : Fin source.things.size) (world : Fin source.worlds.size) (path : Array Nat)
    (found : (compiled.tables.momentOfPathCosted source.things.size
      world.val start.val target.val).value = some path) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    FinitePath (fun x y => M.inheresIn x y world) start target path ∧
      path.size ≤ source.things.size + 1 ∧
      (compiled.tables.momentOfPathCosted source.things.size
        world.val start.val target.val).cost ≤ 11 * source.things.size + 7 :=
  ⟨compileModelSource_ok_modelPath_sound source compiled success hw ht start target world path found,
   FactTables.momentOfPathCosted_some_size _ _ _ _ _ _ found,
   FactTables.momentOfPathCosted_cost_le _ _ _ _ _⟩

example {n : Nat} {edge : Fin n → Fin n → Bool} {start target : Fin n} {path : Array Nat}
    (valid : FinitePath edge start target path) :
    path.toList.head? = some start.val ∧ path.toList.getLast? = some target.val :=
  valid.endpoints

example : ¬ FinitePath (fun _ _ : Fin 5 => true) 0 3 #[0, 99, 3] := by
  intro valid
  have := valid.mem_lt (vertex := 99) (by decide)
  omega

-- Raw tables can fabricate paths. Their termination and cost bounds hold,
-- but soundness requires the compiled-cache invariant used above.
private def forged : FactTables := {
  denseWorldCount := 1
  denseThingCount := 2
  inherenceNextHops := #[#[none, some 1, none, none]]
}

example : forged.momentOfPathCosted 2 0 0 1 = ⟨some #[0, 1], 18⟩ := by native_decide
example : ¬ FinitePath (fun _ _ : Fin 2 => false) 0 1 #[0, 1] := by
  rintro ⟨tail, hpath, hchain, _⟩
  cases tail with
  | nil => simp at hpath
  | cons hop rest =>
      have hedge := (List.isChain_cons_cons.mp hchain).1
      cases hedge

-- Exhaust all 512 directed graphs on three vertices, including self-loops.
-- The general completeness theorem below proves the same fuel guarantee for
-- every finite graph. This regression also exercises native execution.
example : (List.finRange 512).all (fun mask =>
    let edge := fun x y : Fin 3 => mask.val.testBit (x.val * 3 + y.val)
    let state := warshallState 3 edge
    let next := state.nextHop.flatten.toArray.map (Option.map Fin.val)
    (List.finRange 3).all fun source =>
      (List.finRange 3).all fun target =>
        state.reachable.get source target ==
          (FactTables.nextHopPathFromCosted next 3 source.val target.val 3).value.isSome) = true := by
  native_decide

example (n : Nat) (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    (∃ path, (FactTables.nextHopPathFromCosted
      ((warshallState n edge).nextHop.flatten.toArray.map (Option.map Fin.val))
      n source.val target.val n).value = some path) ↔
        (warshallState n edge).reachable.get source target = true :=
  warshall_nextHopPath_exists_iff_reachable n edge source target

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    (start target : Fin source.things.size) (world : Fin source.worlds.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    (∃ path, (compiled.tables.momentOfPathCosted source.things.size
      world.val start.val target.val).value = some path) ↔
        reachableVia (fun x y => M.inheresIn x y world)
          (List.finRange source.things.size) start target = true :=
  compileModelSource_ok_modelPath_exists_iff source compiled success hw ht start target world

private def longChainNext :=
  (warshallState 9 (fun x y => x.val + 1 == y.val)).nextHop.flatten.toArray.map (Option.map Fin.val)

-- Eight edges use 8*11 operations, then the final vertex costs three.
-- Seven hops cannot reach vertex eight, but the production limit of nine can.
example : FactTables.nextHopPathFromCosted longChainNext 9 0 8 9 =
    ⟨some #[0, 1, 2, 3, 4, 5, 6, 7, 8], 91⟩ := by native_decide
example : FactTables.nextHopPathFromCosted longChainNext 9 0 8 7 =
    ⟨none, 80⟩ := by native_decide

end LeanUfo.Test.Complexity.Paths
