import LeanUfo.UFO.DSL.Compiler.VerifiedModel
import Batteries.Data.List.Lemmas

/-!
# Soundness and completeness of diagnostic inherence paths

For compiled caches, path reconstruction succeeds exactly for reachable pairs.
Every returned path follows actual edges and ends at the requested target.
The loop's fuel is the number of pointer steps still permitted. The proofs
establish that the existing limit of one step per vertex is sufficient.
Raw malformed tables retain their unconditional termination and cost bounds,
but need not describe valid graph paths.

Warshall retains the first hop of an existing route. A newly discovered route
inherits a first hop toward its pivot. The pivot cannot equal the source in
that branch: otherwise the route to the target would already exist. This
invariant proves that each followed pointer denotes an original graph edge.
The joint algorithm/evidence verification follows the method of Nipkow et al.,
*Verified Textbook Algorithms* (ATVA 2020), cited in `Complexity/Closure.lean`.

Completeness uses a natural-number rank that decreases along each pointer
toward a fixed target. New routes rank above old routes and decrease toward
the current pivot. Thus a pointer route cannot repeat a vertex. A graph with
`n` vertices needs fewer than `n` hops along such a route, so the production
fuel limit suffices. Ranks and route lists are proof data. Execution neither
computes nor stores them.
-/

namespace LeanUfo.UFO.DSL.Complexity

/-- Away from the target, Warshall's stored first hop is an original edge.
The claim holds at every pivot stage, including repeated pivots. -/
theorem warshallViaState_nextHop_edge
    (edge : Fin n → Fin n → Bool) (pivots : List (Fin n))
    (source target hop : Fin n) (different : source ≠ target)
    (hHop : (warshallViaState edge pivots).nextHop[source.val][target.val] = some hop) :
    edge source hop = true := by
  induction pivots generalizing source target hop with
  | nil =>
      by_cases he : edge source target = true
      · have hh : target = hop := by
          simpa [warshallViaState, initialWarshallState, initialNextMatrix, different, he] using hHop
        simpa [← hh] using he
      · simp [warshallViaState, initialWarshallState, initialNextMatrix, different, he] at hHop
  | cons pivot pivots ih =>
      simp only [warshallViaState, warshallStateStep, Vector.getElem_ofFn] at hHop
      split at hHop
      · exact ih source target hop different hHop
      · rename_i notOld
        split at hHop
        · rename_i via
          have both : (warshallViaState edge pivots).reachable.get source pivot = true ∧
              (warshallViaState edge pivots).reachable.get pivot target = true := by
            simpa using via
          have notPivot : source ≠ pivot := by
            intro same
            apply notOld
            simpa [same] using both.2
          exact ih source pivot hop notPivot hHop
        · cases hHop

/-- A routing rank decreases after each pointer followed toward a fixed target.
The bound is proof data only. It need not be the runtime traversal limit. -/
private def RoutingRank (state : WarshallState n) : Prop :=
  ∃ bound : Nat, ∃ rank : Fin n → Fin n → Nat,
    (∀ source target, rank source target ≤ bound) ∧
    ∀ source target, state.reachable.get source target = true → source ≠ target →
      ∃ hop, state.nextHop[source.val][target.val] = some hop ∧
        state.reachable.get hop target = true ∧ rank hop target < rank source target

/-- Old routes keep their rank. New routes rank above all old routes and
decrease according to the previous route toward the pivot. This prevents a
pointer cycle even when the underlying inherence graph contains cycles. -/
private theorem warshallViaState_routingRank
    (edge : Fin n → Fin n → Bool) (pivots : List (Fin n)) :
    RoutingRank (warshallViaState edge pivots) := by
  induction pivots with
  | nil =>
      refine ⟨1, (fun source target => if source = target then 0 else 1), ?_, ?_⟩
      · intro source target
        dsimp only
        split <;> omega
      · intro source target reach different
        have hedge : edge source target = true := by
          simpa [warshallViaState, initialWarshallState, initialMatrix_get, different] using reach
        refine ⟨target, ?_, ?_, ?_⟩
        · simp [warshallViaState, initialWarshallState, initialNextMatrix, different, hedge]
        · simp [warshallViaState, initialWarshallState, initialMatrix_get]
        · simp [different]
  | cons pivot pivots ih =>
      obtain ⟨bound, rank, bounded, step⟩ := ih
      let previous := warshallViaState edge pivots
      let nextRank := fun source target =>
        if previous.reachable.get source target then rank source target
        else bound + 1 + rank source pivot
      refine ⟨2 * bound + 1, nextRank, ?_, ?_⟩
      · intro source target
        dsimp only [nextRank]
        split
        · have := bounded source target
          omega
        · have := bounded source pivot
          omega
      · intro source target reach different
        change (warshallMatrixStep pivot previous.reachable).get source target = true at reach
        by_cases old : previous.reachable.get source target = true
        · obtain ⟨hop, hhop, hreach, hlt⟩ := step source target old different
          change previous.reachable.get hop target = true at hreach
          refine ⟨hop, ?_, ?_, ?_⟩
          · change (warshallStateStep pivot previous).nextHop[source.val][target.val] = some hop
            simpa [warshallStateStep, old] using hhop
          · change (warshallMatrixStep pivot previous.reachable).get hop target = true
            simp [warshallMatrixStep_get, hreach]
          · simpa [nextRank, old, hreach] using hlt
        · have via : previous.reachable.get source pivot = true ∧
              previous.reachable.get pivot target = true := by
            simpa [warshallMatrixStep_get, old] using reach
          have differentPivot : source ≠ pivot := by
            intro same
            exact old (same ▸ via.2)
          obtain ⟨hop, hhop, hreach, hlt⟩ := step source pivot via.1 differentPivot
          change previous.reachable.get hop pivot = true at hreach
          refine ⟨hop, ?_, ?_, ?_⟩
          · change (warshallStateStep pivot previous).nextHop[source.val][target.val] = some hop
            simpa [warshallStateStep, old, via.1, via.2] using hhop
          · change (warshallMatrixStep pivot previous.reachable).get hop target = true
            simp [warshallMatrixStep_get, hreach, via.2]
          · dsimp only [nextRank]
            by_cases already : previous.reachable.get hop target = true
            · simp only [if_pos already, if_neg old]
              have := bounded hop target
              omega
            · simp only [if_neg already, if_neg old]
              omega

/-- Strictly decreasing ranks give a pointer route with no repeated vertex.
A duplicate-free list of `Fin n` values has at most `n` entries, regardless
of how large the proof-only numerical ranks are. -/
private theorem RoutingRank.route {state : WarshallState n} (valid : RoutingRank state)
    (source target : Fin n) (reachable : state.reachable.get source target = true) :
    ∃ tail : List (Fin n),
      List.IsChain (fun x y => state.nextHop[x.val][target.val] = some y) (source :: tail) ∧
      (source :: tail).getLast? = some target ∧ tail.length < n := by
  obtain ⟨_, rank, _, step⟩ := valid
  have routes : ∀ k, ∀ start : Fin n, rank start target = k →
      state.reachable.get start target = true →
      ∃ tail : List (Fin n),
        List.IsChain (fun x y => state.nextHop[x.val][target.val] = some y) (start :: tail) ∧
        List.Pairwise (fun x y => rank y target < rank x target) (start :: tail) ∧
        (start :: tail).getLast? = some target := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro start hrank hreach
        by_cases same : start = target
        · exact ⟨[], by simp, by simp, by simp [same]⟩
        · obtain ⟨hop, hhop, hopReach, decrease⟩ := step start target hreach same
          obtain ⟨tail, pointerChain, ranks, last⟩ :=
            ih (rank hop target) (by omega) hop rfl hopReach
          refine ⟨hop :: tail, List.IsChain.cons_cons hhop pointerChain, ?_, ?_⟩
          · apply List.pairwise_cons.mpr
            refine ⟨?_, ranks⟩
            intro vertex member
            rcases List.mem_cons.mp member with rfl | member
            · exact decrease
            · have hlt := (List.pairwise_cons.mp ranks).1 vertex member
              omega
          · simpa using last
  obtain ⟨tail, pointerChain, ranks, last⟩ := routes (rank source target) source rfl reachable
  have distinct : (source :: tail).Nodup :=
    ranks.imp (by intro x y decrease same; subst y; omega)
  have lengthBound := distinct.length_le_of_subset
    (l₂ := List.finRange n) (by intro vertex _; exact List.mem_finRange vertex)
  refine ⟨tail, pointerChain, last, ?_⟩
  exact Nat.lt_of_succ_le (by simpa using lengthBound)

private theorem nextHopPathFromCosted_follows_route
    (matrix : NextMatrix n) (target : Fin n) (fuel : Nat)
    (source : Fin n) (tail : List (Fin n)) (acc : Array Nat)
    (chain : List.IsChain (fun x y => matrix[x.val][target.val] = some y) (source :: tail))
    (last : (source :: tail).getLast? = some target) (enough : tail.length ≤ fuel) :
    ∃ path, (FactTables.nextHopPathFromCosted
      (matrix.flatten.toArray.map (Option.map Fin.val)) n source.val target.val fuel acc).value = some path := by
  induction fuel generalizing source tail acc with
  | zero =>
      have empty : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst tail
      have same : source = target := by simpa using last
      refine ⟨acc.push source.val, ?_⟩
      rw [FactTables.nextHopPathFromCosted_value_step]
      simp [same]
  | succ fuel ih =>
      by_cases same : source = target
      · refine ⟨acc.push source.val, ?_⟩
        rw [FactTables.nextHopPathFromCosted_value_step]
        simp [same]
      · cases tail with
        | nil => simp at last; exact False.elim (same last)
        | cons hop rest =>
            obtain ⟨hhop, hchain⟩ := List.isChain_cons_cons.mp chain
            obtain ⟨path, hpath⟩ := ih hop rest (acc.push source.val) hchain
              (by simpa using last) (by simpa using enough)
            refine ⟨path, ?_⟩
            rw [FactTables.nextHopPathFromCosted_value_step]
            have different : source.val ≠ target.val := fun eq => same (Fin.ext eq)
            simp only [beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte]
            rw [Array.getElem?_map, flatten_toArray_getElem?_matrixIndex, hhop]
            exact hpath

/-- A finite path includes its source and target. The intermediate coordinates
are in range, and `IsChain` requires an edge between each adjacent pair.
Vertices can repeat. The predicate does not require a shortest route.
The list is a proof specification for the returned array, not a runtime copy. -/
def FinitePath (edge : Fin n → Fin n → Bool) (source target : Fin n)
    (path : Array Nat) : Prop :=
  ∃ tail : List (Fin n),
    path.toList = (source :: tail).map Fin.val ∧
    List.IsChain (fun x y => edge x y = true) (source :: tail) ∧
    (source :: tail).getLast? = some target

/-- A path witness cannot contain a coordinate outside the finite domain. -/
theorem FinitePath.mem_lt {edge : Fin n → Fin n → Bool} {source target : Fin n}
    {path : Array Nat} (valid : FinitePath edge source target path)
    {vertex : Nat} (member : vertex ∈ path.toList) : vertex < n := by
  obtain ⟨tail, hpath, _, _⟩ := valid
  rw [hpath] at member
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
  exact v.isLt

/-- The first and last coordinates are the requested endpoints, including
the one-vertex path from a vertex to itself. -/
theorem FinitePath.endpoints {edge : Fin n → Fin n → Bool} {source target : Fin n}
    {path : Array Nat} (valid : FinitePath edge source target path) :
    path.toList.head? = some source.val ∧ path.toList.getLast? = some target.val := by
  obtain ⟨tail, hpath, _, hend⟩ := valid
  rw [hpath]
  constructor
  · rfl
  · rw [List.getLast?_map, hend]
    rfl

private theorem nextHopPathFromCosted_some_path_acc
    (edge : Fin n → Fin n → Bool) (row : Array (Option Nat)) (target : Fin n)
    (hHops : ∀ (source : Fin n), source ≠ target → ∀ next,
      row[matrixIndex n source.val target.val]?.join = some next →
        ∃ hop : Fin n, hop.val = next ∧ edge source hop = true)
    (fuel : Nat) (source : Fin n) (acc path : Array Nat)
    (found : (FactTables.nextHopPathFromCosted row n source.val target.val fuel acc).value = some path) :
    ∃ tail : List (Fin n),
      path.toList = acc.toList ++ (source :: tail).map Fin.val ∧
      List.IsChain (fun x y => edge x y = true) (source :: tail) ∧
      (source :: tail).getLast? = some target := by
  induction fuel generalizing source acc with
  | zero =>
      rw [FactTables.nextHopPathFromCosted_value_step] at found
      split at found
      · rename_i same
        have heq : source = target := Fin.ext (by simpa using same)
        cases Option.some.inj found
        exact ⟨[], by simp, by simp, by simp [heq]⟩
      · cases found
  | succ fuel ih =>
      rw [FactTables.nextHopPathFromCosted_value_step] at found
      split at found
      · rename_i same
        have heq : source = target := Fin.ext (by simpa using same)
        cases Option.some.inj found
        exact ⟨[], by simp, by simp, by simp [heq]⟩
      · rename_i different
        dsimp only at found
        split at found
        · cases found
        · rename_i next hnext
          obtain ⟨hop, hval, hedge⟩ := hHops source
            (by intro same; apply different; simp [same]) next hnext
          rw [← hval] at found
          obtain ⟨tail, hpath, hchain, hend⟩ := ih hop (acc.push source.val) found
          refine ⟨hop :: tail, ?_, ?_, ?_⟩
          · simpa [List.append_assoc] using hpath
          · exact List.isChain_cons_cons.mpr ⟨hedge, hchain⟩
          · simpa using hend

/-- Flattening the proved first-hop matrix preserves the edge invariant.
Any path returned by the production loop is therefore a finite graph path. -/
theorem warshall_nextHopPath_sound (n : Nat) (edge : Fin n → Fin n → Bool)
    (source target : Fin n) (fuel : Nat) (path : Array Nat)
    (found : (FactTables.nextHopPathFromCosted
      ((warshallState n edge).nextHop.flatten.toArray.map (Option.map Fin.val))
      n source.val target.val fuel).value = some path) :
    FinitePath edge source target path := by
  have hHops (start : Fin n) (different : start ≠ target) (next : Nat)
      (hnext : ((warshallState n edge).nextHop.flatten.toArray.map
        (Option.map Fin.val))[matrixIndex n start.val target.val]?.join = some next) :
      ∃ hop : Fin n, hop.val = next ∧ edge start hop = true := by
    rw [Array.getElem?_map, flatten_toArray_getElem?_matrixIndex] at hnext
    cases hcell : (warshallState n edge).nextHop[start.val][target.val] with
    | none => simp [hcell] at hnext
    | some hop =>
        refine ⟨hop, by simpa [hcell] using hnext, ?_⟩
        exact warshallViaState_nextHop_edge edge (List.finRange n) start target hop different hcell
  obtain ⟨tail, hpath, hchain, hend⟩ :=
    nextHopPathFromCosted_some_path_acc edge _ target hHops fuel source #[] path found
  exact ⟨tail, by simpa using hpath, hchain, hend⟩

/-- Every reachable pair has a pointer route within the production fuel limit.
Ranks exclude repeated vertices, so the route needs fewer than `n` hops. -/
theorem warshall_nextHopPath_complete (n : Nat) (edge : Fin n → Fin n → Bool)
    (source target : Fin n)
    (reachable : (warshallState n edge).reachable.get source target = true) :
    ∃ path, (FactTables.nextHopPathFromCosted
      ((warshallState n edge).nextHop.flatten.toArray.map (Option.map Fin.val))
      n source.val target.val n).value = some path := by
  obtain ⟨tail, chain, last, length⟩ :=
    (warshallViaState_routingRank edge (List.finRange n)).route source target reachable
  exact nextHopPathFromCosted_follows_route _ target n source tail #[] chain last (by omega)

private theorem warshallViaState_refl (edge : Fin n → Fin n → Bool)
    (pivots : List (Fin n)) (source : Fin n) :
    (warshallViaState edge pivots).reachable.get source source = true := by
  induction pivots with
  | nil => simp [warshallViaState, initialWarshallState, initialMatrix_get]
  | cons pivot pivots ih =>
      simp [warshallViaState, warshallStateStep, warshallMatrixStep_get, ih]

/-- With the existing `n`-hop limit, reconstruction succeeds exactly for the
pairs marked reachable by Warshall. A missing path is therefore not a fuel
failure for a well-formed compiled cache. -/
theorem warshall_nextHopPath_exists_iff_reachable (n : Nat) (edge : Fin n → Fin n → Bool)
    (source target : Fin n) :
    (∃ path, (FactTables.nextHopPathFromCosted
      ((warshallState n edge).nextHop.flatten.toArray.map (Option.map Fin.val))
      n source.val target.val n).value = some path) ↔
        (warshallState n edge).reachable.get source target = true := by
  constructor
  · rintro ⟨path, found⟩
    by_cases same : source = target
    · subst target
      exact warshallViaState_refl edge (List.finRange n) source
    · rw [FactTables.nextHopPathFromCosted_value_step] at found
      have different : source.val ≠ target.val := fun eq => same (Fin.ext eq)
      simp only [beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte] at found
      cases n with
      | zero => exact Fin.elim0 source
      | succ n =>
          dsimp only at found
          rw [Array.getElem?_map, flatten_toArray_getElem?_matrixIndex] at found
          cases hcell : (warshallState (n + 1) edge).nextHop[source.val][target.val] with
          | none => simp [hcell] at found
          | some hop =>
              exact (warshallState_nextHop_exists_iff_reachable _ edge source target).mp ⟨hop, hcell⟩
  · exact warshall_nextHopPath_complete n edge source target

end Complexity

/-- Cache validity connects every returned diagnostic path to the table's
actual dense inherence edges. Dimensions and endpoints must match the cache. -/
theorem FactTables.inherenceCache_path_sound
    (tables : FactTables) (valid : tables.InherenceCacheValid)
    (W T : Nat) (worlds : tables.denseWorldCount = W) (things : tables.denseThingCount = T)
    (source target : Fin T) (world : Fin W) (path : Array Nat)
    (found : (tables.momentOfPathCosted T world.val source.val target.val).value = some path) :
    Complexity.FinitePath (fun x y => tables.binaryTypedTableDense .inheresIn x y world)
      source target path := by
  subst W
  subst T
  rw [FactTables.momentOfPathCosted_value_cases, valid.nextHopAt tables world] at found
  exact Complexity.warshall_nextHopPath_sound _ (tables.inherenceEdgeAt world.val)
    source target tables.denseThingCount path found

/-- Successful source compilation supplies the cache and representation
proofs. Returned path coordinates describe edges in the actual produced model,
not just in an independently chosen graph. -/
theorem compileModelSource_ok_modelPath_sound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    (start target : Fin source.things.size) (world : Fin source.worlds.size)
    (path : Array Nat)
    (found : (compiled.tables.momentOfPathCosted source.things.size
      world.val start.val target.val).value = some path) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    Complexity.FinitePath (fun x y => M.inheresIn x y world) start target path := by
  obtain ⟨worlds, things⟩ := compileModelSource_ok_tableDimensions source compiled success
  have hpath := compiled.tables.inherenceCache_path_sound
    (compileModelSource_ok_inherenceCacheValid source compiled success)
    _ _ worlds things start target world path found
  have edges := congrArg
    (fun lookups : FactTables.TableLookups source.worlds.size source.things.size =>
      fun x y => lookups.binary .inheresIn x y world)
    (compileModelSource_ok_lookups_agree source compiled success).symm
  change (fun x y => compiled.tables.binaryTypedTableDense .inheresIn x y world) = _ at edges
  rw [edges] at hpath
  exact hpath

/-- The compiler's stored next-hop and reachability arrays agree on whether
a path exists. The production traversal's current fuel limit is sufficient. -/
theorem FactTables.inherenceCache_path_exists_iff
    (tables : FactTables) (valid : tables.InherenceCacheValid)
    (W T : Nat) (worlds : tables.denseWorldCount = W) (things : tables.denseThingCount = T)
    (source target : Fin T) (world : Fin W) :
    (∃ path, (tables.momentOfPathCosted T world.val source.val target.val).value = some path) ↔
      tables.inherenceClosureTable source target world = true := by
  subst W
  subst T
  rw [tables.inherenceCache_lookup valid _ _ rfl rfl source target world]
  simp only [FactTables.momentOfPathCosted_value_cases, valid.nextHopAt tables world]
  have result := Complexity.warshall_nextHopPath_exists_iff_reachable tables.denseThingCount
    (tables.inherenceEdgeAt world.val) source target
  rw [Complexity.warshallState_reachable_get] at result
  exact result

/-- For a successfully compiled source, reconstruction succeeds exactly when
the actual produced model's inherence closure relates the requested endpoints.
The source supplies the cache, dimensions, and relation-correspondence proofs. -/
theorem compileModelSource_ok_modelPath_exists_iff
    (source : ModelSource) (compiled : CompiledModelSource)
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
        Complexity.reachableVia (fun x y => M.inheresIn x y world)
          (List.finRange source.things.size) start target = true := by
  obtain ⟨worlds, things⟩ := compileModelSource_ok_tableDimensions source compiled success
  have result := compiled.tables.inherenceCache_path_exists_iff
    (compileModelSource_ok_inherenceCacheValid source compiled success)
    _ _ worlds things start target world
  rw [compileModelSource_ok_modelClosure_lookup source compiled success hw ht start target world] at result
  exact result

end LeanUfo.UFO.DSL
