import LeanUfo.UFO.DSL.Compiler.VerifiedModel
import LeanUfo.UFO.DSL.Checker.Axioms

/-!
# Concrete table costs at checker calls

For 112 registry checks, execution equals a counted computation over the
compiler's table evaluators: axioms 1–104,
the qua-individual/endurant typing check, the four named taxonomy bridges,
and the three distance extensions. The remaining four entries, axioms 105–108,
return `⟨true, 0⟩` because the signature defines their relations by those axioms.
Together these results cover all 116 entries.
The equalities in this module preserve both the Boolean result and its cost.
They concern the dense native lookup, not the work of reducing sparse tables
inside Lean's kernel.

Full counted equality is a source-semantics claim. Native compilation can share
identical calls while the source counter charges both occurrences, as observed
for axioms 53–55 and 58–59. These equalities do not count native function calls.

A direct unary, binary, or ternary read costs eight, eleven, or fourteen operations.
Compiled part and overlap queries first compare coordinates. Equal coordinates
cost two operations and skip the table read; unequal coordinates cost thirteen.
The checker can retain its compact Boolean relation fields and charge the
corresponding amount at each executed call. A block-equality proof expands
that charge into the counted coordinate arithmetic and array read. This is a local
implementation correspondence, in the cost-composition style of Haslbeck's
*Hoare Logics for Time Bounds* (2018). Compiler agreement supplies the value
equality at the representation boundary, following the proof organization
illustrated by de Moura's RadixExperiment. Neither precedent replaces the
equalities proved here. See `docs/dsl/complexity.md` for references and limits.

Arbitrary hand-written Boolean functions do not inherit these fixed-operation
guarantees. The model-specific equalities require the compiler's
verified constructor and its actual sparse/dense agreement proof.
-/

namespace LeanUfo.UFO.DSL.Complexity

/-! ## Primitive table blocks

Each block equality expands the checker's fixed charge into the entire counted
dense read. Optional reads keep the equalities valid even on incomplete arrays.
Ternary width is written with a power in the proof-facing dense function and
with three multiplications in the counted function. Their value proof connects
the two. The compiler's `csimp` equality replaces the dense function with the
counted function's value projection, so native execution uses those explicit
multiplications. This proof does not assign a constant to opaque exponentiation.
The private lemmas then use compiler agreement for the verified model fields.
-/

theorem unaryTableBlock_eq_counted (tables : FactTables) (field : UnaryField)
    {W T : Nat} (x : Fin T) (w : Fin W) :
    Costed.tick (tables.unaryTypedTableDense field x w) 8 =
      tables.unaryTypedTableCosted field x w := by
  rfl

theorem binaryTableBlock_eq_counted (tables : FactTables) (field : BinaryField)
    {W T : Nat} (x y : Fin T) (w : Fin W) :
    Costed.tick (tables.binaryTypedTableDense field x y w) 11 =
      tables.binaryTypedTableCosted field x y w := by
  rfl

theorem ternaryTableBlock_eq_counted (tables : FactTables) (field : TernaryField)
    {W T : Nat} (x y z : Fin T) (w : Fin W) :
    Costed.tick (tables.ternaryTypedTableDense field x y z w) 14 =
      tables.ternaryTypedTableCosted field x y z w := by
  rw [← tables.ternaryTypedTableCosted_value_dense field x y z w]
  rfl

private theorem verifiedUnaryBlock_eq_counted (tables : FactTables) (W T : Nat)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (field : UnaryField) (x : Fin T) (w : Fin W) :
    Costed.tick ((tables.verifiedLookups W T agreement).unary field x w) 8 =
      tables.unaryTypedTableCosted field x w := by
  unfold FactTables.verifiedLookups
  rw [agreement]
  exact unaryTableBlock_eq_counted tables field x w

private theorem verifiedBinaryBlock_eq_counted (tables : FactTables) (W T : Nat)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (field : BinaryField) (x y : Fin T) (w : Fin W) :
    Costed.tick ((tables.verifiedLookups W T agreement).binary field x y w) 11 =
      tables.binaryTypedTableCosted field x y w := by
  unfold FactTables.verifiedLookups
  rw [agreement]
  exact binaryTableBlock_eq_counted tables field x y w

private theorem verifiedTernaryBlock_eq_counted (tables : FactTables) (W T : Nat)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (field : TernaryField) (x y z : Fin T) (w : Fin W) :
    Costed.tick ((tables.verifiedLookups W T agreement).ternary field x y z w) 14 =
      tables.ternaryTypedTableCosted field x y z w := by
  unfold FactTables.verifiedLookups
  rw [agreement]
  exact ternaryTableBlock_eq_counted tables field x y z w

/-- Expand the equal-coordinate shortcut and, only for unequal coordinates,
the full dense read. The counted record includes the equality and branch. -/
theorem reflexiveBinaryBlock_eq_counted (tables : FactTables) (W T : Nat)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (field : BinaryField) (x y : Fin T) (w : Fin W) :
    Checker.reflexiveBinaryQueryCosted
      (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary field a b v)
      x y w =
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted field x y w) := by
  rw [← verifiedBinaryBlock_eq_counted tables W T agreement field x y w]
  cases h : (x == y) <;>
    simp [Checker.reflexiveBinaryQueryCosted, Costed.orElse, Costed.tick, h]

theorem compiledPart_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.reflexiveBinaryQueryCosted M.part x y w =
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w) :=
  reflexiveBinaryBlock_eq_counted tables W T agreement .part x y w

theorem compiledOverlap_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.reflexiveBinaryQueryCosted M.overlap x y w =
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .overlap x y w) :=
  reflexiveBinaryBlock_eq_counted tables W T agreement .overlap x y w

/-! ## Closure construction

The uncached checker builds one reachability matrix per world. Its eleven-unit
edge charge expands to the compiler's counted binary read. The theorem uses
the verified constructor without a cache, so axiom 68 executes this path.
It does not cover the subsequent bearer search.
-/

theorem compiledInherenceMatrices_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement) :
    let M := tables.toFiniteModel4Verified W T hw ht agreement
    Checker.inherenceMatricesCosted M =
      Costed.vectorOfFn (fun w : Fin W =>
        warshallMatrixEvalCosted T
          (fun x y => tables.binaryTypedTableCosted .inheresIn x y w)) := by
  change Costed.vectorOfFn (fun w : Fin W =>
    warshallMatrixEvalCosted T
      (fun x y => Costed.tick
        ((tables.verifiedLookups W T agreement).binary .inheresIn x y w) 11)) = _
  simp only [verifiedBinaryBlock_eq_counted]

/-! ## Bearer search and cached axiom 68

A candidate must not be a moment and must be reachable from the source moment.
The search visits candidates in ascending order. For each qualifying candidate,
it scans again to rule out another qualifying bearer. These equalities replace
each eight-unit classification charge with the complete counted unary read.
Reachability remains a counted parameter until the cached axiom theorem selects
the compiler's actual arrays.
-/

theorem compiledBearerSearch_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (reachable : Fin T → Fin T → Fin W → Costed Bool) (m : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let bearer := fun b : Fin T =>
      Costed.andThen (tables.unaryTypedTableCosted .moment b w).not
        (fun _ => reachable m b w)
    Checker.existsUniqueUltimateBearerCosted M reachable m w =
      anyFinCosted T (fun b => Costed.andThen (bearer b) (fun _ =>
        allFinCosted T (fun other =>
          Costed.implies (bearer other) (fun _ => Costed.tick (decide (other = b)) 1)))) := by
  change
    let bearer := fun b : Fin T =>
      Costed.andThen
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .moment b w) 8).not
        (fun _ => reachable m b w)
    anyFinCosted T (fun b => Costed.andThen (bearer b) (fun _ =>
      allFinCosted T (fun other =>
        Costed.implies (bearer other) (fun _ => Costed.tick (decide (other = b)) 1)))) = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledAx68WithReachability_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (reachable : Fin T → Fin T → Fin W → Costed Bool) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let bearer := fun (m b : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .moment b w).not
        (fun _ => reachable m b w)
    Checker.checkAx68WithReachabilityCosted M reachable =
      allFinCosted T (fun m => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .moment m w) (fun _ =>
          anyFinCosted T (fun b => Costed.andThen (bearer m b w) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies (bearer m other w)
                (fun _ => Costed.tick (decide (other = b)) 1))))))) := by
  change allFinCosted T (fun m => allFinCosted W (fun w =>
    Costed.implies
      (Costed.tick ((tables.verifiedLookups W T agreement).unary .moment m w) 8) (fun _ =>
        Checker.existsUniqueUltimateBearerCosted
          (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things)
          reachable m w))) = _
  simp only [verifiedUnaryBlock_eq_counted,
    compiledBearerSearch_eq_countedTables tables W T hw ht agreement valid worlds things reachable]

/-- The cached production checker executes only classification reads, flat
closure reads, and the displayed finite loops. The cache-selection charge is
included; building the cache belongs to compilation. -/
theorem compiledAx68_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let bearer := fun (m b : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .moment b w).not
        (fun _ => closureLookupCosted tables.inherenceClosures T w.val m.val b.val)
    Checker.checkAx68Costed M =
      Costed.charge 1 (allFinCosted T (fun m => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .moment m w) (fun _ =>
          anyFinCosted T (fun b => Costed.andThen (bearer m b w) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies (bearer m other w)
                (fun _ => Costed.tick (decide (other = b)) 1)))))))) := by
  change Costed.charge 1
    (Checker.checkAx68WithReachabilityCosted
      (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things)
      (fun m b w => closureLookupCosted tables.inherenceClosures T w.val m.val b.val)) = _
  exact congrArg (Costed.charge 1)
    (compiledAx68WithReachability_eq_countedTables tables W T hw ht agreement valid worlds things
      (fun m b w => closureLookupCosted tables.inherenceClosures T w.val m.val b.val))

/-! ## Unary classification shapes

These equalities preserve the production loop order. `iff` evaluates both sides
once to compare their answers. Within either side, `andThen` skips its second
operand after false, and `orElse` skips it after true. These skipped computations
are what “short-circuit” means here.
-/

theorem unaryImplication_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (left right : UnaryField) :
    Checker.checkUnaryTableImplicationCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary left)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary right) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w =>
        Costed.implies (tables.unaryTypedTableCosted left x w)
          (fun _ => tables.unaryTypedTableCosted right x w))) := by
  simp only [Checker.checkUnaryTableImplicationCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem unaryDisjoint_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (left right : UnaryField) :
    Checker.checkUnaryTableDisjointCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary left)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary right) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w =>
        Costed.implies (tables.unaryTypedTableCosted left x w)
          (fun _ => (tables.unaryTypedTableCosted right x w).not))) := by
  simp only [Checker.checkUnaryTableDisjointCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem unaryIffAnd_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (left first second : UnaryField) :
    Checker.checkUnaryIffAndCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary left)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary first)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary second) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w =>
        Costed.iff (tables.unaryTypedTableCosted left x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted first x w)
            (fun _ => tables.unaryTypedTableCosted second x w)))) := by
  simp only [Checker.checkUnaryIffAndCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem unaryIffAndNot_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (left first second : UnaryField) :
    Checker.checkUnaryIffAndNotCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary left)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary first)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary second) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w =>
        Costed.iff (tables.unaryTypedTableCosted left x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted first x w)
            (fun _ => (tables.unaryTypedTableCosted second x w).not)))) := by
  simp only [Checker.checkUnaryIffAndNotCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem unaryIffOrAnd_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (leftA leftB rightA rightB : UnaryField) :
    Checker.checkUnaryIffOrAndCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary leftA)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary leftB)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary rightA)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary rightB) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted leftA x w)
          (fun _ => tables.unaryTypedTableCosted leftB x w)) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted rightA x w)
              (fun _ => tables.unaryTypedTableCosted rightB x w)))) := by
  simp only [Checker.checkUnaryIffOrAndCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem worldFirstDisjoint_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (left right : UnaryField) :
    Checker.checkWorldFirstDisjointCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary left)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary right) =
      allFinCosted M.worldCount (fun w => allFinCosted M.thingCount (fun x =>
        (Costed.andThen (tables.unaryTypedTableCosted left x w)
          (fun _ => tables.unaryTypedTableCosted right x w)).not)) := by
  simp only [Checker.checkWorldFirstDisjointCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem unaryIffOrSingle_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (leftA leftB right : UnaryField) :
    Checker.checkUnaryIffOrSingleCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary leftA)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary leftB)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary right) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted leftA x w)
          (fun _ => tables.unaryTypedTableCosted leftB x w)) (fun _ => tables.unaryTypedTableCosted right x w))) := by
  simp only [Checker.checkUnaryIffOrSingleCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem unaryIffThreeOrSingle_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (leftA leftB leftC right : UnaryField) :
    Checker.checkUnaryIffThreeOrSingleCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary leftA)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary leftB)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary leftC)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary right) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted leftA x w) (fun _ =>
          Costed.orElse (tables.unaryTypedTableCosted leftB x w) (fun _ => tables.unaryTypedTableCosted leftC x w)))
            (fun _ => tables.unaryTypedTableCosted right x w))) := by
  simp only [Checker.checkUnaryIffThreeOrSingleCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

theorem thingWorldWorldImp_eq_countedTables (M : FiniteModel4) (tables : FactTables)
    (agreement : tables.sparseLookups M.worldCount M.thingCount =
      tables.denseLookups M.worldCount M.thingCount) (left right : UnaryField) :
    Checker.checkThingWorldWorldImpCosted M
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary left)
      ((tables.verifiedLookups M.worldCount M.thingCount agreement).unary right) =
      allFinCosted M.thingCount (fun x => allFinCosted M.worldCount (fun w => allFinCosted M.worldCount (fun v =>
        Costed.implies (tables.unaryTypedTableCosted left x w)
          (fun _ => tables.unaryTypedTableCosted right x v)))) := by
  simp only [Checker.checkThingWorldWorldImpCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, verifiedUnaryBlock_eq_counted]

/-! ## Instantiation scans and specialization witnesses

Typehood means that some thing instantiates the candidate in some world.
The scan visits worlds first, then things, and stops at its first witness.
Individualhood is the complement of that scan, with one additional negation.
The current-world argument does not restrict this search.

Axiom 6 searches for a common upper type first. Only after that search fails
does it search for a common lower type. The query equalities retain both the
direction of specialization and the first-witness order.
-/

theorem compiledType_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.typeBCosted M x w =
      anyFinCosted W (fun v => anyFinCosted T (fun y =>
        tables.binaryTypedTableCosted .inst y x v)) := by
  change anyFinCosted W (fun v => anyFinCosted T (fun y =>
        Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y x v) 11)) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledIndividual_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.individualBCosted M x w =
      (anyFinCosted W (fun v => anyFinCosted T (fun y =>
        tables.binaryTypedTableCosted .inst y x v))).not := by
  change (anyFinCosted W (fun v => anyFinCosted T (fun y =>
        Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y x v) 11))).not = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledNoInstances_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.noInstancesEveryWorldCosted M x =
      allFinCosted W (fun v => (anyFinCosted T (fun y =>
        tables.binaryTypedTableCosted .inst y x v)).not) := by
  change allFinCosted W (fun v => (anyFinCosted T (fun y =>
        Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y x v) 11)).not) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledInstSubsumption_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.instSubsumptionCosted M x y =
      allFinCosted W (fun v => allFinCosted T (fun z =>
        Costed.implies (tables.binaryTypedTableCosted .inst z x v) (fun _ =>
          tables.binaryTypedTableCosted .inst z y v))) := by
  change allFinCosted W (fun v => allFinCosted T (fun z =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z x v) 11) (fun _ =>
          Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z y v) 11))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx6Antecedent_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (t1 t2 x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.ax6AntecedentCosted M t1 t2 x w =
      Costed.andThen (tables.binaryTypedTableCosted .inst x t1 w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst x t2 w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .sub t1 t2 w).not (fun _ =>
            (tables.binaryTypedTableCosted .sub t2 t1 w).not))) := by
  change Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t1 w) 11) (fun _ =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t2 w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t1 t2 w) 11).not (fun _ =>
            (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t2 t1 w) 11).not))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx6Witness_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (a b x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.ax6WitnessCosted M a b x w =
      anyFinCosted T (fun t3 =>
        Costed.andThen (tables.binaryTypedTableCosted .sub a t3 w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .sub b t3 w) (fun _ =>
            tables.binaryTypedTableCosted .inst x t3 w))) := by
  change anyFinCosted T (fun t3 =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub a t3 w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub b t3 w) 11) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t3 w) 11))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx6LowerWitness_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (a b x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.ax6LowerWitnessCosted M a b x w =
      anyFinCosted T (fun t3 =>
        Costed.andThen (tables.binaryTypedTableCosted .sub t3 a w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .sub t3 b w) (fun _ =>
            tables.binaryTypedTableCosted .inst x t3 w))) := by
  change anyFinCosted T (fun t3 =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t3 a w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t3 b w) 11) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t3 w) 11))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledSubDef_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
        tables.binaryTypedTableCosted .inst y t v))
    Checker.subDefBCosted M x y w =
      Costed.andThen (scan x) (fun _ => Costed.andThen (scan y) (fun _ =>
        allFinCosted W (fun v => allFinCosted T (fun z =>
        Costed.implies (tables.binaryTypedTableCosted .inst z x v) (fun _ =>
          tables.binaryTypedTableCosted .inst z y v))))) := by
  simp only [Checker.subDefBCosted, compiledType_eq_countedTables,
    compiledInstSubsumption_eq_countedTables]

/-! ## Quality and classification by instances

Quality requires exactly one matching kind. The candidate predicate is a
function of the kind index, not a cached answer: the uniqueness scan evaluates
it again for every visited competitor. The family evaluator then composes an
arbitrary counted leaf, preserving both direct unary reads and the quality
search used by axiom 44.
-/

theorem compiledQuality_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    Checker.qualityBCosted M x w = quality x w := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    quality x w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledTypeByInstances_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (field : UnaryField) (leaf : Fin T → Fin W → Costed Bool) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let family := fun (field : UnaryField) (leaf : Fin T → Fin W → Costed Bool) =>
      allFinCosted T (fun t => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted field t w) (fun _ =>
          Costed.andThen
            (anyFinCosted W (fun v => anyFinCosted T (fun x =>
              tables.binaryTypedTableCosted .inst x t v)))
            (fun _ => allFinCosted W (fun v => allFinCosted T (fun x =>
              Costed.implies (tables.binaryTypedTableCosted .inst x t v)
                (fun _ => leaf x v)))))))
    Checker.typeByInstancesEvalCosted M
      ((tables.verifiedLookups W T agreement).unary field) leaf = family field leaf := by
  change
    let family := fun (field : UnaryField) (leaf : Fin T → Fin W → Costed Bool) =>
      allFinCosted T (fun t => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary field t w) 8) (fun _ =>
          Costed.andThen
            (anyFinCosted W (fun v => anyFinCosted T (fun x =>
              Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11)))
            (fun _ => allFinCosted W (fun v => allFinCosted T (fun x =>
              Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11)
                (fun _ => leaf x v)))))))
    family field leaf = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

/-! ## Compiled checker entries

Each theorem applies to the verified cached constructor used by the frontend.
Its premises concern the exact tables and dimensions in the statement. Caching
and product-family conversion do not change the primitive relation fields.

The numbered checks appear in numerical order, followed by the named extensions.
Axioms 44 and 45 retain their ordered ten-entry and six-entry registries.
The distance triangle retains its left-associated conjunctions: a false early
read skips later reads but
still visits each enclosing branch test.
-/

theorem compiledAx1_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx1Costed M =
      allFinCosted T (fun x => allFinCosted W (fun _w =>
        Costed.bind (scan x) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer)))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted W (fun _w =>
        Costed.bind (scan x) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer)))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx2_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx2Costed M =
      allFinCosted T (fun x => allFinCosted W (fun _w =>
        Costed.iff (scan x).not (fun _ => allFinCosted W (fun v =>
          (anyFinCosted T (fun y => tables.binaryTypedTableCosted .inst y x v)).not)))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted W (fun _w =>
        Costed.iff (scan x).not (fun _ => allFinCosted W (fun v =>
          (anyFinCosted T (fun y =>
            Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y x v) 11)).not)))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx3_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx3Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .inst x y w) (fun _ =>
          Costed.orElse (scan x) (fun _ => (scan x).not))))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x y w) 11) (fun _ =>
          Costed.orElse (scan x) (fun _ => (scan x).not))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx4_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx4Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x =>
        allFinCosted T (fun y => allFinCosted T (fun z =>
          (Costed.andThen (scan x) (fun _ =>
            Costed.andThen (tables.binaryTypedTableCosted .inst x y w) (fun _ =>
              tables.binaryTypedTableCosted .inst y z w))).not)))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted W (fun w => allFinCosted T (fun x =>
        allFinCosted T (fun y => allFinCosted T (fun z =>
          (Costed.andThen (scan x) (fun _ =>
            Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x y w) 11) (fun _ =>
              Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y z w) 11))).not)))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx5_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx5Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (tables.binaryTypedTableCosted .sub x y w) (fun _ =>
          Costed.andThen (scan x) (fun _ => Costed.andThen (scan y) (fun _ =>
            allFinCosted W (fun v => allFinCosted T (fun z =>
              Costed.implies (tables.binaryTypedTableCosted .inst z x v) (fun _ =>
                tables.binaryTypedTableCosted .inst z y v))))))))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub x y w) 11) (fun _ =>
          Costed.andThen (scan x) (fun _ => Costed.andThen (scan y) (fun _ =>
            allFinCosted W (fun v => allFinCosted T (fun z =>
              Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z x v) 11) (fun _ =>
                Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z y v) 11))))))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx6_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let premise := fun (t1 t2 x : Fin T) (w : Fin W) =>
      Costed.andThen (tables.binaryTypedTableCosted .inst x t1 w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst x t2 w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .sub t1 t2 w).not (fun _ =>
            (tables.binaryTypedTableCosted .sub t2 t1 w).not)))
    let upper := fun (t1 t2 x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t3 =>
        Costed.andThen (tables.binaryTypedTableCosted .sub t1 t3 w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .sub t2 t3 w) (fun _ =>
            tables.binaryTypedTableCosted .inst x t3 w)))
    let lower := fun (t1 t2 x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t3 =>
        Costed.andThen (tables.binaryTypedTableCosted .sub t3 t1 w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .sub t3 t2 w) (fun _ =>
            tables.binaryTypedTableCosted .inst x t3 w)))
    Checker.checkAx6Costed M =
      allFinCosted T (fun t1 => allFinCosted T (fun t2 =>
        allFinCosted T (fun x => allFinCosted W (fun w =>
          Costed.implies (premise t1 t2 x w) (fun _ =>
            Costed.orElse (upper t1 t2 x w) (fun _ => lower t1 t2 x w)))))) := by
  change
    let premise := fun (t1 t2 x : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t1 w) 11) (fun _ =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t2 w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t1 t2 w) 11).not (fun _ =>
            (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t2 t1 w) 11).not)))
    let upper := fun (t1 t2 x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t3 =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t1 t3 w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t2 t3 w) 11) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t3 w) 11)))
    let lower := fun (t1 t2 x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t3 =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t3 t1 w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t3 t2 w) 11) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t3 w) 11)))
    allFinCosted T (fun t1 => allFinCosted T (fun t2 =>
        allFinCosted T (fun x => allFinCosted W (fun w =>
          Costed.implies (premise t1 t2 x w) (fun _ =>
            Costed.orElse (upper t1 t2 x w) (fun _ => lower t1 t2 x w)))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx7_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx7Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .concreteIndividual x w) (fun _ =>
          (scan x).not))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .concreteIndividual x w) 8) (fun _ =>
          (scan x).not))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx8_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx8Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .abstractIndividual x w) (fun _ =>
          (scan x).not))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .abstractIndividual x w) 8) (fun _ =>
          (scan x).not))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx9_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx9Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .concreteIndividual x w)
          (fun _ => (tables.unaryTypedTableCosted .abstractIndividual x w).not))) := by
  exact unaryDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .concreteIndividual .abstractIndividual

theorem compiledAx10_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx10Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (scan x).not (fun _ =>
          Costed.orElse (tables.unaryTypedTableCosted .concreteIndividual x w) (fun _ =>
            tables.unaryTypedTableCosted .abstractIndividual x w)))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (scan x).not (fun _ =>
          Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .concreteIndividual x w) 8) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .abstractIndividual x w) 8)))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx11_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx11Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .endurant x w)
          (fun _ => tables.unaryTypedTableCosted .concreteIndividual x w))) := by
  exact unaryImplication_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .endurant .concreteIndividual

theorem compiledAx12_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx12Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .perdurant x w)
          (fun _ => tables.unaryTypedTableCosted .concreteIndividual x w))) := by
  exact unaryImplication_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .perdurant .concreteIndividual

theorem compiledAx13_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx13Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .endurant x w)
          (fun _ => (tables.unaryTypedTableCosted .perdurant x w).not))) := by
  exact unaryDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .endurant .perdurant

theorem compiledAx14_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx14Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .concreteIndividual x w)
          (fun _ => Costed.orElse (tables.unaryTypedTableCosted .endurant x w)
            (fun _ => tables.unaryTypedTableCosted .perdurant x w)))) := by
  change allFinCosted T (fun x => allFinCosted W (fun w =>
    Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .concreteIndividual x w) 8)
      (fun _ => Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant x w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant x w) 8)))) = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledAx15_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx15Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .endurantType x w) (fun _ =>
          scan x))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurantType x w) 8) (fun _ =>
          scan x))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx16_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      tables.binaryTypedTableCosted .inst y t v))
    Checker.checkAx16Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .perdurantType x w) (fun _ =>
          scan x))) := by
  change
    let scan := fun (t : Fin T) => anyFinCosted W (fun v => anyFinCosted T (fun y =>
      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t v) 11))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurantType x w) 8) (fun _ =>
          scan x))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx17_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx17Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .endurantType x w)
          (fun _ => (tables.unaryTypedTableCosted .perdurantType x w).not))) := by
  exact unaryDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .endurantType .perdurantType

/-- Rigidity performs a possible-instance scan before a necessary-instance scan.
Both scans restart at world zero for each thing; the second runs only after a witness. -/
theorem compiledAx18_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx18Costed M =
      allFinCosted T (fun t =>
        allFinCosted W (fun w =>
          Costed.iff (tables.unaryTypedTableCosted .rigid t w) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .endurantType t w) (fun _ =>
              allFinCosted T (fun x =>
                Costed.implies (anyFinCosted W (fun v =>
                    tables.binaryTypedTableCosted .inst x t v)) (fun _ =>
                  allFinCosted W (fun v =>
                    tables.binaryTypedTableCosted .inst x t v))))))) := by
  change
    allFinCosted T (fun t =>
      allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .rigid t w) 8) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurantType t w) 8)
          (fun _ =>
            allFinCosted T (fun x =>
              Costed.implies (anyFinCosted W (fun v =>
                  Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11)) (fun _ =>
                allFinCosted W (fun v =>
                  Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11))))))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx19_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx19Costed M =
      allFinCosted T (fun t =>
        allFinCosted W (fun w =>
          Costed.iff (tables.unaryTypedTableCosted .antiRigid t w) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .endurantType t w) (fun _ =>
              allFinCosted T (fun x =>
                Costed.implies (anyFinCosted W (fun v =>
                    tables.binaryTypedTableCosted .inst x t v)) (fun _ =>
                  anyFinCosted W (fun v =>
                    (tables.binaryTypedTableCosted .inst x t v).not))))))) := by
  change
    allFinCosted T (fun t =>
      allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .antiRigid t w) 8) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurantType t w) 8)
          (fun _ =>
            allFinCosted T (fun x =>
              Costed.implies (anyFinCosted W (fun v =>
                  Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11)) (fun _ =>
                anyFinCosted W (fun v =>
                  (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11).not))))))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx20_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx20Costed M =
      allFinCosted T (fun t =>
        allFinCosted W (fun w =>
          Costed.iff (tables.unaryTypedTableCosted .semiRigid t w) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .endurantType t w) (fun _ =>
              Costed.andThen ((tables.unaryTypedTableCosted .rigid t w).not) (fun _ =>
                (tables.unaryTypedTableCosted .antiRigid t w).not))))) := by
  change
    allFinCosted T (fun t =>
      allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .semiRigid t w) 8) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurantType t w) 8)
          (fun _ =>
            Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).unary .rigid t w) 8).not)
            (fun _ =>
              (Costed.tick ((tables.verifiedLookups W T agreement).unary .antiRigid t w) 8).not))))) = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledAx21_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx21Costed M =
      allFinCosted T (fun x =>
        allFinCosted W (fun w =>
          Costed.implies (tables.unaryTypedTableCosted .endurant x w) (fun _ =>
            anyFinCosted T (fun k =>
              Costed.andThen (tables.unaryTypedTableCosted .kind k w) (fun _ =>
                allFinCosted W (fun v =>
                  tables.binaryTypedTableCosted .inst x k v)))))) := by
  change
    allFinCosted T (fun x =>
      allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant x w) 8) (fun _ =>
          anyFinCosted T (fun k =>
            Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .kind k w) 8) (fun _ =>
              allFinCosted W (fun v =>
                Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x k v) 11)))))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx22_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx22Costed M =
      allFinCosted T (fun k =>
        allFinCosted T (fun x =>
          allFinCosted W (fun w =>
            Costed.implies (Costed.andThen (tables.unaryTypedTableCosted .kind k w) (fun _ =>
                tables.binaryTypedTableCosted .inst x k w)) (fun _ =>
              (anyFinCosted W (fun v =>
                  anyFinCosted T (fun z =>
                    Costed.andThen (tables.unaryTypedTableCosted .kind z v) (fun _ =>
                      Costed.andThen (tables.binaryTypedTableCosted .inst x z v) (fun _ =>
                        Costed.tick (decide (z ≠ k)) 1))))).not)))) := by
  change
    allFinCosted T (fun k =>
      allFinCosted T (fun x =>
        allFinCosted W (fun w =>
          Costed.implies (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .kind k w) 8)
            (fun _ =>
              Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x k w) 11)) (fun _ =>
            (anyFinCosted W (fun v =>
                anyFinCosted T (fun z =>
                  Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .kind z v) 8)
                  (fun _ =>
                    Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x z v) 11)
                    (fun _ =>
                      Costed.tick (decide (z ≠ k)) 1))))).not)))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx23_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx23Costed M =
      allFinCosted T (fun t =>
        allFinCosted W (fun w =>
          Costed.iff (tables.unaryTypedTableCosted .sortal t w) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .endurantType t w) (fun _ =>
              anyFinCosted T (fun k =>
                Costed.andThen (tables.unaryTypedTableCosted .kind k w) (fun _ =>
                  allFinCosted W (fun v =>
                    allFinCosted T (fun x =>
                      Costed.implies (tables.binaryTypedTableCosted .inst x t v) (fun _ =>
                        tables.binaryTypedTableCosted .inst x k v))))))))) := by
  change
    allFinCosted T (fun t =>
      allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .sortal t w) 8) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurantType t w) 8)
          (fun _ =>
            anyFinCosted T (fun k =>
              Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .kind k w) 8)
              (fun _ =>
                allFinCosted W (fun v =>
                  allFinCosted T (fun x =>
                    Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11)
                    (fun _ =>
                      Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x k v) 11))))))))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx24_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx24Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w => Costed.iff (tables.unaryTypedTableCosted .nonSortal x w)
        (fun _ => Costed.andThen (tables.unaryTypedTableCosted .endurantType x w)
          (fun _ => (tables.unaryTypedTableCosted .sortal x w).not)))) := by
  exact unaryIffAndNot_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .nonSortal .endurantType .sortal

theorem compiledAx25_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx25Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .kind x w)
        (fun _ => tables.unaryTypedTableCosted .subKind x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .kind .subKind

theorem compiledAx26_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx26Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted .kind x w)
          (fun _ => tables.unaryTypedTableCosted .subKind x w)) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .rigid x w)
              (fun _ => tables.unaryTypedTableCosted .sortal x w)))) := by
  exact unaryIffOrAnd_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .kind .subKind .rigid .sortal

theorem compiledAx27_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx27Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .phase x w)
        (fun _ => tables.unaryTypedTableCosted .role x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .phase .role

theorem compiledAx28_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx28Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted .phase x w)
          (fun _ => tables.unaryTypedTableCosted .role x w)) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .antiRigid x w)
              (fun _ => tables.unaryTypedTableCosted .sortal x w)))) := by
  exact unaryIffOrAnd_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .phase .role .antiRigid .sortal

theorem compiledAx29_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx29Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w => Costed.iff (tables.unaryTypedTableCosted .semiRigidSortal x w)
        (fun _ => Costed.andThen (tables.unaryTypedTableCosted .semiRigid x w)
          (fun _ => tables.unaryTypedTableCosted .sortal x w)))) := by
  exact unaryIffAnd_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .semiRigidSortal .semiRigid .sortal

theorem compiledAx30_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx30Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w => Costed.iff (tables.unaryTypedTableCosted .category x w)
        (fun _ => Costed.andThen (tables.unaryTypedTableCosted .rigid x w)
          (fun _ => tables.unaryTypedTableCosted .nonSortal x w)))) := by
  exact unaryIffAnd_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .category .rigid .nonSortal

theorem compiledAx31_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx31Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w => Costed.iff (tables.unaryTypedTableCosted .mixin x w) (fun _ =>
        Costed.andThen (tables.unaryTypedTableCosted .semiRigid x w)
          (fun _ => tables.unaryTypedTableCosted .nonSortal x w)))) := by
  exact unaryIffAnd_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .mixin .semiRigid .nonSortal

theorem compiledAx32_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx32Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .phaseMixin x w)
        (fun _ => tables.unaryTypedTableCosted .roleMixin x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .phaseMixin .roleMixin

theorem compiledAx33_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx33Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted .phaseMixin x w)
          (fun _ => tables.unaryTypedTableCosted .roleMixin x w)) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .antiRigid x w)
              (fun _ => tables.unaryTypedTableCosted .nonSortal x w)))) := by
  exact unaryIffOrAnd_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .phaseMixin .roleMixin .antiRigid .nonSortal

theorem compiledAx34_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx34Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted .substantial x w)
          (fun _ => tables.unaryTypedTableCosted .moment x w))
            (fun _ => tables.unaryTypedTableCosted .endurant x w))) := by
  exact unaryIffOrSingle_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .substantial .moment .endurant

theorem compiledAx35_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx35Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x =>
        (Costed.andThen (tables.unaryTypedTableCosted .substantial x w)
          (fun _ => tables.unaryTypedTableCosted .moment x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .substantial .moment

theorem compiledAx36_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx36Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted .object x w) (fun _ =>
          Costed.orElse (tables.unaryTypedTableCosted .collective x w)
            (fun _ => tables.unaryTypedTableCosted .quantity x w)))
              (fun _ => tables.unaryTypedTableCosted .substantial x w))) := by
  exact unaryIffThreeOrSingle_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .object .collective .quantity .substantial

theorem compiledAx37_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx37Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .object x w)
        (fun _ => tables.unaryTypedTableCosted .collective x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .object .collective

theorem compiledAx38_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx38Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .object x w)
        (fun _ => tables.unaryTypedTableCosted .quantity x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .object .quantity

theorem compiledAx39_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx39Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .collective x w)
        (fun _ => tables.unaryTypedTableCosted .quantity x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .collective .quantity

theorem compiledAx40_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx40Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted .relator x w)
          (fun _ => tables.unaryTypedTableCosted .intrinsicMoment x w))
            (fun _ => tables.unaryTypedTableCosted .moment x w))) := by
  exact unaryIffOrSingle_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .relator .intrinsicMoment .moment

theorem compiledAx41_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx41Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .relator x w)
        (fun _ => tables.unaryTypedTableCosted .intrinsicMoment x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .relator .intrinsicMoment

theorem compiledAx42_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    Checker.checkAx42Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (tables.unaryTypedTableCosted .mode x w)
          (fun _ => quality x w)) (fun _ =>
            tables.unaryTypedTableCosted .intrinsicMoment x w))) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8)
          (fun _ => quality x w)) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .intrinsicMoment x w) 8))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx43_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    Checker.checkAx43Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x =>
        (Costed.andThen (tables.unaryTypedTableCosted .mode x w)
          (fun _ => quality x w)).not)) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    allFinCosted W (fun w => allFinCosted T (fun x =>
        (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8)
          (fun _ => quality x w)).not)) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx44_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let family := fun (field : UnaryField) (leaf : Fin T → Fin W → Costed Bool) =>
      allFinCosted T (fun t => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted field t w) (fun _ =>
          Costed.andThen
            (anyFinCosted W (fun v => anyFinCosted T (fun x =>
              tables.binaryTypedTableCosted .inst x t v)))
            (fun _ => allFinCosted W (fun v => allFinCosted T (fun x =>
              Costed.implies (tables.binaryTypedTableCosted .inst x t v)
                (fun _ => leaf x v)))))))
    Checker.checkAx44Costed M =
      checkRegistryCosted #[
        (fun _ => family .endurantType (fun x w => tables.unaryTypedTableCosted .endurant x w)),
        (fun _ => family .perdurantType (fun x w => tables.unaryTypedTableCosted .perdurant x w)),
        (fun _ => family .substantialType (fun x w => tables.unaryTypedTableCosted .substantial x w)),
        (fun _ => family .momentType (fun x w => tables.unaryTypedTableCosted .moment x w)),
        (fun _ => family .objectType (fun x w => tables.unaryTypedTableCosted .object x w)),
        (fun _ => family .collectiveType (fun x w => tables.unaryTypedTableCosted .collective x w)),
        (fun _ => family .quantityType (fun x w => tables.unaryTypedTableCosted .quantity x w)),
        (fun _ => family .relatorType (fun x w => tables.unaryTypedTableCosted .relator x w)),
        (fun _ => family .modeType (fun x w => tables.unaryTypedTableCosted .mode x w)),
        (fun _ => family .qualityType quality)] := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let family := fun (field : UnaryField) (leaf : Fin T → Fin W → Costed Bool) =>
      allFinCosted T (fun t => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary field t w) 8) (fun _ =>
          Costed.andThen
            (anyFinCosted W (fun v => anyFinCosted T (fun x =>
              Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11)))
            (fun _ => allFinCosted W (fun v => allFinCosted T (fun x =>
              Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t v) 11)
                (fun _ => leaf x v)))))))
    checkRegistryCosted #[
      (fun _ => family .endurantType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant x w) 8)),
      (fun _ => family .perdurantType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant x w) 8)),
      (fun _ => family .substantialType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .substantial x w) 8)),
      (fun _ => family .momentType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .moment x w) 8)),
      (fun _ => family .objectType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .object x w) 8)),
      (fun _ => family .collectiveType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .collective x w) 8)),
      (fun _ => family .quantityType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .quantity x w) 8)),
      (fun _ => family .relatorType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .relator x w) 8)),
      (fun _ => family .modeType (fun x w =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8)),
      (fun _ => family .qualityType quality)] = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx45_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx45Costed M = checkRegistryCosted #[
      fun _ => allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .objectKind x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .objectType x w) (fun _ =>
            tables.unaryTypedTableCosted .kind x w)))),
      fun _ => allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .collectiveKind x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .collectiveType x w) (fun _ =>
            tables.unaryTypedTableCosted .kind x w)))),
      fun _ => allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .quantityKind x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .quantityType x w) (fun _ =>
            tables.unaryTypedTableCosted .kind x w)))),
      fun _ => allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .relatorKind x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .relatorType x w) (fun _ =>
            tables.unaryTypedTableCosted .kind x w)))),
      fun _ => allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .modeKind x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .modeType x w) (fun _ =>
            tables.unaryTypedTableCosted .kind x w)))),
      fun _ => allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .qualityKind x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .qualityType x w) (fun _ =>
            tables.unaryTypedTableCosted .kind x w))))] := by
  let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
  have entry (a b : UnaryField) :
      Checker.kindByTypeCosted M ((tables.verifiedLookups W T agreement).unary a)
        ((tables.verifiedLookups W T agreement).unary b) =
        allFinCosted T (fun x => allFinCosted W (fun w =>
          Costed.iff (tables.unaryTypedTableCosted a x w) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted b x w) (fun _ =>
              tables.unaryTypedTableCosted .kind x w)))) :=
    unaryIffAnd_eq_countedTables M tables agreement a b .kind
  change checkRegistryCosted #[
    fun _ => Checker.kindByTypeCosted M ((tables.verifiedLookups W T agreement).unary .objectKind)
      ((tables.verifiedLookups W T agreement).unary .objectType),
    fun _ => Checker.kindByTypeCosted M ((tables.verifiedLookups W T agreement).unary .collectiveKind)
      ((tables.verifiedLookups W T agreement).unary .collectiveType),
    fun _ => Checker.kindByTypeCosted M ((tables.verifiedLookups W T agreement).unary .quantityKind)
      ((tables.verifiedLookups W T agreement).unary .quantityType),
    fun _ => Checker.kindByTypeCosted M ((tables.verifiedLookups W T agreement).unary .relatorKind)
      ((tables.verifiedLookups W T agreement).unary .relatorType),
    fun _ => Checker.kindByTypeCosted M ((tables.verifiedLookups W T agreement).unary .modeKind)
      ((tables.verifiedLookups W T agreement).unary .modeType),
    fun _ => Checker.kindByTypeCosted M ((tables.verifiedLookups W T agreement).unary .qualityKind)
      ((tables.verifiedLookups W T agreement).unary .qualityType)] = _
  simp only [entry]

theorem compiledAx46_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let kind := fun (k : Fin T) (v : Fin W) =>
      Costed.orElse (tables.unaryTypedTableCosted .objectKind k v) (fun _ =>
        Costed.orElse (tables.unaryTypedTableCosted .collectiveKind k v) (fun _ =>
          Costed.orElse (tables.unaryTypedTableCosted .quantityKind k v) (fun _ =>
            Costed.orElse (tables.unaryTypedTableCosted .relatorKind k v) (fun _ =>
              Costed.orElse (tables.unaryTypedTableCosted .modeKind k v) (fun _ =>
                tables.unaryTypedTableCosted .qualityKind k v)))))
    Checker.checkAx46Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .endurant x w) (fun _ =>
          anyFinCosted W (fun v => anyFinCosted T (fun k =>
            Costed.andThen (kind k v)
              (fun _ => tables.binaryTypedTableCosted .inst x k v)))))) := by
  change
    let kind := fun (k : Fin T) (v : Fin W) =>
      Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .objectKind k v) 8) (fun _ =>
        Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .collectiveKind k v) 8) (fun _ =>
          Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .quantityKind k v) 8) (fun _ =>
            Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .relatorKind k v) 8) (fun _ =>
              Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .modeKind k v) 8) (fun _ =>
                Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind k v) 8)))))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant x w) 8) (fun _ =>
          anyFinCosted W (fun v => anyFinCosted T (fun k =>
            Costed.andThen (kind k v)
              (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x k v) 11)))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx47_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    Checker.checkAx47Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w => part x x w)) := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    allFinCosted T (fun x => allFinCosted W (fun w => part x x w)) = _
  simp only [reflexiveBinaryBlock_eq_counted]

theorem compiledAx48_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    Checker.checkAx48Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.andThen (part x y w) (fun _ => part y x w))
          (fun _ => Costed.tick (decide (x = y)) 1)))) := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.andThen (part x y w) (fun _ => part y x w))
          (fun _ => Costed.tick (decide (x = y)) 1)))) = _
  simp only [reflexiveBinaryBlock_eq_counted]

theorem compiledAx49_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    Checker.checkAx49Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun z => allFinCosted W (fun w =>
          Costed.implies (Costed.andThen (part x y w) (fun _ => part y z w))
            (fun _ => part x z w))))) := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun z => allFinCosted W (fun w =>
          Costed.implies (Costed.andThen (part x y w) (fun _ => part y z w))
            (fun _ => part x z w))))) = _
  simp only [reflexiveBinaryBlock_eq_counted]

theorem compiledAx50_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    let overlap := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .overlap x y w)
    Checker.checkAx50Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (overlap x y w) (fun _ => anyFinCosted T (fun z =>
          Costed.andThen (part z x w) (fun _ => part z y w)))))) := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    let overlap := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .overlap a b v)
        x y w
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (overlap x y w) (fun _ => anyFinCosted T (fun z =>
          Costed.andThen (part z x w) (fun _ => part z y w)))))) = _
  simp only [reflexiveBinaryBlock_eq_counted]

theorem compiledAx51_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    let overlap := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .overlap x y w)
    Checker.checkAx51Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (part y x w).not (fun _ => anyFinCosted T (fun z =>
          Costed.andThen (part z y w) (fun _ => (overlap z x w).not)))))) := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    let overlap := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .overlap a b v)
        x y w
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (part y x w).not (fun _ => anyFinCosted T (fun z =>
          Costed.andThen (part z y w) (fun _ => (overlap z x w).not)))))) = _
  simp only [reflexiveBinaryBlock_eq_counted]

theorem compiledAx52_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    Checker.checkAx52Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (tables.binaryTypedTableCosted .properPart x y w) (fun _ =>
          Costed.andThen (part x y w) (fun _ => (part y x w).not))))) := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart x y w) 11) (fun _ =>
          Costed.andThen (part x y w) (fun _ => (part y x w).not))))) = _
  simp only [reflexiveBinaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

/-! ## Functional dependence

The local expressions expose each binary table read and preserve search order.
The definition checks bind each shared predicate once, so its table operations
contribute once to the full value-and-cost equality.
-/

theorem compiledGenericFunctional_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x' y' : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .inst x x' w)
            (fun _ => tables.binaryTypedTableCosted .functionsAs x x' w))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
                (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w)))))
    Checker.genericFunctionalDependenceCosted M x' y' w =
      generic x' y' w := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11)))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
                (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11))))))
    generic x' y' w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledIndividualFunctional_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x x' y y' : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .inst x x' w)
            (fun _ => tables.binaryTypedTableCosted .functionsAs x x' w))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
                (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w)))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst x x' w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inst y y' w) (fun _ =>
            Costed.implies (tables.binaryTypedTableCosted .functionsAs x x' w)
              (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w))))
    Checker.individualFunctionalDependenceCosted M x x' y y' w =
      individual x x' y y' w := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11)))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
                (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11))))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11)) (fun _ =>
          Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11)) (fun _ =>
            Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11)))))
    individual x x' y y' w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledFunctionalComponent_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x x' y y' : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .inst x x' w)
            (fun _ => tables.binaryTypedTableCosted .functionsAs x x' w))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
                (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w)))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst x x' w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inst y y' w) (fun _ =>
            Costed.implies (tables.binaryTypedTableCosted .functionsAs x x' w)
              (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w))))
    let component := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (tables.binaryTypedTableCosted .properPart x y w)
        (fun _ => individual x x' y y' w)
    Checker.functionalComponentCosted M x x' y y' w =
      component x x' y y' w := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11)))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
                (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11))))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11)) (fun _ =>
          Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11)) (fun _ =>
            Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11)))))
    let component := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart x y w) 11))
        (fun _ => individual x x' y y' w)
    component x x' y y' w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx53_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .inst x x' w)
            (fun _ => tables.binaryTypedTableCosted .functionsAs x x' w))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
                (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w)))))
    Checker.checkAx53Costed M =
      allFinCosted T (fun x' => allFinCosted T (fun y' => allFinCosted W (fun w =>
        Costed.bind (generic x' y' w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11)))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
                (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11))))))
    allFinCosted T (fun x' => allFinCosted T (fun y' => allFinCosted W (fun w =>
        Costed.bind (generic x' y' w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx54_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .inst x x' w)
            (fun _ => tables.binaryTypedTableCosted .functionsAs x x' w))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
                (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w)))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst x x' w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inst y y' w) (fun _ =>
            Costed.implies (tables.binaryTypedTableCosted .functionsAs x x' w)
              (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w))))
    Checker.checkAx54Costed M =
      allFinCosted T (fun x => allFinCosted T (fun x' =>
        allFinCosted T (fun y => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.bind (individual x x' y y' w) (fun answer =>
            Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))))) := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11)))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
                (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11))))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11)) (fun _ =>
          Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11)) (fun _ =>
            Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11)))))
    allFinCosted T (fun x => allFinCosted T (fun x' =>
        allFinCosted T (fun y => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.bind (individual x x' y y' w) (fun answer =>
            Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx55_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .inst x x' w)
            (fun _ => tables.binaryTypedTableCosted .functionsAs x x' w))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
                (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w)))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst x x' w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inst y y' w) (fun _ =>
            Costed.implies (tables.binaryTypedTableCosted .functionsAs x x' w)
              (fun _ => tables.binaryTypedTableCosted .functionsAs y y' w))))
    let component := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (tables.binaryTypedTableCosted .properPart x y w)
        (fun _ => individual x x' y y' w)
    Checker.checkAx55Costed M =
      allFinCosted T (fun x => allFinCosted T (fun x' =>
        allFinCosted T (fun y => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.bind (component x x' y y' w) (fun answer =>
            Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))))) := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies
          (Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11)))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (Costed.tick (decide (y ≠ x)) 1) (fun _ =>
              Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
                (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11))))))
    let individual := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (generic x' y' w) (fun _ =>
        Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11)) (fun _ =>
          Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11)) (fun _ =>
            Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs x x' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .functionsAs y y' w) 11)))))
    let component := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart x y w) 11))
        (fun _ => individual x x' y y' w)
    allFinCosted T (fun x => allFinCosted T (fun x' =>
        allFinCosted T (fun y => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.bind (component x x' y y' w) (fun answer =>
            Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

/-! ## Constitution

The equalities preserve classification tests, instance checks, and per-world
witness searches. Axiom 60 repeats its persistence scan for each qualifying
world. Axiom 62 has no relation queries but retains its two finite loops.
-/

theorem compiledAx56_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let sorts := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.iff (tables.unaryTypedTableCosted .endurant x w)
          (fun _ => tables.unaryTypedTableCosted .endurant y w))
        (fun _ => Costed.iff (tables.unaryTypedTableCosted .perdurant x w)
          (fun _ => tables.unaryTypedTableCosted .perdurant y w))
    Checker.checkAx56Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .constitutedBy x y w)
          (fun _ => sorts x y w)))) := by
  change
    let sorts := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.iff ((Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant x w) 8))
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant y w) 8)))
        (fun _ => Costed.iff ((Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant x w) 8))
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant y w) 8)))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11))
          (fun _ => sorts x y w)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx57_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let kinds := fun (x y x' y' : Fin T) (w : Fin W) =>
      Costed.andThen (tables.binaryTypedTableCosted .constitutedBy x y w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst x x' w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inst y y' w) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .kind x' w)
              (fun _ => tables.unaryTypedTableCosted .kind y' w))))
    Checker.checkAx57Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun x' => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.implies (kinds x y x' y' w)
            (fun _ => Costed.tick (decide (x' ≠ y')) 1)))))) := by
  change
    let kinds := fun (x y x' y' : Fin T) (w : Fin W) =>
      Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11)) (fun _ =>
        Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11)) (fun _ =>
          Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11)) (fun _ =>
            Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).unary .kind x' w) 8))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).unary .kind y' w) 8)))))
    allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun x' => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.implies (kinds x y x' y' w)
            (fun _ => Costed.tick (decide (x' ≠ y')) 1)))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledGenericConstitutional_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x' y' : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .inst x x' w)
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
              (fun _ => tables.binaryTypedTableCosted .constitutedBy x y w))))
    Checker.genericConstitutionalDependenceCosted M x' y' w =
      generic x' y' w := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11)))))
    generic x' y' w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledConstitution_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x x' y y' : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .inst x x' w)
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
              (fun _ => tables.binaryTypedTableCosted .constitutedBy x y w))))
    let constitution := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (tables.binaryTypedTableCosted .inst x x' w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst y y' w) (fun _ =>
          Costed.andThen (generic x' y' w)
            (fun _ => tables.binaryTypedTableCosted .constitutedBy x y w)))
    Checker.constitutionCosted M x x' y y' w =
      constitution x x' y y' w := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11)))))
    let constitution := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11)) (fun _ =>
        Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11)) (fun _ =>
          Costed.andThen (generic x' y' w)
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11))))
    constitution x x' y y' w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx58_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .inst x x' w)
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
              (fun _ => tables.binaryTypedTableCosted .constitutedBy x y w))))
    Checker.checkAx58Costed M =
      allFinCosted T (fun x' => allFinCosted T (fun y' => allFinCosted W (fun w =>
        Costed.bind (generic x' y' w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11)))))
    allFinCosted T (fun x' => allFinCosted T (fun y' => allFinCosted W (fun w =>
        Costed.bind (generic x' y' w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx59_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .inst x x' w)
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen (tables.binaryTypedTableCosted .inst y y' w)
              (fun _ => tables.binaryTypedTableCosted .constitutedBy x y w))))
    let constitution := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen (tables.binaryTypedTableCosted .inst x x' w) (fun _ =>
        Costed.andThen (tables.binaryTypedTableCosted .inst y y' w) (fun _ =>
          Costed.andThen (generic x' y' w)
            (fun _ => tables.binaryTypedTableCosted .constitutedBy x y w)))
    Checker.checkAx59Costed M =
      allFinCosted T (fun x => allFinCosted T (fun x' =>
        allFinCosted T (fun y => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.bind (constitution x x' y y' w) (fun answer =>
            Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))))) := by
  change
    let generic := fun (x' y' : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11))
          (fun _ => anyFinCosted T (fun y =>
            Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11))
              (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11)))))
    let constitution := fun (x x' y y' : Fin T) (w : Fin W) =>
      Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x x' w) 11)) (fun _ =>
        Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y y' w) 11)) (fun _ =>
          Costed.andThen (generic x' y' w)
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11))))
    allFinCosted T (fun x => allFinCosted T (fun x' =>
        allFinCosted T (fun y => allFinCosted T (fun y' => allFinCosted W (fun w =>
          Costed.bind (constitution x x' y y' w) (fun answer =>
            Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx60_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let persistence := fun (x y : Fin T) =>
      allFinCosted W (fun v =>
        Costed.implies (tables.unaryTypedTableCosted .ex x v)
          (fun _ => tables.binaryTypedTableCosted .constitutedBy x y v))
    Checker.checkAx60Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen (tables.unaryTypedTableCosted .perdurant x w)
            (fun _ => tables.binaryTypedTableCosted .constitutedBy x y w))
          (fun _ => persistence x y)))) := by
  change
    let persistence := fun (x y : Fin T) =>
      allFinCosted W (fun v =>
        Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8))
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y v) 11)))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen ((Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant x w) 8))
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11)))
          (fun _ => persistence x y)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx61_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx61Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .constitutedBy x y w)
          (fun _ => (tables.binaryTypedTableCosted .constitutedBy y x w).not)))) := by
  change
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies ((Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy x y w) 11))
          (fun _ => ((Costed.tick ((tables.verifiedLookups W T agreement).binary .constitutedBy y x w) 11)).not)))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx62_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx62Costed M =
      allFinCosted T (fun _ => allFinCosted W (fun _ => Costed.pure true)) := by
  rfl

theorem compiledAx83_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx83Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .quale x w)
          (fun _ => tables.unaryTypedTableCosted .abstractIndividual x w))) := by
  exact unaryImplication_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .quale .abstractIndividual

theorem compiledAx84_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx84Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .set_ x w)
          (fun _ => tables.unaryTypedTableCosted .abstractIndividual x w))) := by
  exact unaryImplication_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .set_ .abstractIndividual

theorem compiledAx85_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx85Costed M =
      allFinCosted W (fun w => allFinCosted T (fun x => (Costed.andThen (tables.unaryTypedTableCosted .quale x w)
        (fun _ => tables.unaryTypedTableCosted .set_ x w)).not)) := by
  exact worldFirstDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .quale .set_

theorem compiledAx89_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx89Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .qualityDomain x w)
          (fun _ => (tables.unaryTypedTableCosted .qualityDimension x w).not))) := by
  exact unaryDisjoint_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .qualityDomain .qualityDimension

theorem compiledAx102_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx102Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .manifests x y w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .perdurant x w) (fun _ =>
            tables.unaryTypedTableCosted .endurant y w))))) := by
  change allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .manifests x y w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant x w) 8) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant y w) 8))))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAx104_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx104Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .meet x y w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .perdurant x w) (fun _ =>
            tables.unaryTypedTableCosted .perdurant y w))))) := by
  change allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .meet x y w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant x w) 8) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant y w) 8))))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAxInstEndurant_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxInstEndurantCosted M =
      allFinCosted T (fun a =>
        allFinCosted T (fun b =>
          allFinCosted W (fun w =>
            Costed.implies (Costed.andThen (tables.unaryTypedTableCosted .endurantType a w) (fun _ =>
                tables.binaryTypedTableCosted .inst b a w)) (fun _ =>
              tables.unaryTypedTableCosted .endurant b w)))) := by
  change
    allFinCosted T (fun a =>
      allFinCosted T (fun b =>
        allFinCosted W (fun w =>
          Costed.implies (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurantType a w) 8)
            (fun _ =>
              Costed.tick ((tables.verifiedLookups W T agreement).binary .inst b a w) 11)) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant b w) 8)))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAxSubKindSortal_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxSubKindSortalCosted M =
      allFinCosted T (fun a =>
        allFinCosted T (fun b =>
          allFinCosted W (fun w =>
            Costed.implies (Costed.andThen (tables.binaryTypedTableCosted .sub a b w) (fun _ =>
                tables.unaryTypedTableCosted .kind b w)) (fun _ =>
              tables.unaryTypedTableCosted .sortal a w)))) := by
  change
    allFinCosted T (fun a =>
      allFinCosted T (fun b =>
        allFinCosted W (fun w =>
          Costed.implies (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub a b w) 11)
            (fun _ =>
              Costed.tick ((tables.verifiedLookups W T agreement).unary .kind b w) 8)) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .sortal a w) 8)))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAxNonSortalUp_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxNonSortalUpCosted M =
      allFinCosted T (fun a =>
        allFinCosted T (fun b =>
          allFinCosted W (fun w =>
            Costed.implies (Costed.andThen (tables.unaryTypedTableCosted .nonSortal a w) (fun _ =>
                tables.binaryTypedTableCosted .sub a b w)) (fun _ =>
              tables.unaryTypedTableCosted .nonSortal b w)))) := by
  change
    allFinCosted T (fun a =>
      allFinCosted T (fun b =>
        allFinCosted W (fun w =>
          Costed.implies (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .nonSortal a w) 8)
            (fun _ =>
              Costed.tick ((tables.verifiedLookups W T agreement).binary .sub a b w) 11)) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .nonSortal b w) 8)))) = _
  simp only [verifiedBinaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAxKindStable_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxKindStableCosted M =
      allFinCosted T (fun x => allFinCosted W (fun w => allFinCosted W (fun v =>
        Costed.implies (tables.unaryTypedTableCosted .kind x w)
          (fun _ => tables.unaryTypedTableCosted .kind x v)))) := by
  exact thingWorldWorldImp_eq_countedTables
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) tables agreement
    .kind .kind

theorem compiledAxDistanceIdentity_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxDistanceIdentityCosted M =
      allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun r => allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (Costed.tick (decide (x = y)) 1) (fun _ =>
              tables.ternaryTypedTableCosted .distance x y r w)) (fun _ =>
            tables.unaryTypedTableCosted .distanceZero r w))))) := by
  change allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun r => allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (Costed.tick (decide (x = y)) 1) (fun _ =>
              Costed.tick ((tables.verifiedLookups W T agreement).ternary .distance x y r w) 14)) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).unary .distanceZero r w) 8))))) = _
  simp only [verifiedTernaryBlock_eq_counted, verifiedUnaryBlock_eq_counted]

theorem compiledAxDistanceSymmetry_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxDistanceSymmetryCosted M =
      allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun r => allFinCosted W (fun w =>
          Costed.implies (tables.ternaryTypedTableCosted .distance x y r w) (fun _ =>
            tables.ternaryTypedTableCosted .distance y x r w))))) := by
  change allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun r => allFinCosted W (fun w =>
          Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).ternary .distance x y r w) 14) (fun _ =>
            Costed.tick ((tables.verifiedLookups W T agreement).ternary .distance y x r w) 14))))) = _
  simp only [verifiedTernaryBlock_eq_counted]

theorem compiledAxDistanceTriangle_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxDistanceTriangleCosted M =
      allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun z => allFinCosted T (fun r0 =>
          allFinCosted T (fun r1 => allFinCosted T (fun r2 =>
            allFinCosted T (fun s => allFinCosted W (fun w =>
              Costed.implies
                (Costed.andThen
                  (Costed.andThen
                    (Costed.andThen
                      (tables.ternaryTypedTableCosted .distance x y r0 w) (fun _ =>
                        tables.ternaryTypedTableCosted .distance y z r1 w)) (fun _ =>
                      tables.ternaryTypedTableCosted .distance x z r2 w)) (fun _ =>
                    tables.ternaryTypedTableCosted .distanceSum r0 r1 s w)) (fun _ =>
                tables.binaryTypedTableCosted .distanceGreaterEq s r2 w))))))))) := by
  change allFinCosted T (fun x => allFinCosted T (fun y =>
        allFinCosted T (fun z => allFinCosted T (fun r0 =>
          allFinCosted T (fun r1 => allFinCosted T (fun r2 =>
            allFinCosted T (fun s => allFinCosted W (fun w =>
              Costed.implies
                (Costed.andThen
                  (Costed.andThen
                    (Costed.andThen
                      (Costed.tick ((tables.verifiedLookups W T agreement).ternary .distance x y r0 w) 14) (fun _ =>
                        Costed.tick ((tables.verifiedLookups W T agreement).ternary .distance y z r1 w) 14)) (fun _ =>
                      Costed.tick ((tables.verifiedLookups W T agreement).ternary .distance x z r2 w) 14)) (fun _ =>
                    Costed.tick ((tables.verifiedLookups W T agreement).ternary .distanceSum r0 r1 s w) 14)) (fun _ =>
                Costed.tick ((tables.verifiedLookups W T agreement).binary .distanceGreaterEq s r2 w) 11))))))))) = _
  simp only [verifiedTernaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

/-! ## Existential dependence and inherence

Dependence scans all worlds; independence checks failure of dependence in both
directions. The current-world parameter does not restrict either scan.
Axiom 66 first tests moment classification, then searches for an instance of
the proposed bearer, and checks concrete-individual classification only if
that search fails. Axiom 67 stops at the first pair of distinct bearers.
The equations bind the shared predicate once in definition checks 63 and 64.
-/

theorem compiledExistentialDependence_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.existentialDependenceCosted M x y w =
      allFinCosted W (fun v =>
        Costed.implies (tables.unaryTypedTableCosted .ex x v)
          (fun _ => tables.unaryTypedTableCosted .ex y v)) := by
  change
    allFinCosted W (fun v =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8)) = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledExistentialIndependence_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (tables.unaryTypedTableCosted .ex x v)
          (fun _ => tables.unaryTypedTableCosted .ex y v))
    let independence := fun x y : Fin T =>
      Costed.andThen (dependence x y).not (fun _ => (dependence y x).not)
    Checker.existentialIndependenceCosted M x y w =
      independence x y := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let independence := fun x y : Fin T =>
      Costed.andThen (dependence x y).not (fun _ => (dependence y x).not)
    independence x y = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledAx63_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (tables.unaryTypedTableCosted .ex x v)
          (fun _ => tables.unaryTypedTableCosted .ex y v))
    Checker.checkAx63Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun _w =>
        Costed.bind (dependence x y) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun _w =>
        Costed.bind (dependence x y) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledAx64_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (tables.unaryTypedTableCosted .ex x v)
          (fun _ => tables.unaryTypedTableCosted .ex y v))
    let independence := fun x y : Fin T =>
      Costed.andThen (dependence x y).not (fun _ => (dependence y x).not)
    Checker.checkAx64Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun _w =>
        Costed.bind (independence x y) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let independence := fun x y : Fin T =>
      Costed.andThen (dependence x y).not (fun _ => (dependence y x).not)
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun _w =>
        Costed.bind (independence x y) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledAx65_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (tables.unaryTypedTableCosted .ex x v)
          (fun _ => tables.unaryTypedTableCosted .ex y v))
    Checker.checkAx65Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .inheresIn x y w) (fun _ => dependence x y)))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x y w) 11) (fun _ => dependence x y)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx66Consequent_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.ax66ConsequentCosted M x y w =
      Costed.andThen (tables.unaryTypedTableCosted .moment x w) (fun _ =>
        Costed.orElse
          (anyFinCosted W (fun v => anyFinCosted T (fun z =>
            tables.binaryTypedTableCosted .inst z y v)))
          (fun _ => tables.unaryTypedTableCosted .concreteIndividual y w)) := by
  change
    Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .moment x w) 8) (fun _ =>
        Costed.orElse
          (anyFinCosted W (fun v => anyFinCosted T (fun z =>
            Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z y v) 11)))
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .concreteIndividual y w) 8)) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx66_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx66Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .inheresIn x y w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .moment x w) (fun _ =>
        Costed.orElse
          (anyFinCosted W (fun v => anyFinCosted T (fun z =>
            tables.binaryTypedTableCosted .inst z y v)))
          (fun _ => tables.unaryTypedTableCosted .concreteIndividual y w)))))) := by
  change
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x y w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .moment x w) 8) (fun _ =>
        Costed.orElse
          (anyFinCosted W (fun v => anyFinCosted T (fun z =>
            Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z y v) 11)))
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .concreteIndividual y w) 8)))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx67_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx67Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted T (fun z =>
        allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (tables.binaryTypedTableCosted .inheresIn x y w)
              (fun _ => tables.binaryTypedTableCosted .inheresIn x z w))
            (fun _ => Costed.tick (decide (y = z)) 1))))) := by
  change
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted T (fun z =>
        allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x y w) 11)
              (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11))
            (fun _ => Costed.tick (decide (y = z)) 1))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

/-! ## External dependence

External dependence requires dependence on the proposed object and separation
of that object from every bearer. The two separation scans have independent
witnesses. Failed dependence skips the bearer scan; a failed first separation
scan skips the reverse scan. Mode classification also guards its witness search.
These equations connect both values and source-operation costs to dense reads.
-/

theorem compiledExistenceDifference_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    Checker.existenceDifferenceCosted M x y =
      difference x y := by
  change
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    difference x y = _
  simp only [verifiedUnaryBlock_eq_counted]

theorem compiledExternalSeparation_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y z : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    Checker.externalSeparationCosted M x y z w =
      separation x y z w := by
  change
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    separation x y z w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledExternallyDependent_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    Checker.externallyDependentCosted M x y w =
      external x y w := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    external x y w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledExternallyDependentMode_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .mode x w) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    Checker.externallyDependentModeCosted M x w =
      mode x w := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    mode x w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx69_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    Checker.checkAx69Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.bind (external x y w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.bind (external x y w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx70_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .mode x w) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    Checker.checkAx70Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.bind (mode x w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer)))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.bind (mode x w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

/-! ## Foundations and qua-individuals

The foundation query checks a candidate before its uniqueness scan. The shared
foundation query searches for an object related to both inputs, in that order.
Checks 73 and 78 include the reflexive part shortcut, whose cost depends on
coordinate equality. The equations expose every nested scan and bind the
shared qua-individual search once in axiom 74.
-/

theorem compiledExistsUniqueFoundedBy_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let unique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .foundedBy x y w) (fun _ =>
          allFinCosted T (fun z =>
            Costed.implies (tables.binaryTypedTableCosted .foundedBy x z w) (fun _ =>
              Costed.tick (decide (z = y)) 1))))
    Checker.existsUniqueFoundedByCosted M x w =
      unique x w := by
  change
    let unique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x y w) 11) (fun _ =>
          allFinCosted T (fun z =>
            Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x z w) 11) (fun _ =>
              Costed.tick (decide (z = y)) 1))))
    unique x w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledSameFoundation_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (tables.binaryTypedTableCosted .foundedBy x u w) (fun _ =>
          tables.binaryTypedTableCosted .foundedBy y u w))
    Checker.sameFoundationCosted M x y w =
      same x y w := by
  change
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x u w) 11) (fun _ =>
          Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy y u w) 11))
    same x y w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledQuaIndividualExists_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => tables.binaryTypedTableCosted .quaIndividualOf x y w)
    Checker.quaIndividualExistsCosted M x w =
      qua x w := by
  change
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x y w) 11)
    qua x w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx71_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .mode x w) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    Checker.checkAx71Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .foundedBy x y w) (fun _ =>
          Costed.andThen
            (Costed.orElse (mode x w) (fun _ => tables.unaryTypedTableCosted .relator x w))
            (fun _ => tables.unaryTypedTableCosted .perdurant y w))))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x y w) 11) (fun _ =>
          Costed.andThen
            (Costed.orElse (mode x w) (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .relator x w) 8))
            (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .perdurant y w) 8))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx72_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .mode x w) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    let unique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .foundedBy x y w) (fun _ =>
          allFinCosted T (fun z =>
            Costed.implies (tables.binaryTypedTableCosted .foundedBy x z w) (fun _ =>
              Costed.tick (decide (z = y)) 1))))
    Checker.checkAx72Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (mode x w) (fun _ => unique x w))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    let unique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x y w) 11) (fun _ =>
          allFinCosted T (fun z =>
            Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x z w) 11) (fun _ =>
              Costed.tick (decide (z = y)) 1))))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (mode x w) (fun _ => unique x w))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx73_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .mode x w) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (tables.binaryTypedTableCosted .foundedBy x u w) (fun _ =>
          tables.binaryTypedTableCosted .foundedBy y u w))
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1) (fun _ =>
        tables.binaryTypedTableCosted .part x y w)
    Checker.checkAx73Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (tables.binaryTypedTableCosted .quaIndividualOf x y w) (fun _ =>
          allFinCosted T (fun z =>
            Costed.iff (part z x w) (fun _ =>
              Costed.andThen
                (Costed.andThen (mode z w) (fun _ =>
                  tables.binaryTypedTableCosted .inheresIn z y w))
                (fun _ => same z x w))))))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x u w) 11) (fun _ =>
          Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy y u w) 11))
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x y w) 11) (fun _ =>
          allFinCosted T (fun z =>
            Costed.iff (part z x w) (fun _ =>
              Costed.andThen
                (Costed.andThen (mode z w) (fun _ =>
                  Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z y w) 11))
                (fun _ => same z x w))))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted, reflexiveBinaryBlock_eq_counted]

theorem compiledAx74_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => tables.binaryTypedTableCosted .quaIndividualOf x y w)
    Checker.checkAx74Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.bind (qua x w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer)))) := by
  change
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x y w) 11)
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.bind (qua x w) (fun answer =>
          Costed.iff (Costed.pure answer) (fun _ => Costed.pure answer)))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx75_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        tables.unaryTypedTableCosted .ex y v))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (tables.unaryTypedTableCosted .ex x v) (fun _ =>
        (tables.unaryTypedTableCosted .ex y v).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (tables.binaryTypedTableCosted .inheresIn x z w) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .mode x w) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => tables.binaryTypedTableCosted .quaIndividualOf x y w)
    Checker.checkAx75Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (qua x w) (fun _ => mode x w))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let difference := fun x y : Fin T => anyFinCosted W (fun v =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8) (fun _ =>
        (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8).not))
    let separation := fun (x y z : Fin T) (w : Fin W) =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn x z w) 11) (fun _ =>
        Costed.andThen (difference y z) (fun _ => difference z y))
    let external := fun (x y : Fin T) (w : Fin W) =>
      Costed.andThen (dependence x y) (fun _ =>
        allFinCosted T (fun z => separation x y z w))
    let mode := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .mode x w) 8) (fun _ =>
        anyFinCosted T (fun y => external x y w))
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x y w) 11)
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (qua x w) (fun _ => mode x w))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx76_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx76Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted T (fun z =>
        allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (tables.binaryTypedTableCosted .quaIndividualOf x y w)
              (fun _ => tables.binaryTypedTableCosted .quaIndividualOf x z w))
            (fun _ => Costed.tick (decide (y = z)) 1))))) := by
  change
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted T (fun z =>
        allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x y w) 11)
              (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x z w) 11))
            (fun _ => Costed.tick (decide (y = z)) 1))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx77_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let unique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .foundedBy x y w) (fun _ =>
          allFinCosted T (fun z =>
            Costed.implies (tables.binaryTypedTableCosted .foundedBy x z w) (fun _ =>
              Costed.tick (decide (z = y)) 1))))
    Checker.checkAx77Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (tables.unaryTypedTableCosted .relator x w)
          (fun _ => unique x w))) := by
  change
    let unique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x y w) 11) (fun _ =>
          allFinCosted T (fun z =>
            Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x z w) 11) (fun _ =>
              Costed.tick (decide (z = y)) 1))))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .relator x w) 8)
          (fun _ => unique x w))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx78_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (tables.binaryTypedTableCosted .foundedBy x u w) (fun _ =>
          tables.binaryTypedTableCosted .foundedBy y u w))
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1) (fun _ =>
        tables.binaryTypedTableCosted .part x y w)
    Checker.checkAx78Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen (tables.unaryTypedTableCosted .relator x w)
            (fun _ => part y x w))
          (fun _ => same x y w)))) := by
  change
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x u w) 11) (fun _ =>
          Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy y u w) 11))
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .relator x w) 8)
            (fun _ => part y x w))
          (fun _ => same x y w)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted, reflexiveBinaryBlock_eq_counted]

/-! ## Relators, mediation, and characterization

Relator characterization checks for a proper part, then compatibility of all
part pairs, then inclusion of every compatible candidate. This last condition
is unrelated to computing inherence paths. Mediation reads a qua-individual
edge before part membership. Type characterization checks witnesses in both
directions and requires a unique bearer for each moment instance.
-/

theorem compiledProperPartExists_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let proper := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => tables.binaryTypedTableCosted .properPart y x w)
    Checker.properPartExistsCosted M x w =
      proper x w := by
  change
    let proper := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart y x w) 11)
    proper x w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledMediationWitness_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    let mediation := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun z =>
        Costed.andThen (tables.binaryTypedTableCosted .quaIndividualOf z y w)
          (fun _ => part z x w))
    Checker.mediationWitnessCosted M x y w =
      mediation x y w := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    let mediation := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun z =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf z y w) 11)
          (fun _ => part z x w))
    mediation x y w = _
  simp only [verifiedBinaryBlock_eq_counted, reflexiveBinaryBlock_eq_counted]

theorem compiledExistsUniqueInstInheres_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (z t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let unique := fun (z t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .inst y t w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inheresIn z y w) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies
                (Costed.andThen (tables.binaryTypedTableCosted .inst other t w)
                  (fun _ => tables.binaryTypedTableCosted .inheresIn z other w))
                (fun _ => Costed.tick (decide (other = y)) 1)))))
    Checker.existsUniqueInstInheresCosted M z t w =
      unique z t w := by
  change
    let unique := fun (z t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z y w) 11) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies
                (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst other t w) 11)
                  (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z other w) 11))
                (fun _ => Costed.tick (decide (other = y)) 1)))))
    unique z t w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx81MomentWitness_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (m x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let moment := fun (m x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .inst y m w)
          (fun _ => tables.binaryTypedTableCosted .inheresIn y x w))
    Checker.ax81MomentWitnessCosted M m x w =
      moment m x w := by
  change
    let moment := fun (m x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y m w) 11)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11))
    moment m x w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx79_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (tables.unaryTypedTableCosted .ex x v)
        (fun _ => tables.unaryTypedTableCosted .ex y v))
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => tables.binaryTypedTableCosted .quaIndividualOf x y w)
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (tables.binaryTypedTableCosted .foundedBy x u w)
          (fun _ => tables.binaryTypedTableCosted .foundedBy y u w))
    let proper := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => tables.binaryTypedTableCosted .properPart y x w)
    let compatible := fun (y z : Fin T) (w : Fin W) =>
      Costed.andThen (qua y w) (fun _ =>
        Costed.andThen (qua z w) (fun _ =>
          Costed.andThen (same y z w) (fun _ =>
            Costed.andThen (dependence y z) (fun _ => dependence z y))))
    let pairs := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => allFinCosted T (fun z =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .properPart y x w)
            (fun _ => tables.binaryTypedTableCosted .properPart z x w))
          (fun _ => compatible y z w)))
    let closure := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => allFinCosted T (fun z =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .properPart y x w) (fun _ =>
            Costed.andThen (qua z w) (fun _ =>
              Costed.andThen (same y z w) (fun _ =>
                Costed.andThen (dependence y z) (fun _ => dependence z y)))))
          (fun _ => tables.binaryTypedTableCosted .properPart z x w)))
    let relatorCharacterization := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (proper x w)
        (fun _ => Costed.andThen (pairs x w) (fun _ => closure x w))
    Checker.checkAx79Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .relator x w)
          (fun _ => relatorCharacterization x w))) := by
  change
    let dependence := fun x y : Fin T => allFinCosted W (fun v =>
      Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).unary .ex x v) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .ex y v) 8))
    let qua := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x y w) 11)
    let same := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun u =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy x u w) 11)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .foundedBy y u w) 11))
    let proper := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y => Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart y x w) 11)
    let compatible := fun (y z : Fin T) (w : Fin W) =>
      Costed.andThen (qua y w) (fun _ =>
        Costed.andThen (qua z w) (fun _ =>
          Costed.andThen (same y z w) (fun _ =>
            Costed.andThen (dependence y z) (fun _ => dependence z y))))
    let pairs := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => allFinCosted T (fun z =>
        Costed.implies
          (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart y x w) 11)
            (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart z x w) 11))
          (fun _ => compatible y z w)))
    let closure := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => allFinCosted T (fun z =>
        Costed.implies
          (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart y x w) 11) (fun _ =>
            Costed.andThen (qua z w) (fun _ =>
              Costed.andThen (same y z w) (fun _ =>
                Costed.andThen (dependence y z) (fun _ => dependence z y)))))
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .properPart z x w) 11)))
    let relatorCharacterization := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (proper x w)
        (fun _ => Costed.andThen (pairs x w) (fun _ => closure x w))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .relator x w) 8)
          (fun _ => relatorCharacterization x w))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx80_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let part := fun (x y : Fin T) (w : Fin W) =>
      Costed.orElse (Costed.tick (x == y) 1)
        (fun _ => tables.binaryTypedTableCosted .part x y w)
    let mediation := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun z =>
        Costed.andThen (tables.binaryTypedTableCosted .quaIndividualOf z y w)
          (fun _ => part z x w))
    Checker.checkAx80Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (tables.binaryTypedTableCosted .mediates x y w) (fun _ =>
          Costed.andThen
            (Costed.andThen (tables.unaryTypedTableCosted .relator x w)
              (fun _ => tables.unaryTypedTableCosted .endurant y w))
            (fun _ => mediation x y w))))) := by
  change
    let part := fun (x y : Fin T) (w : Fin W) =>
      Checker.reflexiveBinaryQueryCosted
        (fun a b v => a == b || (tables.verifiedLookups W T agreement).binary .part a b v)
        x y w
    let mediation := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun z =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf z y w) 11)
          (fun _ => part z x w))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).binary .mediates x y w) 11) (fun _ =>
          Costed.andThen
            (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .relator x w) 8)
              (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant y w) 8))
            (fun _ => mediation x y w))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted, reflexiveBinaryBlock_eq_counted]

theorem compiledAxQuaIndividualOfEndurant_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAxQuaIndividualOfEndurantCosted M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .quaIndividualOf x y w)
          (fun _ => tables.unaryTypedTableCosted .endurant y w)))) := by
  change
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .quaIndividualOf x y w) 11)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .endurant y w) 8)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx81_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let moment := fun (m x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .inst y m w)
          (fun _ => tables.binaryTypedTableCosted .inheresIn y x w))
    let unique := fun (z t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .inst y t w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inheresIn z y w) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies
                (Costed.andThen (tables.binaryTypedTableCosted .inst other t w)
                  (fun _ => tables.binaryTypedTableCosted .inheresIn z other w))
                (fun _ => Costed.tick (decide (other = y)) 1)))))
    let typeInstances := fun (t m : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .inst x t w)
          (fun _ => moment m x w))
    let momentInstances := fun (t m : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .inst x m w)
          (fun _ => unique x t w))
    Checker.checkAx81Costed M =
      allFinCosted T (fun t => allFinCosted T (fun m => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .characterization t m w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .endurantType t w) (fun _ =>
            Costed.andThen (tables.unaryTypedTableCosted .momentType m w) (fun _ =>
              Costed.andThen (typeInstances t m w) (fun _ => momentInstances t m w))))))) := by
  change
    let moment := fun (m x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y m w) 11)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11))
    let unique := fun (z t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z y w) 11) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies
                (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst other t w) 11)
                  (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z other w) 11))
                (fun _ => Costed.tick (decide (other = y)) 1)))))
    let typeInstances := fun (t m : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
          (fun _ => moment m x w))
    let momentInstances := fun (t m : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x m w) 11)
          (fun _ => unique x t w))
    allFinCosted T (fun t => allFinCosted T (fun m => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .characterization t m w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .endurantType t w) 8) (fun _ =>
            Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .momentType m w) 8) (fun _ =>
              Costed.andThen (typeInstances t m w) (fun _ => momentInstances t m w))))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx82_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let unique := fun (z t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .inst y t w) (fun _ =>
          Costed.andThen (tables.binaryTypedTableCosted .inheresIn z y w) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies
                (Costed.andThen (tables.binaryTypedTableCosted .inst other t w)
                  (fun _ => tables.binaryTypedTableCosted .inheresIn z other w))
                (fun _ => Costed.tick (decide (other = y)) 1)))))
    let momentInstances := fun (t m : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .inst x m w)
          (fun _ => unique x t w))
    Checker.checkAx82Costed M =
      allFinCosted T (fun t => allFinCosted T (fun q => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen (tables.binaryTypedTableCosted .characterization t q w)
            (fun _ => tables.unaryTypedTableCosted .qualityType q w))
          (fun _ => momentInstances t q w)))) := by
  change
    let unique := fun (z t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y t w) 11) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z y w) 11) (fun _ =>
            allFinCosted T (fun other =>
              Costed.implies
                (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst other t w) 11)
                  (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z other w) 11))
                (fun _ => Costed.tick (decide (other = y)) 1)))))
    let momentInstances := fun (t m : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x m w) 11)
          (fun _ => unique x t w))
    allFinCosted T (fun t => allFinCosted T (fun q => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .characterization t q w) 11)
            (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType q w) 8))
          (fun _ => momentInstances t q w)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

/-! ## Quality structures and proper subset

Structure membership and type association each nest a structure's own
quality-type uniqueness test inside an outer uniqueness search. The equations
include all repeated calls. Proper subset first tests containment and searches
for a strict difference only when containment succeeds.
-/

theorem compiledQualityStructure_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    Checker.qualityStructureCosted M x w =
      qualitySpace x w := by
  change
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    qualitySpace x w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledNonEmptySet_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (s : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let nonempty := fun (s : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x => tables.binaryTypedTableCosted .memberOf x s w)
    Checker.nonEmptySetCosted M s w =
      nonempty s w := by
  change
    let nonempty := fun (s : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x => Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11)
    nonempty s w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledQualityStructureMember_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let member := fun (x s : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace s w)
        (fun _ => tables.binaryTypedTableCosted .memberOf x s w)
    let memberUnique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun s =>
        Costed.andThen (member x s w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (member x other w)
              (fun _ => Costed.tick (decide (other = s)) 1))))
    Checker.existsUniqueQualityStructureMemberCosted M x w =
      memberUnique x w := by
  change
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let member := fun (x s : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace s w)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11)
    let memberUnique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun s =>
        Costed.andThen (member x s w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (member x other w)
              (fun _ => Costed.tick (decide (other = s)) 1))))
    memberUnique x w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledQualityStructureForType_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let typeCandidate := fun (t x : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace x w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let typeUnique := fun (t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (typeCandidate t x w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (typeCandidate t other w)
              (fun _ => Costed.tick (decide (other = x)) 1))))
    Checker.existsUniqueQualityStructureForTypeCosted M t w =
      typeUnique t w := by
  change
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let typeCandidate := fun (t x : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace x w)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let typeUnique := fun (t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (typeCandidate t x w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (typeCandidate t other w)
              (fun _ => Costed.tick (decide (other = x)) 1))))
    typeUnique t w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledProperSubset_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (s t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let contained := fun (s t : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .memberOf x s w)
          (fun _ => tables.binaryTypedTableCosted .memberOf x t w))
    let difference := fun (s t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (tables.binaryTypedTableCosted .memberOf x t w)
          (fun _ => (tables.binaryTypedTableCosted .memberOf x s w).not))
    let subset := fun (s t : Fin T) (w : Fin W) =>
      Costed.andThen (contained s t w) (fun _ => difference s t w)
    Checker.properSubsetCosted M s t w =
      subset s t w := by
  change
    let contained := fun (s t : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x t w) 11))
    let difference := fun (s t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x t w) 11)
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11).not))
    let subset := fun (s t : Fin T) (w : Fin W) =>
      Costed.andThen (contained s t w) (fun _ => difference s t w)
    subset s t w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx86_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let nonempty := fun (s : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x => tables.binaryTypedTableCosted .memberOf x s w)
    Checker.checkAx86Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (qualitySpace x w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .set_ x w)
            (fun _ => nonempty x w)))) := by
  change
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let nonempty := fun (s : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x => Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11)
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (qualitySpace x w) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .set_ x w) 8)
            (fun _ => nonempty x w)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx87_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let member := fun (x s : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace s w)
        (fun _ => tables.binaryTypedTableCosted .memberOf x s w)
    let memberUnique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun s =>
        Costed.andThen (member x s w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (member x other w)
              (fun _ => Costed.tick (decide (other = s)) 1))))
    Checker.checkAx87Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .quale x w)
          (fun _ => memberUnique x w))) := by
  change
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let member := fun (x s : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace s w)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11)
    let memberUnique := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun s =>
        Costed.andThen (member x s w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (member x other w)
              (fun _ => Costed.tick (decide (other = s)) 1))))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .quale x w) 8)
          (fun _ => memberUnique x w))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx88_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    Checker.checkAx88Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (qualitySpace x w) (fun _ =>
          Costed.orElse (tables.unaryTypedTableCosted .qualityDomain x w)
            (fun _ => tables.unaryTypedTableCosted .qualityDimension x w)))) := by
  change
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.iff (qualitySpace x w) (fun _ =>
          Costed.orElse (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityDomain x w) 8)
            (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityDimension x w) 8)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx90_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let contained := fun (s t : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (tables.binaryTypedTableCosted .memberOf x s w)
          (fun _ => tables.binaryTypedTableCosted .memberOf x t w))
    let difference := fun (s t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (tables.binaryTypedTableCosted .memberOf x t w)
          (fun _ => (tables.binaryTypedTableCosted .memberOf x s w).not))
    let subset := fun (s t : Fin T) (w : Fin W) =>
      Costed.andThen (contained s t w) (fun _ => difference s t w)
    Checker.checkAx90Costed M =
      allFinCosted T (fun s => allFinCosted T (fun t =>
        allFinCosted T (fun s' => allFinCosted T (fun t' => allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (tables.binaryTypedTableCosted .associatedWith s t w) (fun _ =>
              Costed.andThen (tables.binaryTypedTableCosted .associatedWith s' t' w) (fun _ =>
                Costed.andThen (tables.binaryTypedTableCosted .sub t' t w)
                  (fun _ => (tables.binaryTypedTableCosted .sub t t' w).not))))
            (fun _ => subset s' s w)))))) := by
  change
    let contained := fun (s t : Fin T) (w : Fin W) =>
      allFinCosted T (fun x =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x t w) 11))
    let difference := fun (s t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x t w) 11)
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf x s w) 11).not))
    let subset := fun (s t : Fin T) (w : Fin W) =>
      Costed.andThen (contained s t w) (fun _ => difference s t w)
    allFinCosted T (fun s => allFinCosted T (fun t =>
        allFinCosted T (fun s' => allFinCosted T (fun t' => allFinCosted W (fun w =>
          Costed.implies
            (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith s t w) 11) (fun _ =>
              Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith s' t' w) 11) (fun _ =>
                Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t' t w) 11)
                  (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .sub t t' w) 11).not))))
            (fun _ => subset s' s w)))))) = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx91_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let typeCandidate := fun (t x : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace x w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w)
    let typeUnique := fun (t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (typeCandidate t x w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (typeCandidate t other w)
              (fun _ => Costed.tick (decide (other = x)) 1))))
    Checker.checkAx91Costed M =
      allFinCosted T (fun t => allFinCosted W (fun w =>
        Costed.iff (tables.unaryTypedTableCosted .qualityType t w) (fun _ =>
          Costed.andThen (tables.unaryTypedTableCosted .intrinsicMomentType t w)
            (fun _ => typeUnique t w)))) := by
  change
    let candidate := fun (x t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let qualitySpace := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t =>
        Costed.andThen (candidate x t w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (candidate x other w)
              (fun _ => Costed.tick (decide (other = t)) 1))))
    let typeCandidate := fun (t x : Fin T) (w : Fin W) =>
      Costed.andThen (qualitySpace x w)
        (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11)
    let typeUnique := fun (t : Fin T) (w : Fin W) =>
      anyFinCosted T (fun x =>
        Costed.andThen (typeCandidate t x w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (typeCandidate t other w)
              (fun _ => Costed.tick (decide (other = x)) 1))))
    allFinCosted T (fun t => allFinCosted W (fun w =>
        Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8) (fun _ =>
          Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .intrinsicMomentType t w) 8)
            (fun _ => typeUnique t w)))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

/-! ## Counted tuple projection

Projection may return its input tuple after a failed slot check, an absent
cell, or an invalid stored result. Equal returned tuples do not imply equal
costs. The internal model therefore retains the counted projection operation.
Table agreement connects its compact proof-facing value to the dense value,
while its cost already comes from that same dense evaluator.
-/

theorem compiledProjection_eq_countedTable (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    {n : Nat} (p : Fin T) (i : Fin n) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    M.tupleProjectionCosted p i w = tables.tupleProjectionTypedTableCosted p i.val w := by
  change (tables.verifiedLookups W T agreement).projectionCosted p i.val w = _
  unfold FactTables.verifiedLookups
  rw [agreement]
  rfl

/-! ## Quality values

A value witness is tested before its uniqueness scan. Axiom 94 first tests
instantiation, then association, then membership. Its left-associated
conjunction still charges the outer branch when instantiation fails.
The equalities preserve these branches and every visited table read.
-/

theorem compiledUniqueHasValue_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let uniqueValue := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .hasValue x y w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (tables.binaryTypedTableCosted .hasValue x other w)
              (fun _ => Costed.tick (decide (other = y)) 1))))
    Checker.existsUniqueHasValueCosted M x w = uniqueValue x w := by
  change
    let uniqueValue := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .hasValue x y w) 11) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .hasValue x other w) 11)
              (fun _ => Costed.tick (decide (other = y)) 1))))
    uniqueValue x w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledQualityValueWitness_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let witness := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t => anyFinCosted T (fun s =>
        Costed.andThen
          (Costed.andThen (tables.binaryTypedTableCosted .inst x t w)
            (fun _ => tables.binaryTypedTableCosted .associatedWith s t w))
          (fun _ => tables.binaryTypedTableCosted .memberOf y s w)))
    Checker.ax94WitnessCosted M x y w = witness x y w := by
  change
    let witness := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t => anyFinCosted T (fun s =>
        Costed.andThen
          (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith s t w) 11)))
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf y s w) 11))))
    witness x y w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledAx92_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    Checker.checkAx92Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .hasValue x y w) (fun _ =>
          Costed.andThen (quality x w)
            (fun _ => tables.unaryTypedTableCosted .quale y w))))) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11))
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .hasValue x y w) 11) (fun _ =>
          Costed.andThen (quality x w)
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).unary .quale y w) 8)))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx93_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let uniqueValue := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (tables.binaryTypedTableCosted .hasValue x y w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (tables.binaryTypedTableCosted .hasValue x other w)
              (fun _ => Costed.tick (decide (other = y)) 1))))
    Checker.checkAx93Costed M = allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (quality x w) (fun _ => uniqueValue x w))) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11))
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let uniqueValue := fun (x : Fin T) (w : Fin W) =>
      anyFinCosted T (fun y =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .hasValue x y w) 11) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .hasValue x other w) 11)
              (fun _ => Costed.tick (decide (other = y)) 1))))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (quality x w) (fun _ => uniqueValue x w))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx94_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let witness := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t => anyFinCosted T (fun s =>
        Costed.andThen
          (Costed.andThen (tables.binaryTypedTableCosted .inst x t w)
            (fun _ => tables.binaryTypedTableCosted .associatedWith s t w))
          (fun _ => tables.binaryTypedTableCosted .memberOf y s w)))
    Checker.checkAx94Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .hasValue x y w)
          (fun _ => witness x y w)))) := by
  change
    let witness := fun (x y : Fin T) (w : Fin W) =>
      anyFinCosted T (fun t => anyFinCosted T (fun s =>
        Costed.andThen
          (Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
            (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith s t w) 11)))
          (fun _ => (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf y s w) 11))))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .hasValue x y w) 11)
          (fun _ => witness x y w)))) = _
  simp only [verifiedBinaryBlock_eq_counted]

/-! ## Simple and complex qualities

Inherence is queried from candidate part to containing quality. Type tests
classify the type before visiting its instances. Each complex-quality test
retains both source occurrences of quality classification. These equalities
do not assume native sharing or a cache. Axiom 97 retains all five conjunction
branches even when an earlier operand is false.
-/

theorem compiledNoInheringThings_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    Checker.noInheringThingsCosted M x w =
      noInhering x w := by
  change
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    noInhering x w = _
  simp only [verifiedBinaryBlock_eq_counted]

theorem compiledSimpleQuality_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    Checker.simpleQualityCosted M x w =
      simple x w := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    simple x w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledComplexQuality_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    Checker.complexQualityCosted M x w =
      complex x w := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    complex x w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledSimpleQualityType_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let simpleType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (tables.binaryTypedTableCosted .inst x t w)
            (fun _ => simple x w)))
    Checker.simpleQualityTypeCosted M t w =
      simpleType t w := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let simpleType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
            (fun _ => simple x w)))
    simpleType t w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledComplexQualityType_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let complexType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (tables.binaryTypedTableCosted .inst x t w)
            (fun _ => complex x w)))
    Checker.complexQualityTypeCosted M t w =
      complexType t w := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let complexType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
            (fun _ => complex x w)))
    complexType t w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx97Antecedent_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) (x y z Y Z : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let antecedent := fun (x y z Y Z : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.andThen
          (Costed.andThen
            (Costed.andThen
              (Costed.andThen (complex x w)
                (fun _ => tables.binaryTypedTableCosted .inst y Y w))
              (fun _ => tables.binaryTypedTableCosted .inst z Z w))
            (fun _ => tables.binaryTypedTableCosted .inheresIn y x w))
          (fun _ => tables.binaryTypedTableCosted .inheresIn z x w))
        (fun _ => Costed.tick (decide (Y = Z)) 1)
    Checker.ax97AntecedentCosted M x y z Y Z w =
      antecedent x y z Y Z w := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let antecedent := fun (x y z Y Z : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.andThen
          (Costed.andThen
            (Costed.andThen
              (Costed.andThen (complex x w)
                (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y Y w) 11))
              (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z Z w) 11))
            (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11))
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z x w) 11))
        (fun _ => Costed.tick (decide (Y = Z)) 1)
    antecedent x y z Y Z w = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx95_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let simpleType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (tables.binaryTypedTableCosted .inst x t w)
            (fun _ => simple x w)))
    Checker.checkAx95Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .associatedWith x y w) (fun _ =>
          Costed.iff (tables.unaryTypedTableCosted .qualityDimension x w)
            (fun _ => simpleType y w))))) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let simpleType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
            (fun _ => simple x w)))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x y w) 11) (fun _ =>
          Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityDimension x w) 8)
            (fun _ => simpleType y w))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx96_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let complexType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (tables.unaryTypedTableCosted .qualityType t w) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (tables.binaryTypedTableCosted .inst x t w)
            (fun _ => complex x w)))
    Checker.checkAx96Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (tables.binaryTypedTableCosted .associatedWith x y w) (fun _ =>
          Costed.iff (tables.unaryTypedTableCosted .qualityDomain x w)
            (fun _ => complexType y w))))) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let complexType := fun (t : Fin T) (w : Fin W) =>
      Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityType t w) 8) (fun _ =>
        allFinCosted T (fun x =>
          Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
            (fun _ => complex x w)))
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .associatedWith x y w) 11) (fun _ =>
          Costed.iff (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityDomain x w) 8)
            (fun _ => complexType y w))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx97_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let antecedent := fun (x y z Y Z : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.andThen
          (Costed.andThen
            (Costed.andThen
              (Costed.andThen (complex x w)
                (fun _ => tables.binaryTypedTableCosted .inst y Y w))
              (fun _ => tables.binaryTypedTableCosted .inst z Z w))
            (fun _ => tables.binaryTypedTableCosted .inheresIn y x w))
          (fun _ => tables.binaryTypedTableCosted .inheresIn z x w))
        (fun _ => Costed.tick (decide (Y = Z)) 1)
    Checker.checkAx97Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted T (fun z =>
        allFinCosted T (fun Y => allFinCosted T (fun Z => allFinCosted W (fun w =>
          Costed.implies (antecedent x y z Y Z w)
            (fun _ => Costed.tick (decide (y = z)) 1))))))) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let antecedent := fun (x y z Y Z : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.andThen
          (Costed.andThen
            (Costed.andThen
              (Costed.andThen (complex x w)
                (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst y Y w) 11))
              (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst z Z w) 11))
            (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11))
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn z x w) 11))
        (fun _ => Costed.tick (decide (Y = Z)) 1)
    allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted T (fun z =>
        allFinCosted T (fun Y => allFinCosted T (fun Z => allFinCosted W (fun w =>
          Costed.implies (antecedent x y z Y Z w)
            (fun _ => Costed.tick (decide (y = z)) 1))))))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

theorem compiledAx98_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (tables.unaryTypedTableCosted .qualityKind t w)
          (fun _ => tables.binaryTypedTableCosted .inst x t w)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (tables.binaryTypedTableCosted .inheresIn y x w).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let parts := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y =>
        Costed.implies (tables.binaryTypedTableCosted .inheresIn y x w)
          (fun _ => simple y w))
    Checker.checkAx98Costed M =
      allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (complex x w) (fun _ => parts x w))) := by
  change
    let quality := fun (x : Fin T) (w : Fin W) =>
      let candidate := fun (t : Fin T) =>
        Costed.andThen (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityKind t w) 8)
          (fun _ => Costed.tick ((tables.verifiedLookups W T agreement).binary .inst x t w) 11)
      anyFinCosted T (fun t => Costed.andThen (candidate t) (fun _ =>
        allFinCosted T (fun other => Costed.implies (candidate other)
          (fun _ => Costed.tick (decide (other = t)) 1))))
    let noInhering := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y => (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11).not)
    let simple := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => noInhering x w)
    let complex := fun (x : Fin T) (w : Fin W) =>
      Costed.andThen (quality x w) (fun _ => (simple x w).not)
    let parts := fun (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun y =>
        Costed.implies (Costed.tick ((tables.verifiedLookups W T agreement).binary .inheresIn y x w) 11)
          (fun _ => simple y w))
    allFinCosted T (fun x => allFinCosted W (fun w =>
        Costed.implies (complex x w) (fun _ => parts x w))) = _
  simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]

/-! ## Product-family witness rows

Projection precedes the dimension-array read in the checker expression.
Association reads both dimension and type slots; characterization reads the
type slot again. The equalities retain those source operations and early exits.
-/

theorem compiledFamilyProjectionRows_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (pf : ProductFamilyWitness T W) (x : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.productFamilyProjectionRowsCosted M pf x w =
      allFinCosted T (fun p =>
        Costed.implies (tables.binaryTypedTableCosted .memberOf p x w) (fun _ =>
          allFinCosted pf.dimensionThings.size (fun i => do
            let component ← tables.tupleProjectionTypedTableCosted p i.val w
            let dimension ← Costed.tick pf.dimensionThings[i] 1
            tables.binaryTypedTableCosted .memberOf component dimension w))) := by
  simp only [Checker.productFamilyProjectionRowsCosted, Checker.allThingsEvalCosted,
    Checker.allFinEvalCosted, Checker.productFamilyDimensions,
    ← verifiedBinaryBlock_eq_counted tables W T agreement]
  apply congrArg (allFinCosted T)
  funext p
  apply congrArg (Costed.implies
    (Costed.tick ((tables.verifiedLookups W T agreement).binary .memberOf p x w) 11))
  funext _
  apply congrArg (allFinCosted pf.dimensionThings.size)
  funext i
  rw [compiledProjection_eq_countedTable tables W T hw ht agreement valid worlds things p i w]
  rfl

theorem compiledFamilyAssociationRows_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.productFamilyAssociationRowsCosted M pf t w =
      allFinCosted pf.dimensionThings.size (fun i =>
        Costed.andThen (do
          let dimension ← Costed.tick (Checker.productFamilyDimensions pf i) 1
          let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
          tables.binaryTypedTableCosted .associatedWith dimension qualityType w)
          (fun _ => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            tables.binaryTypedTableCosted .characterization t qualityType w)) := by
  simp only [Checker.productFamilyAssociationRowsCosted, Checker.allFinEvalCosted,
    ← verifiedBinaryBlock_eq_counted tables W T agreement,
    Bind.bind, Costed.bind, Costed.tick]

  rfl

theorem compiledFamilyCoverageRows_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.productFamilyCoverageRowsCosted M pf t w =
      allFinCosted T (fun u =>
        Costed.implies (tables.binaryTypedTableCosted .characterization t u w) (fun _ =>
          anyFinCosted pf.dimensionThings.size (fun i => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            Costed.tick (decide (u = qualityType)) 1))) := by
  simp only [Checker.productFamilyCoverageRowsCosted, Checker.allThingsEvalCosted,
    Checker.anyFinEvalCosted,
    ← verifiedBinaryBlock_eq_counted tables W T agreement,
    Bind.bind, Costed.bind, Costed.tick]

  rfl

theorem compiledFamilyWitness_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (pf : ProductFamilyWitness T W) (x t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let projection := fun (pf : ProductFamilyWitness T W) (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun p =>
        Costed.implies (tables.binaryTypedTableCosted .memberOf p x w) (fun _ =>
          allFinCosted pf.dimensionThings.size (fun i => do
            let component ← tables.tupleProjectionTypedTableCosted p i.val w
            let dimension ← Costed.tick pf.dimensionThings[i] 1
            tables.binaryTypedTableCosted .memberOf component dimension w)))
    let association := fun (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) =>
      allFinCosted pf.dimensionThings.size (fun i =>
        Costed.andThen (do
          let dimension ← Costed.tick (Checker.productFamilyDimensions pf i) 1
          let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
          tables.binaryTypedTableCosted .associatedWith dimension qualityType w)
          (fun _ => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            tables.binaryTypedTableCosted .characterization t qualityType w))
    let coverage := fun (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) =>
      allFinCosted T (fun u =>
        Costed.implies (tables.binaryTypedTableCosted .characterization t u w) (fun _ =>
          anyFinCosted pf.dimensionThings.size (fun i => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            Costed.tick (decide (u = qualityType)) 1)))
    let witness := fun (pf : ProductFamilyWitness T W) (x t : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.andThen
          (Costed.andThen (Checker.productFamilyHeaderCosted pf x t w)
            (fun _ => projection pf x w))
          (fun _ => association pf t w))
        (fun _ => coverage pf t w)
    Checker.productFamilyWitnessCosted M pf x t w =
      witness pf x t w := by
  simp only [Checker.productFamilyWitnessCosted,
    compiledFamilyProjectionRows_eq_countedTables,
    compiledFamilyAssociationRows_eq_countedTables,
    compiledFamilyCoverageRows_eq_countedTables]
  rfl

theorem compiledFamilySearch_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x t : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let projection := fun (pf : ProductFamilyWitness T W) (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun p =>
        Costed.implies (tables.binaryTypedTableCosted .memberOf p x w) (fun _ =>
          allFinCosted pf.dimensionThings.size (fun i => do
            let component ← tables.tupleProjectionTypedTableCosted p i.val w
            let dimension ← Costed.tick pf.dimensionThings[i] 1
            tables.binaryTypedTableCosted .memberOf component dimension w)))
    let association := fun (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) =>
      allFinCosted pf.dimensionThings.size (fun i =>
        Costed.andThen (do
          let dimension ← Costed.tick (Checker.productFamilyDimensions pf i) 1
          let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
          tables.binaryTypedTableCosted .associatedWith dimension qualityType w)
          (fun _ => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            tables.binaryTypedTableCosted .characterization t qualityType w))
    let coverage := fun (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) =>
      allFinCosted T (fun u =>
        Costed.implies (tables.binaryTypedTableCosted .characterization t u w) (fun _ =>
          anyFinCosted pf.dimensionThings.size (fun i => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            Costed.tick (decide (u = qualityType)) 1)))
    let witness := fun (pf : ProductFamilyWitness T W) (x t : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.andThen
          (Costed.andThen (Checker.productFamilyHeaderCosted pf x t w)
            (fun _ => projection pf x w))
          (fun _ => association pf t w))
        (fun _ => coverage pf t w)
    Checker.productFamilySearchCosted M x t w =
      anyFinCosted M.productFamilies.size (fun i => do
        let pf ← Costed.tick M.productFamilies[i] 1
        witness pf x t w) := by
  dsimp only
  unfold Checker.productFamilySearchCosted Checker.anyFinEvalCosted
  apply congrArg (anyFinCosted _)
  funext i
  rw [compiledFamilyWitness_eq_countedTables tables W T hw ht agreement valid worlds things
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things).productFamilies[i] x t w]
  rfl

theorem compiledAx99_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    let projection := fun (pf : ProductFamilyWitness T W) (x : Fin T) (w : Fin W) =>
      allFinCosted T (fun p =>
        Costed.implies (tables.binaryTypedTableCosted .memberOf p x w) (fun _ =>
          allFinCosted pf.dimensionThings.size (fun i => do
            let component ← tables.tupleProjectionTypedTableCosted p i.val w
            let dimension ← Costed.tick pf.dimensionThings[i] 1
            tables.binaryTypedTableCosted .memberOf component dimension w)))
    let association := fun (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) =>
      allFinCosted pf.dimensionThings.size (fun i =>
        Costed.andThen (do
          let dimension ← Costed.tick (Checker.productFamilyDimensions pf i) 1
          let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
          tables.binaryTypedTableCosted .associatedWith dimension qualityType w)
          (fun _ => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            tables.binaryTypedTableCosted .characterization t qualityType w))
    let coverage := fun (pf : ProductFamilyWitness T W) (t : Fin T) (w : Fin W) =>
      allFinCosted T (fun u =>
        Costed.implies (tables.binaryTypedTableCosted .characterization t u w) (fun _ =>
          anyFinCosted pf.dimensionThings.size (fun i => do
            let qualityType ← Costed.tick (Checker.productFamilyTypes pf i) 1
            Costed.tick (decide (u = qualityType)) 1)))
    let witness := fun (pf : ProductFamilyWitness T W) (x t : Fin T) (w : Fin W) =>
      Costed.andThen
        (Costed.andThen
          (Costed.andThen (Checker.productFamilyHeaderCosted pf x t w)
            (fun _ => projection pf x w))
          (fun _ => association pf t w))
        (fun _ => coverage pf t w)
    Checker.checkAx99Costed M =
      allFinCosted T (fun x => allFinCosted T (fun t => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen (tables.unaryTypedTableCosted .qualityDomain x w)
            (fun _ => tables.binaryTypedTableCosted .associatedWith x t w))
          (fun _ =>
      anyFinCosted M.productFamilies.size (fun i => do
        let pf ← Costed.tick M.productFamilies[i] 1
        witness pf x t w))))) := by
  dsimp only
  unfold Checker.checkAx99Costed Checker.allThingsEvalCosted Checker.allWorldsEvalCosted
  change allFinCosted T (fun (x : Fin T) => allFinCosted T (fun (t : Fin T) =>
    allFinCosted W (fun (w : Fin W) => Costed.implies
      (Checker.ax99AntecedentCosted
        (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) x t w)
      (fun _ => Checker.productFamilySearchCosted
        (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) x t w)))) = _
  apply congrArg (allFinCosted T)
  funext x
  apply congrArg (allFinCosted T)
  funext t
  apply congrArg (allFinCosted W)
  funext w
  rw [compiledFamilySearch_eq_countedTables tables W T hw ht agreement valid worlds things x t w]
  have ha : Checker.ax99AntecedentCosted
      (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things) x t w =
      Costed.andThen (tables.unaryTypedTableCosted .qualityDomain x w)
        (fun _ => tables.binaryTypedTableCosted .associatedWith x t w) := by
    change Costed.andThen
      (Costed.tick ((tables.verifiedLookups W T agreement).unary .qualityDomain x w) 8)
      (fun _ => Costed.tick
        ((tables.verifiedLookups W T agreement).binary .associatedWith x t w) 11) = _
    simp only [verifiedUnaryBlock_eq_counted, verifiedBinaryBlock_eq_counted]
  rw [ha]

/-! ## Distance witnesses and life-of equivalence

Distance candidates start their uniqueness scan only after a successful read.
Life-of equivalence evaluates its right operand for either left-hand value.
The nested overlap test retains the cheaper self case. These equalities expand
the checker calls into the same counted table operations used by the compiler.
-/

theorem compiledCommonQualityStructure_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.commonQualityStructureCosted M x y w =
      anyFinCosted T (fun z =>
        Costed.andThen (tables.binaryTypedTableCosted .memberOf x z w)
          (fun _ => tables.binaryTypedTableCosted .memberOf y z w)) := by
  simp only [Checker.commonQualityStructureCosted, Checker.anyThingsEvalCosted,
    ← verifiedBinaryBlock_eq_counted tables W T agreement]
  rfl

theorem compiledAx100_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx100Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted T (fun r =>
        allFinCosted W (fun w =>
          Costed.implies (tables.ternaryTypedTableCosted .distance x y r w) (fun _ =>
            Costed.andThen
              (Costed.andThen (tables.unaryTypedTableCosted .quale x w)
                (fun _ => tables.unaryTypedTableCosted .quale y w))
              (fun _ => anyFinCosted T (fun z =>
                Costed.andThen (tables.binaryTypedTableCosted .memberOf x z w)
                  (fun _ => tables.binaryTypedTableCosted .memberOf y z w)))))))) := by
  simp only [Checker.checkAx100Costed, Checker.ax100ConsequentCosted,
    Checker.commonQualityStructureCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, Checker.anyThingsEvalCosted,
    ← verifiedUnaryBlock_eq_counted tables W T agreement,
    ← verifiedBinaryBlock_eq_counted tables W T agreement,
    ← verifiedTernaryBlock_eq_counted tables W T agreement]
  rfl

theorem compiledDistanceUniqueFor_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y r : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.distanceUniqueForCosted M x y r w =
      allFinCosted T (fun other =>
        Costed.implies (tables.ternaryTypedTableCosted .distance x y other w)
          (fun _ => Costed.tick (decide (other = r)) 1)) := by
  simp only [Checker.distanceUniqueForCosted, Checker.allThingsEvalCosted,
    ← verifiedTernaryBlock_eq_counted tables W T agreement]
  rfl

theorem compiledUniqueDistance_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.existsUniqueDistanceCosted M x y w =
      anyFinCosted T (fun r =>
        Costed.andThen (tables.ternaryTypedTableCosted .distance x y r w) (fun _ =>
          allFinCosted T (fun other =>
            Costed.implies (tables.ternaryTypedTableCosted .distance x y other w)
              (fun _ => Costed.tick (decide (other = r)) 1)))) := by
  simp only [Checker.existsUniqueDistanceCosted, Checker.distanceWitnessCosted,
    Checker.distanceUniqueForCosted, Checker.anyThingsEvalCosted,
    Checker.allThingsEvalCosted, ← verifiedTernaryBlock_eq_counted tables W T agreement]
  rfl

theorem compiledAx101_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx101Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.implies
          (Costed.andThen (tables.unaryTypedTableCosted .quale x w)
            (fun _ => tables.unaryTypedTableCosted .quale y w))
          (fun _ => anyFinCosted T (fun r =>
            Costed.andThen (tables.ternaryTypedTableCosted .distance x y r w) (fun _ =>
              allFinCosted T (fun other =>
                Costed.implies (tables.ternaryTypedTableCosted .distance x y other w)
                  (fun _ => Costed.tick (decide (other = r)) 1)))))))) := by
  simp only [Checker.checkAx101Costed, Checker.ax101AntecedentCosted,
    Checker.existsUniqueDistanceCosted, Checker.distanceWitnessCosted,
    Checker.distanceUniqueForCosted, Checker.allThingsEvalCosted,
    Checker.allWorldsEvalCosted, Checker.anyThingsEvalCosted,
    ← verifiedUnaryBlock_eq_counted tables W T agreement,
    ← verifiedTernaryBlock_eq_counted tables W T agreement]
  rfl

theorem compiledLifeOverlapRows_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things)
    (x y : Fin T) (w : Fin W) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.ax103OverlapRowsCosted M x y w =
      allFinCosted T (fun z =>
        Costed.iff
          (Costed.orElse (Costed.tick (z == x) 1)
            (fun _ => tables.binaryTypedTableCosted .overlap z x w))
          (fun _ => Costed.andThen (tables.unaryTypedTableCosted .perdurant z w)
            (fun _ => tables.binaryTypedTableCosted .manifests z y w))) := by
  simp only [← reflexiveBinaryBlock_eq_counted tables W T agreement]
  simp only [Checker.ax103OverlapRowsCosted, Checker.allThingsEvalCosted,
    ← verifiedUnaryBlock_eq_counted tables W T agreement,
    ← verifiedBinaryBlock_eq_counted tables W T agreement]
  rfl

theorem compiledAx103_eq_countedTables (tables : FactTables) (W T : Nat)
    (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    let M := tables.toFiniteModel4Cached W T hw ht agreement valid worlds things
    Checker.checkAx103Costed M =
      allFinCosted T (fun x => allFinCosted T (fun y => allFinCosted W (fun w =>
        Costed.iff (tables.binaryTypedTableCosted .lifeOf x y w) (fun _ =>
          Costed.andThen
            (Costed.andThen (tables.unaryTypedTableCosted .perdurant x w)
              (fun _ => tables.unaryTypedTableCosted .endurant y w))
            (fun _ => allFinCosted T (fun z =>
              Costed.iff
                (Costed.orElse (Costed.tick (z == x) 1)
                  (fun _ => tables.binaryTypedTableCosted .overlap z x w))
                (fun _ => Costed.andThen (tables.unaryTypedTableCosted .perdurant z w)
                  (fun _ => tables.binaryTypedTableCosted .manifests z y w)))))))) := by
  simp only [← reflexiveBinaryBlock_eq_counted tables W T agreement]
  simp only [Checker.checkAx103Costed, Checker.ax103ConsequentCosted,
    Checker.ax103OverlapRowsCosted, Checker.allThingsEvalCosted, Checker.allWorldsEvalCosted,
    ← verifiedUnaryBlock_eq_counted tables W T agreement,
    ← verifiedBinaryBlock_eq_counted tables W T agreement]
  rfl

/-! ## Relations defined by their axioms

The finite signature defines disjointness, complete coverage, partitioning,
and categorization by axioms 105–108's right-hand sides. Their soundness proofs
therefore justify constant-true checks for every finite model. No table read
occurs here. The registry loop still charges each visited entry, and validation
of user-written derived assertions has its own counted producer.
-/

theorem definitionChecks_eq_pure (M : FiniteModel4) :
    Checker.checkAx105Costed M = ⟨true, 0⟩ ∧
    Checker.checkAx106Costed M = ⟨true, 0⟩ ∧
    Checker.checkAx107Costed M = ⟨true, 0⟩ ∧
    Checker.checkAx108Costed M = ⟨true, 0⟩ := ⟨rfl, rfl, rfl, rfl⟩

end LeanUfo.UFO.DSL.Complexity
