import LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Unique
import Mathlib.Tactic.Ring

/-!
# Derived-assertion diagnostics

Before axiom certification, the elaborator checks user-written derived facts
against the compiled finite model. This module selects the first failed
assertion in source and scope-world order, then explains that failure.
These checks and reports are separate from the axiom-diagnostic dispatcher.
Both selection and report construction have operational cost bounds. The
production entry points erase costs from that same execution. A proved
nine-row limit preserves all current reports under the default output cap.

The analyzer reuses the axiom analyzer's relation queries and renderers.
It does not introduce another interpretation of those shared predicates.
-/

open Lean

namespace LeanUfo.UFO.DSL

open private
  hasPossibleInstance
  hasPossibleInstanceCosted hasPossibleInstanceCosted_value hasPossibleInstanceCosted_cost_le
  genericFunctionalDependenceLookup
  genericFunctionalDependenceLookupCosted genericFunctionalDependenceLookupCosted_cost_le
  individualFunctionalDependenceLookup
  componentOfLookup
  genericConstitutionalDependenceLookup
  genericConstitutionalDependenceLookupCosted genericConstitutionalDependenceLookupCosted_cost_le
  constitutionLookup
  derivedUnaryLookup
  derivedBinaryLookup
  derivedUnaryLookupCosted derivedUnaryLookupCosted_cost_le
  derivedBinaryLookupCosted derivedBinaryLookupCosted_cost_le derivedLookupCostBound
  individualFunctionalDependenceLookupCosted individualFunctionalDependenceLookupCosted_cost_le
  componentOfLookupCosted componentOfLookupCosted_cost_le
  constitutionLookupCosted constitutionLookupCosted_cost_le
  renderThingPath
  indexedNameCosted indexedNameCosted_value indexedNameCosted_cost
  joinIndexedNamesCosted joinIndexedNamesCosted_value joinIndexedNamesCosted_cost_le
  firstExWithoutCosted firstExWithoutCosted_cost_le
  firstExternalIndependenceFailureCosted firstExternalIndependenceFailureCosted_cost_le
  firstExternalIndependenceFailure?
  firstExternallyDependentFailureReason
  firstExternallyDependentFailureReasonCosted firstExternallyDependentFailureReasonCosted_cost_le
  declaredExternalCandidatesCosted declaredExternalCandidatesCosted_cost_le
  renderExternallyDependentModeStatus
  renderExternallyDependentModeStatusCosted renderExternallyDependentModeStatusCosted_cost_le
  renderExternallyDependentModeStatusCosted_size_le externallyDependentModeStatusCostBound
  externallyDependentWitnessCostBound
  findDiagDomainCosted findDiagDomainCosted_value findDiagDomainCosted_cost_le
  foldDiagDomainCosted foldDiagDomainCosted_value foldDiagDomainCosted_cost_le
  foldDiagDomainCosted_firstSome_value
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

/-!
## Name resolution and numeric predicates

These queries operate on finite coordinates. Their value proofs state when
the dense execution agrees with the relation used by the semantic checker.
The named dispatcher below resolves source references before calling them.
-/

/-- Find the first name whose rendered spelling matches the reference.
A visited entry costs a guarded array read (three), name rendering (one),
and string comparison (one). The shared search adds four control operations.
Name characters and allocator work are outside the primitive-call model. -/
private def thingIndexByStringCosted (names : Array Name) (text : String) : Complexity.Costed (Option Nat) :=
  findDiagDomainCosted names.size fun i =>
    if h : i < names.size then
      Complexity.Costed.tick (names[i].toString == text) 5
    else Complexity.Costed.tick false 2

private theorem thingIndexByStringCosted_value (names : Array Name) (text : String) :
    (thingIndexByStringCosted names text).value = names.findIdx? (fun name => name.toString == text) := by
  rw [thingIndexByStringCosted, findDiagDomainCosted_value names.size _
    (fun i => if h : i < names.size then names[i].toString == text else false)
    (by intro i hi; simp [hi])]
  apply Option.ext
  intro i
  simp only [List.find?_range_eq_some, List.mem_range, Array.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hmatch, hi, hfirst⟩
    refine ⟨hi, ?_, ?_⟩
    · simpa [hi] using hmatch
    · intro j hj
      have h := hfirst j hj
      simpa [Nat.lt_trans hj hi] using h
  · rintro ⟨hi, hmatch, hfirst⟩
    refine ⟨?_, hi, ?_⟩
    · simpa [hi] using hmatch
    · intro j hj
      have h := hfirst j hj
      simpa [Nat.lt_trans hj hi] using h

private theorem thingIndexByStringCosted_cost_le (names : Array Name) (text : String) :
    (thingIndexByStringCosted names text).cost ≤ 9 * names.size := by
  have h := findDiagDomainCosted_cost_le names.size
    (fun i => if h : i < names.size then
      Complexity.Costed.tick (names[i].toString == text) 5
      else Complexity.Costed.tick false 2) 5 (by
        intro i hi
        simp [hi])
  simpa [thingIndexByStringCosted, Nat.mul_comm] using h

private def thingIndexByString? (thingNames : Array Name) (thing : String) : Option Nat :=
  (thingIndexByStringCosted thingNames thing).value

/-
Derived assertions are checked before certification as generated theorems.
When one fails, these evaluators reconstruct the same definition-like relation
from finite tables so the widget can report the false assertion in DSL terms.
-/
private def typeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) : Bool :=
  hasPossibleInstance worldCount thingCount tables thing

/-- Find the first thing related to a target at a world. Membership and
inherence use this same directed search. Its bound is `21T`: at most 17
operations per binary query and four for search control. -/
private def firstRelatedThingCosted
    (worldCount thingCount : Nat) (tables : FactTables) (relation : BinaryField) (x w : Nat) :
    Complexity.Costed (Option Nat) :=
  findDiagDomainCosted thingCount fun y =>
    Complexity.diagnosticBinaryCosted worldCount thingCount tables relation y x w

private theorem firstRelatedThingCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (relation : BinaryField) (x w : Nat) :
    (firstRelatedThingCosted worldCount thingCount tables relation x w).cost ≤ 21 * thingCount := by
  have h := findDiagDomainCosted_cost_le thingCount
    (fun y => Complexity.diagnosticBinaryCosted worldCount thingCount tables relation y x w)
    17 (by intro y hy; exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
  simpa [firstRelatedThingCosted, Nat.mul_comm] using h

private theorem firstRelatedThingCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (relation : BinaryField) (x : Fin thingCount) (w : Fin worldCount) :
    (firstRelatedThingCosted worldCount thingCount tables relation x w).value =
      (List.range thingCount).find? (fun y => tables.binaryLookup relation.toTableField y x w) := by
  apply findDiagDomainCosted_value
  intro y hy
  exact Complexity.diagnosticBinaryCosted_value _ _ _ agreement relation ⟨y, hy⟩ x w

private def nonEmptySetLookupCosted (W T : Nat) (tables : FactTables) (s w : Nat) :
    Complexity.Costed Bool :=
  (firstRelatedThingCosted W T tables .memberOf s w).bind fun member =>
    Complexity.Costed.tick member.isSome 1

private theorem nonEmptySetLookupCosted_cost_le (W T : Nat) (tables : FactTables) (s w : Nat) :
    (nonEmptySetLookupCosted W T tables s w).cost ≤ 21 * T + 1 := by
  simpa [nonEmptySetLookupCosted] using Nat.add_le_add_right
    (firstRelatedThingCosted_cost_le W T tables .memberOf s w) 1

private theorem nonEmptySetLookupCosted_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s : Fin T) (w : Fin W) :
    (nonEmptySetLookupCosted W T tables s w).value =
      ((List.range T).any fun x => tables.binaryLookup "memberOf" x s w) := by
  simp [nonEmptySetLookupCosted, firstRelatedThingCosted_value _ _ _ agreement .memberOf s w,
    List.isSome_find?, BinaryField.toTableField]

private def nonEmptySetLookup (W T : Nat) (tables : FactTables) (s w : Nat) : Bool :=
  (nonEmptySetLookupCosted W T tables s w).value

/-- Find a source related to the left target but not the right target.
Set inclusion uses membership for both relations. Categorization uses
instantiation on the left and specialization on the right. Only a left match
incurs the right query. The first difference ends the search. -/
private def firstRelationDifferenceCosted
    (W T : Nat) (tables : FactTables) (left right : BinaryField) (s t w : Nat) :
    Complexity.Costed (Option Nat) :=
  findDiagDomainCosted T fun x =>
    (Complexity.diagnosticBinaryCosted W T tables left x s w).andThen fun _ =>
      (Complexity.diagnosticBinaryCosted W T tables right x t w).not

/-- Two binary queries cost at most 34. A branch, negation, and four search
controls give at most 40 per candidate. Here `T` is the number of things. -/
private theorem firstRelationDifferenceCosted_cost_le
    (W T : Nat) (tables : FactTables) (left right : BinaryField) (s t w : Nat) :
    (firstRelationDifferenceCosted W T tables left right s t w).cost ≤ 40 * T := by
  have h := findDiagDomainCosted_cost_le T
    (fun x => (Complexity.diagnosticBinaryCosted W T tables left x s w).andThen fun _ =>
      (Complexity.diagnosticBinaryCosted W T tables right x t w).not) 36 (by
      intro x hx
      exact Complexity.Costed.andThen_cost_le _ _ 17 18
        (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
        (by
          simpa using Nat.add_le_add_right
            (Complexity.diagnosticBinaryCosted_cost_le W T tables right x t w) 1))
  simpa [firstRelationDifferenceCosted, Nat.mul_comm] using h

private theorem firstRelationDifferenceCosted_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (left right : BinaryField) (s t : Fin T) (w : Fin W) :
    (firstRelationDifferenceCosted W T tables left right s t w).value =
      (List.range T).find? (fun x => tables.binaryLookup left.toTableField x s w &&
        !tables.binaryLookup right.toTableField x t w) := by
  apply findDiagDomainCosted_value
  intro x hx
  rw [Complexity.Costed.andThen_value, Complexity.Costed.not_value,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement left ⟨x, hx⟩ s w,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement right ⟨x, hx⟩ t w]
  rfl

private def subsetLookupCosted (W T : Nat) (tables : FactTables) (s t w : Nat) :
    Complexity.Costed Bool :=
  (firstRelationDifferenceCosted W T tables .memberOf .memberOf s t w).bind fun failure =>
    Complexity.Costed.tick failure.isNone 1

private theorem subsetLookupCosted_cost_le (W T : Nat) (tables : FactTables) (s t w : Nat) :
    (subsetLookupCosted W T tables s t w).cost ≤ 40 * T + 1 := by
  simpa [subsetLookupCosted] using Nat.add_le_add_right
    (firstRelationDifferenceCosted_cost_le W T tables .memberOf .memberOf s t w) 1

private theorem subsetLookupCosted_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s t : Fin T) (w : Fin W) :
    (subsetLookupCosted W T tables s t w).value =
      !((List.range T).any fun x => tables.binaryLookup "memberOf" x s w &&
        !tables.binaryLookup "memberOf" x t w) := by
  simp [subsetLookupCosted,
    firstRelationDifferenceCosted_value _ _ _ agreement .memberOf .memberOf s t w,
    ← Option.not_isSome, List.isSome_find?, BinaryField.toTableField]

private def subsetLookup (W T : Nat) (tables : FactTables) (s t w : Nat) : Bool :=
  (subsetLookupCosted W T tables s t w).value

private def properSubsetLookupCosted (W T : Nat) (tables : FactTables) (s t w : Nat) :
    Complexity.Costed Bool :=
  (subsetLookupCosted W T tables s t w).andThen fun _ =>
    (firstRelationDifferenceCosted W T tables .memberOf .memberOf t s w).bind fun witness =>
      Complexity.Costed.tick witness.isSome 1

private theorem properSubsetLookupCosted_cost_le (W T : Nat) (tables : FactTables) (s t w : Nat) :
    (properSubsetLookupCosted W T tables s t w).cost ≤ 80 * T + 3 := by
  have h := Complexity.Costed.andThen_cost_le _
    (fun _ => (firstRelationDifferenceCosted W T tables .memberOf .memberOf t s w).bind
      fun witness => Complexity.Costed.tick witness.isSome 1) (40 * T + 1) (40 * T + 1)
    (subsetLookupCosted_cost_le W T tables s t w)
    (by
      simpa using Nat.add_le_add_right
        (firstRelationDifferenceCosted_cost_le W T tables .memberOf .memberOf t s w) 1)
  unfold properSubsetLookupCosted
  omega

private theorem properSubsetLookupCosted_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s t : Fin T) (w : Fin W) :
    (properSubsetLookupCosted W T tables s t w).value =
      (subsetLookup W T tables s t w &&
        ((List.range T).any fun x => tables.binaryLookup "memberOf" x t w &&
          !tables.binaryLookup "memberOf" x s w)) := by
  simp [properSubsetLookupCosted, subsetLookup,
    firstRelationDifferenceCosted_value _ _ _ agreement .memberOf .memberOf t s w,
    List.isSome_find?, BinaryField.toTableField]

private def properSubsetLookup (W T : Nat) (tables : FactTables) (s t w : Nat) : Bool :=
  (properSubsetLookupCosted W T tables s t w).value

private def properSubLookupCosted (W T : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed Bool :=
  (Complexity.diagnosticBinaryCosted W T tables .sub x y w).andThen fun _ =>
    (Complexity.diagnosticBinaryCosted W T tables .sub y x w).not

private theorem properSubLookupCosted_cost_le (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (properSubLookupCosted W T tables x y w).cost ≤ 36 := by
  apply Complexity.Costed.andThen_cost_le _ _ 17 18
  · exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _
  · simpa using Nat.add_le_add_right
      (Complexity.diagnosticBinaryCosted_cost_le W T tables .sub y x w) 1

private theorem properSubLookupCosted_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (properSubLookupCosted W T tables x y w).value =
      (tables.binaryLookup "sub" x y w && !tables.binaryLookup "sub" y x w) := by
  simp [properSubLookupCosted,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .sub x y w,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .sub y x w,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private def properSubLookup (W T : Nat) (tables : FactTables) (x y w : Nat) : Bool :=
  (properSubLookupCosted W T tables x y w).value

/-- Search for the first shared instance. The right query runs only for a
left instance. Two queries, one branch, and four search controls cost at most
39 per thing. Reports reuse this search to select the same witness. -/
private def firstSharedInstanceCosted (W T : Nat) (tables : FactTables) (t t' w : Nat) :
    Complexity.Costed (Option Nat) :=
  findDiagDomainCosted T fun x =>
    (Complexity.diagnosticBinaryCosted W T tables .inst x t w).andThen fun _ =>
      Complexity.diagnosticBinaryCosted W T tables .inst x t' w

private theorem firstSharedInstanceCosted_cost_le (W T : Nat) (tables : FactTables) (t t' w : Nat) :
    (firstSharedInstanceCosted W T tables t t' w).cost ≤ 39 * T := by
  have h := findDiagDomainCosted_cost_le T
    (fun x => (Complexity.diagnosticBinaryCosted W T tables .inst x t w).andThen fun _ =>
      Complexity.diagnosticBinaryCosted W T tables .inst x t' w) 35 (by
      intro x hx
      exact Complexity.Costed.andThen_cost_le _ _ 17 17
        (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
        (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _))
  simpa [firstSharedInstanceCosted, Nat.mul_comm] using h

private theorem firstSharedInstanceCosted_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t t' : Fin T) (w : Fin W) :
    (firstSharedInstanceCosted W T tables t t' w).value =
      (List.range T).find? (fun x => tables.binaryLookup "inst" x t w &&
        tables.binaryLookup "inst" x t' w) := by
  apply findDiagDomainCosted_value
  intro x hx
  rw [Complexity.Costed.andThen_value,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .inst ⟨x, hx⟩ t w,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .inst ⟨x, hx⟩ t' w]
  rfl

private def isDisjointWithLookupCosted (W T : Nat) (tables : FactTables) (t t' w : Nat) :
    Complexity.Costed Bool :=
  ((hasPossibleInstanceCosted W T tables t).andThen
    fun _ => hasPossibleInstanceCosted W T tables t').andThen fun _ =>
      (firstSharedInstanceCosted W T tables t t' w).bind fun shared =>
        Complexity.Costed.tick shared.isNone 1

private theorem isDisjointWithLookupCosted_cost_le (W T : Nat) (tables : FactTables) (t t' w : Nat) :
    (isDisjointWithLookupCosted W T tables t t' w).cost ≤
      2 * (W * (T * 19 + 2)) + 39 * T + 3 := by
  have htypes := Complexity.Costed.andThen_cost_le _ (fun _ => hasPossibleInstanceCosted W T tables t')
    (W * (T * 19 + 2)) (W * (T * 19 + 2))
    (hasPossibleInstanceCosted_cost_le W T tables t)
    (hasPossibleInstanceCosted_cost_le W T tables t')
  have h := Complexity.Costed.andThen_cost_le _
    (fun _ => (firstSharedInstanceCosted W T tables t t' w).bind fun shared =>
      Complexity.Costed.tick shared.isNone 1)
    (W * (T * 19 + 2) + 1 + W * (T * 19 + 2)) (39 * T + 1) htypes
    (by
      simpa using Nat.add_le_add_right (firstSharedInstanceCosted_cost_le W T tables t t' w) 1)
  unfold isDisjointWithLookupCosted
  omega

private theorem isDisjointWithLookupCosted_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t t' : Fin T) (w : Fin W) :
    (isDisjointWithLookupCosted W T tables t t' w).value =
      (typeLookup W T tables t && typeLookup W T tables t' &&
        !((List.range T).any fun x => tables.binaryLookup "inst" x t w &&
          tables.binaryLookup "inst" x t' w)) := by
  simp [isDisjointWithLookupCosted, typeLookup,
    firstSharedInstanceCosted_value _ _ _ agreement t t' w, ← Option.not_isSome, List.isSome_find?]

private def isDisjointWithLookup (W T : Nat) (tables : FactTables) (t t' w : Nat) : Bool :=
  (isDisjointWithLookupCosted W T tables t t' w).value

/-- Find an instance of `t` outside both covering types. Non-instances skip
both cover queries. A match in the first cover skips the second cover query.
Three queries (51), two branches, one negation, and search control (four)
give the bound `58T`. -/
private def firstCoveredInstanceFailureCosted (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) :
    Complexity.Costed (Option Nat) :=
  findDiagDomainCosted T fun x =>
    (Complexity.diagnosticBinaryCosted W T tables .inst x t w).andThen fun _ =>
      ((Complexity.diagnosticBinaryCosted W T tables .inst x t' w).orElse fun _ =>
        Complexity.diagnosticBinaryCosted W T tables .inst x t'' w).not

private theorem firstCoveredInstanceFailureCosted_cost_le
    (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) :
    (firstCoveredInstanceFailureCosted W T tables t t' t'' w).cost ≤ 58 * T := by
  have h := findDiagDomainCosted_cost_le T
    (fun x => (Complexity.diagnosticBinaryCosted W T tables .inst x t w).andThen fun _ =>
      ((Complexity.diagnosticBinaryCosted W T tables .inst x t' w).orElse fun _ =>
        Complexity.diagnosticBinaryCosted W T tables .inst x t'' w).not) 54 (by
      intro x hx
      apply Complexity.Costed.andThen_cost_le _ _ 17 36
      · exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _
      · have hc := Complexity.Costed.orElse_cost_le _
          (fun _ => Complexity.diagnosticBinaryCosted W T tables .inst x t'' w) 17 17
          (Complexity.diagnosticBinaryCosted_cost_le W T tables .inst x t' w)
          (Complexity.diagnosticBinaryCosted_cost_le W T tables .inst x t'' w)
        simpa using Nat.add_le_add_right hc 1)
  simpa [firstCoveredInstanceFailureCosted, Nat.mul_comm] using h

private theorem firstCoveredInstanceFailureCosted_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t t' t'' : Fin T) (w : Fin W) :
    (firstCoveredInstanceFailureCosted W T tables t t' t'' w).value =
      (List.range T).find? (fun x => tables.binaryLookup "inst" x t w &&
        !(tables.binaryLookup "inst" x t' w || tables.binaryLookup "inst" x t'' w)) := by
  apply findDiagDomainCosted_value
  intro x hx
  rw [Complexity.Costed.andThen_value, Complexity.Costed.not_value, Complexity.Costed.orElse_value,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .inst ⟨x, hx⟩ t w,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .inst ⟨x, hx⟩ t' w,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .inst ⟨x, hx⟩ t'' w]
  rfl

private def isCompletelyCoveredByLookupCosted (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) :
    Complexity.Costed Bool :=
  (firstCoveredInstanceFailureCosted W T tables t t' t'' w).bind fun failure =>
    Complexity.Costed.tick failure.isNone 1

private theorem isCompletelyCoveredByLookupCosted_cost_le
    (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) :
    (isCompletelyCoveredByLookupCosted W T tables t t' t'' w).cost ≤ 58 * T + 1 := by
  simpa [isCompletelyCoveredByLookupCosted] using Nat.add_le_add_right
    (firstCoveredInstanceFailureCosted_cost_le W T tables t t' t'' w) 1

private theorem isCompletelyCoveredByLookupCosted_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t t' t'' : Fin T) (w : Fin W) :
    (isCompletelyCoveredByLookupCosted W T tables t t' t'' w).value =
      !((List.range T).any fun x => tables.binaryLookup "inst" x t w &&
        !(tables.binaryLookup "inst" x t' w || tables.binaryLookup "inst" x t'' w)) := by
  simp [isCompletelyCoveredByLookupCosted,
    firstCoveredInstanceFailureCosted_value _ _ _ agreement t t' t'' w,
    ← Option.not_isSome, List.isSome_find?]

private def isCompletelyCoveredByLookup (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) : Bool :=
  (isCompletelyCoveredByLookupCosted W T tables t t' t'' w).value

private def isPartitionedIntoLookupCosted (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) :
    Complexity.Costed Bool :=
  (isCompletelyCoveredByLookupCosted W T tables t t' t'' w).andThen fun _ =>
    isDisjointWithLookupCosted W T tables t' t'' w

private theorem isPartitionedIntoLookupCosted_cost_le
    (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) :
    (isPartitionedIntoLookupCosted W T tables t t' t'' w).cost ≤
      2 * (W * (T * 19 + 2)) + 97 * T + 5 := by
  have h := Complexity.Costed.andThen_cost_le _
    (fun _ => isDisjointWithLookupCosted W T tables t' t'' w)
    (58 * T + 1) (2 * (W * (T * 19 + 2)) + 39 * T + 3)
    (isCompletelyCoveredByLookupCosted_cost_le W T tables t t' t'' w)
    (isDisjointWithLookupCosted_cost_le W T tables t' t'' w)
  unfold isPartitionedIntoLookupCosted
  omega

private theorem isPartitionedIntoLookupCosted_value (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) :
    (isPartitionedIntoLookupCosted W T tables t t' t'' w).value =
      (isCompletelyCoveredByLookup W T tables t t' t'' w && isDisjointWithLookup W T tables t' t'' w) := by
  simp [isPartitionedIntoLookupCosted, isCompletelyCoveredByLookup, isDisjointWithLookup]

private def isPartitionedIntoLookup (W T : Nat) (tables : FactTables) (t t' t'' w : Nat) : Bool :=
  (isPartitionedIntoLookupCosted W T tables t t' t'' w).value

/-- A category must have a possible instance. At the current world, each of
its instances must specialize the target. The counterexample search runs only
after possible typehood succeeds, and skips specialization for non-instances. -/
private def categorizesLookupCosted (W T : Nat) (tables : FactTables) (t1 t2 w : Nat) :
    Complexity.Costed Bool :=
  (hasPossibleInstanceCosted W T tables t1).andThen fun _ =>
    (firstRelationDifferenceCosted W T tables .inst .sub t1 t2 w).bind fun failure =>
      Complexity.Costed.tick failure.isNone 1

private theorem categorizesLookupCosted_cost_le (W T : Nat) (tables : FactTables) (t1 t2 w : Nat) :
    (categorizesLookupCosted W T tables t1 t2 w).cost ≤ W * (T * 19 + 2) + 40 * T + 2 := by
  have h := Complexity.Costed.andThen_cost_le _
    (fun _ => (firstRelationDifferenceCosted W T tables .inst .sub t1 t2 w).bind
      fun failure => Complexity.Costed.tick failure.isNone 1) (W * (T * 19 + 2)) (40 * T + 1)
    (hasPossibleInstanceCosted_cost_le W T tables t1)
    (by
      simpa using Nat.add_le_add_right
        (firstRelationDifferenceCosted_cost_le W T tables .inst .sub t1 t2 w) 1)
  unfold categorizesLookupCosted
  omega

private theorem categorizesLookupCosted_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t1 t2 : Fin T) (w : Fin W) :
    (categorizesLookupCosted W T tables t1 t2 w).value =
      (typeLookup W T tables t1 &&
        !((List.range T).any fun x => tables.binaryLookup "inst" x t1 w &&
          !tables.binaryLookup "sub" x t2 w)) := by
  simp [categorizesLookupCosted, typeLookup,
    firstRelationDifferenceCosted_value _ _ _ agreement .inst .sub t1 t2 w,
    ← Option.not_isSome, List.isSome_find?, BinaryField.toTableField]

private def categorizesLookup (W T : Nat) (tables : FactTables) (t1 t2 w : Nat) : Bool :=
  (categorizesLookupCosted W T tables t1 t2 w).value

/-- Quality and quality structure both require exactly one classified, related
thing. The relation query runs only when the classification holds. A second
match ends the search because later candidates cannot restore uniqueness. -/
private def uniqueRelatedThingCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    Complexity.Costed Bool :=
  (Complexity.uniqueIndexCosted thingCount fun y =>
    (Complexity.diagnosticUnaryCosted worldCount thingCount tables classification y w).andThen
      fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables relation x y w).bind
    fun found => Complexity.Costed.tick found.isSome 1

/-- Each candidate costs at most 12 for classification, one branch, and 17 for
the relation. Search control adds at most four per candidate and one final
test. Inspecting the returned option adds one, giving `34T + 2` for `T` things. -/
private theorem uniqueRelatedThingCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    (uniqueRelatedThingCosted worldCount thingCount tables classification relation x w).cost ≤
      34 * thingCount + 2 := by
  have h := Complexity.uniqueIndexCosted_cost_le thingCount
    (fun y =>
      (Complexity.diagnosticUnaryCosted worldCount thingCount tables classification y w).andThen
        fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables relation x y w)
    30 (by
      intro y hy
      exact Complexity.Costed.andThen_cost_le _ _ 12 17
        (Complexity.diagnosticUnaryCosted_cost_le _ _ _ _ _ _)
        (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _))
  simp only [uniqueRelatedThingCosted, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
  omega

/-- For valid coordinates and agreeing representations, the executed search
accepts exactly when the sparse relation has one classified match. The filter
is a mathematical specification, not an array constructed by the search. -/
private theorem uniqueRelatedThingCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (classification : UnaryField) (relation : BinaryField)
    (x : Fin thingCount) (w : Fin worldCount) :
    (uniqueRelatedThingCosted worldCount thingCount tables classification relation x w).value =
      (((List.range thingCount).filter fun y =>
        tables.unaryLookup classification.toTableField y w &&
          tables.binaryLookup relation.toTableField x y w).length == 1) := by
  have hfilter :
      ((List.range thingCount).filter fun y =>
        ((Complexity.diagnosticUnaryCosted worldCount thingCount tables classification y w).andThen
          fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables relation x y w).value) =
      ((List.range thingCount).filter fun y =>
        tables.unaryLookup classification.toTableField y w &&
          tables.binaryLookup relation.toTableField x y w) := by
    apply List.filter_congr
    intro y hy
    have hy' : y < thingCount := List.mem_range.mp hy
    rw [Complexity.Costed.andThen_value,
      Complexity.diagnosticUnaryCosted_value _ _ _ agreement classification ⟨y, hy'⟩ w,
      Complexity.diagnosticBinaryCosted_value _ _ _ agreement relation x ⟨y, hy'⟩ w]
    rfl
  simp only [uniqueRelatedThingCosted, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.uniqueIndexCosted_value, hfilter]
  generalize ((List.range thingCount).filter _) = witnesses
  cases witnesses with
  | nil => rfl
  | cons y rest => cases rest <;> simp

private def qualityLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (uniqueRelatedThingCosted worldCount thingCount tables .qualityKind .inst x w).value

private def qualityStructureLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (uniqueRelatedThingCosted worldCount thingCount tables .qualityType .associatedWith x w).value

private def simpleQualityLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Complexity.Costed Bool :=
  (uniqueRelatedThingCosted worldCount thingCount tables .qualityKind .inst x w).andThen fun _ =>
    (firstRelatedThingCosted worldCount thingCount tables .inheresIn x w).bind fun found =>
      Complexity.Costed.tick found.isNone 1

private def complexQualityLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Complexity.Costed Bool :=
  (uniqueRelatedThingCosted worldCount thingCount tables .qualityKind .inst x w).andThen fun _ =>
    (firstRelatedThingCosted worldCount thingCount tables .inheresIn x w).bind fun found =>
      Complexity.Costed.tick found.isSome 1

private theorem simpleQualityLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (simpleQualityLookupCosted worldCount thingCount tables x w).cost ≤ 55 * thingCount + 4 := by
  have h := Complexity.Costed.andThen_cost_le _
    (fun _ => (firstRelatedThingCosted worldCount thingCount tables .inheresIn x w).bind fun found =>
      Complexity.Costed.tick found.isNone 1) (34 * thingCount + 2) (21 * thingCount + 1)
    (uniqueRelatedThingCosted_cost_le worldCount thingCount tables .qualityKind .inst x w)
    (show ((firstRelatedThingCosted worldCount thingCount tables .inheresIn x w).bind fun found =>
      Complexity.Costed.tick found.isNone 1).cost ≤ 21 * thingCount + 1 by
      simpa using Nat.add_le_add_right
        (firstRelatedThingCosted_cost_le worldCount thingCount tables .inheresIn x w) 1)
  unfold simpleQualityLookupCosted
  omega

private theorem complexQualityLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (complexQualityLookupCosted worldCount thingCount tables x w).cost ≤ 55 * thingCount + 4 := by
  have h := Complexity.Costed.andThen_cost_le _
    (fun _ => (firstRelatedThingCosted worldCount thingCount tables .inheresIn x w).bind fun found =>
      Complexity.Costed.tick found.isSome 1) (34 * thingCount + 2) (21 * thingCount + 1)
    (uniqueRelatedThingCosted_cost_le worldCount thingCount tables .qualityKind .inst x w)
    (show ((firstRelatedThingCosted worldCount thingCount tables .inheresIn x w).bind fun found =>
      Complexity.Costed.tick found.isSome 1).cost ≤ 21 * thingCount + 1 by
      simpa using Nat.add_le_add_right
        (firstRelatedThingCosted_cost_le worldCount thingCount tables .inheresIn x w) 1)
  unfold complexQualityLookupCosted
  omega

private theorem simpleQualityLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x : Fin thingCount) (w : Fin worldCount) :
    (simpleQualityLookupCosted worldCount thingCount tables x w).value =
      (qualityLookup worldCount thingCount tables x w &&
        !((List.range thingCount).any fun y => tables.binaryLookup "inheresIn" y x w)) := by
  simp [simpleQualityLookupCosted, qualityLookup,
    firstRelatedThingCosted_value _ _ _ agreement .inheresIn x w, ← Option.not_isSome,
    List.isSome_find?, BinaryField.toTableField]

private theorem complexQualityLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x : Fin thingCount) (w : Fin worldCount) :
    (complexQualityLookupCosted worldCount thingCount tables x w).value =
      (qualityLookup worldCount thingCount tables x w &&
        ((List.range thingCount).any fun y => tables.binaryLookup "inheresIn" y x w)) := by
  simp [complexQualityLookupCosted, qualityLookup,
    firstRelatedThingCosted_value _ _ _ agreement .inheresIn x w, List.isSome_find?,
    BinaryField.toTableField]

private def simpleQualityLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (simpleQualityLookupCosted worldCount thingCount tables x w).value

private def complexQualityLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (complexQualityLookupCosted worldCount thingCount tables x w).value

/-- Return the first instance that violates the supplied condition. Non-instances
skip the condition, and the first violation ends the search. Quality-type checks
and reports share this search so that their counterexample order agrees. -/
private def firstInvalidInstanceCosted
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat)
    (condition : Nat → Complexity.Costed Bool) : Complexity.Costed (Option Nat) :=
  findDiagDomainCosted thingCount fun x =>
    (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x t w).andThen
      fun _ => (condition x).not

/-- For condition bound `P`, each candidate costs at most `P + 23`: the
instance query (17), its branch and negation (two), and search control (four).
The bound sums executed query and control costs as in Niu et al.'s compositional
cost semantics (POPL 2022, doi:10.1145/3498670). Skipped conditions add no cost. -/
private theorem firstInvalidInstanceCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat)
    (condition : Nat → Complexity.Costed Bool) (perItem : Nat)
    (bounded : ∀ x, x < thingCount → (condition x).cost ≤ perItem) :
    (firstInvalidInstanceCosted worldCount thingCount tables t w condition).cost ≤
      thingCount * (perItem + 23) := by
  have hsearch := findDiagDomainCosted_cost_le thingCount
    (fun x =>
      (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x t w).andThen
        fun _ => (condition x).not) (perItem + 19) (by
      intro x hx
      have h := Complexity.Costed.andThen_cost_le _ (fun _ => (condition x).not) 17 (perItem + 1)
        (Complexity.diagnosticBinaryCosted_cost_le worldCount thingCount tables .inst x t w)
        (by simpa using Nat.add_le_add_right (bounded x hx) 1)
      omega)
  simpa only [firstInvalidInstanceCosted, Nat.add_assoc] using hsearch

private theorem firstInvalidInstanceCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (t : Fin thingCount) (w : Fin worldCount) (condition : Nat → Complexity.Costed Bool) :
    (firstInvalidInstanceCosted worldCount thingCount tables t w condition).value =
      (List.range thingCount).find? (fun x =>
        tables.binaryLookup "inst" x t w && !(condition x).value) := by
  apply findDiagDomainCosted_value
  intro x hx
  rw [Complexity.Costed.andThen_value, Complexity.Costed.not_value,
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement .inst ⟨x, hx⟩ t w]
  rfl

private theorem firstInvalidInstance_simple_cost_le
    (W T : Nat) (tables : FactTables) (t w : Nat) :
    (firstInvalidInstanceCosted W T tables t w
      (fun x => simpleQualityLookupCosted W T tables x w)).cost ≤ T * (55 * T + 27) :=
  firstInvalidInstanceCosted_cost_le _ _ _ _ _ _ (55 * T + 4)
    (by intro x hx; exact simpleQualityLookupCosted_cost_le _ _ _ _ _)

private theorem firstInvalidInstance_complex_cost_le
    (W T : Nat) (tables : FactTables) (t w : Nat) :
    (firstInvalidInstanceCosted W T tables t w
      (fun x => complexQualityLookupCosted W T tables x w)).cost ≤ T * (55 * T + 27) :=
  firstInvalidInstanceCosted_cost_le _ _ _ _ _ _ (55 * T + 4)
    (by intro x hx; exact complexQualityLookupCosted_cost_le _ _ _ _ _)

/-- A quality type satisfies its instance condition when it has the required
classification and no violating instance. The classification check runs first. -/
private def qualityTypeInstancesCosted
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat)
    (condition : Nat → Complexity.Costed Bool) : Complexity.Costed Bool :=
  (Complexity.diagnosticUnaryCosted worldCount thingCount tables .qualityType t w).andThen fun _ =>
    (firstInvalidInstanceCosted worldCount thingCount tables t w condition).bind fun failure =>
      Complexity.Costed.tick failure.isNone 1

/-- Classification, its branch, and the final option test add at most 14 to
the search bound. A failed classification skips the whole instance search. -/
private theorem qualityTypeInstancesCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat)
    (condition : Nat → Complexity.Costed Bool) (perItem : Nat)
    (bounded : ∀ x, x < thingCount → (condition x).cost ≤ perItem) :
    (qualityTypeInstancesCosted worldCount thingCount tables t w condition).cost ≤
      thingCount * (perItem + 23) + 14 := by
  have hsearch := firstInvalidInstanceCosted_cost_le
    worldCount thingCount tables t w condition perItem bounded
  have h := Complexity.Costed.andThen_cost_le _
    (fun _ => (firstInvalidInstanceCosted worldCount thingCount tables t w condition).bind
      fun failure => Complexity.Costed.tick failure.isNone 1)
    12 (thingCount * (perItem + 23) + 1)
    (Complexity.diagnosticUnaryCosted_cost_le worldCount thingCount tables .qualityType t w)
    (by simpa using Nat.add_le_add_right hsearch 1)
  unfold qualityTypeInstancesCosted
  omega

private theorem qualityTypeInstancesCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (t : Fin thingCount) (w : Fin worldCount) (condition : Nat → Complexity.Costed Bool) :
    (qualityTypeInstancesCosted worldCount thingCount tables t w condition).value =
      (tables.unaryLookup "qualityType" t w &&
        !((List.range thingCount).any fun x =>
          tables.binaryLookup "inst" x t w && !(condition x).value)) := by
  simp [qualityTypeInstancesCosted,
    firstInvalidInstanceCosted_value _ _ _ agreement t w condition,
    Complexity.diagnosticUnaryCosted_value _ _ _ agreement .qualityType t w,
    FactTables.unaryTypedTable, ← Option.not_isSome, List.isSome_find?, UnaryField.toTableField]

private theorem qualityTypeInstances_simple_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat) :
    (qualityTypeInstancesCosted worldCount thingCount tables t w
      (fun x => simpleQualityLookupCosted worldCount thingCount tables x w)).cost ≤
        thingCount * (55 * thingCount + 27) + 14 := by
  exact qualityTypeInstancesCosted_cost_le _ _ _ _ _ _ (55 * thingCount + 4)
    (by intro x hx; exact simpleQualityLookupCosted_cost_le _ _ _ _ _)

private theorem qualityTypeInstances_complex_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat) :
    (qualityTypeInstancesCosted worldCount thingCount tables t w
      (fun x => complexQualityLookupCosted worldCount thingCount tables x w)).cost ≤
        thingCount * (55 * thingCount + 27) + 14 := by
  exact qualityTypeInstancesCosted_cost_le _ _ _ _ _ _ (55 * thingCount + 4)
    (by intro x hx; exact complexQualityLookupCosted_cost_le _ _ _ _ _)

private def simpleQualityTypeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat) : Bool :=
  (qualityTypeInstancesCosted worldCount thingCount tables t w
    (fun x => simpleQualityLookupCosted worldCount thingCount tables x w)).value

private def complexQualityTypeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t w : Nat) : Bool :=
  (qualityTypeInstancesCosted worldCount thingCount tables t w
    (fun x => complexQualityLookupCosted worldCount thingCount tables x w)).value

/-- A bearer must be non-moment and reachable from the given moment. The
closure query runs only after the non-moment test succeeds. Its row width is
the explicit thing count, matching the diagnostic model's coordinates. -/
private def ultimateBearerOfLookupCosted
    (W T : Nat) (tables : FactTables) (b m w : Nat) : Complexity.Costed Bool :=
  (Complexity.diagnosticUnaryCosted W T tables .moment b w).not.andThen fun _ =>
    tables.momentOfClosureCosted T w m b

private theorem ultimateBearerOfLookupCosted_cost_le
    (W T : Nat) (tables : FactTables) (b m w : Nat) :
    (ultimateBearerOfLookupCosted W T tables b m w).cost ≤ 20 := by
  apply Complexity.Costed.andThen_cost_le _ _ 13 6
  · simpa using Nat.add_le_add_right
      (Complexity.diagnosticUnaryCosted_cost_le W T tables .moment b w) 1
  · exact FactTables.momentOfClosureCosted_cost_le _ _ _ _ _

private theorem ultimateBearerOfLookupCosted_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (b m : Fin T) (w : Fin W) :
    (ultimateBearerOfLookupCosted W T tables b m w).value =
      (!tables.unaryLookup "moment" b w && tables.momentOfClosure T w m b) := by
  simp [ultimateBearerOfLookupCosted,
    Complexity.diagnosticUnaryCosted_value _ _ _ agreement .moment b w,
    FactTables.unaryTypedTable, UnaryField.toTableField, FactTables.momentOfClosureCosted_value]

private def ultimateBearerOfLookup (W T : Nat) (tables : FactTables) (b m w : Nat) : Bool :=
  (ultimateBearerOfLookupCosted W T tables b m w).value

/-!
## Named-predicate dispatch

The specification preserves source-facing decisions, including unknown names
and fields. The counted dispatcher composes name resolution with the selected
numeric predicate; its bound includes both kinds of work.
-/

/-- Cost-free specification of the named assertion decision. Its cases fix
the supported spellings, fallback behavior, and left-to-right name resolution.
The production entry point below erases the counted dispatcher. -/
private def evalNamedDerivedFactSpec
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Option Bool := do
  match fact with
  | .unary "Quality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| qualityLookup worldNames.size thingNames.size tables x w
  | .unary "NonEmptySet" x =>
      let x ← thingIndexByString? thingNames x
      pure <| nonEmptySetLookup worldNames.size thingNames.size tables x w
  | .unary "QualityStructure" x =>
      let x ← thingIndexByString? thingNames x
      pure <| qualityStructureLookup worldNames.size thingNames.size tables x w
  | .unary "SimpleQuality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| simpleQualityLookup worldNames.size thingNames.size tables x w
  | .unary "ComplexQuality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| complexQualityLookup worldNames.size thingNames.size tables x w
  | .unary "SimpleQualityType" x =>
      let x ← thingIndexByString? thingNames x
      pure <| simpleQualityTypeLookup worldNames.size thingNames.size tables x w
  | .unary "ComplexQualityType" x =>
      let x ← thingIndexByString? thingNames x
      pure <| complexQualityTypeLookup worldNames.size thingNames.size tables x w
  | .unary field x =>
      let x ← thingIndexByString? thingNames x
      pure <| derivedUnaryLookup worldNames.size thingNames.size tables field x w
  | .binary "UltimateBearerOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| ultimateBearerOfLookup worldNames.size thingNames.size tables x y w
  | .binary "ProperSub" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| properSubLookup worldNames.size thingNames.size tables x y w
  | .binary "SubsetOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| subsetLookup worldNames.size thingNames.size tables x y w
  | .binary "ProperSubsetOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| properSubsetLookup worldNames.size thingNames.size tables x y w
  | .binary "IsDisjointWith" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| isDisjointWithLookup worldNames.size thingNames.size tables x y w
  | .binary "Categorizes" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| categorizesLookup worldNames.size thingNames.size tables x y w
  | .binary field x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| derivedBinaryLookup worldNames.size thingNames.size tables field x y w
  | .ternary "IsCompletelyCoveredBy" x y z =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      let z ← thingIndexByString? thingNames z
      pure <| isCompletelyCoveredByLookup worldNames.size thingNames.size tables x y z w
  | .ternary "IsPartitionedInto" x y z =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      let z ← thingIndexByString? thingNames z
      pure <| isPartitionedIntoLookup worldNames.size thingNames.size tables x y z w
  | .ternary _ _ _ _ =>
      none
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| individualFunctionalDependenceLookup worldNames.size thingNames.size tables x x' y y' w
  | .quaternary "ComponentOf" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| componentOfLookup worldNames.size thingNames.size tables x x' y y' w
  | .quaternary "Constitution" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| constitutionLookup worldNames.size thingNames.size tables x x' y y' w
  | .quaternary _ _ _ _ _ =>
      none

/-- Resolve one argument and stop on an unknown name. The option test costs
one operation. The continuation's work is charged only for a resolved name. -/
private def withResolvedThingCosted (names : Array Name) (name : String)
    (next : Nat → Complexity.Costed (Option Bool)) : Complexity.Costed (Option Bool) :=
  (thingIndexByStringCosted names name).bind fun resolved =>
    Complexity.Costed.charge 1 <| match resolved with
    | none => .pure none
    | some i => next i

private theorem withResolvedThingCosted_value (names : Array Name) (name : String)
    (next : Nat → Complexity.Costed (Option Bool)) :
    (withResolvedThingCosted names name next).value =
      (thingIndexByString? names name).bind (fun i => (next i).value) := by
  simp only [withResolvedThingCosted, Complexity.Costed.bind_value, Complexity.Costed.charge_value,
    thingIndexByString?]
  cases (thingIndexByStringCosted names name).value <;> rfl

private theorem withResolvedThingCosted_cost_le (names : Array Name) (name : String)
    (next : Nat → Complexity.Costed (Option Bool)) (bound : Nat)
    (bounded : ∀ i, (next i).cost ≤ bound) :
    (withResolvedThingCosted names name next).cost ≤ 9 * names.size + 1 + bound := by
  have hn := thingIndexByStringCosted_cost_le names name
  simp only [withResolvedThingCosted, Complexity.Costed.bind_cost]
  split
  · simp only [Complexity.Costed.charge_cost, Complexity.Costed.pure_cost]
    omega
  · simp only [Complexity.Costed.charge_cost]
    rename_i i hi
    have h := bounded i
    omega

/-- One tag test selects the arity. Each field test costs a string comparison
and a branch. Unary and binary names resolve before field selection. Unknown
ternary and quaternary fields return no result without resolving arguments.
String-character work remains outside the primitive-call model. -/
private def evalNamedDerivedFactCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Complexity.Costed (Option Bool) :=
  let W := worldNames.size
  let T := thingNames.size
  Complexity.Costed.charge 1 <| match fact with
  | .unary field x =>
      withResolvedThingCosted thingNames x fun x =>
        Complexity.Costed.map some <|
          Complexity.Costed.charge 2 <|
            if field == "Quality" then
              uniqueRelatedThingCosted W T tables .qualityKind .inst x w
            else
              Complexity.Costed.charge 2 <|
                if field == "NonEmptySet" then
                  nonEmptySetLookupCosted W T tables x w
                else
                  Complexity.Costed.charge 2 <|
                    if field == "QualityStructure" then
                      uniqueRelatedThingCosted W T tables .qualityType .associatedWith x w
                    else
                      Complexity.Costed.charge 2 <|
                        if field == "SimpleQuality" then
                          simpleQualityLookupCosted W T tables x w
                        else
                          Complexity.Costed.charge 2 <|
                            if field == "ComplexQuality" then
                              complexQualityLookupCosted W T tables x w
                            else
                              Complexity.Costed.charge 2 <|
                                if field == "SimpleQualityType" then
                                  qualityTypeInstancesCosted W T tables x w (fun y => simpleQualityLookupCosted W T tables y w)
                                else
                                  Complexity.Costed.charge 2 <|
                                    if field == "ComplexQualityType" then
                                      qualityTypeInstancesCosted W T tables x w (fun y => complexQualityLookupCosted W T tables y w)
                                    else
                                      derivedUnaryLookupCosted W T tables field x w
  | .binary field x y =>
      withResolvedThingCosted thingNames x fun x =>
        withResolvedThingCosted thingNames y fun y =>
          Complexity.Costed.map some <|
            Complexity.Costed.charge 2 <|
              if field == "UltimateBearerOf" then
                ultimateBearerOfLookupCosted W T tables x y w
              else
                Complexity.Costed.charge 2 <|
                  if field == "ProperSub" then
                    properSubLookupCosted W T tables x y w
                  else
                    Complexity.Costed.charge 2 <|
                      if field == "SubsetOf" then
                        subsetLookupCosted W T tables x y w
                      else
                        Complexity.Costed.charge 2 <|
                          if field == "ProperSubsetOf" then
                            properSubsetLookupCosted W T tables x y w
                          else
                            Complexity.Costed.charge 2 <|
                              if field == "IsDisjointWith" then
                                isDisjointWithLookupCosted W T tables x y w
                              else
                                Complexity.Costed.charge 2 <|
                                  if field == "Categorizes" then
                                    categorizesLookupCosted W T tables x y w
                                  else
                                    derivedBinaryLookupCosted W T tables field x y w
  | .ternary field x y z =>
      Complexity.Costed.charge 2 <|
        if field == "IsCompletelyCoveredBy" then
          withResolvedThingCosted thingNames x fun x =>
            withResolvedThingCosted thingNames y fun y =>
              withResolvedThingCosted thingNames z fun z =>
                Complexity.Costed.map some (isCompletelyCoveredByLookupCosted W T tables x y z w)
        else
          Complexity.Costed.charge 2 <|
            if field == "IsPartitionedInto" then
              withResolvedThingCosted thingNames x fun x =>
                withResolvedThingCosted thingNames y fun y =>
                  withResolvedThingCosted thingNames z fun z =>
                    Complexity.Costed.map some (isPartitionedIntoLookupCosted W T tables x y z w)
            else
              .pure none
  | .quaternary field x x' y y' =>
      Complexity.Costed.charge 2 <|
        if field == "IndividualFunctionalDependence" then
          withResolvedThingCosted thingNames x fun x =>
            withResolvedThingCosted thingNames x' fun x' =>
              withResolvedThingCosted thingNames y fun y =>
                withResolvedThingCosted thingNames y' fun y' =>
                  Complexity.Costed.map some (individualFunctionalDependenceLookupCosted W T tables x x' y y' w)
        else
          Complexity.Costed.charge 2 <|
            if field == "ComponentOf" then
              withResolvedThingCosted thingNames x fun x =>
                withResolvedThingCosted thingNames x' fun x' =>
                  withResolvedThingCosted thingNames y fun y =>
                    withResolvedThingCosted thingNames y' fun y' =>
                      Complexity.Costed.map some (componentOfLookupCosted W T tables x x' y y' w)
            else
              Complexity.Costed.charge 2 <|
                if field == "Constitution" then
                  withResolvedThingCosted thingNames x fun x =>
                    withResolvedThingCosted thingNames x' fun x' =>
                      withResolvedThingCosted thingNames y fun y =>
                        withResolvedThingCosted thingNames y' fun y' =>
                          Complexity.Costed.map some (constitutionLookupCosted W T tables x x' y y' w)
                else
                  .pure none

private theorem evalNamedDerivedFactCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (evalNamedDerivedFactCosted worldNames thingNames tables fact w).value =
      evalNamedDerivedFactSpec worldNames thingNames tables fact w := by
  cases fact <;>
    simp only [evalNamedDerivedFactCosted, Complexity.Costed.charge_value,
      withResolvedThingCosted_value, Complexity.Costed.map_value]
  all_goals split_ifs <;>
    simp_all [evalNamedDerivedFactSpec, qualityLookup, qualityStructureLookup,
      simpleQualityLookup, complexQualityLookup, simpleQualityTypeLookup, complexQualityTypeLookup,
      nonEmptySetLookup, ultimateBearerOfLookup, properSubLookup, subsetLookup, properSubsetLookup,
      isDisjointWithLookup, categorizesLookup, isCompletelyCoveredByLookup, isPartitionedIntoLookup,
      derivedUnaryLookup, derivedBinaryLookup, individualFunctionalDependenceLookup,
      componentOfLookup, constitutionLookup]
  all_goals simp only [withResolvedThingCosted_value, Complexity.Costed.map_value]

/-- Sum of the established numeric-predicate bounds. Shared quality-family
bounds occur once. This fixed sum includes stored derived assertions through
`derivedLookupCostBound`; it is not a bound for arbitrary new formulas. -/
private def namedDerivedPredicateCostBound (W T : Nat) (tables : FactTables) : Nat :=
  (34 * T + 2) +
  (21 * T + 1) +
  (55 * T + 4) +
  (T * (55 * T + 27) + 14) +
  (derivedLookupCostBound W T tables) +
  (20) +
  (36) +
  (40 * T + 1) +
  (80 * T + 3) +
  (2 * (W * (T * 19 + 2)) + 39 * T + 3) +
  (W * (T * 19 + 2) + 40 * T + 2) +
  (58 * T + 1) +
  (2 * (W * (T * 19 + 2)) + 97 * T + 5) +
  (T * (39 * T + 39) + 73) +
  (T * (39 * T + 39) + 91) +
  (T * (37 * T + 21) + 54)

/-- At most four names resolve, each at cost `9T + 1`. At most seven field
tests cost 14, and arity selection costs one. The selected predicate contributes
its proved bound. Short-circuit exits can only omit these costs. -/
private theorem evalNamedDerivedFactCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (evalNamedDerivedFactCosted worldNames thingNames tables fact w).cost ≤
      namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
        36 * thingNames.size + 19 := by
  let W := worldNames.size
  let T := thingNames.size
  let B := namedDerivedPredicateCostBound W T tables
  have uniqueBound (classification : UnaryField) (relation : BinaryField) (x : Nat) :
      (uniqueRelatedThingCosted W T tables classification relation x w).cost ≤ B := by
    have h := uniqueRelatedThingCosted_cost_le W T tables classification relation x w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have nonemptyBound (x : Nat) : (nonEmptySetLookupCosted W T tables x w).cost ≤ B := by
    have h := nonEmptySetLookupCosted_cost_le W T tables x w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have simpleBound (x : Nat) : (simpleQualityLookupCosted W T tables x w).cost ≤ B := by
    have h := simpleQualityLookupCosted_cost_le W T tables x w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have complexBound (x : Nat) : (complexQualityLookupCosted W T tables x w).cost ≤ B := by
    have h := complexQualityLookupCosted_cost_le W T tables x w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have simpleTypeBound (x : Nat) :
      (qualityTypeInstancesCosted W T tables x w
        (fun y => simpleQualityLookupCosted W T tables y w)).cost ≤ B := by
    have h := qualityTypeInstances_simple_cost_le W T tables x w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have complexTypeBound (x : Nat) :
      (qualityTypeInstancesCosted W T tables x w
        (fun y => complexQualityLookupCosted W T tables y w)).cost ≤ B := by
    have h := qualityTypeInstances_complex_cost_le W T tables x w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have unaryBound (field : String) (x : Nat) : (derivedUnaryLookupCosted W T tables field x w).cost ≤ B := by
    have h := derivedUnaryLookupCosted_cost_le W T tables field x w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have bearerBound (x y : Nat) : (ultimateBearerOfLookupCosted W T tables x y w).cost ≤ B := by
    have h := ultimateBearerOfLookupCosted_cost_le W T tables x y w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have properSubBound (x y : Nat) : (properSubLookupCosted W T tables x y w).cost ≤ B := by
    have h := properSubLookupCosted_cost_le W T tables x y w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have subsetBound (x y : Nat) : (subsetLookupCosted W T tables x y w).cost ≤ B := by
    have h := subsetLookupCosted_cost_le W T tables x y w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have properSubsetBound (x y : Nat) : (properSubsetLookupCosted W T tables x y w).cost ≤ B := by
    have h := properSubsetLookupCosted_cost_le W T tables x y w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have disjointBound (x y : Nat) : (isDisjointWithLookupCosted W T tables x y w).cost ≤ B := by
    have h := isDisjointWithLookupCosted_cost_le W T tables x y w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have categorizesBound (x y : Nat) : (categorizesLookupCosted W T tables x y w).cost ≤ B := by
    have h := categorizesLookupCosted_cost_le W T tables x y w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have binaryBound (field : String) (x y : Nat) : (derivedBinaryLookupCosted W T tables field x y w).cost ≤ B := by
    have h := derivedBinaryLookupCosted_cost_le W T tables field x y w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have coveredBound (x y z : Nat) : (isCompletelyCoveredByLookupCosted W T tables x y z w).cost ≤ B := by
    have h := isCompletelyCoveredByLookupCosted_cost_le W T tables x y z w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have partitionBound (x y z : Nat) : (isPartitionedIntoLookupCosted W T tables x y z w).cost ≤ B := by
    have h := isPartitionedIntoLookupCosted_cost_le W T tables x y z w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have ifdBound (x x' y y' : Nat) : (individualFunctionalDependenceLookupCosted W T tables x x' y y' w).cost ≤ B := by
    have h := individualFunctionalDependenceLookupCosted_cost_le W T tables x x' y y' w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have componentBound (x x' y y' : Nat) : (componentOfLookupCosted W T tables x x' y y' w).cost ≤ B := by
    have h := componentOfLookupCosted_cost_le W T tables x x' y y' w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  have constitutionBound (x x' y y' : Nat) : (constitutionLookupCosted W T tables x x' y y' w).cost ≤ B := by
    have h := constitutionLookupCosted_cost_le W T tables x x' y y' w
    dsimp [B, namedDerivedPredicateCostBound]
    omega
  cases fact with
  | unary field x =>
      simp only [evalNamedDerivedFactCosted, Complexity.Costed.charge_cost]
      calc
        _ ≤ 1 + (9 * T + 1 + (B + 14)) := Nat.add_le_add_left
          (withResolvedThingCosted_cost_le thingNames x _ (B + 14) (by
            intro x
            simp only [Complexity.Costed.map_cost]
            split_ifs <;> simp only [Complexity.Costed.charge_cost]
            · have h := uniqueBound .qualityKind .inst x
              (dsimp only [B, W, T] at *; omega)
            · have h := nonemptyBound x
              (dsimp only [B, W, T] at *; omega)
            · have h := uniqueBound .qualityType .associatedWith x
              (dsimp only [B, W, T] at *; omega)
            · have h := simpleBound x
              (dsimp only [B, W, T] at *; omega)
            · have h := complexBound x
              (dsimp only [B, W, T] at *; omega)
            · have h := simpleTypeBound x
              (dsimp only [B, W, T] at *; omega)
            · have h := complexTypeBound x
              (dsimp only [B, W, T] at *; omega)
            · have h := unaryBound field x
              (dsimp only [B, W, T] at *; omega)
          )) 1
        _ ≤ _ := by (dsimp only [B, W, T] at *; omega)
  | binary field x y =>
      simp only [evalNamedDerivedFactCosted, Complexity.Costed.charge_cost]
      calc
        _ ≤ 1 + (9 * T + 1 + (9 * T + 1 + (B + 12))) := Nat.add_le_add_left
          (withResolvedThingCosted_cost_le thingNames x _ (9 * T + 1 + (B + 12)) (by
            intro x
            apply withResolvedThingCosted_cost_le
            intro y
            simp only [Complexity.Costed.map_cost]
            split_ifs <;> simp only [Complexity.Costed.charge_cost]
            · have h := bearerBound x y
              (dsimp only [B, W, T] at *; omega)
            · have h := properSubBound x y
              (dsimp only [B, W, T] at *; omega)
            · have h := subsetBound x y
              (dsimp only [B, W, T] at *; omega)
            · have h := properSubsetBound x y
              (dsimp only [B, W, T] at *; omega)
            · have h := disjointBound x y
              (dsimp only [B, W, T] at *; omega)
            · have h := categorizesBound x y
              (dsimp only [B, W, T] at *; omega)
            · have h := binaryBound field x y
              (dsimp only [B, W, T] at *; omega)
          )) 1
        _ ≤ _ := by (dsimp only [B, W, T] at *; omega)
  | ternary field x y z =>
      simp only [evalNamedDerivedFactCosted, Complexity.Costed.charge_cost]
      split_ifs <;> (try simp only [Complexity.Costed.charge_cost, Complexity.Costed.pure_cost])
      · have h : (
          withResolvedThingCosted thingNames x fun x =>
            withResolvedThingCosted thingNames y fun y =>
              withResolvedThingCosted thingNames z fun z =>
                Complexity.Costed.map some (isCompletelyCoveredByLookupCosted W T tables x y z w)).cost ≤
            (9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + B)) := by
          apply withResolvedThingCosted_cost_le
          intro x
          apply withResolvedThingCosted_cost_le
          intro y
          apply withResolvedThingCosted_cost_le
          intro z
          simpa using coveredBound x y z
        (dsimp only [B, W, T] at *; omega)
      · have h : (
          withResolvedThingCosted thingNames x fun x =>
            withResolvedThingCosted thingNames y fun y =>
              withResolvedThingCosted thingNames z fun z =>
                Complexity.Costed.map some (isPartitionedIntoLookupCosted W T tables x y z w)).cost ≤
            (9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + B)) := by
          apply withResolvedThingCosted_cost_le
          intro x
          apply withResolvedThingCosted_cost_le
          intro y
          apply withResolvedThingCosted_cost_le
          intro z
          simpa using partitionBound x y z
        (dsimp only [B, W, T] at *; omega)
      · (dsimp only [B, W, T] at *; omega)
  | quaternary field x x' y y' =>
      simp only [evalNamedDerivedFactCosted, Complexity.Costed.charge_cost]
      split_ifs <;> (try simp only [Complexity.Costed.charge_cost, Complexity.Costed.pure_cost])
      · have h : (
          withResolvedThingCosted thingNames x fun x =>
            withResolvedThingCosted thingNames x' fun x' =>
              withResolvedThingCosted thingNames y fun y =>
                withResolvedThingCosted thingNames y' fun y' =>
                  Complexity.Costed.map some
                    (individualFunctionalDependenceLookupCosted W T tables x x' y y' w)).cost ≤
            (9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + B))) := by
          apply withResolvedThingCosted_cost_le
          intro x
          apply withResolvedThingCosted_cost_le
          intro x'
          apply withResolvedThingCosted_cost_le
          intro y
          apply withResolvedThingCosted_cost_le
          intro y'
          simpa using ifdBound x x' y y'
        (dsimp only [B, W, T] at *; omega)
      · have h : (
          withResolvedThingCosted thingNames x fun x =>
            withResolvedThingCosted thingNames x' fun x' =>
              withResolvedThingCosted thingNames y fun y =>
                withResolvedThingCosted thingNames y' fun y' =>
                  Complexity.Costed.map some (componentOfLookupCosted W T tables x x' y y' w)).cost ≤
            (9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + B))) := by
          apply withResolvedThingCosted_cost_le
          intro x
          apply withResolvedThingCosted_cost_le
          intro x'
          apply withResolvedThingCosted_cost_le
          intro y
          apply withResolvedThingCosted_cost_le
          intro y'
          simpa using componentBound x x' y y'
        (dsimp only [B, W, T] at *; omega)
      · have h : (
          withResolvedThingCosted thingNames x fun x =>
            withResolvedThingCosted thingNames x' fun x' =>
              withResolvedThingCosted thingNames y fun y =>
                withResolvedThingCosted thingNames y' fun y' =>
                  Complexity.Costed.map some (constitutionLookupCosted W T tables x x' y y' w)).cost ≤
            (9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + ((9 * T + 1) + B))) := by
          apply withResolvedThingCosted_cost_le
          intro x
          apply withResolvedThingCosted_cost_le
          intro x'
          apply withResolvedThingCosted_cost_le
          intro y
          apply withResolvedThingCosted_cost_le
          intro y'
          simpa using constitutionBound x x' y y'
        (dsimp only [B, W, T] at *; omega)
      · (dsimp only [B, W, T] at *; omega)

/-- Growing the finite domains or the stored assertion array cannot decrease
the size bound. No relation between the actual predicate values is required. -/
private theorem namedDerivedPredicateCostBound_mono
    {W₁ W₂ T₁ T₂ : Nat} (tables₁ tables₂ : FactTables)
    (hW : W₁ ≤ W₂) (hT : T₁ ≤ T₂)
    (hD : tables₁.derivedProps.size ≤ tables₂.derivedProps.size) :
    namedDerivedPredicateCostBound W₁ T₁ tables₁ ≤ namedDerivedPredicateCostBound W₂ T₂ tables₂ := by
  unfold namedDerivedPredicateCostBound derivedLookupCostBound
  repeat' first
    | assumption
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul
    | exact Nat.le_refl _

/-!
## First-failure selection

Selection pairs source and resolved facts by index, then searches their worlds
in scope order. The retained record carries the assignment and failure kind
into report construction, so the assertion need not be checked again.
-/

/-- The first failed assertion retains the data needed by its report.
A reconstructed failure means evaluation returned `some false`. Otherwise
evaluation returned `none`, so the report explains reconstruction failure. -/
private structure FailedDerivedAssertion where
  fact : NamedDerivedFact
  scope : NamedFactScope
  world : Nat
  reconstructed : Bool
  deriving Repr, DecidableEq

private def failedDerivedAtSpec
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (w : Nat) :
    Option FailedDerivedAssertion :=
  match evalNamedDerivedFactSpec worldNames thingNames tables fact w with
  | some true => none
  | some false => some ⟨fact, scope, w, true⟩
  | none => some ⟨fact, scope, w, false⟩

/-- Evaluate an assignment once. Inspecting the optional result costs one.
A present result incurs one further Boolean test. Successful assignments
produce no failure record. -/
private def failedDerivedAtCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (w : Nat) :
    Complexity.Costed (Option FailedDerivedAssertion) :=
  (evalNamedDerivedFactCosted worldNames thingNames tables fact w).bind fun result =>
    Complexity.Costed.charge 1 <| match result with
    | none => .pure (some ⟨fact, scope, w, false⟩)
    | some value => Complexity.Costed.tick
        (if value then none else some ⟨fact, scope, w, true⟩) 1

private theorem failedDerivedAtCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (w : Nat) :
    (failedDerivedAtCosted worldNames thingNames tables fact scope w).value =
      failedDerivedAtSpec worldNames thingNames tables fact scope w := by
  simp only [failedDerivedAtCosted, Complexity.Costed.bind_value,
    evalNamedDerivedFactCosted_value, Complexity.Costed.charge_value, failedDerivedAtSpec]
  cases evalNamedDerivedFactSpec worldNames thingNames tables fact w with
  | none => rfl
  | some value => cases value <;> rfl

private theorem failedDerivedAtCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (w : Nat) :
    (failedDerivedAtCosted worldNames thingNames tables fact scope w).cost ≤
      namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
        36 * thingNames.size + 21 := by
  have h := evalNamedDerivedFactCosted_cost_le worldNames thingNames tables fact w
  simp only [failedDerivedAtCosted, Complexity.Costed.bind_cost]
  split <;> simp only [Complexity.Costed.charge_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost] <;> omega

private def firstScopedDerivedFailureSpec
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (resolved : FactScope) :
    Option FailedDerivedAssertion :=
  match resolved with
  | .at w => failedDerivedAtSpec worldNames thingNames tables fact scope w
  | .everywhere => (List.range worldNames.size).findSome?
      (failedDerivedAtSpec worldNames thingNames tables fact scope)

/-- An everywhere scope visits numeric coordinates without allocating an
array of worlds. The loop retains the first failure record. An at-scope
evaluates its single world directly. The scope tag costs one in either case. -/
private def firstScopedDerivedFailureCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (resolved : FactScope) :
    Complexity.Costed (Option FailedDerivedAssertion) :=
  Complexity.Costed.charge 1 <| match resolved with
  | .at w => failedDerivedAtCosted worldNames thingNames tables fact scope w
  | .everywhere => foldDiagDomainCosted 0 worldNames.size none Option.isSome fun _ w =>
      failedDerivedAtCosted worldNames thingNames tables fact scope w

private theorem firstScopedDerivedFailureCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (resolved : FactScope) :
    (firstScopedDerivedFailureCosted worldNames thingNames tables fact scope resolved).value =
      firstScopedDerivedFailureSpec worldNames thingNames tables fact scope resolved := by
  cases resolved with
  | «at» w => simp [firstScopedDerivedFailureCosted, firstScopedDerivedFailureSpec,
      failedDerivedAtCosted_value]
  | everywhere =>
      simp only [firstScopedDerivedFailureCosted, firstScopedDerivedFailureSpec,
        Complexity.Costed.charge_value]
      exact foldDiagDomainCosted_firstSome_value _ _ _
        (by intro w hw; exact failedDerivedAtCosted_value _ _ _ _ _ _)

/-- With per-assignment dispatch bound C, an everywhere scope costs at most
1 + W(C + 5): two result tests and three loop controls per world. An at-scope
costs at most C + 3. The uniform bound below covers both, including W = 0. -/
private theorem firstScopedDerivedFailureCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (scope : NamedFactScope) (resolved : FactScope) :
    (firstScopedDerivedFailureCosted worldNames thingNames tables fact scope resolved).cost ≤
      1 + (worldNames.size + 1) *
        (namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
          36 * thingNames.size + 24) := by
  cases resolved with
  | «at» w =>
      have h := failedDerivedAtCosted_cost_le worldNames thingNames tables fact scope w
      simp only [firstScopedDerivedFailureCosted, Complexity.Costed.charge_cost]
      rw [Nat.add_mul]
      omega
  | everywhere =>
      have h := foldDiagDomainCosted_cost_le 0 worldNames.size
        (none : Option FailedDerivedAssertion) Option.isSome
        (fun _ w => failedDerivedAtCosted worldNames thingNames tables fact scope w)
        (namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
          36 * thingNames.size + 21)
        (by intro state w hlo hhi; exact failedDerivedAtCosted_cost_le _ _ _ _ _ _)
      have reassociate (n : Nat) : n + 21 + 3 = n + 24 := by omega
      rw [reassociate] at h
      simp only [firstScopedDerivedFailureCosted, Complexity.Costed.charge_cost]
      rw [Nat.add_mul]
      omega

private def firstDerivedFailureAtIndexSpec
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) (i : Nat) :
    Option FailedDerivedAssertion :=
  match namedFacts[i]?, scopedFacts[i]? with
  | some (.derived fact scope), some (.derived _ resolved) =>
      firstScopedDerivedFailureSpec worldNames thingNames tables fact scope resolved
  | _, _ => none

/-- Read the paired source entries before inspecting their tags. Missing or
non-derived entries skip evaluation. Four tag tests suffice for a pair of
derived facts. The resolved proposition builder is never called here. -/
private def firstDerivedFailureAtIndexCosted
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) (i : Nat) :
    Complexity.Costed (Option FailedDerivedAssertion) := do
  let named ← Complexity.Costed.tick namedFacts[i]? 1
  let resolved ← Complexity.Costed.tick scopedFacts[i]? 1
  Complexity.Costed.charge 1 <| match named with
  | none => .pure none
  | some named => Complexity.Costed.charge 1 <| match named with
    | .derived fact scope => Complexity.Costed.charge 1 <| match resolved with
      | none => .pure none
      | some resolved => Complexity.Costed.charge 1 <| match resolved with
        | .derived _ resolved => firstScopedDerivedFailureCosted
            worldNames thingNames tables fact scope resolved
        | _ => .pure none
    | _ => .pure none

private theorem firstDerivedFailureAtIndexCosted_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) (i : Nat) :
    (firstDerivedFailureAtIndexCosted worldNames thingNames namedFacts scopedFacts tables i).value =
      firstDerivedFailureAtIndexSpec worldNames thingNames namedFacts scopedFacts tables i := by
  cases hn : namedFacts[i]? with
  | none => simp [firstDerivedFailureAtIndexCosted, firstDerivedFailureAtIndexSpec,
      hn, Bind.bind, Complexity.Costed.bind]
  | some named =>
      cases named <;> cases hs : scopedFacts[i]? with
      | none => simp [firstDerivedFailureAtIndexCosted, firstDerivedFailureAtIndexSpec,
          hn, hs, Bind.bind, Complexity.Costed.bind]
      | some resolved =>
          cases resolved <;>
            simp [firstDerivedFailureAtIndexCosted, firstDerivedFailureAtIndexSpec,
              hn, hs, Bind.bind, Complexity.Costed.bind, firstScopedDerivedFailureCosted_value]

private theorem firstDerivedFailureAtIndexCosted_cost_le
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) (i : Nat) :
    (firstDerivedFailureAtIndexCosted worldNames thingNames namedFacts scopedFacts tables i).cost ≤
      7 + (worldNames.size + 1) *
        (namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
          36 * thingNames.size + 24) := by
  cases hn : namedFacts[i]? with
  | none =>
      simp only [firstDerivedFailureAtIndexCosted, hn, Bind.bind,
        Complexity.Costed.bind, Complexity.Costed.tick, Complexity.Costed.charge,
        Complexity.Costed.pure]
      omega
  | some named =>
      cases named with
      | derived fact scope =>
          cases hs : scopedFacts[i]? with
          | none =>
              simp only [firstDerivedFailureAtIndexCosted, hn, hs, Bind.bind,
                Complexity.Costed.bind, Complexity.Costed.tick, Complexity.Costed.charge,
                Complexity.Costed.pure]
              omega
          | some resolved =>
              cases resolved with
              | derived prop resolvedScope =>
                  have h := firstScopedDerivedFailureCosted_cost_le
                    worldNames thingNames tables fact scope resolvedScope
                  simp only [firstDerivedFailureAtIndexCosted, hn, hs, Bind.bind,
                    Complexity.Costed.bind_cost, Complexity.Costed.tick_value,
                    Complexity.Costed.tick_cost, Complexity.Costed.charge_cost]
                  omega
              | _ =>
                  simp only [firstDerivedFailureAtIndexCosted, hn, hs, Bind.bind,
                    Complexity.Costed.bind, Complexity.Costed.tick, Complexity.Costed.charge,
                    Complexity.Costed.pure]
                  omega
      | _ =>
          simp only [firstDerivedFailureAtIndexCosted, hn, Bind.bind,
            Complexity.Costed.bind, Complexity.Costed.tick, Complexity.Costed.charge,
            Complexity.Costed.pure]
          omega

private def firstDerivedAssertionFailureSpec
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Option FailedDerivedAssertion :=
  (List.range namedFacts.size).findSome?
    (firstDerivedFailureAtIndexSpec worldNames thingNames namedFacts scopedFacts tables)

/-- Source traversal stops at the first failing fact and world. The retained
record supplies the report's inputs without a second predicate evaluation. -/
private def firstDerivedAssertionFailureCosted
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    Complexity.Costed (Option FailedDerivedAssertion) :=
  foldDiagDomainCosted 0 namedFacts.size none Option.isSome fun _ i =>
    firstDerivedFailureAtIndexCosted worldNames thingNames namedFacts scopedFacts tables i

private theorem firstDerivedAssertionFailureCosted_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (firstDerivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).value =
      firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables := by
  apply foldDiagDomainCosted_firstSome_value
  intro i hi
  exact firstDerivedFailureAtIndexCosted_value _ _ _ _ _ _

private theorem firstDerivedAssertionFailureCosted_cost_le
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (firstDerivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).cost ≤
      namedFacts.size * (10 + (worldNames.size + 1) *
        (namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
          36 * thingNames.size + 24)) := by
  have h := foldDiagDomainCosted_cost_le 0 namedFacts.size
    (none : Option FailedDerivedAssertion) Option.isSome
    (fun _ i => firstDerivedFailureAtIndexCosted worldNames thingNames namedFacts scopedFacts tables i)
    (7 + (worldNames.size + 1) *
      (namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
        36 * thingNames.size + 24))
    (by intro state i hlo hhi; exact firstDerivedFailureAtIndexCosted_cost_le _ _ _ _ _ _)
  have reassociate (n : Nat) : 7 + n + 3 = 10 + n := by omega
  rw [reassociate] at h
  exact h

/-- The selection bound grows with source facts F, worlds W, things T, and
stored derived propositions D. Exact execution counts can decrease when a
new fact supplies an earlier witness or failure. -/
private theorem firstDerivedAssertionFailureCostBound_mono
    {F₁ F₂ W₁ W₂ T₁ T₂ : Nat} (tables₁ tables₂ : FactTables)
    (hF : F₁ ≤ F₂) (hW : W₁ ≤ W₂) (hT : T₁ ≤ T₂)
    (hD : tables₁.derivedProps.size ≤ tables₂.derivedProps.size) :
    F₁ * (10 + (W₁ + 1) *
      (namedDerivedPredicateCostBound W₁ T₁ tables₁ + 36 * T₁ + 24)) ≤
    F₂ * (10 + (W₂ + 1) *
      (namedDerivedPredicateCostBound W₂ T₂ tables₂ + 36 * T₂ + 24)) := by
  have hB := namedDerivedPredicateCostBound_mono tables₁ tables₂ hW hT hD
  apply Nat.mul_le_mul hF
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul (Nat.add_le_add_right hW 1)
  exact Nat.add_le_add_right (Nat.add_le_add hB (Nat.mul_le_mul_left 36 hT)) 24

/-!
## Report components

Each component keeps its executable definition, value proof, cost bound, and
output-size proof together. The outer dispatchers below combine these bounds.
Shared searches are defined once and reused by the relevant field families.
-/

/-- Cost-free specification of the diagnostic advice. Production uses the
counted selector below, whose value theorem preserves every literal. -/
private def derivedAssertionSuggestionSpec (fact : NamedDerivedFact) : String :=
  match fact with
  | .unary "Quality" _ =>
      "Computed from `QualityKind(k)` plus `x :: k`, with exactly one such quality kind. Add exactly one quality-kind instantiation for the individual, and avoid competing quality-kind instantiations."
  | .unary "ExternallyDependentMode" _ =>
      "Computed from `Mode(x)` plus some computed `ExternallyDependent(x, y)`. `ExternallyDependent` itself is computed from modal existential dependence and independence from each bearer reached by `InheresIn`. Add `Mode`, `InheresIn`, and modal `Ex` facts that make a witness true, or remove the unsupported assertion."
  | .unary "QuaIndividual" _ =>
      "Computed from `QuaIndividualOf(x, y)`. Add a matching `QuaIndividualOf` fact and satisfy the §3.10 foundation requirements checked by the relator axioms, or remove the unsupported assertion."
  | .unary "NonEmptySet" _ =>
      "Computed from membership at the current world. Add at least one `MemberOf(member, set)` fact at this world, or remove the unsupported assertion."
  | .unary "QualityStructure" _ =>
      "Computed from exactly one association with a `QualityType`. Add exactly one `AssociatedWith(structure, qualityType)` fact whose target is a `QualityType`, or remove the unsupported assertion."
  | .unary "SimpleQuality" _ =>
      "Computed from `Quality(x)` plus absence of `InheresIn(_, x)`. Make the thing a computed `Quality` and ensure no other thing inheres in it at this world."
  | .unary "ComplexQuality" _ =>
      "Computed from `Quality(x)` plus at least one `InheresIn(_, x)`. Make the thing a computed `Quality` and add at least one `InheresIn(part, quality)` fact."
  | .unary "SimpleQualityType" _ =>
      "Computed from `QualityType(t)` plus every current instance of `t` being a computed `SimpleQuality`. Assert `QualityType(type)` and repair any non-simple-quality instance."
  | .unary "ComplexQualityType" _ =>
      "Computed from `QualityType(t)` plus every current instance of `t` being a computed `ComplexQuality`. Assert `QualityType(type)` and repair any non-complex-quality instance."
  | .binary "ProperSub" _ _ =>
      "Computed from `Sub(left, right)` and absence of reverse `Sub(right, left)`. Add the forward `Sub` fact and ensure the reverse `Sub` fact is not present."
  | .binary "GenericFunctionalDependence" _ _ =>
      "Computed from `Inst` and `FunctionsAs`: every instance functioning as the source type needs a distinct instance functioning as the target type."
  | .quaternary "IndividualFunctionalDependence" _ _ _ _ =>
      "Computed from generic functional dependence, the two instantiations, and the source-to-target `FunctionsAs` implication. Make the type-level dependence true, add the required instantiations, and ensure the target functions whenever the source functions."
  | .quaternary "ComponentOf" _ _ _ _ =>
      "Computed from `ProperPart(component, whole)` plus the corresponding computed `IndividualFunctionalDependence`. Add the proper-part fact and repair the functional-dependence side."
  | .binary "GenericConstitutionalDependence" _ _ =>
      "Computed from `Inst` and `ConstitutedBy`: every source-type instance needs a target-type instance that constitutionally bears it."
  | .quaternary "Constitution" _ _ _ _ =>
      "Computed from the two instantiations, computed generic constitutional dependence, and `ConstitutedBy(instance, constituter)`. Add the required instantiations, repair generic constitutional dependence, and add the concrete `ConstitutedBy` fact."
  | .binary "ExternallyDependent" _ _ =>
      "Computed from modal existential dependence plus existential independence from every bearer reached by `InheresIn`. Add modal `Ex` variation and `InheresIn` facts that satisfy external dependence, or remove the unsupported assertion."
  | .binary "ExistentialDependence" _ _ =>
      "Computed from `Ex` facts across worlds: every world where the dependent exists must also have the target existing. Add the missing `Ex` facts, or remove the unsupported assertion."
  | .binary "ExistentialIndependence" _ _ =>
      "Computed from `Ex` facts across worlds: each side must have a witness world where it exists without the other. Add those modal `Ex` variations, or remove the unsupported assertion."
  | .binary "UltimateBearerOf" _ _ =>
      "Computed from the `InheresIn` transitive closure and `Moment`: the bearer must be non-moment and reachable from the moment. Add an `InheresIn` path from the moment to the bearer and ensure the bearer is not a moment."
  | .binary "SubsetOf" _ _ =>
      "Computed from `MemberOf`: every member of the left set must also be a member of the right set at this world."
  | .binary "ProperSubsetOf" _ _ =>
      "Computed from `SubsetOf(left, right)` plus a strictness witness: some right-set member must not be in the left set."
  | .binary "IsDisjointWith" _ _ =>
      "Computed from typehood and `Inst`: the two types must have no shared instance. Remove the assertion, or remove the common instance facts that make the two types overlap."
  | .ternary "IsCompletelyCoveredBy" _ _ _ =>
      "Computed from `Inst`: every instance of the covered type must instantiate at least one covering type. Add missing instantiation facts, or remove the assertion."
  | .ternary "IsPartitionedInto" _ _ _ =>
      "Computed from complete coverage plus disjointness of the two covering types. Make the cover complete and the covering types disjoint, or remove the assertion."
  | .binary "Categorizes" _ _ =>
      "Computed from typehood, `Inst`, and `Sub`: every type instantiating the category must specialize the categorized type. Add missing specialization facts, or remove the assertion."
  | _ =>
      "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."

/-- Select a literal suggestion with one arity test and two operations per
visited field: a string comparison and its branch. No argument name is read.
The finite decision specification fixes the text independently of charges. -/
private def derivedAssertionSuggestionCosted (fact : NamedDerivedFact) : Complexity.Costed String :=
  Complexity.Costed.charge 1 <| match fact with
  | .unary field _ =>
      Complexity.Costed.charge 2 <| if field == "Quality" then
        .pure "Computed from `QualityKind(k)` plus `x :: k`, with exactly one such quality kind. Add exactly one quality-kind instantiation for the individual, and avoid competing quality-kind instantiations."
      else
        Complexity.Costed.charge 2 <| if field == "ExternallyDependentMode" then
          .pure "Computed from `Mode(x)` plus some computed `ExternallyDependent(x, y)`. `ExternallyDependent` itself is computed from modal existential dependence and independence from each bearer reached by `InheresIn`. Add `Mode`, `InheresIn`, and modal `Ex` facts that make a witness true, or remove the unsupported assertion."
        else
          Complexity.Costed.charge 2 <| if field == "QuaIndividual" then
            .pure "Computed from `QuaIndividualOf(x, y)`. Add a matching `QuaIndividualOf` fact and satisfy the §3.10 foundation requirements checked by the relator axioms, or remove the unsupported assertion."
          else
            Complexity.Costed.charge 2 <| if field == "NonEmptySet" then
              .pure "Computed from membership at the current world. Add at least one `MemberOf(member, set)` fact at this world, or remove the unsupported assertion."
            else
              Complexity.Costed.charge 2 <| if field == "QualityStructure" then
                .pure "Computed from exactly one association with a `QualityType`. Add exactly one `AssociatedWith(structure, qualityType)` fact whose target is a `QualityType`, or remove the unsupported assertion."
              else
                Complexity.Costed.charge 2 <| if field == "SimpleQuality" then
                  .pure "Computed from `Quality(x)` plus absence of `InheresIn(_, x)`. Make the thing a computed `Quality` and ensure no other thing inheres in it at this world."
                else
                  Complexity.Costed.charge 2 <| if field == "ComplexQuality" then
                    .pure "Computed from `Quality(x)` plus at least one `InheresIn(_, x)`. Make the thing a computed `Quality` and add at least one `InheresIn(part, quality)` fact."
                  else
                    Complexity.Costed.charge 2 <| if field == "SimpleQualityType" then
                      .pure "Computed from `QualityType(t)` plus every current instance of `t` being a computed `SimpleQuality`. Assert `QualityType(type)` and repair any non-simple-quality instance."
                    else
                      Complexity.Costed.charge 2 <| if field == "ComplexQualityType" then
                        .pure "Computed from `QualityType(t)` plus every current instance of `t` being a computed `ComplexQuality`. Assert `QualityType(type)` and repair any non-complex-quality instance."
                      else
                        .pure "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."
  | .binary field _ _ =>
      Complexity.Costed.charge 2 <| if field == "ProperSub" then
        .pure "Computed from `Sub(left, right)` and absence of reverse `Sub(right, left)`. Add the forward `Sub` fact and ensure the reverse `Sub` fact is not present."
      else
        Complexity.Costed.charge 2 <| if field == "GenericFunctionalDependence" then
          .pure "Computed from `Inst` and `FunctionsAs`: every instance functioning as the source type needs a distinct instance functioning as the target type."
        else
          Complexity.Costed.charge 2 <| if field == "GenericConstitutionalDependence" then
            .pure "Computed from `Inst` and `ConstitutedBy`: every source-type instance needs a target-type instance that constitutionally bears it."
          else
            Complexity.Costed.charge 2 <| if field == "ExternallyDependent" then
              .pure "Computed from modal existential dependence plus existential independence from every bearer reached by `InheresIn`. Add modal `Ex` variation and `InheresIn` facts that satisfy external dependence, or remove the unsupported assertion."
            else
              Complexity.Costed.charge 2 <| if field == "ExistentialDependence" then
                .pure "Computed from `Ex` facts across worlds: every world where the dependent exists must also have the target existing. Add the missing `Ex` facts, or remove the unsupported assertion."
              else
                Complexity.Costed.charge 2 <| if field == "ExistentialIndependence" then
                  .pure "Computed from `Ex` facts across worlds: each side must have a witness world where it exists without the other. Add those modal `Ex` variations, or remove the unsupported assertion."
                else
                  Complexity.Costed.charge 2 <| if field == "UltimateBearerOf" then
                    .pure "Computed from the `InheresIn` transitive closure and `Moment`: the bearer must be non-moment and reachable from the moment. Add an `InheresIn` path from the moment to the bearer and ensure the bearer is not a moment."
                  else
                    Complexity.Costed.charge 2 <| if field == "SubsetOf" then
                      .pure "Computed from `MemberOf`: every member of the left set must also be a member of the right set at this world."
                    else
                      Complexity.Costed.charge 2 <| if field == "ProperSubsetOf" then
                        .pure "Computed from `SubsetOf(left, right)` plus a strictness witness: some right-set member must not be in the left set."
                      else
                        Complexity.Costed.charge 2 <| if field == "IsDisjointWith" then
                          .pure "Computed from typehood and `Inst`: the two types must have no shared instance. Remove the assertion, or remove the common instance facts that make the two types overlap."
                        else
                          Complexity.Costed.charge 2 <| if field == "Categorizes" then
                            .pure "Computed from typehood, `Inst`, and `Sub`: every type instantiating the category must specialize the categorized type. Add missing specialization facts, or remove the assertion."
                          else
                            .pure "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."
  | .ternary field _ _ _ =>
      Complexity.Costed.charge 2 <| if field == "IsCompletelyCoveredBy" then
        .pure "Computed from `Inst`: every instance of the covered type must instantiate at least one covering type. Add missing instantiation facts, or remove the assertion."
      else
        Complexity.Costed.charge 2 <| if field == "IsPartitionedInto" then
          .pure "Computed from complete coverage plus disjointness of the two covering types. Make the cover complete and the covering types disjoint, or remove the assertion."
        else
          .pure "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."
  | .quaternary field _ _ _ _ =>
      Complexity.Costed.charge 2 <| if field == "IndividualFunctionalDependence" then
        .pure "Computed from generic functional dependence, the two instantiations, and the source-to-target `FunctionsAs` implication. Make the type-level dependence true, add the required instantiations, and ensure the target functions whenever the source functions."
      else
        Complexity.Costed.charge 2 <| if field == "ComponentOf" then
          .pure "Computed from `ProperPart(component, whole)` plus the corresponding computed `IndividualFunctionalDependence`. Add the proper-part fact and repair the functional-dependence side."
        else
          Complexity.Costed.charge 2 <| if field == "Constitution" then
            .pure "Computed from the two instantiations, computed generic constitutional dependence, and `ConstitutedBy(instance, constituter)`. Add the required instantiations, repair generic constitutional dependence, and add the concrete `ConstitutedBy` fact."
          else
            .pure "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."

private theorem derivedAssertionSuggestionCosted_value (fact : NamedDerivedFact) :
    (derivedAssertionSuggestionCosted fact).value = derivedAssertionSuggestionSpec fact := by
  -- Remove each charge before splitting its branch. The proof keeps the
  -- literal text opaque until it reaches the selected suggestion.
  cases fact <;> unfold derivedAssertionSuggestionCosted
  all_goals
    repeat' first
      | rw [Complexity.Costed.charge_value]
      | split
      | rw [Complexity.Costed.pure_value]
    all_goals simp_all [derivedAssertionSuggestionSpec]

/-- The longest branch contains eleven binary field tests. The arity test
and two operations per visited field give a constant bound of 23. Text-prefix
construction and row emission belong to the caller, not this selector. -/
private theorem derivedAssertionSuggestionCosted_cost_le (fact : NamedDerivedFact) :
    (derivedAssertionSuggestionCosted fact).cost ≤ 23 := by
  cases fact <;> unfold derivedAssertionSuggestionCosted
  all_goals
    repeat' first
      | rw [Complexity.Costed.charge_cost]
      | split
      | rw [Complexity.Costed.pure_cost]
    all_goals omega

/-- Collect every classified target related to x, in declaration order.
Reports need all competing targets, whereas uniqueness checks stop at the
second. The accumulator charges initialization and each retained index.
As in cost-aware semantics (Niu et al., POPL 2022, doi:10.1145/3498670),
the value proof discards costs compositionally without changing the scan. -/
private def relatedCandidatesCosted (W T : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    Complexity.Costed (Array Nat) := Complexity.Costed.charge 1 <|
  foldDiagDomainCosted 0 T #[] (fun _ => false) fun out y => do
    let isMatch ← Complexity.Costed.andThen
      (Complexity.diagnosticUnaryCosted W T tables classification y w)
      (fun _ => Complexity.diagnosticBinaryCosted W T tables relation x y w)
    Complexity.Costed.charge 1 <|
      if isMatch then .tick (out.push y) 1 else .pure out

private theorem relatedCandidatesCosted_value (W T : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    (relatedCandidatesCosted W T tables classification relation x w).value =
      ((List.range T).filter fun y =>
        (Complexity.diagnosticUnaryCosted W T tables classification y w).value &&
        (Complexity.diagnosticBinaryCosted W T tables relation x y w).value).toArray := by
  let p := fun y =>
    (Complexity.diagnosticUnaryCosted W T tables classification y w).value &&
    (Complexity.diagnosticBinaryCosted W T tables relation x y w).value
  have scan (xs : List Nat) (out : Array Nat) :
      xs.foldl (fun out y => if p y then out.push y else out) out =
        out ++ (xs.filter p).toArray := by
    induction xs generalizing out with
    | nil => simp
    | cons y ys ih =>
        cases h : p y <;> simp [List.foldl_cons, h, ih]
  simpa only [relatedCandidatesCosted, Complexity.Costed.charge_value,
    foldDiagDomainCosted_value, ← List.range_eq_range', Bool.false_eq_true,
    ↓reduceIte, Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.andThen_value,
    apply_ite, Complexity.Costed.tick_value, Complexity.Costed.pure_value, Array.empty_append]
    using scan (List.range T) #[]

/-- At most 30 query operations, one match test, one retained-index write,
and three loop controls per thing. The initial empty array costs one. -/
private theorem relatedCandidatesCosted_cost_le (W T : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    (relatedCandidatesCosted W T tables classification relation x w).cost ≤ 1 + 35 * T := by
  have scan := foldDiagDomainCosted_cost_le 0 T (#[] : Array Nat) (fun _ => false)
    (fun out y => do
      let isMatch ← Complexity.Costed.andThen
        (Complexity.diagnosticUnaryCosted W T tables classification y w)
        (fun _ => Complexity.diagnosticBinaryCosted W T tables relation x y w)
      Complexity.Costed.charge 1 <|
        if isMatch then .tick (out.push y) 1 else .pure out) 32 (by
      intro out y hlo hhi
      have query := Complexity.Costed.andThen_cost_le
        (Complexity.diagnosticUnaryCosted W T tables classification y w)
        (fun _ => Complexity.diagnosticBinaryCosted W T tables relation x y w)
        12 17 (Complexity.diagnosticUnaryCosted_cost_le _ _ _ _ _ _)
        (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.charge_cost,
        Complexity.Costed.tick_cost, Complexity.Costed.pure_cost] <;> omega)
  simpa [relatedCandidatesCosted, Complexity.Costed.charge_cost, Nat.mul_comm]
    using Nat.add_le_add_left scan 1

private theorem relatedCandidatesCosted_sparse_value (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (classification : UnaryField) (relation : BinaryField) (x : Fin T) (w : Fin W) :
    (relatedCandidatesCosted W T tables classification relation x w).value =
      ((List.range T).filter fun y => tables.unaryLookup classification.toTableField y w &&
        tables.binaryLookup relation.toTableField x y w).toArray := by
  rw [relatedCandidatesCosted_value]
  congr 1
  apply List.filter_congr
  intro y hy
  have hy : y < T := List.mem_range.mp hy
  rw [Complexity.diagnosticUnaryCosted_value W T tables agreement classification ⟨y, hy⟩ w,
    Complexity.diagnosticBinaryCosted_value W T tables agreement relation x ⟨y, hy⟩ w]
  rfl

private theorem relatedCandidatesCosted_size_le (W T : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    (relatedCandidatesCosted W T tables classification relation x w).value.size ≤ T := by
  rw [relatedCandidatesCosted_value, List.size_toArray]
  exact (List.length_filter_le _ _).trans_eq List.length_range

/-- Collect every QuaIndividualOf target for the source, in declaration order.
The relation runs from source to target. Each coordinate occurs once even when
a fact is duplicated. The numeric loop allocates no list of candidate indices. -/
private def quaIndividualTargetsCosted (W T : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  Complexity.Costed.charge 1 <|
    foldDiagDomainCosted 0 T #[] (fun _ => false) fun out y => do
      let isTarget ← Complexity.diagnosticBinaryCosted W T tables .quaIndividualOf x y w
      if isTarget then Complexity.Costed.tick (out.push y) 2
      else Complexity.Costed.tick out 1

private theorem quaIndividualTargetsCosted_value (W T : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualTargetsCosted W T tables x w).value =
      ((List.range T).filter fun y =>
        (Complexity.diagnosticBinaryCosted W T tables .quaIndividualOf x y w).value).toArray := by
  let p := fun y => (Complexity.diagnosticBinaryCosted W T tables .quaIndividualOf x y w).value
  have scan (xs : List Nat) (out : Array Nat) :
      xs.foldl (fun out y => if p y then out.push y else out) out =
        out ++ (xs.filter p).toArray := by
    induction xs generalizing out with
    | nil => simp
    | cons y ys ih =>
        cases h : p y <;> simp [List.foldl_cons, h, ih]
  simpa only [quaIndividualTargetsCosted, Complexity.Costed.charge_value,
    foldDiagDomainCosted_value, ← List.range_eq_range', Bool.false_eq_true,
    ↓reduceIte, Bind.bind, Complexity.Costed.bind_value, apply_ite,
    Complexity.Costed.tick_value, Array.empty_append]
    using scan (List.range T) #[]

private theorem quaIndividualTargetsCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (quaIndividualTargetsCosted W T tables x w).value =
      ((List.range T).filter fun y => tables.binaryLookup "quaIndividualOf" x y w).toArray := by
  rw [quaIndividualTargetsCosted_value]
  congr 1
  apply List.filter_congr
  intro y hy
  exact Complexity.diagnosticBinaryCosted_value W T tables agreement .quaIndividualOf
    x ⟨y, List.mem_range.mp hy⟩ w

/-- Each target costs at most 17 for its guarded query, one branch, one
optional push, and three loop controls. Initializing the array adds one. -/
private theorem quaIndividualTargetsCosted_cost_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualTargetsCosted W T tables x w).cost ≤ 22 * T + 1 := by
  have scan := foldDiagDomainCosted_cost_le 0 T (#[] : Array Nat) (fun _ => false)
    (fun out y => do
      let isTarget ← Complexity.diagnosticBinaryCosted W T tables .quaIndividualOf x y w
      if isTarget then Complexity.Costed.tick (out.push y) 2
      else Complexity.Costed.tick out 1) 19 (by
      intro out y hlo hhi
      have hquery := Complexity.diagnosticBinaryCosted_cost_le W T tables .quaIndividualOf x y w
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.tick_cost] <;> omega)
  simpa [quaIndividualTargetsCosted, Complexity.Costed.charge_cost, Nat.mul_comm, Nat.add_comm]
    using Nat.add_le_add_right scan 1

private theorem quaIndividualTargetsCosted_size_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualTargetsCosted W T tables x w).value.size ≤ T := by
  rw [quaIndividualTargetsCosted_value, List.size_toArray]
  exact (List.length_filter_le _ _).trans_eq List.length_range

private theorem quaIndividualTargetsCosted_nodup
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualTargetsCosted W T tables x w).value.toList.Nodup := by
  rw [quaIndividualTargetsCosted_value]
  exact (List.nodup_range (n := T)).filter _

/-- Construct both QuaIndividual evidence rows for a source already resolved
to its thing index. The collector retains all targets for the name list.
The cost composes collection with names, text, and emitted rows, following
Niu et al.'s cost semantics (POPL 2022, doi:10.1145/3498670).
Field dispatch, source-name resolution, and output budgeting belong to the caller. -/
private def quaIndividualEvidenceCosted
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array String) := do
  let targets ← quaIndividualTargetsCosted W thingNames.size tables x w
  let xn ← indexedNameCosted thingNames x
  let assertion ← ((Complexity.Costed.pure "  - User assertion: `QuaIndividual(").appendString
    (.pure xn)).appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 3 <| if targets.isEmpty then
    Complexity.Costed.tick
      (out.push "  - Computed QuaIndividual: false, because no `QuaIndividualOf` fact has this thing on the left.") 2
  else do
    let row ← ((Complexity.Costed.pure "  - `QuaIndividualOf` candidate(s) exist: ").appendString
      (joinIndexedNamesCosted thingNames targets)).appendString
      (.pure "; inspect the corresponding §3.10 foundation diagnostics if certification still fails.")
    Complexity.Costed.tick (out.push row) 2

private theorem quaIndividualEvidenceCosted_value
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (quaIndividualEvidenceCosted W thingNames tables x w).value =
      let targets := (quaIndividualTargetsCosted W thingNames.size tables x w).value
      if targets.isEmpty then
        #[s!"  - User assertion: `QuaIndividual({indexedName thingNames x})`.",
          "  - Computed QuaIndividual: false, because no `QuaIndividualOf` fact has this thing on the left."]
      else
        #[s!"  - User assertion: `QuaIndividual({indexedName thingNames x})`.",
          s!"  - `QuaIndividualOf` candidate(s) exist: {String.intercalate ", " (targets.toList.map (indexedName thingNames))}; inspect the corresponding §3.10 foundation diagnostics if certification still fails."] := by
  simp only [quaIndividualEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    Complexity.Costed.tick_value, Complexity.Costed.charge_value, indexedNameCosted_value]
  split
  · rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
      Complexity.Costed.pure_value, Complexity.Costed.tick_value, joinIndexedNamesCosted_value]
    rfl

/-- Collection costs at most 22T+1. Rendering uses at most 9N+17 further
operations for N ≤ T targets: source name, target names, size/branch tests,
concatenations, output initialization, and two row writes/emissions. -/
private theorem quaIndividualEvidenceCosted_cost_le
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (quaIndividualEvidenceCosted W thingNames tables x w).cost ≤ 31 * thingNames.size + 18 := by
  have htargets := quaIndividualTargetsCosted_cost_le W thingNames.size tables x w
  have hsize := quaIndividualTargetsCosted_size_le W thingNames.size tables x w
  have hjoin := joinIndexedNamesCosted_cost_le thingNames
    (quaIndividualTargetsCosted W thingNames.size tables x w).value
  simp only [quaIndividualEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost, Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split
  · simp only [Complexity.Costed.tick_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
      Complexity.Costed.pure_cost, Complexity.Costed.tick_cost]
    omega

private theorem quaIndividualEvidenceCosted_size
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (quaIndividualEvidenceCosted W thingNames tables x w).value.size = 2 := by
  rw [quaIndividualEvidenceCosted_value]
  dsimp only
  split <;> rfl

/-- The required-missing text states the absent relation without another
model query. Reuse the source name in both positions and render the world once. -/
private def quaIndividualRequiredMissingCosted
    (worldNames thingNames : Array Name) (x w : Nat) : Complexity.Costed String := do
  let xn ← indexedNameCosted thingNames x
  let text := (Complexity.Costed.pure "`QuaIndividual(").appendString (.pure xn)
  let text := text.appendString (.pure ")` requires some `QuaIndividualOf(")
  let text := text.appendString (.pure xn)
  let text := text.appendString (.pure ", y)`; missing any such fact at `")
  let text := text.appendString (indexedNameCosted worldNames w)
  text.appendString (.pure "`.")

private theorem quaIndividualRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (x w : Nat) :
    (quaIndividualRequiredMissingCosted worldNames thingNames x w).value =
      s!"`QuaIndividual({indexedName thingNames x})` requires some `QuaIndividualOf({indexedName thingNames x}, y)`; missing any such fact at `{indexedName worldNames w}`." := by
  simp only [quaIndividualRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value, indexedNameCosted_value]
  rfl

/-- Two indexed names cost eight operations and six concatenations cost six.
The same count covers an out-of-range name rendered as #n. -/
private theorem quaIndividualRequiredMissingCosted_cost
    (worldNames thingNames : Array Name) (x w : Nat) :
    (quaIndividualRequiredMissingCosted worldNames thingNames x w).cost = 14 := by
  simp only [quaIndividualRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost, indexedNameCosted_cost]

private def qualityStatusEvidenceSpec
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array String :=
  let candidates := (relatedCandidatesCosted worldCount thingNames.size tables .qualityKind .inst x w).value
  if candidates.isEmpty then
    #[s!"  - Computed Quality: false, because `{indexedName thingNames x}` instantiates no `QualityKind` at this world."]
  else if candidates.size == 1 then
    let q := candidates[0]!
    #[s!"  - Computed Quality: true, uniquely witnessed by `QualityKind({indexedName thingNames q})` and `{indexedName thingNames x} :: {indexedName thingNames q}`."]
  else
    let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
    #[s!"  - Computed Quality: false, because `{indexedName thingNames x}` instantiates multiple quality kinds at this world: {rendered}."]

/-- Build one quality-status row, including all competing kinds when uniqueness
fails. Name rendering and joining use the same counted primitives as axiom
reports. Each size query, comparison, and branch costs three in total.
Concatenations are counted individually. Character copying remains outside
the primitive-call model. -/
private def qualityStatusEvidenceCosted
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array String) := do
  let candidates ← relatedCandidatesCosted worldCount thingNames.size tables .qualityKind .inst x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 3 <| if candidates.isEmpty then do
      let text ← Complexity.Costed.tick ("  - Computed Quality: false, because `" ++ xn) 1
      let text ← Complexity.Costed.tick
        (text ++ "` instantiates no `QualityKind` at this world.") 1
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      Complexity.Costed.tick (out.push text) 2
    else Complexity.Costed.charge 3 <| if h : candidates.size = 1 then do
      let q ← Complexity.Costed.tick candidates[0] 1
      let qn ← indexedNameCosted thingNames q
      let text ← Complexity.Costed.tick
        ("  - Computed Quality: true, uniquely witnessed by `QualityKind(" ++ qn) 1
      let text ← Complexity.Costed.tick (text ++ ")` and `") 1
      let text ← Complexity.Costed.tick (text ++ xn) 1
      let text ← Complexity.Costed.tick (text ++ " :: ") 1
      let text ← Complexity.Costed.tick (text ++ qn) 1
      let text ← Complexity.Costed.tick (text ++ "`.") 1
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      Complexity.Costed.tick (out.push text) 2
    else do
      let names ← joinIndexedNamesCosted thingNames candidates
      let text ← Complexity.Costed.tick ("  - Computed Quality: false, because `" ++ xn) 1
      let text ← Complexity.Costed.tick
        (text ++ "` instantiates multiple quality kinds at this world: ") 1
      let text ← Complexity.Costed.tick (text ++ names) 1
      let text ← Complexity.Costed.tick (text ++ ".") 1
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      Complexity.Costed.tick (out.push text) 2

private theorem qualityStatusEvidenceCosted_value
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStatusEvidenceCosted worldCount thingNames tables x w).value =
      qualityStatusEvidenceSpec worldCount thingNames tables x w := by
  unfold qualityStatusEvidenceCosted qualityStatusEvidenceSpec
  simp only [Bind.bind, Complexity.Costed.bind_value, indexedNameCosted_value,
    Complexity.Costed.charge_value]
  split <;> (try split) <;>
    simp_all [Complexity.Costed.bind_value, indexedNameCosted_value,
      Complexity.Costed.charge_value, Complexity.Costed.tick_value,
      joinIndexedNamesCosted_value]
  all_goals rfl

/-- Collection costs at most 35T + 1 and retains at most T indices. Rendering
the row costs at most 9N + 24 for N retained indices, giving 44T + 25 overall. -/
private theorem qualityStatusEvidenceCosted_cost_le
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStatusEvidenceCosted worldCount thingNames tables x w).cost ≤
      44 * thingNames.size + 25 := by
  have collected := relatedCandidatesCosted_cost_le worldCount thingNames.size tables .qualityKind .inst x w
  have size := relatedCandidatesCosted_size_le worldCount thingNames.size tables .qualityKind .inst x w
  have joined := joinIndexedNamesCosted_cost_le thingNames
    (relatedCandidatesCosted worldCount thingNames.size tables .qualityKind .inst x w).value
  unfold qualityStatusEvidenceCosted
  simp only [Bind.bind, Complexity.Costed.bind_cost, indexedNameCosted_cost,
    Complexity.Costed.charge_cost]
  split <;> (try split) <;>
    simp only [Complexity.Costed.charge_cost, Complexity.Costed.bind_cost,
      Complexity.Costed.tick_cost, indexedNameCosted_cost] <;> omega

private theorem qualityStatusEvidenceCosted_size
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStatusEvidenceCosted worldCount thingNames tables x w).value.size = 1 := by
  rw [qualityStatusEvidenceCosted_value]
  unfold qualityStatusEvidenceSpec
  dsimp only
  split <;> (try split) <;> rfl

/-- Explain missing or competing quality-kind instantiations. The source name
is rendered once and reused. Candidate names and the current world use the
shared counted renderers, and every surrounding concatenation adds one. -/
private def qualityRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed String := do
  let candidates ← relatedCandidatesCosted worldNames.size thingNames.size tables .qualityKind .inst x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 3 <| if candidates.isEmpty then
    let text := Complexity.Costed.pure "`Quality("
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ")` requires exactly one `QualityKind` instantiation; missing any `QualityKind(k)` with `")
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure " :: k` at `")
    let text := text.appendString (indexedNameCosted worldNames w)
    text.appendString (Complexity.Costed.pure "`.")
  else
    let text := Complexity.Costed.pure "`Quality("
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ")` requires exactly one `QualityKind` instantiation; found competing quality kinds ")
    let text := text.appendString (joinIndexedNamesCosted thingNames candidates)
    let text := text.appendString (Complexity.Costed.pure " at `")
    let text := text.appendString (indexedNameCosted worldNames w)
    text.appendString (Complexity.Costed.pure "`.")

private theorem qualityRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityRequiredMissingCosted worldNames thingNames tables x w).value =
      let candidates := (relatedCandidatesCosted worldNames.size thingNames.size tables .qualityKind .inst x w).value
      if candidates.isEmpty then
        s!"`Quality({indexedName thingNames x})` requires exactly one `QualityKind` instantiation; missing any `QualityKind(k)` with `{indexedName thingNames x} :: k` at `{indexedName worldNames w}`."
      else
        let rendered := String.intercalate ", " (candidates.toList.map (indexedName thingNames))
        s!"`Quality({indexedName thingNames x})` requires exactly one `QualityKind` instantiation; found competing quality kinds {rendered} at `{indexedName worldNames w}`." := by
  simp only [qualityRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, indexedNameCosted_value]
  split
  all_goals simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    indexedNameCosted_value, joinIndexedNamesCosted_value]
  all_goals rfl

/-- Collection costs at most 35T+1 for T things. Beyond the candidate join,
two indexed names, six concatenations, and the size test cost 17. Joining
N ≤ T names costs at most 9N+1, giving the total bound 44T+19. -/
private theorem qualityRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityRequiredMissingCosted worldNames thingNames tables x w).cost ≤ 44 * thingNames.size + 19 := by
  have collected := relatedCandidatesCosted_cost_le worldNames.size thingNames.size tables .qualityKind .inst x w
  have size := relatedCandidatesCosted_size_le worldNames.size thingNames.size tables .qualityKind .inst x w
  have joined := joinIndexedNamesCosted_cost_le thingNames
    (relatedCandidatesCosted worldNames.size thingNames.size tables .qualityKind .inst x w).value
  simp only [qualityRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split
  all_goals simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    indexedNameCosted_cost]
  all_goals omega

/-- Explain missing or competing quality-type associations. The query uses
the supplied world, although this message does not display its name. Candidate
names retain declaration order and the source name is rendered once. -/
private def qualityStructureRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed String := do
  let candidates ← relatedCandidatesCosted worldNames.size thingNames.size tables .qualityType .associatedWith x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 3 <| if candidates.isEmpty then
    let text := Complexity.Costed.pure "`QualityStructure("
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ")` requires exactly one associated `QualityType`; missing any `AssociatedWith(")
    let text := text.appendString (Complexity.Costed.pure xn)
    text.appendString (Complexity.Costed.pure ", t)` where `QualityType(t)` holds.")
  else
    let text := Complexity.Costed.pure "`QualityStructure("
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ")` requires exactly one associated `QualityType`; found competing associated quality types ")
    let text := text.appendString (joinIndexedNamesCosted thingNames candidates)
    text.appendString (Complexity.Costed.pure ".")

private theorem qualityStructureRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureRequiredMissingCosted worldNames thingNames tables x w).value =
      let candidates := (relatedCandidatesCosted worldNames.size thingNames.size tables .qualityType .associatedWith x w).value
      if candidates.isEmpty then
        s!"`QualityStructure({indexedName thingNames x})` requires exactly one associated `QualityType`; missing any `AssociatedWith({indexedName thingNames x}, t)` where `QualityType(t)` holds."
      else
        let rendered := String.intercalate ", " (candidates.toList.map (indexedName thingNames))
        s!"`QualityStructure({indexedName thingNames x})` requires exactly one associated `QualityType`; found competing associated quality types {rendered}." := by
  simp only [qualityStructureRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, indexedNameCosted_value]
  split
  all_goals simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    joinIndexedNamesCosted_value]
  all_goals rfl

/-- Collection costs at most 35T+1. The source name, four concatenations, and
the size test add 11. Joining N ≤ T candidate names adds at most 9N+1,
giving 44T+13 for T things. -/
private theorem qualityStructureRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureRequiredMissingCosted worldNames thingNames tables x w).cost ≤ 44 * thingNames.size + 13 := by
  have collected := relatedCandidatesCosted_cost_le worldNames.size thingNames.size tables .qualityType .associatedWith x w
  have size := relatedCandidatesCosted_size_le worldNames.size thingNames.size tables .qualityType .associatedWith x w
  have joined := joinIndexedNamesCosted_cost_le thingNames
    (relatedCandidatesCosted worldNames.size thingNames.size tables .qualityType .associatedWith x w).value
  simp only [qualityStructureRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split
  all_goals simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
  all_goals omega

private def qualityStructureEvidenceSpec
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array String :=
  let candidates := (relatedCandidatesCosted worldNames.size thingNames.size
    tables .qualityType .associatedWith x w).value
  if candidates.isEmpty then
    #[
      s!"  - User assertion: `QualityStructure({indexedName thingNames x})`.",
      s!"  - Computed QualityStructure: false, because `{indexedName thingNames x}` is not associated with any `QualityType` at `{indexedName worldNames w}`."
    ]
  else if candidates.size == 1 then
    #[
      s!"  - User assertion: `QualityStructure({indexedName thingNames x})`.",
      s!"  - Computed QualityStructure: true, uniquely associated with `{indexedName thingNames candidates[0]!}`."
    ]
  else
    let rendered := String.intercalate ", " (candidates.toList.map (indexedName thingNames))
    #[
      s!"  - User assertion: `QualityStructure({indexedName thingNames x})`.",
      s!"  - Computed QualityStructure: false, because multiple associated quality types are present: {rendered}."
    ]

/-- Emit the assertion row followed by the computed quality-structure status.
A unique association uses its sole indexed target. Competing associations
retain all target names in declaration order. This follows the compositional
cost method of Niu et al. (POPL 2022, doi:10.1145/3498670): the output carries
the costs of collection, names, control, text, and both emitted rows. -/
private def qualityStructureEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array String) := do
  let candidates ← relatedCandidatesCosted worldNames.size thingNames.size tables .qualityType .associatedWith x w
  let xn ← indexedNameCosted thingNames x
  let assertion ← ((Complexity.Costed.pure "  - User assertion: `QualityStructure(").appendString
    (.pure xn)).appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 3 <| if candidates.isEmpty then do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed QualityStructure: false, because `"
      let text := text.appendString (Complexity.Costed.pure xn)
      let text := text.appendString (Complexity.Costed.pure "` is not associated with any `QualityType` at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (Complexity.Costed.pure "`.")
    Complexity.Costed.tick (out.push row) 2
  else Complexity.Costed.charge 3 <| if h : candidates.size = 1 then do
    let q ← Complexity.Costed.tick candidates[0] 1
    let row ← do
      let text := Complexity.Costed.pure "  - Computed QualityStructure: true, uniquely associated with `"
      let text := text.appendString (indexedNameCosted thingNames q)
      text.appendString (Complexity.Costed.pure "`.")
    Complexity.Costed.tick (out.push row) 2
  else do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed QualityStructure: false, because multiple associated quality types are present: "
      let text := text.appendString (joinIndexedNamesCosted thingNames candidates)
      text.appendString (Complexity.Costed.pure ".")
    Complexity.Costed.tick (out.push row) 2

private theorem qualityStructureEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureEvidenceCosted worldNames thingNames tables x w).value =
      qualityStructureEvidenceSpec worldNames thingNames tables x w := by
  unfold qualityStructureEvidenceCosted qualityStructureEvidenceSpec
  simp only [Bind.bind, Complexity.Costed.bind_value, indexedNameCosted_value,
    Complexity.Costed.charge_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value]
  split <;> (try split) <;>
    simp_all [Complexity.Costed.bind_value, indexedNameCosted_value,
      Complexity.Costed.charge_value, Complexity.Costed.tick_value,
      Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
      joinIndexedNamesCosted_value]
  all_goals exact ⟨rfl, rfl⟩

/-- Collection costs at most 35T+1 for T things and retains N ≤ T indices.
The remaining names, text, size tests, and row operations cost at most 9N+24.
Together they give the bound 44T+25 for the complete two-row component. -/
private theorem qualityStructureEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureEvidenceCosted worldNames thingNames tables x w).cost ≤ 44 * thingNames.size + 25 := by
  have collected := relatedCandidatesCosted_cost_le worldNames.size thingNames.size tables .qualityType .associatedWith x w
  have size := relatedCandidatesCosted_size_le worldNames.size thingNames.size tables .qualityType .associatedWith x w
  have joined := joinIndexedNamesCosted_cost_le thingNames
    (relatedCandidatesCosted worldNames.size thingNames.size tables .qualityType .associatedWith x w).value
  simp only [qualityStructureEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
  split <;> (try split) <;>
    simp only [Complexity.Costed.charge_cost, Complexity.Costed.bind_cost,
      Complexity.Costed.tick_cost, Complexity.Costed.appendString_cost,
      Complexity.Costed.pure_cost, indexedNameCosted_cost] <;> omega

private theorem qualityStructureEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureEvidenceCosted worldNames thingNames tables x w).value.size = 2 := by
  rw [qualityStructureEvidenceCosted_value]
  unfold qualityStructureEvidenceSpec
  dsimp only
  split <;> (try split) <;> rfl

/-- Prepend the Quality assertion to its counted status row. Array append
visits the status array once, charging its read, write, and loop control.
Both child rows already charge their own emission. -/
private def qualityEvidenceCosted
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let assertion ← ((Complexity.Costed.pure "  - User assertion: `Quality(").appendString
    (.pure xn)).appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  let status ← qualityStatusEvidenceCosted W thingNames tables x w
  Complexity.Costed.appendArray out status

private theorem qualityEvidenceCosted_value
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityEvidenceCosted W thingNames tables x w).value =
      #[s!"  - User assertion: `Quality({indexedName thingNames x})`."] ++
        qualityStatusEvidenceSpec W thingNames tables x w := by
  simp only [qualityEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    Complexity.Costed.tick_value, indexedNameCosted_value,
    Complexity.Costed.appendArray_value, qualityStatusEvidenceCosted_value]
  rfl

/-- The assertion row costs nine operations. Copying the one-row status array
costs three. The complete bound adds these twelve to the status-row bound. -/
private theorem qualityEvidenceCosted_cost_le
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityEvidenceCosted W thingNames tables x w).cost ≤ 44 * thingNames.size + 37 := by
  have hstatus := qualityStatusEvidenceCosted_cost_le W thingNames tables x w
  simp only [qualityEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost, indexedNameCosted_cost,
    Complexity.Costed.appendArray_cost, qualityStatusEvidenceCosted_size]
  omega

private theorem qualityEvidenceCosted_size
    (W : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityEvidenceCosted W thingNames tables x w).value.size = 2 := by
  simp only [qualityEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.appendArray_value,
    Array.size_append, Array.size_push, Array.size_empty, qualityStatusEvidenceCosted_size]

/-- Return the first functioning source instance without a distinct functioning
target instance. Ineligible sources skip target search. The target conjunction
is left-associated: even a failed distinctness test incurs both branch tests.
The inner loop stops at its first witness, and the outer loop at its first failure. -/
private def firstFunctionalDependenceFailureCosted
    (W T : Nat) (tables : FactTables) (sourceType targetType w : Nat) :
    Complexity.Costed (Option Nat) :=
  findDiagDomainCosted T fun x =>
    ((Complexity.diagnosticBinaryCosted W T tables .inst x sourceType w).andThen
      fun _ => Complexity.diagnosticBinaryCosted W T tables .functionsAs x sourceType w).andThen
      fun _ => (Complexity.anyFinCosted T fun y =>
        ((Complexity.Costed.tick (y.val != x) 1).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .functionsAs y targetType w).not

private theorem firstFunctionalDependenceFailureCosted_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (sourceType targetType : Fin T) (w : Fin W) :
    (firstFunctionalDependenceFailureCosted W T tables sourceType targetType w).value =
      (List.range T).find? (fun x =>
        (tables.binaryLookup "inst" x sourceType w &&
          tables.binaryLookup "functionsAs" x sourceType w) &&
        !((List.finRange T).any fun y =>
          (y.val != x && tables.binaryLookup "inst" y targetType w) &&
            tables.binaryLookup "functionsAs" y targetType w)) := by
  apply findDiagDomainCosted_value
  intro x hx
  simp only [Complexity.Costed.andThen_value, Complexity.Costed.not_value,
    Complexity.anyFinCosted_eq_list, Complexity.anyListCosted_value,
    Complexity.Costed.tick_value,
    Complexity.diagnosticBinaryCosted_value W T tables agreement .inst ⟨x, hx⟩ sourceType w,
    Complexity.diagnosticBinaryCosted_value W T tables agreement .functionsAs ⟨x, hx⟩ sourceType w,
    Complexity.diagnosticBinaryCosted_value W T tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

/-- Two source queries cost at most 35. Target candidates cost at most 39,
including two loop controls. Negation, the source branch, and four outer
search controls give the bound T(39T + 41). -/
private theorem firstFunctionalDependenceFailureCosted_cost_le
    (W T : Nat) (tables : FactTables) (sourceType targetType w : Nat) :
    (firstFunctionalDependenceFailureCosted W T tables sourceType targetType w).cost ≤
      T * (39 * T + 41) := by
  have targets (x : Nat) :
      (Complexity.anyFinCosted T fun y =>
        ((Complexity.Costed.tick (y.val != x) 1).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .functionsAs y targetType w).cost ≤
        39 * T := by
    rw [Complexity.anyFinCosted_eq_list]
    have h := Complexity.anyListCosted_cost_le (List.finRange T)
      (fun y => ((Complexity.Costed.tick (y.val != x) 1).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .functionsAs y targetType w)
      37 (by
        intro y hy
        exact Complexity.Costed.andThen_cost_le _ _ 19 17
          (Complexity.Costed.andThen_cost_le _ _ 1 17 (by rfl)
            (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _))
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _))
    simpa [Nat.mul_comm] using h
  have h := findDiagDomainCosted_cost_le T
    (fun x =>
      ((Complexity.diagnosticBinaryCosted W T tables .inst x sourceType w).andThen
        fun _ => Complexity.diagnosticBinaryCosted W T tables .functionsAs x sourceType w).andThen
        fun _ => (Complexity.anyFinCosted T fun y =>
          ((Complexity.Costed.tick (y.val != x) 1).andThen
            fun _ => Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
            fun _ => Complexity.diagnosticBinaryCosted W T tables .functionsAs y targetType w).not)
    (39 * T + 37) (by
      intro x hx
      refine le_trans (Complexity.Costed.andThen_cost_le _ _ 35 (39 * T + 1) ?_ ?_) ?_
      · exact Complexity.Costed.andThen_cost_le _ _ 17 17
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
      · simpa only [Complexity.Costed.not_cost] using Nat.add_le_add_right (targets x) 1
      · omega)
  have reassociate (n : Nat) : n + 37 + 4 = n + 41 := by omega
  simpa only [firstFunctionalDependenceFailureCosted, reassociate] using h

/-- Return the first source instance without a target instance that constitutes
it. The relation is directed from source to target. Target search runs only
for source instances and stops at its first witness. -/
private def firstConstitutionalDependenceFailureCosted
    (W T : Nat) (tables : FactTables) (sourceType targetType w : Nat) :
    Complexity.Costed (Option Nat) :=
  findDiagDomainCosted T fun x =>
    (Complexity.diagnosticBinaryCosted W T tables .inst x sourceType w).andThen
      fun _ => (Complexity.anyFinCosted T fun y =>
        (Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .constitutedBy x y w).not

private theorem firstConstitutionalDependenceFailureCosted_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (sourceType targetType : Fin T) (w : Fin W) :
    (firstConstitutionalDependenceFailureCosted W T tables sourceType targetType w).value =
      (List.range T).find? (fun x => tables.binaryLookup "inst" x sourceType w &&
        !((List.finRange T).any fun y => tables.binaryLookup "inst" y targetType w &&
          tables.binaryLookup "constitutedBy" x y w)) := by
  apply findDiagDomainCosted_value
  intro x hx
  simp only [Complexity.Costed.andThen_value, Complexity.Costed.not_value,
    Complexity.anyFinCosted_eq_list, Complexity.anyListCosted_value,
    Complexity.diagnosticBinaryCosted_value W T tables agreement .inst ⟨x, hx⟩ sourceType w,
    Complexity.diagnosticBinaryCosted_value W T tables agreement .constitutedBy ⟨x, hx⟩,
    Complexity.diagnosticBinaryCosted_value W T tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

/-- The source query costs at most 17. Each target costs at most 35 for its
queries and branch, plus two loop controls. Negation, the source branch, and
four outer search controls give T(37T + 23). -/
private theorem firstConstitutionalDependenceFailureCosted_cost_le
    (W T : Nat) (tables : FactTables) (sourceType targetType w : Nat) :
    (firstConstitutionalDependenceFailureCosted W T tables sourceType targetType w).cost ≤
      T * (37 * T + 23) := by
  have targets (x : Nat) :
      (Complexity.anyFinCosted T fun y =>
        (Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .constitutedBy x y w).cost ≤
        37 * T := by
    rw [Complexity.anyFinCosted_eq_list]
    have h := Complexity.anyListCosted_cost_le (List.finRange T)
      (fun y => (Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
        fun _ => Complexity.diagnosticBinaryCosted W T tables .constitutedBy x y w)
      35 (by
        intro y hy
        exact Complexity.Costed.andThen_cost_le _ _ 17 17
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _))
    simpa [Nat.mul_comm] using h
  have h := findDiagDomainCosted_cost_le T
    (fun x => (Complexity.diagnosticBinaryCosted W T tables .inst x sourceType w).andThen
      fun _ => (Complexity.anyFinCosted T fun y =>
        (Complexity.diagnosticBinaryCosted W T tables .inst y targetType w).andThen
          fun _ => Complexity.diagnosticBinaryCosted W T tables .constitutedBy x y w).not)
    (37 * T + 19) (by
      intro x hx
      refine le_trans (Complexity.Costed.andThen_cost_le _ _ 17 (37 * T + 1) ?_ ?_) ?_
      · exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _
      · simpa only [Complexity.Costed.not_cost] using Nat.add_le_add_right (targets x) 1
      · omega)
  have reassociate (n : Nat) : n + 19 + 4 = n + 23 := by omega
  simpa only [firstConstitutionalDependenceFailureCosted, reassociate] using h

/-- The generic failure text includes the declared relation and current world.
The summary and indexed-name renderers carry their own costs. Each surrounding
text append adds one, including when the world is rendered as an out-of-range index. -/
private def requiredMissingFallbackCosted
    (worldNames : Array Name) (fact : NamedDerivedFact) (w : Nat) : Complexity.Costed String :=
  let text := Complexity.Costed.pure "asserted derived relation `"
  let text := text.appendString (namedDerivedFactSummaryCosted fact)
  let text := text.appendString (.pure "` must be true under the computed semantics at `")
  let text := text.appendString (indexedNameCosted worldNames w)
  text.appendString (.pure "`, but its definition evaluates to false.")

private theorem requiredMissingFallbackCosted_value
    (worldNames : Array Name) (fact : NamedDerivedFact) (w : Nat) :
    (requiredMissingFallbackCosted worldNames fact w).value =
      s!"asserted derived relation `{namedDerivedFactSummary fact}` must be true under the computed semantics at `{indexedName worldNames w}`, but its definition evaluates to false." := by
  simp only [requiredMissingFallbackCosted, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, indexedNameCosted_value, namedDerivedFactSummary]
  rfl

private theorem requiredMissingFallbackCosted_cost_le
    (worldNames : Array Name) (fact : NamedDerivedFact) (w : Nat) :
    (requiredMissingFallbackCosted worldNames fact w).cost ≤ 18 := by
  have h := namedDerivedFactSummaryCosted_cost_le fact
  simp only [requiredMissingFallbackCosted, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, indexedNameCosted_cost]
  omega

/-- Prefer the first declared external-dependence candidate, otherwise the first
inherence target. An empty scan returns no candidate; the report does not invent
a thing-zero fallback. Candidate-array initialization is charged by the collector. -/
private def firstDeclaredOrInherenceCandidateCosted
    (W T : Nat) (tables : FactTables) (x w : Nat) : Complexity.Costed (Option Nat) := do
  let declared ← declaredExternalCandidatesCosted T tables x w
  if h : 0 < declared.size then
    Complexity.Costed.tick (some declared[0]) 3
  else
    Complexity.Costed.charge 2 <|
      findDiagDomainCosted T fun y => Complexity.diagnosticBinaryCosted W T tables .inheresIn x y w

private theorem firstDeclaredOrInherenceCandidateCosted_cost_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (firstDeclaredOrInherenceCandidateCosted W T tables x w).cost ≤
      T * (4 * tables.derivedProps.size + 42) + 4 := by
  have hdeclared := declaredExternalCandidatesCosted_cost_le T tables x w
  have hscan := findDiagDomainCosted_cost_le T
    (fun y => Complexity.diagnosticBinaryCosted W T tables .inheresIn x y w)
    17 (by intro y hy; exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
  simp only [firstDeclaredOrInherenceCandidateCosted, Bind.bind, Complexity.Costed.bind_cost]
  split <;> simp only [Complexity.Costed.tick_cost, Complexity.Costed.charge_cost]
  all_goals simp only [Nat.mul_add] at hdeclared ⊢
  all_goals omega

/-- The list is a specification of ascending-coordinate search, not a runtime
allocation. Sparse correspondence requires agreeing tables and valid indices. -/
private theorem firstDeclaredOrInherenceCandidateCosted_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (firstDeclaredOrInherenceCandidateCosted W T tables x w).value =
      let declared := (declaredExternalCandidatesCosted T tables x w).value
      if h : 0 < declared.size then some declared[0] else
        (List.range T).find? (fun y => tables.binaryLookup "inheresIn" x y w) := by
  simp only [firstDeclaredOrInherenceCandidateCosted, Bind.bind, Complexity.Costed.bind_value]
  split
  · rfl
  · simp only [Complexity.Costed.charge_value]
    apply findDiagDomainCosted_value
    intro y hy
    exact Complexity.diagnosticBinaryCosted_value W T tables agreement .inheresIn x ⟨y, hy⟩ w

/-- Construct the complete required-missing explanation for a resolved external
mode. A false mode classification skips candidate collection and failure-reason
search. Repeated occurrences of the source name reuse one rendered string.
Following compositional cost semantics (Niu et al., POPL 2022,
doi:10.1145/3498670), every child search and text append contributes its cost.
The caller separately charges field dispatch and source-name resolution. -/
private def externalModeRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed String := do
  let mode ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .mode x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 2 <| if !mode then
    let text := Complexity.Costed.pure "`ExternallyDependentMode("
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ")` requires `Mode(")
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ")` and some computed `ExternallyDependent(")
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ", y)`; missing `Mode(")
    let text := text.appendString (Complexity.Costed.pure xn)
    let text := text.appendString (Complexity.Costed.pure ")` at `")
    let text := text.appendString (indexedNameCosted worldNames w)
    text.appendString (Complexity.Costed.pure "`.")
  else do
    let candidate ← firstDeclaredOrInherenceCandidateCosted worldNames.size thingNames.size tables x w
    Complexity.Costed.charge 1 <| match candidate with
    | some y =>
      let text := Complexity.Costed.pure "`ExternallyDependentMode("
      let text := text.appendString (Complexity.Costed.pure xn)
      let text := text.appendString (Complexity.Costed.pure ")` requires `Mode(")
      let text := text.appendString (Complexity.Costed.pure xn)
      let text := text.appendString (Complexity.Costed.pure ")` and at least one computed `ExternallyDependent(")
      let text := text.appendString (Complexity.Costed.pure xn)
      let text := text.appendString (Complexity.Costed.pure ", y)`; missing such a witness. Candidate `")
      let text := text.appendString (indexedNameCosted thingNames y)
      let text := text.appendString (Complexity.Costed.pure "` fails because ")
      text.appendString (firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w)
    | none =>
      let text := Complexity.Costed.pure "`ExternallyDependentMode("
      let text := text.appendString (Complexity.Costed.pure xn)
      let text := text.appendString (Complexity.Costed.pure ")` requires `Mode(")
      let text := text.appendString (Complexity.Costed.pure xn)
      let text := text.appendString (Complexity.Costed.pure ")` and at least one computed `ExternallyDependent(")
      let text := text.appendString (Complexity.Costed.pure xn)
      text.appendString (Complexity.Costed.pure ", y)`; missing any candidate witness and any relevant `InheresIn` bearer evidence.")

private theorem externalModeRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (w : Fin worldNames.size) :
    (externalModeRequiredMissingCosted worldNames thingNames tables x w).value =
      if !tables.unaryLookup "mode" x w then
        s!"`ExternallyDependentMode({indexedName thingNames x})` requires `Mode({indexedName thingNames x})` and some computed `ExternallyDependent({indexedName thingNames x}, y)`; missing `Mode({indexedName thingNames x})` at `{indexedName worldNames w}`."
      else
        match (firstDeclaredOrInherenceCandidateCosted worldNames.size thingNames.size tables x w).value with
        | some y =>
            s!"`ExternallyDependentMode({indexedName thingNames x})` requires `Mode({indexedName thingNames x})` and at least one computed `ExternallyDependent({indexedName thingNames x}, y)`; missing such a witness. Candidate `{indexedName thingNames y}` fails because {firstExternallyDependentFailureReason worldNames thingNames tables x y w}"
        | none =>
            s!"`ExternallyDependentMode({indexedName thingNames x})` requires `Mode({indexedName thingNames x})` and at least one computed `ExternallyDependent({indexedName thingNames x}, y)`; missing any candidate witness and any relevant `InheresIn` bearer evidence." := by
  have hmode := Complexity.diagnosticUnaryCosted_value worldNames.size thingNames.size
    tables agreement .mode x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .mode x w).value =
    tables.unaryLookup "mode" x w at hmode
  simp only [externalModeRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    indexedNameCosted_value, Complexity.Costed.charge_value, hmode]
  split
  · simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
      indexedNameCosted_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstDeclaredOrInherenceCandidateCosted worldNames.size thingNames.size tables x w).value
    all_goals simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
      indexedNameCosted_value, firstExternallyDependentFailureReason]
    all_goals rfl

/-- Declared selection costs at most T(4D+42)+4 for T things and D assertions.
The selected reason costs at most 30W+T(60W+40)+28 for W worlds. Mode/name
queries, branches, and concatenations add at most 32. The bound counts calls
to string primitives, not the characters copied by those calls. -/
private theorem externalModeRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externalModeRequiredMissingCosted worldNames thingNames tables x w).cost ≤
      thingNames.size * (4 * tables.derivedProps.size + 42) +
        (30 * worldNames.size + thingNames.size * (60 * worldNames.size + 40) + 28) + 36 := by
  have hmode := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .mode x w
  have hcandidate := firstDeclaredOrInherenceCandidateCosted_cost_le
    worldNames.size thingNames.size tables x w
  have hreason (y : Nat) := firstExternallyDependentFailureReasonCosted_cost_le
    worldNames thingNames tables x y w
  simp only [externalModeRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split
  · simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
      indexedNameCosted_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstDeclaredOrInherenceCandidateCosted worldNames.size thingNames.size tables x w).value with
    | none =>
        simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
        omega
    | some y =>
        have hr := hreason y
        simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
          indexedNameCosted_cost]
        omega

/-- Required-missing text states the absent membership without another query.
Name resolution and the outer report budget belong to the caller. -/
private def nonEmptySetRequiredMissingCosted
    (worldNames thingNames : Array Name) (x w : Nat) : Complexity.Costed String := do
  let xn ← indexedNameCosted thingNames x
  let text := Complexity.Costed.pure "`NonEmptySet("
  let text := text.appendString (.pure xn)
  let text := text.appendString (.pure ")` requires some `MemberOf(member, ")
  let text := text.appendString (.pure xn)
  let text := text.appendString (.pure ")`; missing any member at `")
  let text := text.appendString (indexedNameCosted worldNames w)
  text.appendString (.pure "`.")

private theorem nonEmptySetRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (x w : Nat) :
    (nonEmptySetRequiredMissingCosted worldNames thingNames x w).value =
      s!"`NonEmptySet({indexedName thingNames x})` requires some `MemberOf(member, {indexedName thingNames x})`; missing any member at `{indexedName worldNames w}`." := by
  simp only [nonEmptySetRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    indexedNameCosted_value]
  rfl

/-- Two name renderings and six concatenations cost 14 primitive calls. -/
private theorem nonEmptySetRequiredMissingCosted_cost
    (worldNames thingNames : Array Name) (x w : Nat) :
    (nonEmptySetRequiredMissingCosted worldNames thingNames x w).cost = 14 := by
  simp only [nonEmptySetRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    indexedNameCosted_cost]

/-- The first incoming MemberOf edge supplies the witness, in declaration order.
Query costs compose with text and array construction, following Niu et al.'s
cost semantics (POPL 2022, doi:10.1145/3498670). -/
private def nonEmptySetEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array String) := do
  let member ← firstRelatedThingCosted worldNames.size thingNames.size tables .memberOf x w
  let xn ← indexedNameCosted thingNames x
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `NonEmptySet("
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 1 <| match member with
  | some member => do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed NonEmptySet: true, witnessed by `MemberOf("
      let text := text.appendString (indexedNameCosted thingNames member)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ")` at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
    Complexity.Costed.tick (out.push row) 2
  | none => do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed NonEmptySet: false, because no `MemberOf(_, "
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ")` fact holds at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
    Complexity.Costed.tick (out.push row) 2

private theorem nonEmptySetEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (nonEmptySetEvidenceCosted worldNames thingNames tables x w).value =
      match (firstRelatedThingCosted worldNames.size thingNames.size tables .memberOf x w).value with
      | some member => #[s!"  - User assertion: `NonEmptySet({indexedName thingNames x})`.",
          s!"  - Computed NonEmptySet: true, witnessed by `MemberOf({indexedName thingNames member}, {indexedName thingNames x})` at `{indexedName worldNames w}`."]
      | none => #[s!"  - User assertion: `NonEmptySet({indexedName thingNames x})`.",
          s!"  - Computed NonEmptySet: false, because no `MemberOf(_, {indexedName thingNames x})` fact holds at `{indexedName worldNames w}`."] := by
  simp only [nonEmptySetEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    Complexity.Costed.tick_value, Complexity.Costed.charge_value, indexedNameCosted_value]
  cases (firstRelatedThingCosted worldNames.size thingNames.size tables .memberOf x w).value
  all_goals simp only [Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    Complexity.Costed.tick_value, indexedNameCosted_value]
  all_goals rfl

/-- For T things the search costs at most 21T. The larger rendering branch
adds 12 name operations, eight concatenations, one match, and five array
initialization/write/emission operations. The bound is monotone in T. -/
private theorem nonEmptySetEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (nonEmptySetEvidenceCosted worldNames thingNames tables x w).cost ≤
      21 * thingNames.size + 26 := by
  have hsearch := firstRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .memberOf x w
  simp only [nonEmptySetEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost, Complexity.Costed.charge_cost, indexedNameCosted_cost]
  cases (firstRelatedThingCosted worldNames.size thingNames.size tables .memberOf x w).value
  all_goals simp only [Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost, indexedNameCosted_cost]
  all_goals omega

private theorem nonEmptySetEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (nonEmptySetEvidenceCosted worldNames thingNames tables x w).value.size = 2 := by
  rw [nonEmptySetEvidenceCosted_value]
  cases (firstRelatedThingCosted worldNames.size thingNames.size tables .memberOf x w).value <;> rfl

/-- This text explains an already failed assertion. Only the forward Sub query
is needed to choose between a missing forward edge and a conflicting reverse edge. -/
private def properSubRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed String := do
  let sub ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .sub x y w
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  Complexity.Costed.charge 2 <| if !sub then
    let text := Complexity.Costed.pure "`ProperSub("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires `Sub(")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`; missing the forward `Sub` fact.")
  else
    let text := Complexity.Costed.pure "`ProperSub("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires absence of reverse `Sub`; conflicting `Sub(")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")` is present.")

private theorem properSubRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x y : Fin thingNames.size) (w : Fin worldNames.size) :
    (properSubRequiredMissingCosted worldNames thingNames tables x y w).value =
      if !tables.binaryLookup "sub" x y w then
        s!"`ProperSub({indexedName thingNames x}, {indexedName thingNames y})` requires `Sub({indexedName thingNames x}, {indexedName thingNames y})`; missing the forward `Sub` fact."
      else
        s!"`ProperSub({indexedName thingNames x}, {indexedName thingNames y})` requires absence of reverse `Sub`; conflicting `Sub({indexedName thingNames y}, {indexedName thingNames x})` is present." := by
  have hsub := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .sub x y w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .sub x y w).value =
    tables.binaryLookup "sub" x y w at hsub
  simp only [properSubRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, indexedNameCosted_value, hsub]
  split <;> rfl

/-- One query costs at most 17. Names cost eight, negation and branching cost
two, and either text has eight concatenations. -/
private theorem properSubRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubRequiredMissingCosted worldNames thingNames tables x y w).cost ≤ 35 := by
  have hsub := Complexity.diagnosticBinaryCosted_cost_le
    worldNames.size thingNames.size tables .sub x y w
  simp only [properSubRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split <;> simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost] <;> omega

/-- Evidence displays both relation values, so it evaluates both queries even
when the forward edge is absent. The Boolean checker can instead stop there.
Each displayed Boolean charges its own branch. -/
private def properSubEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Array String) := do
  let sub ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .sub x y w
  let reverse ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .sub y x w
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ProperSub("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let forwardRow ← do
    let text := Complexity.Costed.pure "  - Sub("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure "): ")
    let text := text.appendString (Complexity.Costed.tick (if sub then "true" else "false") 1)
    text.appendString (.pure ".")
  let reverseRow ← do
    let text := Complexity.Costed.pure "  - Reverse Sub("
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure "): ")
    let text := text.appendString (Complexity.Costed.tick (if reverse then "true" else "false") 1)
    text.appendString (.pure ".")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  let out ← Complexity.Costed.tick (out.push forwardRow) 2
  Complexity.Costed.tick (out.push reverseRow) 2

private theorem properSubEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x y : Fin thingNames.size) (w : Fin worldNames.size) :
    (properSubEvidenceCosted worldNames thingNames tables x y w).value =
      let sub := tables.binaryLookup "sub" x y w
      let reverse := tables.binaryLookup "sub" y x w
      #[s!"  - User assertion: `ProperSub({indexedName thingNames x}, {indexedName thingNames y})`.",
          s!"  - Sub({indexedName thingNames x}, {indexedName thingNames y}): {if sub then "true" else "false"}.",
        s!"  - Reverse Sub({indexedName thingNames y}, {indexedName thingNames x}): {if reverse then "true" else "false"}."] := by
  have hsub := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .sub x y w
  have hreverse := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .sub y x w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .sub x y w).value =
    tables.binaryLookup "sub" x y w at hsub
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .sub y x w).value =
    tables.binaryLookup "sub" y x w at hreverse
  dsimp only [properSubEvidenceCosted, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_value, hsub, hreverse]
  rfl

/-- Two queries cost at most 34. Rendering adds eight name operations, 16
concatenations, two Boolean branches, one array initialization, and six row
writes/emissions. String-character work is outside this primitive-call bound. -/
private theorem properSubEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubEvidenceCosted worldNames thingNames tables x y w).cost ≤ 67 := by
  have hsub := Complexity.diagnosticBinaryCosted_cost_le
    worldNames.size thingNames.size tables .sub x y w
  have hreverse := Complexity.diagnosticBinaryCosted_cost_le
    worldNames.size thingNames.size tables .sub y x w
  simp only [properSubEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost, indexedNameCosted_cost]
  omega

private theorem properSubEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubEvidenceCosted worldNames thingNames tables x y w).value.size = 3 := by
  simp only [properSubEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    Complexity.Costed.tick_value, indexedNameCosted_value]
  rfl

/-- Subset reports use the first left-only membership witness. Costs include
the search, names, text, and emitted rows, using the compositional method of
Niu et al. (POPL 2022, doi:10.1145/3498670). The caller supplies fallback text
and accounts for its construction, name resolution, and report budgeting. -/
private def subsetRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let failure ← firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w
  Complexity.Costed.charge 1 <| match failure with
  | none => .pure fallback
  | some z => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let text := Complexity.Costed.pure "`SubsetOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires every left member to be a right member; `")
    let text := text.appendString (indexedNameCosted thingNames z)
    let text := text.appendString (.pure "` is in `")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure "` but missing from `")
    let text := text.appendString (.pure yn)
    text.appendString (.pure "`.")

private theorem subsetRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (subsetRequiredMissingCosted worldNames thingNames tables x y w fallback).value =
      match (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value with
      | some z => s!"`SubsetOf({indexedName thingNames x}, {indexedName thingNames y})` requires every left member to be a right member; `{indexedName thingNames z}` is in `{indexedName thingNames x}` but missing from `{indexedName thingNames y}`."
      | none => fallback := by
  simp only [subsetRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value
  all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.pure_value,
    Complexity.Costed.appendString_value, indexedNameCosted_value]
  all_goals rfl

/-- A difference search costs at most 40T for T things. The witness branch
adds 12 name operations, ten concatenations, and one match. -/
private theorem subsetRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (subsetRequiredMissingCosted worldNames thingNames tables x y w fallback).cost ≤
      40 * thingNames.size + 23 := by
  have hsearch := firstRelationDifferenceCosted_cost_le
    worldNames.size thingNames.size tables .memberOf .memberOf x y w
  simp only [subsetRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value
  all_goals simp only [Complexity.Costed.bind_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.appendString_cost, indexedNameCosted_cost]
  all_goals omega

private def subsetEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : Complexity.Costed (Array String) := do
  let failure ← firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w
  Complexity.Costed.charge 1 <| match failure with
  | none => .tick #[] 1
  | some z => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let assertion ← do
      let text := Complexity.Costed.pure "  - User assertion: `SubsetOf("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yn)
      text.appendString (.pure ")`.")
    let row ← do
      let text := Complexity.Costed.pure "  - Computed SubsetOf: false, because `"
      let text := text.appendString (indexedNameCosted thingNames z)
      let text := text.appendString (.pure "` is a member of `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` but not of `")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure "` at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
    let out ← Complexity.Costed.tick (#[] : Array String) 1
    let out ← Complexity.Costed.tick (out.push assertion) 2
    Complexity.Costed.tick (out.push row) 2

private theorem subsetEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (subsetEvidenceCosted worldNames thingNames tables x y w).value =
      match (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value with
      | some z => #[s!"  - User assertion: `SubsetOf({indexedName thingNames x}, {indexedName thingNames y})`.",
          s!"  - Computed SubsetOf: false, because `{indexedName thingNames z}` is a member of `{indexedName thingNames x}` but not of `{indexedName thingNames y}` at `{indexedName worldNames w}`."]
      | none => #[] := by
  simp only [subsetEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value
  all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.pure_value,
    Complexity.Costed.appendString_value, Complexity.Costed.tick_value, indexedNameCosted_value]
  all_goals rfl

/-- Beyond the search, the witness branch uses 16 name operations, 12
concatenations, five array initialization/write/emission operations, and a match.
The no-witness branch initializes an empty array and renders no names. -/
private theorem subsetEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (subsetEvidenceCosted worldNames thingNames tables x y w).cost ≤
      40 * thingNames.size + 34 := by
  have hsearch := firstRelationDifferenceCosted_cost_le
    worldNames.size thingNames.size tables .memberOf .memberOf x y w
  simp only [subsetEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value
  all_goals simp only [Complexity.Costed.bind_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
  all_goals omega

private theorem subsetEvidenceCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (subsetEvidenceCosted worldNames thingNames tables x y w).value.size ≤ 2 := by
  rw [subsetEvidenceCosted_value]
  cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value <;> simp

/-- The Boolean subset check asks whether this same search has no witness.
Keep the witness instead of checking the Boolean and repeating the search.
The value theorem proves equality with that decision structure, including its
unreachable false-subset/no-witness branch. -/
private def properSubsetRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : Complexity.Costed String := do
  let failure ← firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  Complexity.Costed.charge 1 <| match failure with
  | some z =>
    let text := Complexity.Costed.pure "`ProperSubsetOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` first requires `SubsetOf`; `")
    let text := text.appendString (indexedNameCosted thingNames z)
    text.appendString (.pure "` is in the left set but missing from the right set.")
  | none =>
    let text := Complexity.Costed.pure "`ProperSubsetOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires strictness; missing a member of `")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure "` that is not also a member of `")
    let text := text.appendString (.pure xn)
    text.appendString (.pure "`.")

private theorem properSubsetRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetRequiredMissingCosted worldNames thingNames tables x y w).value =
      if !subsetLookup worldNames.size thingNames.size tables x y w then
        match (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value with
        | some z => s!"`ProperSubsetOf({indexedName thingNames x}, {indexedName thingNames y})` first requires `SubsetOf`; `{indexedName thingNames z}` is in the left set but missing from the right set."
        | none => s!"`ProperSubsetOf({indexedName thingNames x}, {indexedName thingNames y})` first requires `SubsetOf({indexedName thingNames x}, {indexedName thingNames y})`; that subset condition is false."
      else s!"`ProperSubsetOf({indexedName thingNames x}, {indexedName thingNames y})` requires strictness; missing a member of `{indexedName thingNames y}` that is not also a member of `{indexedName thingNames x}`." := by
  simp only [properSubsetRequiredMissingCosted, subsetLookup, subsetLookupCosted,
    Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value,
    Complexity.Costed.charge_value, indexedNameCosted_value]
  split <;> simp_all [Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, indexedNameCosted_value]
  all_goals rfl

/-- One search costs at most 40T for T things. Rendering adds at most 19:
three names, six concatenations, and one match. The strictness branch needs
two names and eight concatenations, totaling 17. -/
private theorem properSubsetRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetRequiredMissingCosted worldNames thingNames tables x y w).cost ≤
      40 * thingNames.size + 19 := by
  have hsearch := firstRelationDifferenceCosted_cost_le
    worldNames.size thingNames.size tables .memberOf .memberOf x y w
  simp only [properSubsetRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value
  all_goals simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    indexedNameCosted_cost]
  all_goals omega

private def properSubsetEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : Complexity.Costed (Array String) := do
  let failure ← firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ProperSubsetOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 1 <| match failure with
  | some z => do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed ProperSubsetOf: false, because the subset condition already fails: `"
      let text := text.appendString (indexedNameCosted thingNames z)
      let text := text.appendString (.pure "` is a member of `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` but not of `")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure "` at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
    Complexity.Costed.tick (out.push row) 2
  | none => do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed ProperSubsetOf: false, because no member of `"
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure "` is outside `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
    Complexity.Costed.tick (out.push row) 2

private theorem properSubsetEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetEvidenceCosted worldNames thingNames tables x y w).value =
      if !subsetLookup worldNames.size thingNames.size tables x y w then
        match (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value with
        | some z => #[s!"  - User assertion: `ProperSubsetOf({indexedName thingNames x}, {indexedName thingNames y})`.",
            s!"  - Computed ProperSubsetOf: false, because the subset condition already fails: `{indexedName thingNames z}` is a member of `{indexedName thingNames x}` but not of `{indexedName thingNames y}` at `{indexedName worldNames w}`."]
        | none => #[s!"  - User assertion: `ProperSubsetOf({indexedName thingNames x}, {indexedName thingNames y})`.",
            "  - Computed ProperSubsetOf: false, because the subset condition fails."]
      else #[s!"  - User assertion: `ProperSubsetOf({indexedName thingNames x}, {indexedName thingNames y})`.",
          s!"  - Computed ProperSubsetOf: false, because no member of `{indexedName thingNames y}` is outside `{indexedName thingNames x}` at `{indexedName worldNames w}`."] := by
  simp only [properSubsetEvidenceCosted, subsetLookup, subsetLookupCosted,
    Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value,
    Complexity.Costed.charge_value, indexedNameCosted_value]
  split <;> simp_all [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value]
  all_goals exact ⟨rfl, rfl⟩

/-- The witness branch adds 34 operations, as in SubsetOf evidence. The
strictness branch adds 28. Neither branch repeats the difference search. -/
private theorem properSubsetEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetEvidenceCosted worldNames thingNames tables x y w).cost ≤
      40 * thingNames.size + 34 := by
  have hsearch := firstRelationDifferenceCosted_cost_le
    worldNames.size thingNames.size tables .memberOf .memberOf x y w
  simp only [properSubsetEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    indexedNameCosted_cost, Complexity.Costed.tick_cost]
  cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value
  all_goals simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
  all_goals omega

private theorem properSubsetEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetEvidenceCosted worldNames thingNames tables x y w).value.size = 2 := by
  rw [properSubsetEvidenceCosted_value]
  split
  · cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .memberOf .memberOf x y w).value <;> rfl
  · rfl

/-- Required-missing text explains an assertion already found false. A failed
quality check skips the inherence search. The caller accounts for fallback
construction and name resolution separately. -/
private def simpleQualityRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let quality ← uniqueRelatedThingCosted worldNames.size thingNames.size tables .qualityKind .inst x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 2 <| if !quality then
    let text := Complexity.Costed.pure "`SimpleQuality("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ")` requires computed `Quality(")
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`; missing the quality condition.")
  else do
    let part ← firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w
    Complexity.Costed.charge 1 <| match part with
    | some y =>
      let text := Complexity.Costed.pure "`SimpleQuality("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ")` requires no thing to inhere in it; conflicting `InheresIn(")
      let text := text.appendString (indexedNameCosted thingNames y)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure xn)
      text.appendString (.pure ")` is present.")
    | none => .pure fallback

private theorem simpleQualityRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    (simpleQualityRequiredMissingCosted worldNames thingNames tables x w fallback).value =
      if !qualityLookup worldNames.size thingNames.size tables x w then
        s!"`SimpleQuality({indexedName thingNames x})` requires computed `Quality({indexedName thingNames x})`; missing the quality condition."
      else
        match (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value with
        | some y => s!"`SimpleQuality({indexedName thingNames x})` requires no thing to inhere in it; conflicting `InheresIn({indexedName thingNames y}, {indexedName thingNames x})` is present."
        | none => fallback := by
  simp only [simpleQualityRequiredMissingCosted, qualityLookup, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value, indexedNameCosted_value]
  split <;> simp_all only [ite_true]
  · simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value
    all_goals simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
      indexedNameCosted_value]
    all_goals rfl

/-- For T things, quality costs at most 34T+2 and the selected inherence search
at most 21T. Rendering and control add at most 17 operations. The caller
accounts for construction of the supplied fallback. -/
private theorem simpleQualityRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    (simpleQualityRequiredMissingCosted worldNames thingNames tables x w fallback).cost ≤
      55 * thingNames.size + 19 := by
  have hquality := uniqueRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .qualityKind .inst x w
  have hpart := firstRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .inheresIn x w
  simp only [simpleQualityRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split
  · simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value
    all_goals simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
      indexedNameCosted_cost]
    all_goals omega

/-- After a failed assertion, a successful quality check leaves only the
missing inhering part to explain. This component does not search for that part. -/
private def complexQualityRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Complexity.Costed String := do
  let quality ← uniqueRelatedThingCosted worldNames.size thingNames.size tables .qualityKind .inst x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 2 <| if !quality then
    let text := Complexity.Costed.pure "`ComplexQuality("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ")` requires computed `Quality(")
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`; missing the quality condition.")
  else
    let text := Complexity.Costed.pure "`ComplexQuality("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ")` requires at least one `InheresIn(part, ")
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`; missing any inhering part.")

private theorem complexQualityRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityRequiredMissingCosted worldNames thingNames tables x w).value =
      if !qualityLookup worldNames.size thingNames.size tables x w then
        s!"`ComplexQuality({indexedName thingNames x})` requires computed `Quality({indexedName thingNames x})`; missing the quality condition."
      else s!"`ComplexQuality({indexedName thingNames x})` requires at least one `InheresIn(part, {indexedName thingNames x})`; missing any inhering part." := by
  simp only [complexQualityRequiredMissingCosted, qualityLookup, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value, indexedNameCosted_value]
  split <;> simp_all only [ite_true] <;> rfl

/-- One name, four concatenations, negation, and branching add ten operations
to the quality check's 34T+2 bound, for T things. -/
private theorem complexQualityRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityRequiredMissingCosted worldNames thingNames tables x w).cost ≤
      34 * thingNames.size + 12 := by
  have hquality := uniqueRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .qualityKind .inst x w
  simp only [complexQualityRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split <;> simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost] <;> omega

/-- Evidence preserves the quality explanation or the first incoming inherence
witness. The failed-quality branch includes both the uniqueness check and the
separate status collector. Their costs compose through bind, as in Niu et al.
(POPL 2022, doi:10.1145/3498670), without assuming those searches are shared. -/
private def simpleQualityEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Complexity.Costed (Array String) := do
  let quality ← uniqueRelatedThingCosted worldNames.size thingNames.size tables .qualityKind .inst x w
  let xn ← indexedNameCosted thingNames x
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `SimpleQuality("
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 2 <| if !quality then do
    let status ← qualityStatusEvidenceCosted worldNames.size thingNames tables x w
    Complexity.Costed.appendArray out status
  else do
    let part ← firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w
    Complexity.Costed.charge 1 <| match part with
    | some y => do
      let row ← do
        let text := Complexity.Costed.pure "  - Computed SimpleQuality: false, because `"
        let text := text.appendString (indexedNameCosted thingNames y)
        let text := text.appendString (.pure "` inheres in `")
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure "` at `")
        let text := text.appendString (indexedNameCosted worldNames w)
        text.appendString (.pure "`.")
      Complexity.Costed.tick (out.push row) 2
    | none => Complexity.Costed.tick (out.push "  - Computed SimpleQuality: true, because it is a computed `Quality` and no thing inheres in it.") 2

private theorem simpleQualityEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityEvidenceCosted worldNames thingNames tables x w).value =
      if !qualityLookup worldNames.size thingNames.size tables x w then
        #[s!"  - User assertion: `SimpleQuality({indexedName thingNames x})`."] ++ qualityStatusEvidenceSpec worldNames.size thingNames tables x w
      else
        match (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value with
        | some y => #[s!"  - User assertion: `SimpleQuality({indexedName thingNames x})`.",
            s!"  - Computed SimpleQuality: false, because `{indexedName thingNames y}` inheres in `{indexedName thingNames x}` at `{indexedName worldNames w}`."]
        | none => #[s!"  - User assertion: `SimpleQuality({indexedName thingNames x})`.", "  - Computed SimpleQuality: true, because it is a computed `Quality` and no thing inheres in it."] := by
  simp only [simpleQualityEvidenceCosted, qualityLookup, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value, Complexity.Costed.charge_value]
  split <;> simp_all only [ite_true]
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.appendArray_value,
      qualityStatusEvidenceCosted_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value
    all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value]
    all_goals rfl

/-- Let T be the number of things. A failed quality check costs at most
(34T+2)+(44T+25)+14, including its status report and one-row copy. With a valid
quality, the check and inherence search cost at most (34T+2)+21T, and rendering
adds at most 28. Both branches satisfy 78T+41. -/
private theorem simpleQualityEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityEvidenceCosted worldNames thingNames tables x w).cost ≤ 78 * thingNames.size + 41 := by
  have hquality := uniqueRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .qualityKind .inst x w
  have hpart := firstRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .inheresIn x w
  have hstatus := qualityStatusEvidenceCosted_cost_le worldNames.size thingNames tables x w
  have hsize := qualityStatusEvidenceCosted_size worldNames.size thingNames tables x w
  simp only [simpleQualityEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendArray_cost, hsize]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value
    all_goals simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
    all_goals omega

private theorem simpleQualityEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityEvidenceCosted worldNames thingNames tables x w).value.size = 2 := by
  rw [simpleQualityEvidenceCosted_value]
  split
  · rw [← qualityStatusEvidenceCosted_value, Array.size_append, qualityStatusEvidenceCosted_size]
    rfl
  · cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value <;> rfl

/-- Complex-quality evidence uses the same quality/status choice. An incoming
inherence witness makes the predicate true. With no witness, the report states
that the quality has no inhering part. -/
private def complexQualityEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Complexity.Costed (Array String) := do
  let quality ← uniqueRelatedThingCosted worldNames.size thingNames.size tables .qualityKind .inst x w
  let xn ← indexedNameCosted thingNames x
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ComplexQuality("
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 2 <| if !quality then do
    let status ← qualityStatusEvidenceCosted worldNames.size thingNames tables x w
    Complexity.Costed.appendArray out status
  else do
    let part ← firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w
    Complexity.Costed.charge 1 <| match part with
    | some y => do
      let row ← do
        let text := Complexity.Costed.pure "  - Computed ComplexQuality: true, witnessed by `InheresIn("
        let text := text.appendString (indexedNameCosted thingNames y)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure ")` at `")
        let text := text.appendString (indexedNameCosted worldNames w)
        text.appendString (.pure "`.")
      Complexity.Costed.tick (out.push row) 2
    | none => Complexity.Costed.tick (out.push "  - Computed ComplexQuality: false, because it is a computed `Quality` but no thing inheres in it.") 2

private theorem complexQualityEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityEvidenceCosted worldNames thingNames tables x w).value =
      if !qualityLookup worldNames.size thingNames.size tables x w then
        #[s!"  - User assertion: `ComplexQuality({indexedName thingNames x})`."] ++ qualityStatusEvidenceSpec worldNames.size thingNames tables x w
      else
        match (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value with
        | some y => #[s!"  - User assertion: `ComplexQuality({indexedName thingNames x})`.",
            s!"  - Computed ComplexQuality: true, witnessed by `InheresIn({indexedName thingNames y}, {indexedName thingNames x})` at `{indexedName worldNames w}`."]
        | none => #[s!"  - User assertion: `ComplexQuality({indexedName thingNames x})`.", "  - Computed ComplexQuality: false, because it is a computed `Quality` but no thing inheres in it."] := by
  simp only [complexQualityEvidenceCosted, qualityLookup, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value, Complexity.Costed.charge_value]
  split <;> simp_all only [ite_true]
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.appendArray_value,
      qualityStatusEvidenceCosted_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value
    all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value]
    all_goals rfl

/-- Let T be the number of things. A failed quality check costs at most
(34T+2)+(44T+25)+14, including its status report and one-row copy. With a valid
quality, the check and inherence search cost at most (34T+2)+21T, and rendering
adds at most 28. Both branches satisfy 78T+41. -/
private theorem complexQualityEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityEvidenceCosted worldNames thingNames tables x w).cost ≤ 78 * thingNames.size + 41 := by
  have hquality := uniqueRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .qualityKind .inst x w
  have hpart := firstRelatedThingCosted_cost_le
    worldNames.size thingNames.size tables .inheresIn x w
  have hstatus := qualityStatusEvidenceCosted_cost_le worldNames.size thingNames tables x w
  have hsize := qualityStatusEvidenceCosted_size worldNames.size thingNames tables x w
  simp only [complexQualityEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendArray_cost, hsize]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value
    all_goals simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
    all_goals omega

private theorem complexQualityEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityEvidenceCosted worldNames thingNames tables x w).value.size = 2 := by
  rw [complexQualityEvidenceCosted_value]
  split
  · rw [← qualityStatusEvidenceCosted_value, Array.size_append, qualityStatusEvidenceCosted_size]
    rfl
  · cases (firstRelatedThingCosted worldNames.size thingNames.size tables .inheresIn x w).value <;> rfl

/-- The primitive classification check precedes all instance work. On a
classified type, the first violating instance determines the explanation.
The caller accounts for construction of the supplied fallback. -/
private def simpleQualityTypeRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let classified ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 2 <| if !classified then
    let text := Complexity.Costed.pure "`SimpleQualityType("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ")` requires `QualityType(")
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`; missing that primitive classification.")
  else do
    let failure ← firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)
    Complexity.Costed.charge 1 <| match failure with
    | none => .pure fallback
    | some y =>
      let text := Complexity.Costed.pure "`SimpleQualityType("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ")` requires every instance to be a computed `SimpleQuality`; instance `")
      let text := text.appendString (indexedNameCosted thingNames y)
      text.appendString (.pure "` is not simple.")

private theorem simpleQualityTypeRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (w : Fin worldNames.size) (fallback : String) :
    (simpleQualityTypeRequiredMissingCosted worldNames thingNames tables x w fallback).value =
      if !tables.unaryLookup "qualityType" x w then
        s!"`SimpleQualityType({indexedName thingNames x})` requires `QualityType({indexedName thingNames x})`; missing that primitive classification."
      else
        match (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)).value with
        | some y => s!"`SimpleQualityType({indexedName thingNames x})` requires every instance to be a computed `SimpleQuality`; instance `{indexedName thingNames y}` is not simple."
        | none => fallback := by
  have hclassification := Complexity.diagnosticUnaryCosted_value
    worldNames.size thingNames.size tables agreement .qualityType x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w).value =
    tables.unaryLookup "qualityType" x w at hclassification
  simp only [simpleQualityTypeRequiredMissingCosted, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value,
    indexedNameCosted_value, hclassification]
  split
  · simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
      indexedNameCosted_value]
    all_goals rfl

/-- For T things, the instance search costs at most T(55T+27). A classification
query costs at most 12. The witness branch adds 15 for two names, four
concatenations, negation, branching, and an option match. -/
private theorem simpleQualityTypeRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    (simpleQualityTypeRequiredMissingCosted worldNames thingNames tables x w fallback).cost ≤
      thingNames.size * (55 * thingNames.size + 27) + 27 := by
  have hclassification := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .qualityType x w
  have hsearch := firstInvalidInstance_simple_cost_le worldNames.size thingNames.size tables x w
  simp only [simpleQualityTypeRequiredMissingCosted, Bind.bind,
    Complexity.Costed.bind_cost, Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split
  · simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
      indexedNameCosted_cost]
    all_goals omega

/-- A failing instance produces a third row that explains its quality status.
The search, text, status report, and array copy all contribute to the cost.
This composition follows Niu et al. (POPL 2022, doi:10.1145/3498670).
Name resolution and the outer report budget belong to the caller. -/
private def simpleQualityTypeEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Complexity.Costed (Array String) := do
  let classified ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w
  let xn ← indexedNameCosted thingNames x
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `SimpleQualityType("
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 2 <| if !classified then do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed SimpleQualityType: false, because `QualityType("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ")` is not true at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
    Complexity.Costed.tick (out.push row) 2
  else do
    let failure ← firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)
    Complexity.Costed.charge 1 <| match failure with
    | none => Complexity.Costed.tick (out.push "  - Computed SimpleQualityType: true; every current instance is a computed `SimpleQuality`.") 2
    | some y => do
      let row ← do
        let text := Complexity.Costed.pure "  - Computed SimpleQualityType: false, because instance `"
        let text := text.appendString (indexedNameCosted thingNames y)
        let text := text.appendString (.pure "` is not a computed `SimpleQuality` at `")
        let text := text.appendString (indexedNameCosted worldNames w)
        text.appendString (.pure "`.")
      let out ← Complexity.Costed.tick (out.push row) 2
      let status ← qualityStatusEvidenceCosted worldNames.size thingNames tables y w
      Complexity.Costed.appendArray out status

private theorem simpleQualityTypeEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (w : Fin worldNames.size) :
    (simpleQualityTypeEvidenceCosted worldNames thingNames tables x w).value =
      if !tables.unaryLookup "qualityType" x w then
        #[s!"  - User assertion: `SimpleQualityType({indexedName thingNames x})`.",
          s!"  - Computed SimpleQualityType: false, because `QualityType({indexedName thingNames x})` is not true at `{indexedName worldNames w}`."]
      else
        match (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)).value with
        | some y => #[s!"  - User assertion: `SimpleQualityType({indexedName thingNames x})`.",
            s!"  - Computed SimpleQualityType: false, because instance `{indexedName thingNames y}` is not a computed `SimpleQuality` at `{indexedName worldNames w}`."] ++ qualityStatusEvidenceSpec worldNames.size thingNames tables y w
        | none => #[s!"  - User assertion: `SimpleQualityType({indexedName thingNames x})`.", "  - Computed SimpleQualityType: true; every current instance is a computed `SimpleQuality`."] := by
  have hclassification := Complexity.diagnosticUnaryCosted_value
    worldNames.size thingNames.size tables agreement .qualityType x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w).value =
    tables.unaryLookup "qualityType" x w at hclassification
  simp only [simpleQualityTypeEvidenceCosted, Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value,
    Complexity.Costed.charge_value, hclassification]
  split
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value,
      Complexity.Costed.appendArray_value, qualityStatusEvidenceCosted_value]
    all_goals rfl

/-- Let T count things. The failure branch uses at most T(55T+27) for the
instance search, 44T+25 for its status report, and 41 for classification,
names, text, branch tests, row construction, and a one-row copy. The other
branches cost at most 33, or T(55T+27)+26. -/
private theorem simpleQualityTypeEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityTypeEvidenceCosted worldNames thingNames tables x w).cost ≤
      thingNames.size * (55 * thingNames.size + 27) + 44 * thingNames.size + 66 := by
  have hclassification := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .qualityType x w
  have hsearch := firstInvalidInstance_simple_cost_le worldNames.size thingNames.size tables x w
  have hstatus (y : Nat) := qualityStatusEvidenceCosted_cost_le worldNames.size thingNames tables y w
  have hsize (y : Nat) := qualityStatusEvidenceCosted_size worldNames.size thingNames tables y w
  simp only [simpleQualityTypeEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)).value with
    | none =>
        simp only [Complexity.Costed.tick_cost]
        omega
    | some y =>
        have hs := hstatus y
        simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.appendArray_cost, hsize]
        omega

private theorem simpleQualityTypeEvidenceCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityTypeEvidenceCosted worldNames thingNames tables x w).value.size ≤ 3 := by
  have hsize (y : Nat) := qualityStatusEvidenceCosted_size worldNames.size thingNames tables y w
  simp only [simpleQualityTypeEvidenceCosted, Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value, Complexity.Costed.charge_value]
  split
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value]
    simp
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => simpleQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value, Complexity.Costed.appendArray_value,
      Array.size_append, hsize]
    all_goals simp

/-- The primitive classification check precedes all instance work. On a
classified type, the first violating instance determines the explanation.
The caller accounts for construction of the supplied fallback. -/
private def complexQualityTypeRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let classified ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w
  let xn ← indexedNameCosted thingNames x
  Complexity.Costed.charge 2 <| if !classified then
    let text := Complexity.Costed.pure "`ComplexQualityType("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ")` requires `QualityType(")
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`; missing that primitive classification.")
  else do
    let failure ← firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)
    Complexity.Costed.charge 1 <| match failure with
    | none => .pure fallback
    | some y =>
      let text := Complexity.Costed.pure "`ComplexQualityType("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ")` requires every instance to be a computed `ComplexQuality`; instance `")
      let text := text.appendString (indexedNameCosted thingNames y)
      text.appendString (.pure "` is not complex.")

private theorem complexQualityTypeRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (w : Fin worldNames.size) (fallback : String) :
    (complexQualityTypeRequiredMissingCosted worldNames thingNames tables x w fallback).value =
      if !tables.unaryLookup "qualityType" x w then
        s!"`ComplexQualityType({indexedName thingNames x})` requires `QualityType({indexedName thingNames x})`; missing that primitive classification."
      else
        match (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)).value with
        | some y => s!"`ComplexQualityType({indexedName thingNames x})` requires every instance to be a computed `ComplexQuality`; instance `{indexedName thingNames y}` is not complex."
        | none => fallback := by
  have hclassification := Complexity.diagnosticUnaryCosted_value
    worldNames.size thingNames.size tables agreement .qualityType x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w).value =
    tables.unaryLookup "qualityType" x w at hclassification
  simp only [complexQualityTypeRequiredMissingCosted, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value,
    indexedNameCosted_value, hclassification]
  split
  · simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
      indexedNameCosted_value]
    all_goals rfl

/-- For T things, the instance search costs at most T(55T+27). A classification
query costs at most 12. The witness branch adds 15 for two names, four
concatenations, negation, branching, and an option match. -/
private theorem complexQualityTypeRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    (complexQualityTypeRequiredMissingCosted worldNames thingNames tables x w fallback).cost ≤
      thingNames.size * (55 * thingNames.size + 27) + 27 := by
  have hclassification := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .qualityType x w
  have hsearch := firstInvalidInstance_complex_cost_le worldNames.size thingNames.size tables x w
  simp only [complexQualityTypeRequiredMissingCosted, Bind.bind,
    Complexity.Costed.bind_cost, Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split
  · simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
      indexedNameCosted_cost]
    all_goals omega

/-- Complex-quality-type evidence adds the failing instance's quality-status
row after its assertion and failure rows. The copy and status computation are
both counted, with the same caller exclusions as simple-quality-type evidence. -/
private def complexQualityTypeEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Complexity.Costed (Array String) := do
  let classified ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w
  let xn ← indexedNameCosted thingNames x
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ComplexQualityType("
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.charge 2 <| if !classified then do
    let row ← do
      let text := Complexity.Costed.pure "  - Computed ComplexQualityType: false, because `QualityType("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ")` is not true at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
    Complexity.Costed.tick (out.push row) 2
  else do
    let failure ← firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)
    Complexity.Costed.charge 1 <| match failure with
    | none => Complexity.Costed.tick (out.push "  - Computed ComplexQualityType: true; every current instance is a computed `ComplexQuality`.") 2
    | some y => do
      let row ← do
        let text := Complexity.Costed.pure "  - Computed ComplexQualityType: false, because instance `"
        let text := text.appendString (indexedNameCosted thingNames y)
        let text := text.appendString (.pure "` is not a computed `ComplexQuality` at `")
        let text := text.appendString (indexedNameCosted worldNames w)
        text.appendString (.pure "`.")
      let out ← Complexity.Costed.tick (out.push row) 2
      let status ← qualityStatusEvidenceCosted worldNames.size thingNames tables y w
      Complexity.Costed.appendArray out status

private theorem complexQualityTypeEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (w : Fin worldNames.size) :
    (complexQualityTypeEvidenceCosted worldNames thingNames tables x w).value =
      if !tables.unaryLookup "qualityType" x w then
        #[s!"  - User assertion: `ComplexQualityType({indexedName thingNames x})`.",
          s!"  - Computed ComplexQualityType: false, because `QualityType({indexedName thingNames x})` is not true at `{indexedName worldNames w}`."]
      else
        match (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)).value with
        | some y => #[s!"  - User assertion: `ComplexQualityType({indexedName thingNames x})`.",
            s!"  - Computed ComplexQualityType: false, because instance `{indexedName thingNames y}` is not a computed `ComplexQuality` at `{indexedName worldNames w}`."] ++ qualityStatusEvidenceSpec worldNames.size thingNames tables y w
        | none => #[s!"  - User assertion: `ComplexQualityType({indexedName thingNames x})`.", "  - Computed ComplexQualityType: true; every current instance is a computed `ComplexQuality`."] := by
  have hclassification := Complexity.diagnosticUnaryCosted_value
    worldNames.size thingNames.size tables agreement .qualityType x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityType x w).value =
    tables.unaryLookup "qualityType" x w at hclassification
  simp only [complexQualityTypeEvidenceCosted, Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value,
    Complexity.Costed.charge_value, hclassification]
  split
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value]
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value,
      Complexity.Costed.appendArray_value, qualityStatusEvidenceCosted_value]
    all_goals rfl

/-- Let T count things. The failure branch uses at most T(55T+27) for the
instance search, 44T+25 for its status report, and 41 for classification,
names, text, branch tests, row construction, and a one-row copy. The other
branches cost at most 33, or T(55T+27)+26. -/
private theorem complexQualityTypeEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityTypeEvidenceCosted worldNames thingNames tables x w).cost ≤
      thingNames.size * (55 * thingNames.size + 27) + 44 * thingNames.size + 66 := by
  have hclassification := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .qualityType x w
  have hsearch := firstInvalidInstance_complex_cost_le worldNames.size thingNames.size tables x w
  have hstatus (y : Nat) := qualityStatusEvidenceCosted_cost_le worldNames.size thingNames tables y w
  have hsize (y : Nat) := qualityStatusEvidenceCosted_size worldNames.size thingNames tables y w
  simp only [complexQualityTypeEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)).value with
    | none =>
        simp only [Complexity.Costed.tick_cost]
        omega
    | some y =>
        have hs := hstatus y
        simp only [Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.appendArray_cost, hsize]
        omega

private theorem complexQualityTypeEvidenceCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityTypeEvidenceCosted worldNames thingNames tables x w).value.size ≤ 3 := by
  have hsize (y : Nat) := qualityStatusEvidenceCosted_size worldNames.size thingNames tables y w
  simp only [complexQualityTypeEvidenceCosted, Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value, Complexity.Costed.charge_value]
  split
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value]
    simp
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (firstInvalidInstanceCosted worldNames.size thingNames.size tables x w
      (fun y => complexQualityLookupCosted worldNames.size thingNames.size tables y w)).value
    all_goals simp only [Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value, Complexity.Costed.appendArray_value,
      Array.size_append, hsize]
    all_goals simp

/-- Explain an already failed ultimate-bearer assertion. A moment cannot be
the ultimate bearer. Otherwise the missing condition is the directed path
from y to x; this text does not reconstruct that path. -/
private def ultimateBearerRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : Complexity.Costed String := do
  let bearerIsMoment ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .moment x w
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  Complexity.Costed.charge 1 <| if bearerIsMoment then
    let text := Complexity.Costed.pure "`UltimateBearerOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires bearer `")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure "` not to be a `Moment`; conflicting `Moment(")
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")` holds.")
  else
    let text := Complexity.Costed.pure "`UltimateBearerOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires an `InheresIn` path from `")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure "` to bearer `")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure "`; missing that path at `")
    let text := text.appendString (indexedNameCosted worldNames w)
    text.appendString (.pure "`.")

private theorem ultimateBearerRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x y : Fin thingNames.size) (w : Fin worldNames.size) :
    (ultimateBearerRequiredMissingCosted worldNames thingNames tables x y w).value =
      if tables.unaryLookup "moment" x w then
        s!"`UltimateBearerOf({indexedName thingNames x}, {indexedName thingNames y})` requires bearer `{indexedName thingNames x}` not to be a `Moment`; conflicting `Moment({indexedName thingNames x})` holds."
      else s!"`UltimateBearerOf({indexedName thingNames x}, {indexedName thingNames y})` requires an `InheresIn` path from `{indexedName thingNames y}` to bearer `{indexedName thingNames x}`; missing that path at `{indexedName worldNames w}`." := by
  have hmoment := Complexity.diagnosticUnaryCosted_value
    worldNames.size thingNames.size tables agreement .moment x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .moment x w).value = tables.unaryLookup "moment" x w at hmoment
  simp only [ultimateBearerRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, indexedNameCosted_value, hmoment]
  split
  · rfl
  · simp only [Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
      indexedNameCosted_value]
    rfl

/-- The larger branch uses one classification query (at most 12), three names
(12), ten concatenations, and one branch. The moment branch needs only 29. -/
private theorem ultimateBearerRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (ultimateBearerRequiredMissingCosted worldNames thingNames tables x y w).cost ≤ 35 := by
  have hmoment := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .moment x w
  simp only [ultimateBearerRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost]
  split <;> simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    indexedNameCosted_cost] <;> omega

/-- Evidence displays both moment classification and the path from y to x.
It reconstructs the path even when x is a moment. The next-hop traversal
already limits its work by T, the number of things, and returns at most T+1
vertices. This bound does not assert path validity for arbitrary raw tables.
The composed query, path, and rendering costs follow Niu et al.'s cost semantics
(POPL 2022, doi:10.1145/3498670). -/
private def ultimateBearerEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : Complexity.Costed (Array String) := do
  let bearerIsMoment ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .moment x w
  let path? ← tables.momentOfPathCosted thingNames.size w y x
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let pathEvidence ← Complexity.Costed.charge 1 <| match path? with
    | some path =>
      let text := Complexity.Costed.pure "`InheresIn` path exists: "
      let text := text.appendString (joinIndexedNamesCosted thingNames path " InheresIn ")
      text.appendString (.pure ".")
    | none =>
      let text := Complexity.Costed.pure "no `InheresIn` path reaches `"
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` from `")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure "` at `")
      let text := text.appendString (indexedNameCosted worldNames w)
      text.appendString (.pure "`.")
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `UltimateBearerOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let classification ← do
    let text := Complexity.Costed.pure "  - Bearer `"
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure "` is a Moment: ")
    let text := text.appendString (Complexity.Costed.tick (if bearerIsMoment then "true" else "false") 1)
    text.appendString (.pure ".")
  let pathRow ← (Complexity.Costed.pure "  - ").appendString (.pure pathEvidence)
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  let out ← Complexity.Costed.tick (out.push classification) 2
  Complexity.Costed.tick (out.push pathRow) 2

private theorem ultimateBearerEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x y : Fin thingNames.size) (w : Fin worldNames.size) :
    (ultimateBearerEvidenceCosted worldNames thingNames tables x y w).value =
      let bearerIsMoment := tables.unaryLookup "moment" x w
      let pathEvidence :=
        match tables.momentOfPath? thingNames.size w y x with
        | some path => s!"`InheresIn` path exists: {renderThingPath thingNames path}."
        | none => s!"no `InheresIn` path reaches `{indexedName thingNames x}` from `{indexedName thingNames y}` at `{indexedName worldNames w}`."
      #[s!"  - User assertion: `UltimateBearerOf({indexedName thingNames x}, {indexedName thingNames y})`.",
        s!"  - Bearer `{indexedName thingNames x}` is a Moment: {if bearerIsMoment then "true" else "false"}.", s!"  - {pathEvidence}"] := by
  have hmoment := Complexity.diagnosticUnaryCosted_value
    worldNames.size thingNames.size tables agreement .moment x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .moment x w).value = tables.unaryLookup "moment" x w at hmoment
  -- Reduce the record projections before rewriting query correspondence.
  -- Rewriting each bind separately builds large proof terms that repeat cost
  -- fields unused by this value equality. Definitional reduction avoids them.
  dsimp only [ultimateBearerEvidenceCosted, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.tick, Complexity.Costed.charge, Complexity.Costed.appendString,
    Complexity.Costed.pure, FactTables.momentOfPath?]
  cases (tables.momentOfPathCosted thingNames.size w y x).value
  all_goals simp only [indexedNameCosted_value, renderThingPath, hmoment]
  all_goals rfl

/-- Path reconstruction costs at most 11T+7. For N ≤ T+1 vertices, joining
costs at most 9N+1. Its prefix/suffix add two operations; other report work
adds at most 38. The no-path branch adds ten instead of the join and its
prefix/suffix. Both cases fit 20T+57 in the primitive-call model. -/
private theorem ultimateBearerEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (ultimateBearerEvidenceCosted worldNames thingNames tables x y w).cost ≤
      20 * thingNames.size + 57 := by
  have hmoment := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .moment x w
  have hpath := tables.momentOfPathCosted_cost_le thingNames.size w y x
  simp only [ultimateBearerEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.charge_cost]
  cases found : (tables.momentOfPathCosted thingNames.size w y x).value with
  | none =>
      simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
        indexedNameCosted_cost]
      omega
  | some path =>
      have hsize := tables.momentOfPathCosted_some_size thingNames.size w y x path found
      have hjoin := joinIndexedNamesCosted_cost_le thingNames path " InheresIn "
      simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
      omega

private theorem ultimateBearerEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (ultimateBearerEvidenceCosted worldNames thingNames tables x y w).value.size = 3 := by
  simp only [ultimateBearerEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value]
  rfl

/-- The two introductory rows precede the complete mode-status report.
The status builder performs its own searches and row construction. This
component charges those costs and the subsequent copy of its rows. -/
private def externalModeEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ExternallyDependentMode("
    let text := text.appendString (.pure xn)
    text.appendString (.pure ")`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  let out ← Complexity.Costed.tick (out.push "  - Certification treats this as a computed predicate, not as a primitive classification.") 2
  let status ← renderExternallyDependentModeStatusCosted worldNames thingNames tables x w
  Complexity.Costed.appendArray out status

private theorem externalModeEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externalModeEvidenceCosted worldNames thingNames tables x w).value =
      #[s!"  - User assertion: `ExternallyDependentMode({indexedName thingNames x})`.",
        "  - Certification treats this as a computed predicate, not as a primitive classification."] ++ renderExternallyDependentModeStatus worldNames thingNames tables x w := by
  simp only [externalModeEvidenceCosted, Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value,
    Complexity.Costed.appendArray_value, renderExternallyDependentModeStatus]
  rfl

/-- Names, text, initialization, and two row writes/emissions cost 11.
Copying the status builder's at most three rows costs at most nine more. -/
private theorem externalModeEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externalModeEvidenceCosted worldNames thingNames tables x w).cost ≤
      externallyDependentModeStatusCostBound worldNames.size thingNames.size tables + 20 := by
  have hstatus := renderExternallyDependentModeStatusCosted_cost_le worldNames thingNames tables x w
  have hsize := renderExternallyDependentModeStatusCosted_size_le worldNames thingNames tables x w
  simp only [externalModeEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.appendArray_cost]
  omega

private theorem externalModeEvidenceCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externalModeEvidenceCosted worldNames thingNames tables x w).value.size ≤ 5 := by
  have hsize := renderExternallyDependentModeStatusCosted_size_le worldNames thingNames tables x w
  rw [externalModeEvidenceCosted_value, Array.size_append]
  change 2 + (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value.size ≤ 5
  omega

/-- Explain the first failed existence implication, or otherwise the first
failing bearer. The shared reason builder owns both searches and their order.
Two rendered names and seven concatenations add 15 to its cost. -/
private def externallyDependentRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed String := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let reason ← firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w
  let text := Complexity.Costed.pure "`ExternallyDependent("
  let text := text.appendString (.pure xn)
  let text := text.appendString (.pure ", ")
  let text := text.appendString (.pure yn)
  let text := text.appendString (.pure ")` requires existential dependence plus independence from every bearer of `")
  let text := text.appendString (.pure xn)
  let text := text.appendString (.pure "`; missing condition: ")
  text.appendString (.pure reason)

private theorem externallyDependentRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentRequiredMissingCosted worldNames thingNames tables x y w).value =
      s!"`ExternallyDependent({indexedName thingNames x}, {indexedName thingNames y})` requires existential dependence plus independence from every bearer of `{indexedName thingNames x}`; missing condition: {firstExternallyDependentFailureReason worldNames thingNames tables x y w}" := by
  simp only [externallyDependentRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value,
    indexedNameCosted_value,
    firstExternallyDependentFailureReason]
  rfl

private theorem externallyDependentRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentRequiredMissingCosted worldNames thingNames tables x y w).cost ≤ 30 * worldNames.size + thingNames.size * (60 * worldNames.size + 40) + 43 := by
  have h := firstExternallyDependentFailureReasonCosted_cost_le worldNames thingNames tables x y w
  simp only [externallyDependentRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost,
    indexedNameCosted_cost]
  omega

/-- Include the complete external-dependence reason in three evidence rows.
Names cost eight, concatenations five, and array initialization plus three
writes/emissions seven. The report therefore adds 20 to the reason cost. -/
private def externallyDependentEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Array String) := do
  let reason ← firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ExternallyDependent("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let detail ← do
    let text := Complexity.Costed.pure "  - Computed ExternallyDependent: false. "
    text.appendString (.pure reason)
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  let out ← Complexity.Costed.tick (out.push "  - Certification computes this from existential dependence plus existential independence from every bearer.") 2
  Complexity.Costed.tick (out.push detail) 2

private theorem externallyDependentEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentEvidenceCosted worldNames thingNames tables x y w).value =
      #[s!"  - User assertion: `ExternallyDependent({indexedName thingNames x}, {indexedName thingNames y})`.",
        "  - Certification computes this from existential dependence plus existential independence from every bearer.",
        s!"  - Computed ExternallyDependent: false. {firstExternallyDependentFailureReason worldNames thingNames tables x y w}"] := by
  dsimp only [externallyDependentEvidenceCosted, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.tick, Complexity.Costed.appendString, Complexity.Costed.pure,
    firstExternallyDependentFailureReason]
  simp only [indexedNameCosted_value]
  rfl

private theorem externallyDependentEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentEvidenceCosted worldNames thingNames tables x y w).cost ≤ 30 * worldNames.size + thingNames.size * (60 * worldNames.size + 40) + 48 := by
  have h := firstExternallyDependentFailureReasonCosted_cost_le worldNames thingNames tables x y w
  simp only [externallyDependentEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost,
    indexedNameCosted_cost]
  omega

private theorem externallyDependentEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentEvidenceCosted worldNames thingNames tables x y w).value.size = 3 := by
  rw [externallyDependentEvidenceCosted_value]
  rfl

/-- Report the first world where x exists without y. With no such world,
return the supplied fallback without rendering names. A found world adds
one match, three names, and twelve concatenations: at most 25 operations. -/
private def existentialDependenceRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    Complexity.Costed String := do
  let failure ← firstExWithoutCosted worldNames.size thingNames.size tables x y
  Complexity.Costed.charge 1 <| match failure with
  | none => .pure fallback
  | some witnessWorld => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let wn ← indexedNameCosted worldNames witnessWorld
    let text := Complexity.Costed.pure "`ExistentialDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires `Ex(")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` in every world where `Ex(")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ")` holds; missing `Ex(")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` at `")
    let text := text.appendString (.pure wn)
    text.appendString (.pure "`.")

private theorem existentialDependenceRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    (existentialDependenceRequiredMissingCosted worldNames thingNames tables x y fallback).value =
      match (firstExWithoutCosted worldNames.size thingNames.size tables x y).value with
      | some witnessWorld =>
          s!"`ExistentialDependence({indexedName thingNames x}, {indexedName thingNames y})` requires `Ex({indexedName thingNames y})` in every world where `Ex({indexedName thingNames x})` holds; missing `Ex({indexedName thingNames y})` at `{indexedName worldNames witnessWorld}`."
      | none => fallback := by
  simp only [existentialDependenceRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  cases (firstExWithoutCosted worldNames.size thingNames.size tables x y).value
  all_goals simp only [Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value,
    indexedNameCosted_value]
  all_goals rfl

private theorem existentialDependenceRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    (existentialDependenceRequiredMissingCosted worldNames thingNames tables x y fallback).cost ≤ 30 * worldNames.size + 25 := by
  have h := firstExWithoutCosted_cost_le worldNames.size thingNames.size tables x y
  simp only [existentialDependenceRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  cases (firstExWithoutCosted worldNames.size thingNames.size tables x y).value
  all_goals simp only [Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost,
    indexedNameCosted_cost]
  all_goals omega

/-- Retain the first failed modal implication and its world in two rows.
The search costs at most 30W for W worlds. Rendering adds at most 28:
three names, ten concatenations, one match, and five array operations. -/
private def existentialDependenceEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    Complexity.Costed (Array String) := do
  let failure ← firstExWithoutCosted worldNames.size thingNames.size tables x y
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ExistentialDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let detail ← Complexity.Costed.charge 1 <| match failure with
    | none => .pure "  - No concrete `Ex` counter-witness was isolated; inspect world-scoped `Ex` facts."
    | some witnessWorld => do
      let wn ← indexedNameCosted worldNames witnessWorld
      let text := Complexity.Costed.pure "  - Computed ExistentialDependence: false, because `"
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` exists at `")
      let text := text.appendString (.pure wn)
      let text := text.appendString (.pure "` but `")
      let text := text.appendString (.pure yn)
      text.appendString (.pure "` does not.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem existentialDependenceEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialDependenceEvidenceCosted worldNames thingNames tables x y).value =
      match (firstExWithoutCosted worldNames.size thingNames.size tables x y).value with
      | some witnessWorld =>
          #[s!"  - User assertion: `ExistentialDependence({indexedName thingNames x}, {indexedName thingNames y})`.",
            s!"  - Computed ExistentialDependence: false, because `{indexedName thingNames x}` exists at `{indexedName worldNames witnessWorld}` but `{indexedName thingNames y}` does not."]
      | none => #[s!"  - User assertion: `ExistentialDependence({indexedName thingNames x}, {indexedName thingNames y})`.",
          "  - No concrete `Ex` counter-witness was isolated; inspect world-scoped `Ex` facts."] := by
  dsimp only [existentialDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.tick, Complexity.Costed.charge, Complexity.Costed.appendString,
    Complexity.Costed.pure]
  cases (firstExWithoutCosted worldNames.size thingNames.size tables x y).value
  all_goals simp only [indexedNameCosted_value]
  all_goals rfl

private theorem existentialDependenceEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialDependenceEvidenceCosted worldNames thingNames tables x y).cost ≤ 30 * worldNames.size + 28 := by
  have h := firstExWithoutCosted_cost_le worldNames.size thingNames.size tables x y
  simp only [existentialDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost,
    Complexity.Costed.charge_cost]
  cases (firstExWithoutCosted worldNames.size thingNames.size tables x y).value
  all_goals simp only [Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost,
    indexedNameCosted_cost]
  all_goals omega

private theorem existentialDependenceEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialDependenceEvidenceCosted worldNames thingNames tables x y).value.size = 2 := by
  rw [existentialDependenceEvidenceCosted_value]
  cases (firstExWithoutCosted worldNames.size thingNames.size tables x y).value <;> rfl

/-- The shared reason builder searches both directions to explain which
separation witness is missing. A reason adds two names, six concatenations,
and one match (15). A successful independence check returns the fallback. -/
private def existentialIndependenceRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    Complexity.Costed String := do
  let failure ← firstExternalIndependenceFailureCosted worldNames thingNames tables x y
  Complexity.Costed.charge 1 <| match failure with
  | none => .pure fallback
  | some reason => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let text := Complexity.Costed.pure "`ExistentialIndependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires two modal `Ex` separation witnesses; missing condition: ")
    let text := text.appendString (.pure reason)
    text.appendString (.pure ".")

private theorem existentialIndependenceRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    (existentialIndependenceRequiredMissingCosted worldNames thingNames tables x y fallback).value =
      match firstExternalIndependenceFailure? worldNames thingNames tables x y with
      | some reason =>
          s!"`ExistentialIndependence({indexedName thingNames x}, {indexedName thingNames y})` requires two modal `Ex` separation witnesses; missing condition: {reason}."
      | none => fallback := by
  simp only [existentialIndependenceRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind_value,
    Complexity.Costed.charge_value,
    firstExternalIndependenceFailure?]
  cases (firstExternalIndependenceFailureCosted worldNames thingNames tables x y).value
  all_goals simp only [Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value,
    indexedNameCosted_value]
  all_goals rfl

private theorem existentialIndependenceRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    (existentialIndependenceRequiredMissingCosted worldNames thingNames tables x y fallback).cost ≤ 60 * worldNames.size + 33 := by
  have h := firstExternalIndependenceFailureCosted_cost_le worldNames thingNames tables x y
  simp only [existentialIndependenceRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  cases (firstExternalIndependenceFailureCosted worldNames thingNames tables x y).value
  all_goals simp only [Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost,
    indexedNameCosted_cost]
  all_goals omega

/-- Count both separation searches and the resulting two-row report.
The shared reason costs at most 60W+18. Names, text, the option match, and
array operations add at most 20, giving 60W+38. -/
private def existentialIndependenceEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    Complexity.Costed (Array String) := do
  let failure ← firstExternalIndependenceFailureCosted worldNames thingNames tables x y
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ExistentialIndependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let detail ← Complexity.Costed.charge 1 <| match failure with
    | none => .pure "  - No concrete missing independence witness was isolated; inspect world-scoped `Ex` facts."
    | some reason => do
      let text := Complexity.Costed.pure "  - Computed ExistentialIndependence: false: "
      let text := text.appendString (.pure reason)
      text.appendString (.pure ".")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem existentialIndependenceEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceEvidenceCosted worldNames thingNames tables x y).value =
      match firstExternalIndependenceFailure? worldNames thingNames tables x y with
      | some reason =>
          #[s!"  - User assertion: `ExistentialIndependence({indexedName thingNames x}, {indexedName thingNames y})`.",
            s!"  - Computed ExistentialIndependence: false: {reason}."]
      | none => #[s!"  - User assertion: `ExistentialIndependence({indexedName thingNames x}, {indexedName thingNames y})`.",
          "  - No concrete missing independence witness was isolated; inspect world-scoped `Ex` facts."] := by
  simp only [existentialIndependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, Complexity.Costed.tick_value, indexedNameCosted_value,
    Complexity.Costed.charge_value, firstExternalIndependenceFailure?]
  cases (firstExternalIndependenceFailureCosted worldNames thingNames tables x y).value
  all_goals simp only [Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value]
  all_goals rfl

private theorem existentialIndependenceEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceEvidenceCosted worldNames thingNames tables x y).cost ≤ 60 * worldNames.size + 38 := by
  have h := firstExternalIndependenceFailureCosted_cost_le worldNames thingNames tables x y
  simp only [existentialIndependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost,
    Complexity.Costed.charge_cost]
  cases (firstExternalIndependenceFailureCosted worldNames thingNames tables x y).value
  all_goals simp only [Complexity.Costed.appendString_cost,
    Complexity.Costed.pure_cost]
  all_goals omega

private theorem existentialIndependenceEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceEvidenceCosted worldNames thingNames tables x y).value.size = 2 := by
  rw [existentialIndependenceEvidenceCosted_value]
  cases firstExternalIndependenceFailure? worldNames thingNames tables x y <;> rfl


/-- Check that category x has an instance in some world before searching
for missing specialization in the report's world.
For W worlds and T things, the two searches cost at most P = W(19T+2)
and 40T. The no-type branch adds 16 for names, text, negation, and branching.
The witness branch adds 25, giving P+40T+25. A supplied fallback has no
construction cost here. As in Niu et al. (POPL 2022, doi:10.1145/3498670),
the report composes the costs of the computations it actually selects. -/
private def categorizesRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let isType ← hasPossibleInstanceCosted worldNames.size thingNames.size tables x
  Complexity.Costed.charge 2 <| if !isType then do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let text := Complexity.Costed.pure "`Categorizes("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires `")
    let text := text.appendString (.pure xn)
    text.appendString (.pure "` to be a computed `Type`; missing any possible instance.")
  else do
    let failure ← firstRelationDifferenceCosted worldNames.size thingNames.size tables .inst .sub x y w
    Complexity.Costed.charge 1 <| match failure with
    | some witness => do
      let xn ← indexedNameCosted thingNames x
      let yn ← indexedNameCosted thingNames y
      let witnessName ← indexedNameCosted thingNames witness
      let text := Complexity.Costed.pure "`Categorizes("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure ")` requires each category-instance type to specialize `")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure "`; missing `Sub(")
      let text := text.appendString (.pure witnessName)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yn)
      text.appendString (.pure ")`.")
    | none => .pure fallback

private theorem categorizesRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (categorizesRequiredMissingCosted worldNames thingNames tables x y w fallback).value =
      if !typeLookup worldNames.size thingNames.size tables x then
        s!"`Categorizes({indexedName thingNames x}, {indexedName thingNames y})` requires `{indexedName thingNames x}` to be a computed `Type`; missing any possible instance."
      else
        match (firstRelationDifferenceCosted worldNames.size thingNames.size tables
          .inst .sub x y w).value with
        | some instType =>
            s!"`Categorizes({indexedName thingNames x}, {indexedName thingNames y})` requires each category-instance type to specialize `{indexedName thingNames y}`; missing `Sub({indexedName thingNames instType}, {indexedName thingNames y})`."
        | none => fallback := by
  dsimp only [categorizesRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    typeLookup,
    hasPossibleInstance]
  split
  all_goals cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .inst .sub x y w).value
  all_goals simp_all only [indexedNameCosted_value, ite_true]
  all_goals rfl

private theorem categorizesRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (categorizesRequiredMissingCosted worldNames thingNames tables x y w fallback).cost ≤ worldNames.size * (thingNames.size * 19 + 2) + 40 * thingNames.size + 25 := by
  have htype := hasPossibleInstanceCosted_cost_le worldNames.size thingNames.size tables x
  have hsearch := firstRelationDifferenceCosted_cost_le worldNames.size thingNames.size tables .inst .sub x y w
  dsimp only [categorizesRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure]
  split
  all_goals cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .inst .sub x y w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

/-- On an already failed disjointness assertion, prefer the first shared
instance. With no shared instance, the unmet condition is typehood.
The search costs at most 39T for T things. A witness adds three names,
six concatenations, and one match (19); the no-witness branch adds 13. -/
private def disjointTypesRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed String := do
  let failure ← firstSharedInstanceCosted worldNames.size thingNames.size tables x y w
  Complexity.Costed.charge 1 <| match failure with
  | some witness => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let witnessName ← indexedNameCosted thingNames witness
    let text := Complexity.Costed.pure "`IsDisjointWith("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires no shared instance; `")
    let text := text.appendString (.pure witnessName)
    text.appendString (.pure "` instantiates both types.")
  | none => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let text := Complexity.Costed.pure "`IsDisjointWith("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")` requires both arguments to be computed types and have no shared instance; missing typehood for one argument.")

private theorem disjointTypesRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesRequiredMissingCosted worldNames thingNames tables x y w).value =
      match (firstSharedInstanceCosted worldNames.size thingNames.size tables x y w).value with
      | some z =>
          s!"`IsDisjointWith({indexedName thingNames x}, {indexedName thingNames y})` requires no shared instance; `{indexedName thingNames z}` instantiates both types."
      | none =>
          s!"`IsDisjointWith({indexedName thingNames x}, {indexedName thingNames y})` requires both arguments to be computed types and have no shared instance; missing typehood for one argument." := by
  dsimp only [disjointTypesRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure]
  cases (firstSharedInstanceCosted worldNames.size thingNames.size tables x y w).value
  all_goals simp only [indexedNameCosted_value]
  all_goals rfl

private theorem disjointTypesRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesRequiredMissingCosted worldNames thingNames tables x y w).cost ≤ 39 * thingNames.size + 19 := by
  have hsearch := firstSharedInstanceCosted_cost_le worldNames.size thingNames.size tables x y w
  dsimp only [disjointTypesRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure]
  cases (firstSharedInstanceCosted worldNames.size thingNames.size tables x y w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

/-- Find the first covered-type instance outside both covers. The counted
search costs at most 58T for T things. Four names, fourteen concatenations,
and one match add 31. No counterexample returns the supplied fallback. -/
private def completeCoverageRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let failure ← firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w
  Complexity.Costed.charge 1 <| match failure with
  | some witness => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let zn ← indexedNameCosted thingNames z
    let witnessName ← indexedNameCosted thingNames witness
    let text := Complexity.Costed.pure "`IsCompletelyCoveredBy("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure zn)
    let text := text.appendString (.pure ")` requires every `")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure "` instance to instantiate at least one covering type; `")
    let text := text.appendString (.pure witnessName)
    let text := text.appendString (.pure "` instantiates neither `")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure "` nor `")
    let text := text.appendString (.pure zn)
    text.appendString (.pure "`.")
  | none => .pure fallback

private theorem completeCoverageRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    (completeCoverageRequiredMissingCosted worldNames thingNames tables x y z w fallback).value =
      match (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value with
      | some instIdx =>
          s!"`IsCompletelyCoveredBy({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})` requires every `{indexedName thingNames x}` instance to instantiate at least one covering type; `{indexedName thingNames instIdx}` instantiates neither `{indexedName thingNames y}` nor `{indexedName thingNames z}`."
      | none => fallback := by
  dsimp only [completeCoverageRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals simp only [indexedNameCosted_value]
  all_goals rfl

private theorem completeCoverageRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    (completeCoverageRequiredMissingCosted worldNames thingNames tables x y z w fallback).cost ≤ 58 * thingNames.size + 31 := by
  have hsearch := firstCoveredInstanceFailureCosted_cost_le worldNames.size thingNames.size tables x y z w
  dsimp only [completeCoverageRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

/-- Coverage failure takes precedence over overlapping parts. Only a
successful coverage scan starts the shared-instance scan. Their bounds are
58T and 39T for T things. Rendering adds at most 24, and the selected path
has one or two option matches, giving 97T+26. -/
private def partitionRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let failure ← firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w
  Complexity.Costed.charge 1 <| match failure with
  | some witness => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let zn ← indexedNameCosted thingNames z
    let witnessName ← indexedNameCosted thingNames witness
    let text := Complexity.Costed.pure "`IsPartitionedInto("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure zn)
    let text := text.appendString (.pure ")` first requires complete coverage; `")
    let text := text.appendString (.pure witnessName)
    text.appendString (.pure "` instantiates the partitioned type but neither part type.")
  | none => do
    let shared ← firstSharedInstanceCosted worldNames.size thingNames.size tables y z w
    Complexity.Costed.charge 1 <| match shared with
    | some witness => do
      let xn ← indexedNameCosted thingNames x
      let yn ← indexedNameCosted thingNames y
      let zn ← indexedNameCosted thingNames z
      let witnessName ← indexedNameCosted thingNames witness
      let text := Complexity.Costed.pure "`IsPartitionedInto("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure zn)
      let text := text.appendString (.pure ")` also requires disjoint parts; `")
      let text := text.appendString (.pure witnessName)
      text.appendString (.pure "` instantiates both part types.")
    | none => .pure fallback

private theorem partitionRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    (partitionRequiredMissingCosted worldNames thingNames tables x y z w fallback).value =
      match (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value with
      | some instIdx =>
          s!"`IsPartitionedInto({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})` first requires complete coverage; `{indexedName thingNames instIdx}` instantiates the partitioned type but neither part type."
      | none =>
          match (firstSharedInstanceCosted worldNames.size thingNames.size tables y z w).value with
          | some instIdx =>
              s!"`IsPartitionedInto({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})` also requires disjoint parts; `{indexedName thingNames instIdx}` instantiates both part types."
          | none => fallback := by
  dsimp only [partitionRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals cases (firstSharedInstanceCosted worldNames.size thingNames.size tables y z w).value
  all_goals simp only [indexedNameCosted_value]
  all_goals rfl

private theorem partitionRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    (partitionRequiredMissingCosted worldNames thingNames tables x y z w fallback).cost ≤ 97 * thingNames.size + 26 := by
  have hsearch := firstCoveredInstanceFailureCosted_cost_le worldNames.size thingNames.size tables x y z w
  have hshared := firstSharedInstanceCosted_cost_le worldNames.size thingNames.size tables y z w
  dsimp only [partitionRequiredMissingCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals cases (firstSharedInstanceCosted worldNames.size thingNames.size tables y z w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

/-- Show typehood failure, missing specialization, or a successful category
check in two rows. The assertion and array cost 17. Typehood costs at most
P = W(19T+2), and its negation/branch cost two. The specialization path adds
at most 40T for search, one match, and 18 for witness text: P+40T+38. -/
private def categorizesEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `Categorizes("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let detail ← do
    let isType ← hasPossibleInstanceCosted worldNames.size thingNames.size tables x
    Complexity.Costed.charge 2 <| if !isType then do
      let text := Complexity.Costed.pure "  - Computed Categorizes: false, because `"
      let text := text.appendString (.pure xn)
      text.appendString (.pure "` is not a computed `Type`.")
    else do
      let failure ← firstRelationDifferenceCosted worldNames.size thingNames.size tables .inst .sub x y w
      Complexity.Costed.charge 1 <| match failure with
      | some witness => do
        let witnessName ← indexedNameCosted thingNames witness
        let wn ← indexedNameCosted worldNames w
        let text := Complexity.Costed.pure "  - Computed Categorizes: false, because `"
        let text := text.appendString (.pure witnessName)
        let text := text.appendString (.pure "` instantiates `")
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure "` at `")
        let text := text.appendString (.pure wn)
        let text := text.appendString (.pure "` but `Sub(")
        let text := text.appendString (.pure witnessName)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yn)
        text.appendString (.pure ")` is missing.")
      | none => do
        let text := Complexity.Costed.pure "  - Computed Categorizes: true; every instance type of `"
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure "` specializes `")
        let text := text.appendString (.pure yn)
        text.appendString (.pure "`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem categorizesEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (categorizesEvidenceCosted worldNames thingNames tables x y w).value =
      if !typeLookup worldNames.size thingNames.size tables x then
        #[
          s!"  - User assertion: `Categorizes({indexedName thingNames x}, {indexedName thingNames y})`.",
          s!"  - Computed Categorizes: false, because `{indexedName thingNames x}` is not a computed `Type`."
        ]
      else
        match (firstRelationDifferenceCosted worldNames.size thingNames.size tables
          .inst .sub x y w).value with
        | some instType =>
            #[
              s!"  - User assertion: `Categorizes({indexedName thingNames x}, {indexedName thingNames y})`.",
              s!"  - Computed Categorizes: false, because `{indexedName thingNames instType}` instantiates `{indexedName thingNames x}` at `{indexedName worldNames w}` but `Sub({indexedName thingNames instType}, {indexedName thingNames y})` is missing."
            ]
        | none =>
            #[
              s!"  - User assertion: `Categorizes({indexedName thingNames x}, {indexedName thingNames y})`.",
              s!"  - Computed Categorizes: true; every instance type of `{indexedName thingNames x}` specializes `{indexedName thingNames y}`."
            ] := by
  dsimp only [categorizesEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick,
    typeLookup,
    hasPossibleInstance]
  split
  all_goals cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .inst .sub x y w).value
  all_goals simp_all only [indexedNameCosted_value, ite_true]
  all_goals rfl

private theorem categorizesEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (categorizesEvidenceCosted worldNames thingNames tables x y w).cost ≤ worldNames.size * (thingNames.size * 19 + 2) + 40 * thingNames.size + 38 := by
  have htype := hasPossibleInstanceCosted_cost_le worldNames.size thingNames.size tables x
  have hsearch := firstRelationDifferenceCosted_cost_le worldNames.size thingNames.size tables .inst .sub x y w
  dsimp only [categorizesEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick]
  split
  all_goals cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .inst .sub x y w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

private theorem categorizesEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (categorizesEvidenceCosted worldNames thingNames tables x y w).value.size = 2 := by
  rw [categorizesEvidenceCosted_value]
  cases typeLookup worldNames.size thingNames.size tables x
  all_goals cases (firstRelationDifferenceCosted worldNames.size thingNames.size tables .inst .sub x y w).value
  all_goals rfl

/-- Show the first shared instance, or the no-witness explanation, in two
rows. Search costs at most 39T for T things. Names, the assertion, the option
match, and array operations add 18. Witness text adds at most twelve. -/
private def disjointTypesEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `IsDisjointWith("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let detail ← do
    let failure ← firstSharedInstanceCosted worldNames.size thingNames.size tables x y w
    Complexity.Costed.charge 1 <| match failure with
    | some witness => do
      let witnessName ← indexedNameCosted thingNames witness
      let wn ← indexedNameCosted worldNames w
      let text := Complexity.Costed.pure "  - Computed IsDisjointWith: false, because `"
      let text := text.appendString (.pure witnessName)
      let text := text.appendString (.pure "` instantiates both types at `")
      let text := text.appendString (.pure wn)
      text.appendString (.pure "`.")
    | none => .pure "  - No shared instance was isolated; inspect typehood and instantiation facts."
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem disjointTypesEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesEvidenceCosted worldNames thingNames tables x y w).value =
      match (firstSharedInstanceCosted worldNames.size thingNames.size tables x y w).value with
      | some z =>
          #[
            s!"  - User assertion: `IsDisjointWith({indexedName thingNames x}, {indexedName thingNames y})`.",
            s!"  - Computed IsDisjointWith: false, because `{indexedName thingNames z}` instantiates both types at `{indexedName worldNames w}`."
          ]
      | none =>
          #[
            s!"  - User assertion: `IsDisjointWith({indexedName thingNames x}, {indexedName thingNames y})`.",
            "  - No shared instance was isolated; inspect typehood and instantiation facts."
          ] := by
  dsimp only [disjointTypesEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick]
  cases (firstSharedInstanceCosted worldNames.size thingNames.size tables x y w).value
  all_goals simp only [indexedNameCosted_value]
  all_goals rfl

private theorem disjointTypesEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesEvidenceCosted worldNames thingNames tables x y w).cost ≤ 39 * thingNames.size + 30 := by
  have hsearch := firstSharedInstanceCosted_cost_le worldNames.size thingNames.size tables x y w
  dsimp only [disjointTypesEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick]
  cases (firstSharedInstanceCosted worldNames.size thingNames.size tables x y w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

private theorem disjointTypesEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesEvidenceCosted worldNames thingNames tables x y w).value.size = 2 := by
  rw [disjointTypesEvidenceCosted_value]
  cases (firstSharedInstanceCosted worldNames.size thingNames.size tables x y w).value
  all_goals rfl

/-- Include the first uncovered instance in the two-row report. Search
costs at most 58T for T things. The assertion, names, match, and array cost
24, and witness text adds fourteen. The no-witness row needs no extra search. -/
private def completeCoverageEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let zn ← indexedNameCosted thingNames z
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `IsCompletelyCoveredBy("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure zn)
    text.appendString (.pure ")`.")
  let detail ← do
    let failure ← firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w
    Complexity.Costed.charge 1 <| match failure with
    | some witness => do
      let witnessName ← indexedNameCosted thingNames witness
      let wn ← indexedNameCosted worldNames w
      let text := Complexity.Costed.pure "  - Computed IsCompletelyCoveredBy: false, because `"
      let text := text.appendString (.pure witnessName)
      let text := text.appendString (.pure "` instantiates `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` but instantiates neither covering type at `")
      let text := text.appendString (.pure wn)
      text.appendString (.pure "`.")
    | none => .pure "  - Computed IsCompletelyCoveredBy: true; every current covered instance is assigned to at least one covering type."
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem completeCoverageEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (completeCoverageEvidenceCosted worldNames thingNames tables x y z w).value =
      match (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value with
      | some instIdx =>
          #[
            s!"  - User assertion: `IsCompletelyCoveredBy({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})`.",
            s!"  - Computed IsCompletelyCoveredBy: false, because `{indexedName thingNames instIdx}` instantiates `{indexedName thingNames x}` but instantiates neither covering type at `{indexedName worldNames w}`."
          ]
      | none =>
          #[
            s!"  - User assertion: `IsCompletelyCoveredBy({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})`.",
            "  - Computed IsCompletelyCoveredBy: true; every current covered instance is assigned to at least one covering type."
          ] := by
  dsimp only [completeCoverageEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals simp only [indexedNameCosted_value]
  all_goals rfl

private theorem completeCoverageEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (completeCoverageEvidenceCosted worldNames thingNames tables x y z w).cost ≤ 58 * thingNames.size + 38 := by
  have hsearch := firstCoveredInstanceFailureCosted_cost_le worldNames.size thingNames.size tables x y z w
  dsimp only [completeCoverageEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

private theorem completeCoverageEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (completeCoverageEvidenceCosted worldNames thingNames tables x y z w).value.size = 2 := by
  rw [completeCoverageEvidenceCosted_value]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals rfl

/-- Display a coverage failure before considering overlapping parts.
The coverage and shared-instance scans cost at most 58T and 39T for T things.
Common names, assertion text, and array operations cost 23. A coverage witness
adds fifteen for its match and text; a shared witness adds fourteen including
both matches. All branches fit 97T+38 and return two rows. -/
private def partitionEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let zn ← indexedNameCosted thingNames z
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `IsPartitionedInto("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure zn)
    text.appendString (.pure ")`.")
  let detail ← do
    let failure ← firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w
    Complexity.Costed.charge 1 <| match failure with
    | some witness => do
      let witnessName ← indexedNameCosted thingNames witness
      let wn ← indexedNameCosted worldNames w
      let text := Complexity.Costed.pure "  - Computed IsPartitionedInto: false, because coverage fails: `"
      let text := text.appendString (.pure witnessName)
      let text := text.appendString (.pure "` instantiates `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` but instantiates neither covering type at `")
      let text := text.appendString (.pure wn)
      text.appendString (.pure "`.")
    | none => do
      let shared ← firstSharedInstanceCosted worldNames.size thingNames.size tables y z w
      Complexity.Costed.charge 1 <| match shared with
      | some witness => do
        let witnessName ← indexedNameCosted thingNames witness
        let wn ← indexedNameCosted worldNames w
        let text := Complexity.Costed.pure "  - Computed IsPartitionedInto: false, because disjointness fails: `"
        let text := text.appendString (.pure witnessName)
        let text := text.appendString (.pure "` instantiates both covering types at `")
        let text := text.appendString (.pure wn)
        text.appendString (.pure "`.")
      | none => .pure "  - Coverage and disjointness counterexamples were not isolated; inspect typehood and instantiation facts."
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem partitionEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (partitionEvidenceCosted worldNames thingNames tables x y z w).value =
      match (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value with
      | some instIdx =>
          #[
            s!"  - User assertion: `IsPartitionedInto({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})`.",
            s!"  - Computed IsPartitionedInto: false, because coverage fails: `{indexedName thingNames instIdx}` instantiates `{indexedName thingNames x}` but instantiates neither covering type at `{indexedName worldNames w}`."
          ]
      | none =>
          match (firstSharedInstanceCosted worldNames.size thingNames.size tables y z w).value with
          | some instIdx =>
              #[
                s!"  - User assertion: `IsPartitionedInto({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})`.",
                s!"  - Computed IsPartitionedInto: false, because disjointness fails: `{indexedName thingNames instIdx}` instantiates both covering types at `{indexedName worldNames w}`."
              ]
          | none =>
              #[
                s!"  - User assertion: `IsPartitionedInto({indexedName thingNames x}, {indexedName thingNames y}, {indexedName thingNames z})`.",
                "  - Coverage and disjointness counterexamples were not isolated; inspect typehood and instantiation facts."
              ] := by
  dsimp only [partitionEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals cases (firstSharedInstanceCosted worldNames.size thingNames.size tables y z w).value
  all_goals simp only [indexedNameCosted_value]
  all_goals rfl

private theorem partitionEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (partitionEvidenceCosted worldNames thingNames tables x y z w).cost ≤ 97 * thingNames.size + 38 := by
  have hsearch := firstCoveredInstanceFailureCosted_cost_le worldNames.size thingNames.size tables x y z w
  have hshared := firstSharedInstanceCosted_cost_le worldNames.size thingNames.size tables y z w
  dsimp only [partitionEvidenceCosted,
    Bind.bind,
    Complexity.Costed.bind,
    Complexity.Costed.charge,
    Complexity.Costed.appendString,
    Complexity.Costed.pure,
    Complexity.Costed.tick]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals cases (firstSharedInstanceCosted worldNames.size thingNames.size tables y z w).value
  all_goals simp only [indexedNameCosted_cost]
  all_goals omega

private theorem partitionEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (partitionEvidenceCosted worldNames thingNames tables x y z w).value.size = 2 := by
  rw [partitionEvidenceCosted_value]
  cases (firstCoveredInstanceFailureCosted worldNames.size thingNames.size tables x y z w).value
  all_goals cases (firstSharedInstanceCosted worldNames.size thingNames.size tables y z w).value
  all_goals rfl


/-- The first source without a distinct target determines the functional report.
Only the selected failure branch constructs text. Name resolution and any
caller-supplied fallback are charged by the outer report.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def genericFunctionalDependenceRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let failure ← firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w
  Complexity.Costed.charge 1 <| match failure with
  | some witness => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let witnessName ← indexedNameCosted thingNames witness
    let text := Complexity.Costed.pure "`GenericFunctionalDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires a distinct target-functioning witness for source-functioning `")
    let text := text.appendString (.pure witnessName)
    let text := text.appendString (.pure "`; missing such a `")
    let text := text.appendString (.pure yn)
    text.appendString (.pure "` instance.")
  | none => do
    .pure fallback

private theorem genericFunctionalDependenceRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (genericFunctionalDependenceRequiredMissingCosted worldNames thingNames tables x y w fallback).value =
      match (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
      | some witness =>
          s!"`GenericFunctionalDependence({indexedName thingNames x}, {indexedName thingNames y})` requires a distinct target-functioning witness for source-functioning `{indexedName thingNames witness}`; missing such a `{indexedName thingNames y}` instance."
      | none => fallback := by
  dsimp only [genericFunctionalDependenceRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_value]
  cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    rfl
  | some witness =>
    rfl

private theorem genericFunctionalDependenceRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (genericFunctionalDependenceRequiredMissingCosted worldNames thingNames tables x y w fallback).cost ≤
      thingNames.size * (39 * thingNames.size + 41) + 21 := by
  have h0 := firstFunctionalDependenceFailureCosted_cost_le worldNames.size thingNames.size tables x y w
  dsimp only [genericFunctionalDependenceRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    dsimp only
    omega
  | some witness =>
    dsimp only
    omega

/-- Check generic dependence before source and target instantiation.
Only the selected failure branch constructs text. Name resolution and any
caller-supplied fallback are charged by the outer report.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def individualFunctionalDependenceRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    Complexity.Costed String := do
  let xn ← indexedNameCosted thingNames x
  let xTypeName ← indexedNameCosted thingNames xType
  let yn ← indexedNameCosted thingNames y
  let yTypeName ← indexedNameCosted thingNames yType
  let result ← genericFunctionalDependenceLookupCosted worldNames.size thingNames.size tables xType yType w
  Complexity.Costed.charge 2 <| if !result then do
    let text := Complexity.Costed.pure "`IndividualFunctionalDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    let text := text.appendString (.pure ")` requires `GenericFunctionalDependence(")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    text.appendString (.pure ")`; that computed type-level dependence is false.")
  else do
    let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w
    Complexity.Costed.charge 2 <| if !result then do
      let text := Complexity.Costed.pure "`IndividualFunctionalDependence("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure xTypeName)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yTypeName)
      let text := text.appendString (.pure ")` requires `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure " :: ")
      let text := text.appendString (.pure xTypeName)
      text.appendString (.pure "`; missing that instantiation.")
    else do
      let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w
      Complexity.Costed.charge 2 <| if !result then do
        let text := Complexity.Costed.pure "`IndividualFunctionalDependence("
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure xTypeName)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yTypeName)
        let text := text.appendString (.pure ")` requires `")
        let text := text.appendString (.pure yn)
        let text := text.appendString (.pure " :: ")
        let text := text.appendString (.pure yTypeName)
        text.appendString (.pure "`; missing that instantiation.")
      else do
        let text := Complexity.Costed.pure "`IndividualFunctionalDependence("
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure xTypeName)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yTypeName)
        let text := text.appendString (.pure ")` requires `")
        let text := text.appendString (.pure yn)
        let text := text.appendString (.pure "` to function as `")
        let text := text.appendString (.pure yTypeName)
        let text := text.appendString (.pure "` whenever `")
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure "` functions as `")
        let text := text.appendString (.pure xTypeName)
        text.appendString (.pure "`; missing the target `FunctionsAs` fact.")

private theorem individualFunctionalDependenceRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x xType y yType : Fin thingNames.size) (w : Fin worldNames.size) :
    (individualFunctionalDependenceRequiredMissingCosted worldNames thingNames tables x xType y yType w).value =
      if !genericFunctionalDependenceLookup worldNames.size thingNames.size tables xType yType w then
        s!"`IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `GenericFunctionalDependence({indexedName thingNames xType}, {indexedName thingNames yType})`; that computed type-level dependence is false."
      else if !tables.binaryLookup "inst" x xType w then
        s!"`IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `{indexedName thingNames x} :: {indexedName thingNames xType}`; missing that instantiation."
      else if !tables.binaryLookup "inst" y yType w then
        s!"`IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `{indexedName thingNames y} :: {indexedName thingNames yType}`; missing that instantiation."
      else
        s!"`IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `{indexedName thingNames y}` to function as `{indexedName thingNames yType}` whenever `{indexedName thingNames x}` functions as `{indexedName thingNames xType}`; missing the target `FunctionsAs` fact." := by
  have h0 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst x xType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w).value =
    tables.binaryLookup "inst" x xType w at h0
  have h1 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst y yType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w).value =
    tables.binaryLookup "inst" y yType w at h1
  dsimp only [individualFunctionalDependenceRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick, genericFunctionalDependenceLookup]
  simp only [indexedNameCosted_value]
  split
  · simp only [h0, h1] at *
    simp_all only [ite_true]
    rfl
  · split
    · simp only [h0, h1] at *
      simp_all only [ite_true]
      rfl
    · split
      · simp only [h0, h1] at *
        simp_all only [ite_true]
        rfl
      · simp only [h0, h1] at *
        simp_all only
        rfl

private theorem individualFunctionalDependenceRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (individualFunctionalDependenceRequiredMissingCosted worldNames thingNames tables x xType y yType w).cost ≤
      thingNames.size * (39 * thingNames.size + 39) + 72 := by
  have h0 := genericFunctionalDependenceLookupCosted_cost_le worldNames.size thingNames.size tables xType yType w
  have h1 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst x xType w
  have h2 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst y yType w
  dsimp only [individualFunctionalDependenceRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  split
  · dsimp only
    omega
  · split
    · dsimp only
      omega
    · split
      · dsimp only
        omega
      · dsimp only
        omega

/-- Check proper parthood before explaining individual functional dependence.
Only the selected failure branch constructs text. Name resolution and any
caller-supplied fallback are charged by the outer report.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def componentOfRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    Complexity.Costed String := do
  let xn ← indexedNameCosted thingNames x
  let xTypeName ← indexedNameCosted thingNames xType
  let yn ← indexedNameCosted thingNames y
  let yTypeName ← indexedNameCosted thingNames yType
  let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .properPart x y w
  Complexity.Costed.charge 2 <| if !result then do
    let text := Complexity.Costed.pure "`ComponentOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    let text := text.appendString (.pure ")` requires `ProperPart(")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`; missing that proper-part fact.")
  else do
    let text := Complexity.Costed.pure "`ComponentOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    text.appendString (.pure ")` also requires computed `IndividualFunctionalDependence`; that dependence is false.")

private theorem componentOfRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x xType y yType : Fin thingNames.size) (w : Fin worldNames.size) :
    (componentOfRequiredMissingCosted worldNames thingNames tables x xType y yType w).value =
      if !tables.binaryLookup "properPart" x y w then
        s!"`ComponentOf({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `ProperPart({indexedName thingNames x}, {indexedName thingNames y})`; missing that proper-part fact."
      else
        s!"`ComponentOf({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` also requires computed `IndividualFunctionalDependence`; that dependence is false." := by
  have h0 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .properPart x y w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .properPart x y w).value =
    tables.binaryLookup "properPart" x y w at h0
  dsimp only [componentOfRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_value]
  split
  · simp only [h0] at *
    simp_all only [ite_true]
    rfl
  · simp only [h0] at *
    simp_all only
    rfl

private theorem componentOfRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (componentOfRequiredMissingCosted worldNames thingNames tables x xType y yType w).cost ≤
      47 := by
  have h0 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .properPart x y w
  dsimp only [componentOfRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  split
  · dsimp only
    omega
  · dsimp only
    omega

/-- The first source without a constituting target determines the report.
Only the selected failure branch constructs text. Name resolution and any
caller-supplied fallback are charged by the outer report.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def genericConstitutionalDependenceRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    Complexity.Costed String := do
  let failure ← firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w
  Complexity.Costed.charge 1 <| match failure with
  | some witness => do
    let xn ← indexedNameCosted thingNames x
    let yn ← indexedNameCosted thingNames y
    let witnessName ← indexedNameCosted thingNames witness
    let text := Complexity.Costed.pure "`GenericConstitutionalDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ")` requires a `")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure "` instance that constitutionally bears source instance `")
    let text := text.appendString (.pure witnessName)
    let text := text.appendString (.pure "`; missing such a `ConstitutedBy(")
    let text := text.appendString (.pure witnessName)
    text.appendString (.pure ", _)` witness.")
  | none => do
    .pure fallback

private theorem genericConstitutionalDependenceRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (genericConstitutionalDependenceRequiredMissingCosted worldNames thingNames tables x y w fallback).value =
      match (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
      | some witness =>
          s!"`GenericConstitutionalDependence({indexedName thingNames x}, {indexedName thingNames y})` requires a `{indexedName thingNames y}` instance that constitutionally bears source instance `{indexedName thingNames witness}`; missing such a `ConstitutedBy({indexedName thingNames witness}, _)` witness."
      | none => fallback := by
  dsimp only [genericConstitutionalDependenceRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_value]
  cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    rfl
  | some witness =>
    rfl

private theorem genericConstitutionalDependenceRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (genericConstitutionalDependenceRequiredMissingCosted worldNames thingNames tables x y w fallback).cost ≤
      thingNames.size * (37 * thingNames.size + 23) + 23 := by
  have h0 := firstConstitutionalDependenceFailureCosted_cost_le worldNames.size thingNames.size tables x y w
  dsimp only [genericConstitutionalDependenceRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    dsimp only
    omega
  | some witness =>
    dsimp only
    omega

/-- Check both instantiations before generic constitutional dependence.
Only the selected failure branch constructs text. Name resolution and any
caller-supplied fallback are charged by the outer report.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def constitutionRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    Complexity.Costed String := do
  let xn ← indexedNameCosted thingNames x
  let xTypeName ← indexedNameCosted thingNames xType
  let yn ← indexedNameCosted thingNames y
  let yTypeName ← indexedNameCosted thingNames yType
  let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w
  Complexity.Costed.charge 2 <| if !result then do
    let text := Complexity.Costed.pure "`Constitution("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    let text := text.appendString (.pure ")` requires `")
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure " :: ")
    let text := text.appendString (.pure xTypeName)
    text.appendString (.pure "`; missing that instantiation.")
  else do
    let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w
    Complexity.Costed.charge 2 <| if !result then do
      let text := Complexity.Costed.pure "`Constitution("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure xTypeName)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yTypeName)
      let text := text.appendString (.pure ")` requires `")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure " :: ")
      let text := text.appendString (.pure yTypeName)
      text.appendString (.pure "`; missing that instantiation.")
    else do
      let result ← genericConstitutionalDependenceLookupCosted worldNames.size thingNames.size tables xType yType w
      Complexity.Costed.charge 2 <| if !result then do
        let text := Complexity.Costed.pure "`Constitution("
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure xTypeName)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yTypeName)
        let text := text.appendString (.pure ")` requires computed `GenericConstitutionalDependence(")
        let text := text.appendString (.pure xTypeName)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yTypeName)
        text.appendString (.pure ")`; that dependence is false.")
      else do
        let text := Complexity.Costed.pure "`Constitution("
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure xTypeName)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yTypeName)
        let text := text.appendString (.pure ")` requires `ConstitutedBy(")
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure ", ")
        let text := text.appendString (.pure yn)
        text.appendString (.pure ")`; missing that fact.")

private theorem constitutionRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x xType y yType : Fin thingNames.size) (w : Fin worldNames.size) :
    (constitutionRequiredMissingCosted worldNames thingNames tables x xType y yType w).value =
      if !tables.binaryLookup "inst" x xType w then
        s!"`Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `{indexedName thingNames x} :: {indexedName thingNames xType}`; missing that instantiation."
      else if !tables.binaryLookup "inst" y yType w then
        s!"`Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `{indexedName thingNames y} :: {indexedName thingNames yType}`; missing that instantiation."
      else if !genericConstitutionalDependenceLookup worldNames.size thingNames.size tables xType yType w then
        s!"`Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires computed `GenericConstitutionalDependence({indexedName thingNames xType}, {indexedName thingNames yType})`; that dependence is false."
      else
        s!"`Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})` requires `ConstitutedBy({indexedName thingNames x}, {indexedName thingNames y})`; missing that fact." := by
  have h0 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst x xType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w).value =
    tables.binaryLookup "inst" x xType w at h0
  have h1 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst y yType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w).value =
    tables.binaryLookup "inst" y yType w at h1
  dsimp only [constitutionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick, genericConstitutionalDependenceLookup]
  simp only [indexedNameCosted_value]
  split
  · simp only [h0, h1] at *
    simp_all only [ite_true]
    rfl
  · split
    · simp only [h0, h1] at *
      simp_all only [ite_true]
      rfl
    · split
      · simp only [h0, h1] at *
        simp_all only [ite_true]
        rfl
      · simp only [h0, h1] at *
        simp_all only
        rfl

private theorem constitutionRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (constitutionRequiredMissingCosted worldNames thingNames tables x xType y yType w).cost ≤
      thingNames.size * (37 * thingNames.size + 21) + 68 := by
  have h0 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst x xType w
  have h1 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst y yType w
  have h2 := genericConstitutionalDependenceLookupCosted_cost_le worldNames.size thingNames.size tables xType yType w
  dsimp only [constitutionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  split
  · dsimp only
    omega
  · split
    · dsimp only
      omega
    · split
      · dsimp only
        omega
      · dsimp only
        omega

/-- The first source without a distinct target determines the functional report.
The witness search and construction of both rows are charged.
It emits two rows; the caller accounts for dispatch and the output budget.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def genericFunctionalDependenceEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `GenericFunctionalDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let detail ← do
    let failure ← firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w
    Complexity.Costed.charge 1 <| match failure with
    | some witness => do
      let witnessName ← indexedNameCosted thingNames witness
      let wn ← indexedNameCosted worldNames w
      let text := Complexity.Costed.pure "  - Computed GenericFunctionalDependence: false, because `"
      let text := text.appendString (.pure witnessName)
      let text := text.appendString (.pure "` instantiates and functions as `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` at `")
      let text := text.appendString (.pure wn)
      let text := text.appendString (.pure "`, but there is no distinct thing that instantiates and functions as `")
      let text := text.appendString (.pure yn)
      text.appendString (.pure "`.")
    | none => do
      .pure "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem genericFunctionalDependenceEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericFunctionalDependenceEvidenceCosted worldNames thingNames tables x y w).value =
      match (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
      | some witness =>
          #[
            s!"  - User assertion: `GenericFunctionalDependence({indexedName thingNames x}, {indexedName thingNames y})`.",
            s!"  - Computed GenericFunctionalDependence: false, because `{indexedName thingNames witness}` instantiates and functions as `{indexedName thingNames x}` at `{indexedName worldNames w}`, but there is no distinct thing that instantiates and functions as `{indexedName thingNames y}`."
          ]
      | none =>
          #[
            s!"  - User assertion: `GenericFunctionalDependence({indexedName thingNames x}, {indexedName thingNames y})`.",
            "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."
          ] := by
  dsimp only [genericFunctionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_value]
  cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    rfl
  | some witness =>
    rfl

private theorem genericFunctionalDependenceEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericFunctionalDependenceEvidenceCosted worldNames thingNames tables x y w).cost ≤
      thingNames.size * (39 * thingNames.size + 41) + 34 := by
  have h0 := firstFunctionalDependenceFailureCosted_cost_le worldNames.size thingNames.size tables x y w
  dsimp only [genericFunctionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    dsimp only
    omega
  | some witness =>
    dsimp only
    omega

private theorem genericFunctionalDependenceEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericFunctionalDependenceEvidenceCosted worldNames thingNames tables x y w).value.size = 2 := by
  dsimp only [genericFunctionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    rfl
  | some witness =>
    rfl

/-- Check generic dependence before source and target instantiation.
The evidence path counts its Boolean check and any separate witness search.
It emits two rows; the caller accounts for dispatch and the output budget.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def individualFunctionalDependenceEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let xTypeName ← indexedNameCosted thingNames xType
  let yn ← indexedNameCosted thingNames y
  let yTypeName ← indexedNameCosted thingNames yType
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `IndividualFunctionalDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    text.appendString (.pure ")`.")
  let detail ← do
    let result ← genericFunctionalDependenceLookupCosted worldNames.size thingNames.size tables xType yType w
    Complexity.Costed.charge 2 <| if !result then do
      let failure ← firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w
      Complexity.Costed.charge 1 <| match failure with
      | some witness => do
        let witnessName ← indexedNameCosted thingNames witness
        let text := Complexity.Costed.pure "  - Computed IndividualFunctionalDependence: false, because type-level functional dependence fails for source witness `"
        let text := text.appendString (.pure witnessName)
        text.appendString (.pure "`.")
      | none => do
        .pure "  - Computed IndividualFunctionalDependence: false, because type-level functional dependence is false."
    else do
      let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w
      Complexity.Costed.charge 2 <| if !result then do
        let wn ← indexedNameCosted worldNames w
        let text := Complexity.Costed.pure "  - Computed IndividualFunctionalDependence: false, because `"
        let text := text.appendString (.pure xn)
        let text := text.appendString (.pure " :: ")
        let text := text.appendString (.pure xTypeName)
        let text := text.appendString (.pure "` is missing at `")
        let text := text.appendString (.pure wn)
        text.appendString (.pure "`.")
      else do
        let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w
        Complexity.Costed.charge 2 <| if !result then do
          let wn ← indexedNameCosted worldNames w
          let text := Complexity.Costed.pure "  - Computed IndividualFunctionalDependence: false, because `"
          let text := text.appendString (.pure yn)
          let text := text.appendString (.pure " :: ")
          let text := text.appendString (.pure yTypeName)
          let text := text.appendString (.pure "` is missing at `")
          let text := text.appendString (.pure wn)
          text.appendString (.pure "`.")
        else do
          let wn ← indexedNameCosted worldNames w
          let text := Complexity.Costed.pure "  - Computed IndividualFunctionalDependence: false, because `"
          let text := text.appendString (.pure xn)
          let text := text.appendString (.pure "` functions as `")
          let text := text.appendString (.pure xTypeName)
          let text := text.appendString (.pure "` but `")
          let text := text.appendString (.pure yn)
          let text := text.appendString (.pure "` does not function as `")
          let text := text.appendString (.pure yTypeName)
          let text := text.appendString (.pure "` at `")
          let text := text.appendString (.pure wn)
          text.appendString (.pure "`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem individualFunctionalDependenceEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x xType y yType : Fin thingNames.size) (w : Fin worldNames.size) :
    (individualFunctionalDependenceEvidenceCosted worldNames thingNames tables x xType y yType w).value =
      if !genericFunctionalDependenceLookup worldNames.size thingNames.size tables xType yType w then
        match (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
        | some witness =>
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
              s!"  - Computed IndividualFunctionalDependence: false, because type-level functional dependence fails for source witness `{indexedName thingNames witness}`."
            ]
        | none =>
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
              "  - Computed IndividualFunctionalDependence: false, because type-level functional dependence is false."
            ]
      else if !tables.binaryLookup "inst" x xType w then
        #[
          s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames x} :: {indexedName thingNames xType}` is missing at `{indexedName worldNames w}`."
        ]
      else if !tables.binaryLookup "inst" y yType w then
        #[
          s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames y} :: {indexedName thingNames yType}` is missing at `{indexedName worldNames w}`."
        ]
      else
        #[
          s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames x}` functions as `{indexedName thingNames xType}` but `{indexedName thingNames y}` does not function as `{indexedName thingNames yType}` at `{indexedName worldNames w}`."
        ] := by
  have h0 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst x xType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w).value =
    tables.binaryLookup "inst" x xType w at h0
  have h1 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst y yType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w).value =
    tables.binaryLookup "inst" y yType w at h1
  dsimp only [individualFunctionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick, genericFunctionalDependenceLookup]
  simp only [indexedNameCosted_value]
  split
  · cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
    | none =>
      simp only [h0, h1] at *
      simp_all only [ite_true]
      rfl
    | some witness =>
      simp only [h0, h1] at *
      simp_all only [ite_true]
      rfl
  · split
    · simp only [h0, h1] at *
      simp_all only [ite_true]
      rfl
    · split
      · simp only [h0, h1] at *
        simp_all only [ite_true]
        rfl
      · simp only [h0, h1] at *
        simp_all only
        rfl

private theorem individualFunctionalDependenceEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (individualFunctionalDependenceEvidenceCosted worldNames thingNames tables x xType y yType w).cost ≤
      thingNames.size * (39 * thingNames.size + 39) + thingNames.size * (39 * thingNames.size + 41) + 83 := by
  have h0 := genericFunctionalDependenceLookupCosted_cost_le worldNames.size thingNames.size tables xType yType w
  have h1 := firstFunctionalDependenceFailureCosted_cost_le worldNames.size thingNames.size tables xType yType w
  have h2 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst x xType w
  have h3 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst y yType w
  dsimp only [individualFunctionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  split
  · cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
    | none =>
      dsimp only
      omega
    | some witness =>
      dsimp only
      omega
  · split
    · dsimp only
      omega
    · split
      · dsimp only
        omega
      · dsimp only
        omega

private theorem individualFunctionalDependenceEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (individualFunctionalDependenceEvidenceCosted worldNames thingNames tables x xType y yType w).value.size = 2 := by
  dsimp only [individualFunctionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  split
  · cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
    | none =>
      rfl
    | some witness =>
      rfl
  · split
    · rfl
    · split
      · rfl
      · rfl

/-- Check proper parthood before explaining individual functional dependence.
The evidence path counts its Boolean check and any separate witness search.
It emits two rows; the caller accounts for dispatch and the output budget.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def componentOfEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let xTypeName ← indexedNameCosted thingNames xType
  let yn ← indexedNameCosted thingNames y
  let yTypeName ← indexedNameCosted thingNames yType
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `ComponentOf("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    text.appendString (.pure ")`.")
  let detail ← do
    let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .properPart x y w
    Complexity.Costed.charge 2 <| if !result then do
      let wn ← indexedNameCosted worldNames w
      let text := Complexity.Costed.pure "  - Computed ComponentOf: false, because `ProperPart("
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure ", ")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure ")` is missing at `")
      let text := text.appendString (.pure wn)
      text.appendString (.pure "`.")
    else do
      let ifdReason ← do
        let result ← genericFunctionalDependenceLookupCosted worldNames.size thingNames.size tables xType yType w
        Complexity.Costed.charge 2 <| if !result then do
          let failure ← firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w
          Complexity.Costed.charge 1 <| match failure with
          | some witness => do
            let witnessName ← indexedNameCosted thingNames witness
            let text := Complexity.Costed.pure "type-level functional dependence fails for source witness `"
            let text := text.appendString (.pure witnessName)
            text.appendString (.pure "`")
          | none => do
            .pure "type-level functional dependence is false"
        else do
          let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w
          Complexity.Costed.charge 2 <| if !result then do
            let text := Complexity.Costed.pure "`"
            let text := text.appendString (.pure xn)
            let text := text.appendString (.pure " :: ")
            let text := text.appendString (.pure xTypeName)
            text.appendString (.pure "` is missing")
          else do
            let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w
            Complexity.Costed.charge 2 <| if !result then do
              let text := Complexity.Costed.pure "`"
              let text := text.appendString (.pure yn)
              let text := text.appendString (.pure " :: ")
              let text := text.appendString (.pure yTypeName)
              text.appendString (.pure "` is missing")
            else do
              let text := Complexity.Costed.pure "`"
              let text := text.appendString (.pure xn)
              let text := text.appendString (.pure "` functions as `")
              let text := text.appendString (.pure xTypeName)
              let text := text.appendString (.pure "` but `")
              let text := text.appendString (.pure yn)
              let text := text.appendString (.pure "` does not function as `")
              let text := text.appendString (.pure yTypeName)
              text.appendString (.pure "`")
      let text := Complexity.Costed.pure "  - Computed ComponentOf: false, because the required individual functional dependence is false: "
      let text := text.appendString (.pure ifdReason)
      text.appendString (.pure ".")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem componentOfEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x xType y yType : Fin thingNames.size) (w : Fin worldNames.size) :
    (componentOfEvidenceCosted worldNames thingNames tables x xType y yType w).value =
      if !tables.binaryLookup "properPart" x y w then
        #[
          s!"  - User assertion: `ComponentOf({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed ComponentOf: false, because `ProperPart({indexedName thingNames x}, {indexedName thingNames y})` is missing at `{indexedName worldNames w}`."
        ]
      else
        let ifdReason :=
          if !genericFunctionalDependenceLookup worldNames.size thingNames.size tables xType yType w then
            match (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
            | some witness =>
                s!"type-level functional dependence fails for source witness `{indexedName thingNames witness}`"
            | none => "type-level functional dependence is false"
          else if !tables.binaryLookup "inst" x xType w then
            s!"`{indexedName thingNames x} :: {indexedName thingNames xType}` is missing"
          else if !tables.binaryLookup "inst" y yType w then
            s!"`{indexedName thingNames y} :: {indexedName thingNames yType}` is missing"
          else
            s!"`{indexedName thingNames x}` functions as `{indexedName thingNames xType}` but `{indexedName thingNames y}` does not function as `{indexedName thingNames yType}`"
        #[
          s!"  - User assertion: `ComponentOf({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed ComponentOf: false, because the required individual functional dependence is false: {ifdReason}."
        ] := by
  have h0 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .properPart x y w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .properPart x y w).value =
    tables.binaryLookup "properPart" x y w at h0
  have h1 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst x xType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w).value =
    tables.binaryLookup "inst" x xType w at h1
  have h2 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst y yType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w).value =
    tables.binaryLookup "inst" y yType w at h2
  dsimp only [componentOfEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick, genericFunctionalDependenceLookup]
  simp only [indexedNameCosted_value]
  split
  · simp only [h0, h1, h2] at *
    simp_all only [ite_true]
    rfl
  · split
    · cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
      | none =>
        simp only [h0, h1, h2] at *
        simp_all only [ite_true]
        rfl
      | some witness =>
        simp only [h0, h1, h2] at *
        simp_all only [ite_true]
        rfl
    · split
      · simp only [h0, h1, h2] at *
        simp_all only [ite_true]
        rfl
      · split
        · simp only [h0, h1, h2] at *
          simp_all only [ite_true]
          rfl
        · simp only [h0, h1, h2] at *
          simp_all only
          rfl

private theorem componentOfEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (componentOfEvidenceCosted worldNames thingNames tables x xType y yType w).cost ≤
      thingNames.size * (39 * thingNames.size + 39) + thingNames.size * (39 * thingNames.size + 41) + 98 := by
  have h0 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .properPart x y w
  have h1 := genericFunctionalDependenceLookupCosted_cost_le worldNames.size thingNames.size tables xType yType w
  have h2 := firstFunctionalDependenceFailureCosted_cost_le worldNames.size thingNames.size tables xType yType w
  have h3 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst x xType w
  have h4 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst y yType w
  dsimp only [componentOfEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  split
  · dsimp only
    omega
  · split
    · cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
      | none =>
        dsimp only
        omega
      | some witness =>
        dsimp only
        omega
    · split
      · dsimp only
        omega
      · split
        · dsimp only
          omega
        · dsimp only
          omega

private theorem componentOfEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (componentOfEvidenceCosted worldNames thingNames tables x xType y yType w).value.size = 2 := by
  dsimp only [componentOfEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  split
  · rfl
  · split
    · cases (firstFunctionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
      | none =>
        rfl
      | some witness =>
        rfl
    · split
      · rfl
      · split
        · rfl
        · rfl

/-- The first source without a constituting target determines the report.
The witness search and construction of both rows are charged.
It emits two rows; the caller accounts for dispatch and the output budget.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def genericConstitutionalDependenceEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `GenericConstitutionalDependence("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    text.appendString (.pure ")`.")
  let detail ← do
    let failure ← firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w
    Complexity.Costed.charge 1 <| match failure with
    | some witness => do
      let witnessName ← indexedNameCosted thingNames witness
      let wn ← indexedNameCosted worldNames w
      let text := Complexity.Costed.pure "  - Computed GenericConstitutionalDependence: false, because `"
      let text := text.appendString (.pure witnessName)
      let text := text.appendString (.pure "` instantiates `")
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure "` at `")
      let text := text.appendString (.pure wn)
      let text := text.appendString (.pure "`, but no `")
      let text := text.appendString (.pure yn)
      let text := text.appendString (.pure "` instance is related by `ConstitutedBy(")
      let text := text.appendString (.pure witnessName)
      text.appendString (.pure ", _)`.")
    | none => do
      .pure "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem genericConstitutionalDependenceEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericConstitutionalDependenceEvidenceCosted worldNames thingNames tables x y w).value =
      match (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
      | some witness =>
          #[
            s!"  - User assertion: `GenericConstitutionalDependence({indexedName thingNames x}, {indexedName thingNames y})`.",
            s!"  - Computed GenericConstitutionalDependence: false, because `{indexedName thingNames witness}` instantiates `{indexedName thingNames x}` at `{indexedName worldNames w}`, but no `{indexedName thingNames y}` instance is related by `ConstitutedBy({indexedName thingNames witness}, _)`."
          ]
      | none =>
          #[
            s!"  - User assertion: `GenericConstitutionalDependence({indexedName thingNames x}, {indexedName thingNames y})`.",
            "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."
          ] := by
  dsimp only [genericConstitutionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_value]
  cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    rfl
  | some witness =>
    rfl

private theorem genericConstitutionalDependenceEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericConstitutionalDependenceEvidenceCosted worldNames thingNames tables x y w).cost ≤
      thingNames.size * (37 * thingNames.size + 23) + 36 := by
  have h0 := firstConstitutionalDependenceFailureCosted_cost_le worldNames.size thingNames.size tables x y w
  dsimp only [genericConstitutionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    dsimp only
    omega
  | some witness =>
    dsimp only
    omega

private theorem genericConstitutionalDependenceEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericConstitutionalDependenceEvidenceCosted worldNames thingNames tables x y w).value.size = 2 := by
  dsimp only [genericConstitutionalDependenceEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables x y w).value with
  | none =>
    rfl
  | some witness =>
    rfl

/-- Check both instantiations before generic constitutional dependence.
The evidence path counts its Boolean check and any separate witness search.
It emits two rows; the caller accounts for dispatch and the output budget.
The compositional counting method follows Niu et al. (POPL 2022,
doi:10.1145/3498670); string-character work is outside this model. -/
private def constitutionEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let xTypeName ← indexedNameCosted thingNames xType
  let yn ← indexedNameCosted thingNames y
  let yTypeName ← indexedNameCosted thingNames yType
  let assertion ← do
    let text := Complexity.Costed.pure "  - User assertion: `Constitution("
    let text := text.appendString (.pure xn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure xTypeName)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yn)
    let text := text.appendString (.pure ", ")
    let text := text.appendString (.pure yTypeName)
    text.appendString (.pure ")`.")
  let detail ← do
    let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w
    Complexity.Costed.charge 2 <| if !result then do
      let wn ← indexedNameCosted worldNames w
      let text := Complexity.Costed.pure "  - Computed Constitution: false, because `"
      let text := text.appendString (.pure xn)
      let text := text.appendString (.pure " :: ")
      let text := text.appendString (.pure xTypeName)
      let text := text.appendString (.pure "` is missing at `")
      let text := text.appendString (.pure wn)
      text.appendString (.pure "`.")
    else do
      let result ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w
      Complexity.Costed.charge 2 <| if !result then do
        let wn ← indexedNameCosted worldNames w
        let text := Complexity.Costed.pure "  - Computed Constitution: false, because `"
        let text := text.appendString (.pure yn)
        let text := text.appendString (.pure " :: ")
        let text := text.appendString (.pure yTypeName)
        let text := text.appendString (.pure "` is missing at `")
        let text := text.appendString (.pure wn)
        text.appendString (.pure "`.")
      else do
        let result ← genericConstitutionalDependenceLookupCosted worldNames.size thingNames.size tables xType yType w
        Complexity.Costed.charge 2 <| if !result then do
          let failure ← firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w
          Complexity.Costed.charge 1 <| match failure with
          | some witness => do
            let witnessName ← indexedNameCosted thingNames witness
            let text := Complexity.Costed.pure "  - Computed Constitution: false, because generic constitutional dependence fails for source witness `"
            let text := text.appendString (.pure witnessName)
            text.appendString (.pure "`.")
          | none => do
            .pure "  - Computed Constitution: false, because generic constitutional dependence is false."
        else do
          let wn ← indexedNameCosted worldNames w
          let text := Complexity.Costed.pure "  - Computed Constitution: false, because `ConstitutedBy("
          let text := text.appendString (.pure xn)
          let text := text.appendString (.pure ", ")
          let text := text.appendString (.pure yn)
          let text := text.appendString (.pure ")` is missing at `")
          let text := text.appendString (.pure wn)
          text.appendString (.pure "`.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assertion) 2
  Complexity.Costed.tick (out.push detail) 2

private theorem constitutionEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x xType y yType : Fin thingNames.size) (w : Fin worldNames.size) :
    (constitutionEvidenceCosted worldNames thingNames tables x xType y yType w).value =
      if !tables.binaryLookup "inst" x xType w then
        #[
          s!"  - User assertion: `Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed Constitution: false, because `{indexedName thingNames x} :: {indexedName thingNames xType}` is missing at `{indexedName worldNames w}`."
        ]
      else if !tables.binaryLookup "inst" y yType w then
        #[
          s!"  - User assertion: `Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed Constitution: false, because `{indexedName thingNames y} :: {indexedName thingNames yType}` is missing at `{indexedName worldNames w}`."
        ]
      else if !genericConstitutionalDependenceLookup worldNames.size thingNames.size tables xType yType w then
        match (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
        | some witness =>
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
              s!"  - Computed Constitution: false, because generic constitutional dependence fails for source witness `{indexedName thingNames witness}`."
            ]
        | none =>
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
              "  - Computed Constitution: false, because generic constitutional dependence is false."
            ]
      else
        #[
          s!"  - User assertion: `Constitution({indexedName thingNames x}, {indexedName thingNames xType}, {indexedName thingNames y}, {indexedName thingNames yType})`.",
          s!"  - Computed Constitution: false, because `ConstitutedBy({indexedName thingNames x}, {indexedName thingNames y})` is missing at `{indexedName worldNames w}`."
        ] := by
  have h0 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst x xType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst x xType w).value =
    tables.binaryLookup "inst" x xType w at h0
  have h1 := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inst y yType w
  change (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .inst y yType w).value =
    tables.binaryLookup "inst" y yType w at h1
  dsimp only [constitutionEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick, genericConstitutionalDependenceLookup]
  simp only [indexedNameCosted_value]
  split
  · simp only [h0, h1] at *
    simp_all only [ite_true]
    rfl
  · split
    · simp only [h0, h1] at *
      simp_all only [ite_true]
      rfl
    · split
      · cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
        | none =>
          simp only [h0, h1] at *
          simp_all only [ite_true]
          rfl
        | some witness =>
          simp only [h0, h1] at *
          simp_all only [ite_true]
          rfl
      · simp only [h0, h1] at *
        simp_all only
        rfl

private theorem constitutionEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (constitutionEvidenceCosted worldNames thingNames tables x xType y yType w).cost ≤
      thingNames.size * (37 * thingNames.size + 21) + thingNames.size * (37 * thingNames.size + 23) + 79 := by
  have h0 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst x xType w
  have h1 := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size tables .inst y yType w
  have h2 := genericConstitutionalDependenceLookupCosted_cost_le worldNames.size thingNames.size tables xType yType w
  have h3 := firstConstitutionalDependenceFailureCosted_cost_le worldNames.size thingNames.size tables xType yType w
  dsimp only [constitutionEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  simp only [indexedNameCosted_cost]
  split
  · dsimp only
    omega
  · split
    · dsimp only
      omega
    · split
      · cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
        | none =>
          dsimp only
          omega
        | some witness =>
          dsimp only
          omega
      · dsimp only
        omega

private theorem constitutionEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (constitutionEvidenceCosted worldNames thingNames tables x xType y yType w).value.size = 2 := by
  dsimp only [constitutionEvidenceCosted, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge,
    Complexity.Costed.appendString, Complexity.Costed.pure, Complexity.Costed.tick]
  split
  · rfl
  · split
    · rfl
    · split
      · cases (firstConstitutionalDependenceFailureCosted worldNames.size thingNames.size tables xType yType w).value with
        | none =>
          rfl
        | some witness =>
          rfl
      · rfl

/-!
## Report dispatch and composition

These dispatchers resolve the names used by a report and select its components.
Resolution is eager: all requested names are searched before inspecting the
results. Bounds include those searches even when an earlier name is missing.
-/

/-- Resolve one report argument before inspecting the results.
The option match is charged before selecting a report or its fallback. -/
private def resolveReport1Costed (names : Array Name) (a0 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Complexity.Costed α) : Complexity.Costed α := do
  let r0 ← thingIndexByStringCosted names a0
  Complexity.Costed.charge 1 <| match r0 with
  | none => fallback ()
  | some i0 =>
    next i0

private theorem resolveReport1Costed_value (names : Array Name) (a0 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Complexity.Costed α) :
    (resolveReport1Costed names a0 fallback next).value =
      match thingIndexByString? names a0 with
      | some i0 => (next i0).value
      | _ => (fallback ()).value := by
  dsimp only [resolveReport1Costed, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.charge, thingIndexByString?]
  all_goals cases (thingIndexByStringCosted names a0).value
  all_goals rfl

private theorem resolveReport1Costed_cost_le (names : Array Name) (a0 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Complexity.Costed α) (B : Nat)
    (hf : (fallback ()).cost ≤ B)
    (hn : ∀ i0, (next i0).cost ≤ B) :
    (resolveReport1Costed names a0 fallback next).cost ≤ 9 * names.size + 1 + B := by
  have h0 := thingIndexByStringCosted_cost_le names a0
  dsimp only [resolveReport1Costed, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge]
  cases (thingIndexByStringCosted names a0).value with
  | none =>
    dsimp only
    omega
  | some i0 =>
    have h := hn i0
    dsimp only
    omega

/-- Resolve 2 report arguments before inspecting the results.
All name searches run, even if an earlier name is unknown. The result
matches then stop at the first missing name, as in the existing formatter. -/
private def resolveReport2Costed (names : Array Name) (a0 a1 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Complexity.Costed α) : Complexity.Costed α := do
  let r0 ← thingIndexByStringCosted names a0
  let r1 ← thingIndexByStringCosted names a1
  Complexity.Costed.charge 1 <| match r0 with
  | none => fallback ()
  | some i0 =>
    Complexity.Costed.charge 1 <| match r1 with
    | none => fallback ()
    | some i1 =>
      next i0 i1

private theorem resolveReport2Costed_value (names : Array Name) (a0 a1 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Complexity.Costed α) :
    (resolveReport2Costed names a0 a1 fallback next).value =
      match thingIndexByString? names a0, thingIndexByString? names a1 with
      | some i0, some i1 => (next i0 i1).value
      | _, _ => (fallback ()).value := by
  dsimp only [resolveReport2Costed, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.charge, thingIndexByString?]
  all_goals cases (thingIndexByStringCosted names a0).value
  all_goals cases (thingIndexByStringCosted names a1).value
  all_goals rfl

private theorem resolveReport2Costed_cost_le (names : Array Name) (a0 a1 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Complexity.Costed α) (B : Nat)
    (hf : (fallback ()).cost ≤ B)
    (hn : ∀ i0 i1, (next i0 i1).cost ≤ B) :
    (resolveReport2Costed names a0 a1 fallback next).cost ≤ 18 * names.size + 2 + B := by
  have h0 := thingIndexByStringCosted_cost_le names a0
  have h1 := thingIndexByStringCosted_cost_le names a1
  dsimp only [resolveReport2Costed, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge]
  cases (thingIndexByStringCosted names a0).value with
  | none =>
    dsimp only
    omega
  | some i0 =>
    cases (thingIndexByStringCosted names a1).value with
    | none =>
      dsimp only
      omega
    | some i1 =>
      have h := hn i0 i1
      dsimp only
      omega

/-- Resolve 3 report arguments before inspecting the results.
All name searches run, even if an earlier name is unknown. The result
matches then stop at the first missing name, as in the existing formatter. -/
private def resolveReport3Costed (names : Array Name) (a0 a1 a2 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Nat → Complexity.Costed α) : Complexity.Costed α := do
  let r0 ← thingIndexByStringCosted names a0
  let r1 ← thingIndexByStringCosted names a1
  let r2 ← thingIndexByStringCosted names a2
  Complexity.Costed.charge 1 <| match r0 with
  | none => fallback ()
  | some i0 =>
    Complexity.Costed.charge 1 <| match r1 with
    | none => fallback ()
    | some i1 =>
      Complexity.Costed.charge 1 <| match r2 with
      | none => fallback ()
      | some i2 =>
        next i0 i1 i2

private theorem resolveReport3Costed_value (names : Array Name) (a0 a1 a2 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Nat → Complexity.Costed α) :
    (resolveReport3Costed names a0 a1 a2 fallback next).value =
      match thingIndexByString? names a0, thingIndexByString? names a1, thingIndexByString? names a2 with
      | some i0, some i1, some i2 => (next i0 i1 i2).value
      | _, _, _ => (fallback ()).value := by
  dsimp only [resolveReport3Costed, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.charge, thingIndexByString?]
  all_goals cases (thingIndexByStringCosted names a0).value
  all_goals cases (thingIndexByStringCosted names a1).value
  all_goals cases (thingIndexByStringCosted names a2).value
  all_goals rfl

private theorem resolveReport3Costed_cost_le (names : Array Name) (a0 a1 a2 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Nat → Complexity.Costed α) (B : Nat)
    (hf : (fallback ()).cost ≤ B)
    (hn : ∀ i0 i1 i2, (next i0 i1 i2).cost ≤ B) :
    (resolveReport3Costed names a0 a1 a2 fallback next).cost ≤ 27 * names.size + 3 + B := by
  have h0 := thingIndexByStringCosted_cost_le names a0
  have h1 := thingIndexByStringCosted_cost_le names a1
  have h2 := thingIndexByStringCosted_cost_le names a2
  dsimp only [resolveReport3Costed, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge]
  cases (thingIndexByStringCosted names a0).value with
  | none =>
    dsimp only
    omega
  | some i0 =>
    cases (thingIndexByStringCosted names a1).value with
    | none =>
      dsimp only
      omega
    | some i1 =>
      cases (thingIndexByStringCosted names a2).value with
      | none =>
        dsimp only
        omega
      | some i2 =>
        have h := hn i0 i1 i2
        dsimp only
        omega

/-- Resolve 4 report arguments before inspecting the results.
All name searches run, even if an earlier name is unknown. The result
matches then stop at the first missing name, as in the existing formatter. -/
private def resolveReport4Costed (names : Array Name) (a0 a1 a2 a3 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Nat → Nat → Complexity.Costed α) : Complexity.Costed α := do
  let r0 ← thingIndexByStringCosted names a0
  let r1 ← thingIndexByStringCosted names a1
  let r2 ← thingIndexByStringCosted names a2
  let r3 ← thingIndexByStringCosted names a3
  Complexity.Costed.charge 1 <| match r0 with
  | none => fallback ()
  | some i0 =>
    Complexity.Costed.charge 1 <| match r1 with
    | none => fallback ()
    | some i1 =>
      Complexity.Costed.charge 1 <| match r2 with
      | none => fallback ()
      | some i2 =>
        Complexity.Costed.charge 1 <| match r3 with
        | none => fallback ()
        | some i3 =>
          next i0 i1 i2 i3

private theorem resolveReport4Costed_value (names : Array Name) (a0 a1 a2 a3 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Nat → Nat → Complexity.Costed α) :
    (resolveReport4Costed names a0 a1 a2 a3 fallback next).value =
      match thingIndexByString? names a0, thingIndexByString? names a1, thingIndexByString? names a2, thingIndexByString? names a3 with
      | some i0, some i1, some i2, some i3 => (next i0 i1 i2 i3).value
      | _, _, _, _ => (fallback ()).value := by
  dsimp only [resolveReport4Costed, Bind.bind, Complexity.Costed.bind,
    Complexity.Costed.charge, thingIndexByString?]
  all_goals cases (thingIndexByStringCosted names a0).value
  all_goals cases (thingIndexByStringCosted names a1).value
  all_goals cases (thingIndexByStringCosted names a2).value
  all_goals cases (thingIndexByStringCosted names a3).value
  all_goals rfl

private theorem resolveReport4Costed_cost_le (names : Array Name) (a0 a1 a2 a3 : String)
    (fallback : Unit → Complexity.Costed α) (next : Nat → Nat → Nat → Nat → Complexity.Costed α) (B : Nat)
    (hf : (fallback ()).cost ≤ B)
    (hn : ∀ i0 i1 i2 i3, (next i0 i1 i2 i3).cost ≤ B) :
    (resolveReport4Costed names a0 a1 a2 a3 fallback next).cost ≤ 36 * names.size + 4 + B := by
  have h0 := thingIndexByStringCosted_cost_le names a0
  have h1 := thingIndexByStringCosted_cost_le names a1
  have h2 := thingIndexByStringCosted_cost_le names a2
  have h3 := thingIndexByStringCosted_cost_le names a3
  dsimp only [resolveReport4Costed, Bind.bind, Complexity.Costed.bind, Complexity.Costed.charge]
  cases (thingIndexByStringCosted names a0).value with
  | none =>
    dsimp only
    omega
  | some i0 =>
    cases (thingIndexByStringCosted names a1).value with
    | none =>
      dsimp only
      omega
    | some i1 =>
      cases (thingIndexByStringCosted names a2).value with
      | none =>
        dsimp only
        omega
      | some i2 =>
        cases (thingIndexByStringCosted names a3).value with
        | none =>
          dsimp only
          omega
        | some i3 =>
          have h := hn i0 i1 i2 i3
          dsimp only
          omega

private theorem resolveReport1Costed_size_le (names : Array Name) (a0 : String)
    (fallback : Unit → Complexity.Costed (Array α))
    (next : Nat → Complexity.Costed (Array α)) (B : Nat)
    (hf : (fallback ()).value.size ≤ B)
    (hn : ∀ i0, (next i0).value.size ≤ B) :
    (resolveReport1Costed names a0 fallback next).value.size ≤ B := by
  rw [resolveReport1Costed_value]
  all_goals cases (thingIndexByString? names a0)
  all_goals dsimp only
  all_goals first | exact hf | apply hn

private theorem resolveReport2Costed_size_le (names : Array Name) (a0 a1 : String)
    (fallback : Unit → Complexity.Costed (Array α))
    (next : Nat → Nat → Complexity.Costed (Array α)) (B : Nat)
    (hf : (fallback ()).value.size ≤ B)
    (hn : ∀ i0 i1, (next i0 i1).value.size ≤ B) :
    (resolveReport2Costed names a0 a1 fallback next).value.size ≤ B := by
  rw [resolveReport2Costed_value]
  all_goals cases (thingIndexByString? names a0)
  all_goals cases (thingIndexByString? names a1)
  all_goals dsimp only
  all_goals first | exact hf | apply hn

private theorem resolveReport3Costed_size_le (names : Array Name) (a0 a1 a2 : String)
    (fallback : Unit → Complexity.Costed (Array α))
    (next : Nat → Nat → Nat → Complexity.Costed (Array α)) (B : Nat)
    (hf : (fallback ()).value.size ≤ B)
    (hn : ∀ i0 i1 i2, (next i0 i1 i2).value.size ≤ B) :
    (resolveReport3Costed names a0 a1 a2 fallback next).value.size ≤ B := by
  rw [resolveReport3Costed_value]
  all_goals cases (thingIndexByString? names a0)
  all_goals cases (thingIndexByString? names a1)
  all_goals cases (thingIndexByString? names a2)
  all_goals dsimp only
  all_goals first | exact hf | apply hn

private theorem resolveReport4Costed_size_le (names : Array Name) (a0 a1 a2 a3 : String)
    (fallback : Unit → Complexity.Costed (Array α))
    (next : Nat → Nat → Nat → Nat → Complexity.Costed (Array α)) (B : Nat)
    (hf : (fallback ()).value.size ≤ B)
    (hn : ∀ i0 i1 i2 i3, (next i0 i1 i2 i3).value.size ≤ B) :
    (resolveReport4Costed names a0 a1 a2 a3 fallback next).value.size ≤ B := by
  rw [resolveReport4Costed_value]
  all_goals cases (thingIndexByString? names a0)
  all_goals cases (thingIndexByString? names a1)
  all_goals cases (thingIndexByString? names a2)
  all_goals cases (thingIndexByString? names a3)
  all_goals dsimp only
  all_goals first | exact hf | apply hn

/-- Common polynomial upper bound for a selected report component. The first
term is the mode-report search bound; the remaining terms cover the finite
functional, quality, type, and rendering work. This is an upper bound, never
an assigned execution count. Each caller first accumulates its actual costs. -/
private def derivedReportComponentCostBound (W T : Nat) (tables : FactTables) : Nat :=
  externallyDependentModeStatusCostBound W T tables +
    T * (78 * T + 100) + W * (19 * T + 62) + 200 * T + 120

private def derivedAssertionRequiredMissingSpec
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : String :=
  let fallback := (requiredMissingFallbackCosted worldNames fact w).value
  match fact with
  | .unary "Quality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (qualityRequiredMissingCosted worldNames thingNames tables xIdx w).value
      | none => fallback
  | .unary "ExternallyDependentMode" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (externalModeRequiredMissingCosted worldNames thingNames tables xIdx w).value
      | none => fallback
  | .binary "ExternallyDependent" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (externallyDependentRequiredMissingCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => fallback
  | .binary "ExistentialDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (existentialDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx fallback).value
      | _, _ => fallback
  | .binary "ExistentialIndependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (existentialIndependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx fallback).value
      | _, _ => fallback
  | .unary "NonEmptySet" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (nonEmptySetRequiredMissingCosted worldNames thingNames xIdx w).value
      | none => fallback
  | .unary "QualityStructure" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (qualityStructureRequiredMissingCosted worldNames thingNames tables xIdx w).value
      | none => fallback
  | .unary "SimpleQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (simpleQualityRequiredMissingCosted worldNames thingNames tables xIdx w fallback).value
      | none => fallback
  | .unary "ComplexQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (complexQualityRequiredMissingCosted worldNames thingNames tables xIdx w).value
      | none => fallback
  | .unary "SimpleQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (simpleQualityTypeRequiredMissingCosted worldNames thingNames tables xIdx w fallback).value
      | none => fallback
  | .unary "ComplexQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (complexQualityTypeRequiredMissingCosted worldNames thingNames tables xIdx w fallback).value
      | none => fallback
  | .unary "QuaIndividual" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (quaIndividualRequiredMissingCosted worldNames thingNames xIdx w).value
      | none => fallback
  | .binary "UltimateBearerOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (ultimateBearerRequiredMissingCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => fallback
  | .binary "SubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (subsetRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback).value
      | _, _ => fallback
  | .binary "ProperSubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (properSubsetRequiredMissingCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => fallback
  | .binary "ProperSub" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (properSubRequiredMissingCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => fallback
  | .binary "GenericFunctionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (genericFunctionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback).value
      | _, _ => fallback
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          (individualFunctionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w).value
      | _, _, _, _ => fallback
  | .quaternary "ComponentOf" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          (componentOfRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w).value
      | _, _, _, _ => fallback
  | .binary "GenericConstitutionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (genericConstitutionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback).value
      | _, _ => fallback
  | .quaternary "Constitution" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          (constitutionRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w).value
      | _, _, _, _ => fallback
  | .binary "Categorizes" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (categorizesRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback).value
      | _, _ => fallback
  | .binary "IsDisjointWith" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (disjointTypesRequiredMissingCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => fallback
  | .ternary "IsCompletelyCoveredBy" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          (completeCoverageRequiredMissingCosted worldNames thingNames tables xIdx yIdx zIdx w fallback).value
      | _, _, _ => fallback
  | .ternary "IsPartitionedInto" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          (partitionRequiredMissingCosted worldNames thingNames tables xIdx yIdx zIdx w fallback).value
      | _, _, _ => fallback
  | _ => fallback

/-- Count arity and field selection, eager name resolution, and the selected
component. Fallback text is constructed before dispatch, including on successful paths.
As in compositional cost semantics (Niu et al., POPL 2022,
doi:10.1145/3498670), the report and its cost come from the same execution. -/
private def derivedAssertionRequiredMissingCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Complexity.Costed (String) := do
  let fallback ← requiredMissingFallbackCosted worldNames fact w
  Complexity.Costed.charge 1 <| match fact with
  | .unary field x =>
      Complexity.Costed.charge 2 <| if field == "Quality" then
        resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx => qualityRequiredMissingCosted worldNames thingNames tables xIdx w)
      else
        Complexity.Costed.charge 2 <| if field == "ExternallyDependentMode" then
          resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx => externalModeRequiredMissingCosted worldNames thingNames tables xIdx w)
        else
          Complexity.Costed.charge 2 <| if field == "NonEmptySet" then
            resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
              (fun xIdx => nonEmptySetRequiredMissingCosted worldNames thingNames xIdx w)
          else
            Complexity.Costed.charge 2 <| if field == "QualityStructure" then
              resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
                (fun xIdx => qualityStructureRequiredMissingCosted worldNames thingNames tables xIdx w)
            else
              Complexity.Costed.charge 2 <| if field == "SimpleQuality" then
                resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
                  (fun xIdx => simpleQualityRequiredMissingCosted worldNames thingNames tables xIdx w fallback)
              else
                Complexity.Costed.charge 2 <| if field == "ComplexQuality" then
                  resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
                    (fun xIdx => complexQualityRequiredMissingCosted worldNames thingNames tables xIdx w)
                else
                  Complexity.Costed.charge 2 <| if field == "SimpleQualityType" then
                    resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
                      (fun xIdx => simpleQualityTypeRequiredMissingCosted worldNames thingNames tables xIdx w fallback)
                  else
                    Complexity.Costed.charge 2 <| if field == "ComplexQualityType" then
                      resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
                        (fun xIdx => complexQualityTypeRequiredMissingCosted worldNames thingNames tables xIdx w fallback)
                    else
                      Complexity.Costed.charge 2 <| if field == "QuaIndividual" then
                        resolveReport1Costed thingNames x (fun _ => Complexity.Costed.pure fallback)
                          (fun xIdx => quaIndividualRequiredMissingCosted worldNames thingNames xIdx w)
                      else
                        Complexity.Costed.pure fallback
  | .binary field x y =>
      Complexity.Costed.charge 2 <| if field == "ExternallyDependent" then
        resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx yIdx => externallyDependentRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
      else
        Complexity.Costed.charge 2 <| if field == "ExistentialDependence" then
          resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx yIdx => existentialDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx fallback)
        else
          Complexity.Costed.charge 2 <| if field == "ExistentialIndependence" then
            resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
              (fun xIdx yIdx => existentialIndependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx fallback)
          else
            Complexity.Costed.charge 2 <| if field == "UltimateBearerOf" then
              resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                (fun xIdx yIdx => ultimateBearerRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
            else
              Complexity.Costed.charge 2 <| if field == "SubsetOf" then
                resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                  (fun xIdx yIdx => subsetRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
              else
                Complexity.Costed.charge 2 <| if field == "ProperSubsetOf" then
                  resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                    (fun xIdx yIdx => properSubsetRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
                else
                  Complexity.Costed.charge 2 <| if field == "ProperSub" then
                    resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                      (fun xIdx yIdx => properSubRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
                  else
                    Complexity.Costed.charge 2 <| if field == "GenericFunctionalDependence" then
                      resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                        (fun xIdx yIdx => genericFunctionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
                    else
                      Complexity.Costed.charge 2 <| if field == "GenericConstitutionalDependence" then
                        resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                          (fun xIdx yIdx => genericConstitutionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
                      else
                        Complexity.Costed.charge 2 <| if field == "Categorizes" then
                          resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                            (fun xIdx yIdx => categorizesRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
                        else
                          Complexity.Costed.charge 2 <| if field == "IsDisjointWith" then
                            resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.pure fallback)
                              (fun xIdx yIdx => disjointTypesRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
                          else
                            Complexity.Costed.pure fallback
  | .ternary field x y z =>
      Complexity.Costed.charge 2 <| if field == "IsCompletelyCoveredBy" then
        resolveReport3Costed thingNames x y z (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx yIdx zIdx => completeCoverageRequiredMissingCosted worldNames thingNames tables xIdx yIdx zIdx w fallback)
      else
        Complexity.Costed.charge 2 <| if field == "IsPartitionedInto" then
          resolveReport3Costed thingNames x y z (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx yIdx zIdx => partitionRequiredMissingCosted worldNames thingNames tables xIdx yIdx zIdx w fallback)
        else
          Complexity.Costed.pure fallback
  | .quaternary field x y z u =>
      Complexity.Costed.charge 2 <| if field == "IndividualFunctionalDependence" then
        resolveReport4Costed thingNames x y z u (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx xTypeIdx yIdx yTypeIdx => individualFunctionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
      else
        Complexity.Costed.charge 2 <| if field == "ComponentOf" then
          resolveReport4Costed thingNames x y z u (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx xTypeIdx yIdx yTypeIdx => componentOfRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
        else
          Complexity.Costed.charge 2 <| if field == "Constitution" then
            resolveReport4Costed thingNames x y z u (fun _ => Complexity.Costed.pure fallback)
              (fun xIdx xTypeIdx yIdx yTypeIdx => constitutionRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
          else
            Complexity.Costed.pure fallback

private theorem derivedAssertionRequiredMissingCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (derivedAssertionRequiredMissingCosted worldNames thingNames tables fact w).value =
      derivedAssertionRequiredMissingSpec worldNames thingNames tables fact w := by
  cases fact with
  | unary field x =>
      by_cases hf0 : field = "Quality"
      · subst field
        simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
        all_goals cases (thingIndexByString? thingNames x) <;> rfl
      · by_cases hf1 : field = "ExternallyDependentMode"
        · subst field
          simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
          all_goals cases (thingIndexByString? thingNames x) <;> rfl
        · by_cases hf2 : field = "NonEmptySet"
          · subst field
            simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
            all_goals cases (thingIndexByString? thingNames x) <;> rfl
          · by_cases hf3 : field = "QualityStructure"
            · subst field
              simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
              all_goals cases (thingIndexByString? thingNames x) <;> rfl
            · by_cases hf4 : field = "SimpleQuality"
              · subst field
                simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
                all_goals cases (thingIndexByString? thingNames x) <;> rfl
              · by_cases hf5 : field = "ComplexQuality"
                · subst field
                  simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
                  all_goals cases (thingIndexByString? thingNames x) <;> rfl
                · by_cases hf6 : field = "SimpleQualityType"
                  · subst field
                    simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
                    all_goals cases (thingIndexByString? thingNames x) <;> rfl
                  · by_cases hf7 : field = "ComplexQualityType"
                    · subst field
                      simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
                      all_goals cases (thingIndexByString? thingNames x) <;> rfl
                    · by_cases hf8 : field = "QuaIndividual"
                      · subst field
                        simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport1Costed_value]
                        all_goals cases (thingIndexByString? thingNames x) <;> rfl
                      · simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
  | binary field x y =>
      by_cases hf0 : field = "ExternallyDependent"
      · subst field
        simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
      · by_cases hf1 : field = "ExistentialDependence"
        · subst field
          simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
        · by_cases hf2 : field = "ExistentialIndependence"
          · subst field
            simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
          · by_cases hf3 : field = "UltimateBearerOf"
            · subst field
              simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
            · by_cases hf4 : field = "SubsetOf"
              · subst field
                simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
              · by_cases hf5 : field = "ProperSubsetOf"
                · subst field
                  simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
                · by_cases hf6 : field = "ProperSub"
                  · subst field
                    simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
                  · by_cases hf7 : field = "GenericFunctionalDependence"
                    · subst field
                      simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
                    · by_cases hf8 : field = "GenericConstitutionalDependence"
                      · subst field
                        simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
                      · by_cases hf9 : field = "Categorizes"
                        · subst field
                          simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
                        · by_cases hf10 : field = "IsDisjointWith"
                          · subst field
                            simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport2Costed_value]
                          · simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
  | ternary field x y z =>
      by_cases hf0 : field = "IsCompletelyCoveredBy"
      · subst field
        simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport3Costed_value]
      · by_cases hf1 : field = "IsPartitionedInto"
        · subst field
          simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport3Costed_value]
        · simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, hf0, hf1]
  | quaternary field x y z u =>
      by_cases hf0 : field = "IndividualFunctionalDependence"
      · subst field
        simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport4Costed_value]
      · by_cases hf1 : field = "ComponentOf"
        · subst field
          simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport4Costed_value]
        · by_cases hf2 : field = "Constitution"
          · subst field
            simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, resolveReport4Costed_value]
          · simp [derivedAssertionRequiredMissingCosted, derivedAssertionRequiredMissingSpec, Bind.bind, Complexity.Costed.bind_value, hf0, hf1, hf2]

private def derivedAssertionEvidenceSpec
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Array String :=
  match fact with
  | .unary "Quality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (qualityEvidenceCosted worldNames.size thingNames tables xIdx w).value
      | none => #[]
  | .unary "ExternallyDependentMode" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (externalModeEvidenceCosted worldNames thingNames tables xIdx w).value
      | none => #[]
  | .binary "ExternallyDependent" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (externallyDependentEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .binary "ExistentialDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (existentialDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx).value
      | _, _ => #[]
  | .binary "UltimateBearerOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (ultimateBearerEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .binary "ExistentialIndependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (existentialIndependenceEvidenceCosted worldNames thingNames tables xIdx yIdx).value
      | _, _ => #[]
  | .unary "NonEmptySet" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (nonEmptySetEvidenceCosted worldNames thingNames tables xIdx w).value
      | none => #[]
  | .unary "QualityStructure" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (qualityStructureEvidenceCosted worldNames thingNames tables xIdx w).value
      | none => #[]
  | .unary "SimpleQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (simpleQualityEvidenceCosted worldNames thingNames tables xIdx w).value
      | none => #[]
  | .unary "ComplexQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (complexQualityEvidenceCosted worldNames thingNames tables xIdx w).value
      | none => #[]
  | .unary "SimpleQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (simpleQualityTypeEvidenceCosted worldNames thingNames tables xIdx w).value
      | none => #[]
  | .unary "ComplexQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (complexQualityTypeEvidenceCosted worldNames thingNames tables xIdx w).value
      | none => #[]
  | .unary "QuaIndividual" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          (quaIndividualEvidenceCosted worldNames.size thingNames tables xIdx w).value
      | none => #[]
  | .binary "IsDisjointWith" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (disjointTypesEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .binary "SubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (subsetEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .binary "ProperSubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (properSubsetEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .binary "ProperSub" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (properSubEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .binary "GenericFunctionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (genericFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          (individualFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w).value
      | _, _, _, _ => #[]
  | .quaternary "ComponentOf" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          (componentOfEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w).value
      | _, _, _, _ => #[]
  | .binary "GenericConstitutionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (genericConstitutionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .quaternary "Constitution" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          (constitutionEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w).value
      | _, _, _, _ => #[]
  | .binary "Categorizes" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          (categorizesEvidenceCosted worldNames thingNames tables xIdx yIdx w).value
      | _, _ => #[]
  | .ternary "IsCompletelyCoveredBy" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          (completeCoverageEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w).value
      | _, _, _ => #[]
  | .ternary "IsPartitionedInto" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          (partitionEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w).value
      | _, _, _ => #[]
  | _ => #[]

/-- Count arity and field selection, eager name resolution, and the selected
component. An unrecognized field or missing name emits an empty array.
As in compositional cost semantics (Niu et al., POPL 2022,
doi:10.1145/3498670), the report and its cost come from the same execution. -/
private def derivedAssertionEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Complexity.Costed (Array String) := do
  Complexity.Costed.charge 1 <| match fact with
  | .unary field x =>
      Complexity.Costed.charge 2 <| if field == "Quality" then
        resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx => qualityEvidenceCosted worldNames.size thingNames tables xIdx w)
      else
        Complexity.Costed.charge 2 <| if field == "ExternallyDependentMode" then
          resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx => externalModeEvidenceCosted worldNames thingNames tables xIdx w)
        else
          Complexity.Costed.charge 2 <| if field == "NonEmptySet" then
            resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx => nonEmptySetEvidenceCosted worldNames thingNames tables xIdx w)
          else
            Complexity.Costed.charge 2 <| if field == "QualityStructure" then
              resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                (fun xIdx => qualityStructureEvidenceCosted worldNames thingNames tables xIdx w)
            else
              Complexity.Costed.charge 2 <| if field == "SimpleQuality" then
                resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                  (fun xIdx => simpleQualityEvidenceCosted worldNames thingNames tables xIdx w)
              else
                Complexity.Costed.charge 2 <| if field == "ComplexQuality" then
                  resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                    (fun xIdx => complexQualityEvidenceCosted worldNames thingNames tables xIdx w)
                else
                  Complexity.Costed.charge 2 <| if field == "SimpleQualityType" then
                    resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                      (fun xIdx => simpleQualityTypeEvidenceCosted worldNames thingNames tables xIdx w)
                  else
                    Complexity.Costed.charge 2 <| if field == "ComplexQualityType" then
                      resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                        (fun xIdx => complexQualityTypeEvidenceCosted worldNames thingNames tables xIdx w)
                    else
                      Complexity.Costed.charge 2 <| if field == "QuaIndividual" then
                        resolveReport1Costed thingNames x (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                          (fun xIdx => quaIndividualEvidenceCosted worldNames.size thingNames tables xIdx w)
                      else
                        Complexity.Costed.tick #[] 1
  | .binary field x y =>
      Complexity.Costed.charge 2 <| if field == "ExternallyDependent" then
        resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx yIdx => externallyDependentEvidenceCosted worldNames thingNames tables xIdx yIdx w)
      else
        Complexity.Costed.charge 2 <| if field == "ExistentialDependence" then
          resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx yIdx => existentialDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx)
        else
          Complexity.Costed.charge 2 <| if field == "UltimateBearerOf" then
            resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx yIdx => ultimateBearerEvidenceCosted worldNames thingNames tables xIdx yIdx w)
          else
            Complexity.Costed.charge 2 <| if field == "ExistentialIndependence" then
              resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                (fun xIdx yIdx => existentialIndependenceEvidenceCosted worldNames thingNames tables xIdx yIdx)
            else
              Complexity.Costed.charge 2 <| if field == "IsDisjointWith" then
                resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                  (fun xIdx yIdx => disjointTypesEvidenceCosted worldNames thingNames tables xIdx yIdx w)
              else
                Complexity.Costed.charge 2 <| if field == "SubsetOf" then
                  resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                    (fun xIdx yIdx => subsetEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                else
                  Complexity.Costed.charge 2 <| if field == "ProperSubsetOf" then
                    resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                      (fun xIdx yIdx => properSubsetEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                  else
                    Complexity.Costed.charge 2 <| if field == "ProperSub" then
                      resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                        (fun xIdx yIdx => properSubEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                    else
                      Complexity.Costed.charge 2 <| if field == "GenericFunctionalDependence" then
                        resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                          (fun xIdx yIdx => genericFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                      else
                        Complexity.Costed.charge 2 <| if field == "GenericConstitutionalDependence" then
                          resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                            (fun xIdx yIdx => genericConstitutionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                        else
                          Complexity.Costed.charge 2 <| if field == "Categorizes" then
                            resolveReport2Costed thingNames x y (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                              (fun xIdx yIdx => categorizesEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                          else
                            Complexity.Costed.tick #[] 1
  | .ternary field x y z =>
      Complexity.Costed.charge 2 <| if field == "IsCompletelyCoveredBy" then
        resolveReport3Costed thingNames x y z (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx yIdx zIdx => completeCoverageEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w)
      else
        Complexity.Costed.charge 2 <| if field == "IsPartitionedInto" then
          resolveReport3Costed thingNames x y z (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx yIdx zIdx => partitionEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w)
        else
          Complexity.Costed.tick #[] 1
  | .quaternary field x y z u =>
      Complexity.Costed.charge 2 <| if field == "IndividualFunctionalDependence" then
        resolveReport4Costed thingNames x y z u (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx xTypeIdx yIdx yTypeIdx => individualFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
      else
        Complexity.Costed.charge 2 <| if field == "ComponentOf" then
          resolveReport4Costed thingNames x y z u (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx xTypeIdx yIdx yTypeIdx => componentOfEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
        else
          Complexity.Costed.charge 2 <| if field == "Constitution" then
            resolveReport4Costed thingNames x y z u (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx xTypeIdx yIdx yTypeIdx => constitutionEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
          else
            Complexity.Costed.tick #[] 1

private theorem derivedAssertionEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (derivedAssertionEvidenceCosted worldNames thingNames tables fact w).value =
      derivedAssertionEvidenceSpec worldNames thingNames tables fact w := by
  cases fact with
  | unary field x =>
      by_cases hf0 : field = "Quality"
      · subst field
        simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
        all_goals cases (thingIndexByString? thingNames x) <;> rfl
      · by_cases hf1 : field = "ExternallyDependentMode"
        · subst field
          simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
          all_goals cases (thingIndexByString? thingNames x) <;> rfl
        · by_cases hf2 : field = "NonEmptySet"
          · subst field
            simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
            all_goals cases (thingIndexByString? thingNames x) <;> rfl
          · by_cases hf3 : field = "QualityStructure"
            · subst field
              simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
              all_goals cases (thingIndexByString? thingNames x) <;> rfl
            · by_cases hf4 : field = "SimpleQuality"
              · subst field
                simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
                all_goals cases (thingIndexByString? thingNames x) <;> rfl
              · by_cases hf5 : field = "ComplexQuality"
                · subst field
                  simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
                  all_goals cases (thingIndexByString? thingNames x) <;> rfl
                · by_cases hf6 : field = "SimpleQualityType"
                  · subst field
                    simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
                    all_goals cases (thingIndexByString? thingNames x) <;> rfl
                  · by_cases hf7 : field = "ComplexQualityType"
                    · subst field
                      simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
                      all_goals cases (thingIndexByString? thingNames x) <;> rfl
                    · by_cases hf8 : field = "QuaIndividual"
                      · subst field
                        simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport1Costed_value]
                        all_goals cases (thingIndexByString? thingNames x) <;> rfl
                      · simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
  | binary field x y =>
      by_cases hf0 : field = "ExternallyDependent"
      · subst field
        simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
      · by_cases hf1 : field = "ExistentialDependence"
        · subst field
          simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
        · by_cases hf2 : field = "UltimateBearerOf"
          · subst field
            simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
          · by_cases hf3 : field = "ExistentialIndependence"
            · subst field
              simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
            · by_cases hf4 : field = "IsDisjointWith"
              · subst field
                simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
              · by_cases hf5 : field = "SubsetOf"
                · subst field
                  simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
                · by_cases hf6 : field = "ProperSubsetOf"
                  · subst field
                    simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
                  · by_cases hf7 : field = "ProperSub"
                    · subst field
                      simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
                    · by_cases hf8 : field = "GenericFunctionalDependence"
                      · subst field
                        simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
                      · by_cases hf9 : field = "GenericConstitutionalDependence"
                        · subst field
                          simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
                        · by_cases hf10 : field = "Categorizes"
                          · subst field
                            simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport2Costed_value]
                          · simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
  | ternary field x y z =>
      by_cases hf0 : field = "IsCompletelyCoveredBy"
      · subst field
        simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport3Costed_value]
      · by_cases hf1 : field = "IsPartitionedInto"
        · subst field
          simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport3Costed_value]
        · simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, hf0, hf1]
  | quaternary field x y z u =>
      by_cases hf0 : field = "IndividualFunctionalDependence"
      · subst field
        simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport4Costed_value]
      · by_cases hf1 : field = "ComponentOf"
        · subst field
          simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport4Costed_value]
        · by_cases hf2 : field = "Constitution"
          · subst field
            simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, resolveReport4Costed_value]
          · simp [derivedAssertionEvidenceCosted, derivedAssertionEvidenceSpec, hf0, hf1, hf2]


/-- Resolution costs at most 36T+4, and arity plus field selection costs
at most 23. The eager required-missing fallback adds at most 18. -/
private theorem derivedAssertionRequiredMissingCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (derivedAssertionRequiredMissingCosted worldNames thingNames tables fact w).cost ≤
      derivedReportComponentCostBound worldNames.size thingNames.size tables + 36 * thingNames.size + 45 := by
  let fallback := (requiredMissingFallbackCosted worldNames fact w).value
  have hfallback := requiredMissingFallbackCosted_cost_le worldNames fact w
  cases fact with
  | unary field x =>
      by_cases hf0 : field = "Quality"
      · subst field
        have hr := resolveReport1Costed_cost_le thingNames x
          (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx => qualityRequiredMissingCosted worldNames thingNames tables xIdx w)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx
            have hc := qualityRequiredMissingCosted_cost_le worldNames thingNames tables xIdx w
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        dsimp only [fallback] at hr
        simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "ExternallyDependentMode"
        · subst field
          have hr := resolveReport1Costed_cost_le thingNames x
            (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx => externalModeRequiredMissingCosted worldNames thingNames tables xIdx w)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx
              have hc := externalModeRequiredMissingCosted_cost_le worldNames thingNames tables xIdx w
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          dsimp only [fallback] at hr
          simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
          omega
        · by_cases hf2 : field = "NonEmptySet"
          · subst field
            have hr := resolveReport1Costed_cost_le thingNames x
              (fun _ => Complexity.Costed.pure fallback)
              (fun xIdx => nonEmptySetRequiredMissingCosted worldNames thingNames xIdx w)
              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                omega) (by
                intro xIdx
                have hc := nonEmptySetRequiredMissingCosted_cost worldNames thingNames xIdx w
                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                  externallyDependentWitnessCostBound] at hc ⊢
                ring_nf at hc ⊢
                omega)
            dsimp only [fallback] at hr
            simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
            omega
          · by_cases hf3 : field = "QualityStructure"
            · subst field
              have hr := resolveReport1Costed_cost_le thingNames x
                (fun _ => Complexity.Costed.pure fallback)
                (fun xIdx => qualityStructureRequiredMissingCosted worldNames thingNames tables xIdx w)
                (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                  dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                  omega) (by
                  intro xIdx
                  have hc := qualityStructureRequiredMissingCosted_cost_le worldNames thingNames tables xIdx w
                  dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                    externallyDependentWitnessCostBound] at hc ⊢
                  ring_nf at hc ⊢
                  omega)
              dsimp only [fallback] at hr
              simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
              omega
            · by_cases hf4 : field = "SimpleQuality"
              · subst field
                have hr := resolveReport1Costed_cost_le thingNames x
                  (fun _ => Complexity.Costed.pure fallback)
                  (fun xIdx => simpleQualityRequiredMissingCosted worldNames thingNames tables xIdx w fallback)
                  (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                    dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                    omega) (by
                    intro xIdx
                    have hc := simpleQualityRequiredMissingCosted_cost_le worldNames thingNames tables xIdx w fallback
                    dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                      externallyDependentWitnessCostBound] at hc ⊢
                    ring_nf at hc ⊢
                    omega)
                dsimp only [fallback] at hr
                simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                omega
              · by_cases hf5 : field = "ComplexQuality"
                · subst field
                  have hr := resolveReport1Costed_cost_le thingNames x
                    (fun _ => Complexity.Costed.pure fallback)
                    (fun xIdx => complexQualityRequiredMissingCosted worldNames thingNames tables xIdx w)
                    (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                      dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                      omega) (by
                      intro xIdx
                      have hc := complexQualityRequiredMissingCosted_cost_le worldNames thingNames tables xIdx w
                      dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                        externallyDependentWitnessCostBound] at hc ⊢
                      ring_nf at hc ⊢
                      omega)
                  dsimp only [fallback] at hr
                  simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                  omega
                · by_cases hf6 : field = "SimpleQualityType"
                  · subst field
                    have hr := resolveReport1Costed_cost_le thingNames x
                      (fun _ => Complexity.Costed.pure fallback)
                      (fun xIdx => simpleQualityTypeRequiredMissingCosted worldNames thingNames tables xIdx w fallback)
                      (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                        dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                        omega) (by
                        intro xIdx
                        have hc := simpleQualityTypeRequiredMissingCosted_cost_le worldNames thingNames tables xIdx w fallback
                        dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                          externallyDependentWitnessCostBound] at hc ⊢
                        ring_nf at hc ⊢
                        omega)
                    dsimp only [fallback] at hr
                    simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                    omega
                  · by_cases hf7 : field = "ComplexQualityType"
                    · subst field
                      have hr := resolveReport1Costed_cost_le thingNames x
                        (fun _ => Complexity.Costed.pure fallback)
                        (fun xIdx => complexQualityTypeRequiredMissingCosted worldNames thingNames tables xIdx w fallback)
                        (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                          dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                          omega) (by
                          intro xIdx
                          have hc := complexQualityTypeRequiredMissingCosted_cost_le worldNames thingNames tables xIdx w fallback
                          dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                            externallyDependentWitnessCostBound] at hc ⊢
                          ring_nf at hc ⊢
                          omega)
                      dsimp only [fallback] at hr
                      simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                      omega
                    · by_cases hf8 : field = "QuaIndividual"
                      · subst field
                        have hr := resolveReport1Costed_cost_le thingNames x
                          (fun _ => Complexity.Costed.pure fallback)
                          (fun xIdx => quaIndividualRequiredMissingCosted worldNames thingNames xIdx w)
                          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                            omega) (by
                            intro xIdx
                            have hc := quaIndividualRequiredMissingCosted_cost worldNames thingNames xIdx w
                            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                              externallyDependentWitnessCostBound] at hc ⊢
                            ring_nf at hc ⊢
                            omega)
                        dsimp only [fallback] at hr
                        simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                        omega
                      · simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
                        omega
  | binary field x y =>
      by_cases hf0 : field = "ExternallyDependent"
      · subst field
        have hr := resolveReport2Costed_cost_le thingNames x y
          (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx yIdx => externallyDependentRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx yIdx
            have hc := externallyDependentRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        dsimp only [fallback] at hr
        simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "ExistentialDependence"
        · subst field
          have hr := resolveReport2Costed_cost_le thingNames x y
            (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx yIdx => existentialDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx fallback)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx yIdx
              have hc := existentialDependenceRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx fallback
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          dsimp only [fallback] at hr
          simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
          omega
        · by_cases hf2 : field = "ExistentialIndependence"
          · subst field
            have hr := resolveReport2Costed_cost_le thingNames x y
              (fun _ => Complexity.Costed.pure fallback)
              (fun xIdx yIdx => existentialIndependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx fallback)
              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                omega) (by
                intro xIdx yIdx
                have hc := existentialIndependenceRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx fallback
                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                  externallyDependentWitnessCostBound] at hc ⊢
                ring_nf at hc ⊢
                omega)
            dsimp only [fallback] at hr
            simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
            omega
          · by_cases hf3 : field = "UltimateBearerOf"
            · subst field
              have hr := resolveReport2Costed_cost_le thingNames x y
                (fun _ => Complexity.Costed.pure fallback)
                (fun xIdx yIdx => ultimateBearerRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
                (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                  dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                  omega) (by
                  intro xIdx yIdx
                  have hc := ultimateBearerRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w
                  dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                    externallyDependentWitnessCostBound] at hc ⊢
                  ring_nf at hc ⊢
                  omega)
              dsimp only [fallback] at hr
              simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
              omega
            · by_cases hf4 : field = "SubsetOf"
              · subst field
                have hr := resolveReport2Costed_cost_le thingNames x y
                  (fun _ => Complexity.Costed.pure fallback)
                  (fun xIdx yIdx => subsetRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
                  (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                    dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                    omega) (by
                    intro xIdx yIdx
                    have hc := subsetRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w fallback
                    dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                      externallyDependentWitnessCostBound] at hc ⊢
                    ring_nf at hc ⊢
                    omega)
                dsimp only [fallback] at hr
                simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                omega
              · by_cases hf5 : field = "ProperSubsetOf"
                · subst field
                  have hr := resolveReport2Costed_cost_le thingNames x y
                    (fun _ => Complexity.Costed.pure fallback)
                    (fun xIdx yIdx => properSubsetRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
                    (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                      dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                      omega) (by
                      intro xIdx yIdx
                      have hc := properSubsetRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w
                      dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                        externallyDependentWitnessCostBound] at hc ⊢
                      ring_nf at hc ⊢
                      omega)
                  dsimp only [fallback] at hr
                  simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                  omega
                · by_cases hf6 : field = "ProperSub"
                  · subst field
                    have hr := resolveReport2Costed_cost_le thingNames x y
                      (fun _ => Complexity.Costed.pure fallback)
                      (fun xIdx yIdx => properSubRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
                      (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                        dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                        omega) (by
                        intro xIdx yIdx
                        have hc := properSubRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w
                        dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                          externallyDependentWitnessCostBound] at hc ⊢
                        ring_nf at hc ⊢
                        omega)
                    dsimp only [fallback] at hr
                    simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                    omega
                  · by_cases hf7 : field = "GenericFunctionalDependence"
                    · subst field
                      have hr := resolveReport2Costed_cost_le thingNames x y
                        (fun _ => Complexity.Costed.pure fallback)
                        (fun xIdx yIdx => genericFunctionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
                        (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                          dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                          omega) (by
                          intro xIdx yIdx
                          have hc := genericFunctionalDependenceRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w fallback
                          dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                            externallyDependentWitnessCostBound] at hc ⊢
                          ring_nf at hc ⊢
                          omega)
                      dsimp only [fallback] at hr
                      simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                      omega
                    · by_cases hf8 : field = "GenericConstitutionalDependence"
                      · subst field
                        have hr := resolveReport2Costed_cost_le thingNames x y
                          (fun _ => Complexity.Costed.pure fallback)
                          (fun xIdx yIdx => genericConstitutionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
                          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                            omega) (by
                            intro xIdx yIdx
                            have hc := genericConstitutionalDependenceRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w fallback
                            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                              externallyDependentWitnessCostBound] at hc ⊢
                            ring_nf at hc ⊢
                            omega)
                        dsimp only [fallback] at hr
                        simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                        omega
                      · by_cases hf9 : field = "Categorizes"
                        · subst field
                          have hr := resolveReport2Costed_cost_le thingNames x y
                            (fun _ => Complexity.Costed.pure fallback)
                            (fun xIdx yIdx => categorizesRequiredMissingCosted worldNames thingNames tables xIdx yIdx w fallback)
                            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                              omega) (by
                              intro xIdx yIdx
                              have hc := categorizesRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w fallback
                              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                                externallyDependentWitnessCostBound] at hc ⊢
                              ring_nf at hc ⊢
                              omega)
                          dsimp only [fallback] at hr
                          simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                          omega
                        · by_cases hf10 : field = "IsDisjointWith"
                          · subst field
                            have hr := resolveReport2Costed_cost_le thingNames x y
                              (fun _ => Complexity.Costed.pure fallback)
                              (fun xIdx yIdx => disjointTypesRequiredMissingCosted worldNames thingNames tables xIdx yIdx w)
                              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                                omega) (by
                                intro xIdx yIdx
                                have hc := disjointTypesRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx w
                                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                                  externallyDependentWitnessCostBound] at hc ⊢
                                ring_nf at hc ⊢
                                omega)
                            dsimp only [fallback] at hr
                            simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
                            omega
                          · simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
                            omega
  | ternary field x y z =>
      by_cases hf0 : field = "IsCompletelyCoveredBy"
      · subst field
        have hr := resolveReport3Costed_cost_le thingNames x y z
          (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx yIdx zIdx => completeCoverageRequiredMissingCosted worldNames thingNames tables xIdx yIdx zIdx w fallback)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx yIdx zIdx
            have hc := completeCoverageRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx zIdx w fallback
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        dsimp only [fallback] at hr
        simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "IsPartitionedInto"
        · subst field
          have hr := resolveReport3Costed_cost_le thingNames x y z
            (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx yIdx zIdx => partitionRequiredMissingCosted worldNames thingNames tables xIdx yIdx zIdx w fallback)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx yIdx zIdx
              have hc := partitionRequiredMissingCosted_cost_le worldNames thingNames tables xIdx yIdx zIdx w fallback
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          dsimp only [fallback] at hr
          simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
          omega
        · simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost, hf0, hf1]
          omega
  | quaternary field x y z u =>
      by_cases hf0 : field = "IndividualFunctionalDependence"
      · subst field
        have hr := resolveReport4Costed_cost_le thingNames x y z u
          (fun _ => Complexity.Costed.pure fallback)
          (fun xIdx xTypeIdx yIdx yTypeIdx => individualFunctionalDependenceRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx xTypeIdx yIdx yTypeIdx
            have hc := individualFunctionalDependenceRequiredMissingCosted_cost_le worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        dsimp only [fallback] at hr
        simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "ComponentOf"
        · subst field
          have hr := resolveReport4Costed_cost_le thingNames x y z u
            (fun _ => Complexity.Costed.pure fallback)
            (fun xIdx xTypeIdx yIdx yTypeIdx => componentOfRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx xTypeIdx yIdx yTypeIdx
              have hc := componentOfRequiredMissingCosted_cost_le worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          dsimp only [fallback] at hr
          simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
          omega
        · by_cases hf2 : field = "Constitution"
          · subst field
            have hr := resolveReport4Costed_cost_le thingNames x y z u
              (fun _ => Complexity.Costed.pure fallback)
              (fun xIdx xTypeIdx yIdx yTypeIdx => constitutionRequiredMissingCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                omega) (by
                intro xIdx xTypeIdx yIdx yTypeIdx
                have hc := constitutionRequiredMissingCosted_cost_le worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                  externallyDependentWitnessCostBound] at hc ⊢
                ring_nf at hc ⊢
                omega)
            dsimp only [fallback] at hr
            simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
            omega
          · simp [derivedAssertionRequiredMissingCosted, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost, hf0, hf1, hf2]
            omega

/-- Resolution costs at most 36T+4, and arity plus field selection costs
at most 23. The component bound includes the empty-array fallback. -/
private theorem derivedAssertionEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (derivedAssertionEvidenceCosted worldNames thingNames tables fact w).cost ≤
      derivedReportComponentCostBound worldNames.size thingNames.size tables + 36 * thingNames.size + 27 := by
  cases fact with
  | unary field x =>
      by_cases hf0 : field = "Quality"
      · subst field
        have hr := resolveReport1Costed_cost_le thingNames x
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx => qualityEvidenceCosted worldNames.size thingNames tables xIdx w)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx
            have hc := qualityEvidenceCosted_cost_le worldNames.size thingNames tables xIdx w
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "ExternallyDependentMode"
        · subst field
          have hr := resolveReport1Costed_cost_le thingNames x
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx => externalModeEvidenceCosted worldNames thingNames tables xIdx w)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx
              have hc := externalModeEvidenceCosted_cost_le worldNames thingNames tables xIdx w
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
          omega
        · by_cases hf2 : field = "NonEmptySet"
          · subst field
            have hr := resolveReport1Costed_cost_le thingNames x
              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx => nonEmptySetEvidenceCosted worldNames thingNames tables xIdx w)
              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                omega) (by
                intro xIdx
                have hc := nonEmptySetEvidenceCosted_cost_le worldNames thingNames tables xIdx w
                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                  externallyDependentWitnessCostBound] at hc ⊢
                ring_nf at hc ⊢
                omega)
            simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
            omega
          · by_cases hf3 : field = "QualityStructure"
            · subst field
              have hr := resolveReport1Costed_cost_le thingNames x
                (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                (fun xIdx => qualityStructureEvidenceCosted worldNames thingNames tables xIdx w)
                (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                  dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                  omega) (by
                  intro xIdx
                  have hc := qualityStructureEvidenceCosted_cost_le worldNames thingNames tables xIdx w
                  dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                    externallyDependentWitnessCostBound] at hc ⊢
                  ring_nf at hc ⊢
                  omega)
              simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
              omega
            · by_cases hf4 : field = "SimpleQuality"
              · subst field
                have hr := resolveReport1Costed_cost_le thingNames x
                  (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                  (fun xIdx => simpleQualityEvidenceCosted worldNames thingNames tables xIdx w)
                  (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                    dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                    omega) (by
                    intro xIdx
                    have hc := simpleQualityEvidenceCosted_cost_le worldNames thingNames tables xIdx w
                    dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                      externallyDependentWitnessCostBound] at hc ⊢
                    ring_nf at hc ⊢
                    omega)
                simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                omega
              · by_cases hf5 : field = "ComplexQuality"
                · subst field
                  have hr := resolveReport1Costed_cost_le thingNames x
                    (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                    (fun xIdx => complexQualityEvidenceCosted worldNames thingNames tables xIdx w)
                    (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                      dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                      omega) (by
                      intro xIdx
                      have hc := complexQualityEvidenceCosted_cost_le worldNames thingNames tables xIdx w
                      dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                        externallyDependentWitnessCostBound] at hc ⊢
                      ring_nf at hc ⊢
                      omega)
                  simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                  omega
                · by_cases hf6 : field = "SimpleQualityType"
                  · subst field
                    have hr := resolveReport1Costed_cost_le thingNames x
                      (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                      (fun xIdx => simpleQualityTypeEvidenceCosted worldNames thingNames tables xIdx w)
                      (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                        dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                        omega) (by
                        intro xIdx
                        have hc := simpleQualityTypeEvidenceCosted_cost_le worldNames thingNames tables xIdx w
                        dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                          externallyDependentWitnessCostBound] at hc ⊢
                        ring_nf at hc ⊢
                        omega)
                    simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                    omega
                  · by_cases hf7 : field = "ComplexQualityType"
                    · subst field
                      have hr := resolveReport1Costed_cost_le thingNames x
                        (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                        (fun xIdx => complexQualityTypeEvidenceCosted worldNames thingNames tables xIdx w)
                        (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                          dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                          omega) (by
                          intro xIdx
                          have hc := complexQualityTypeEvidenceCosted_cost_le worldNames thingNames tables xIdx w
                          dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                            externallyDependentWitnessCostBound] at hc ⊢
                          ring_nf at hc ⊢
                          omega)
                      simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                      omega
                    · by_cases hf8 : field = "QuaIndividual"
                      · subst field
                        have hr := resolveReport1Costed_cost_le thingNames x
                          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                          (fun xIdx => quaIndividualEvidenceCosted worldNames.size thingNames tables xIdx w)
                          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                            omega) (by
                            intro xIdx
                            have hc := quaIndividualEvidenceCosted_cost_le worldNames.size thingNames tables xIdx w
                            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                              externallyDependentWitnessCostBound] at hc ⊢
                            ring_nf at hc ⊢
                            omega)
                        simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                        omega
                      · simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
  | binary field x y =>
      by_cases hf0 : field = "ExternallyDependent"
      · subst field
        have hr := resolveReport2Costed_cost_le thingNames x y
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx yIdx => externallyDependentEvidenceCosted worldNames thingNames tables xIdx yIdx w)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx yIdx
            have hc := externallyDependentEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "ExistentialDependence"
        · subst field
          have hr := resolveReport2Costed_cost_le thingNames x y
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx yIdx => existentialDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx yIdx
              have hc := existentialDependenceEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
          omega
        · by_cases hf2 : field = "UltimateBearerOf"
          · subst field
            have hr := resolveReport2Costed_cost_le thingNames x y
              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx yIdx => ultimateBearerEvidenceCosted worldNames thingNames tables xIdx yIdx w)
              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                omega) (by
                intro xIdx yIdx
                have hc := ultimateBearerEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                  externallyDependentWitnessCostBound] at hc ⊢
                ring_nf at hc ⊢
                omega)
            simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
            omega
          · by_cases hf3 : field = "ExistentialIndependence"
            · subst field
              have hr := resolveReport2Costed_cost_le thingNames x y
                (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                (fun xIdx yIdx => existentialIndependenceEvidenceCosted worldNames thingNames tables xIdx yIdx)
                (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                  dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                  omega) (by
                  intro xIdx yIdx
                  have hc := existentialIndependenceEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx
                  dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                    externallyDependentWitnessCostBound] at hc ⊢
                  ring_nf at hc ⊢
                  omega)
              simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
              omega
            · by_cases hf4 : field = "IsDisjointWith"
              · subst field
                have hr := resolveReport2Costed_cost_le thingNames x y
                  (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                  (fun xIdx yIdx => disjointTypesEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                  (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                    dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                    omega) (by
                    intro xIdx yIdx
                    have hc := disjointTypesEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                    dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                      externallyDependentWitnessCostBound] at hc ⊢
                    ring_nf at hc ⊢
                    omega)
                simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                omega
              · by_cases hf5 : field = "SubsetOf"
                · subst field
                  have hr := resolveReport2Costed_cost_le thingNames x y
                    (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                    (fun xIdx yIdx => subsetEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                    (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                      dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                      omega) (by
                      intro xIdx yIdx
                      have hc := subsetEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                      dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                        externallyDependentWitnessCostBound] at hc ⊢
                      ring_nf at hc ⊢
                      omega)
                  simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                  omega
                · by_cases hf6 : field = "ProperSubsetOf"
                  · subst field
                    have hr := resolveReport2Costed_cost_le thingNames x y
                      (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                      (fun xIdx yIdx => properSubsetEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                      (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                        dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                        omega) (by
                        intro xIdx yIdx
                        have hc := properSubsetEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                        dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                          externallyDependentWitnessCostBound] at hc ⊢
                        ring_nf at hc ⊢
                        omega)
                    simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                    omega
                  · by_cases hf7 : field = "ProperSub"
                    · subst field
                      have hr := resolveReport2Costed_cost_le thingNames x y
                        (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                        (fun xIdx yIdx => properSubEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                        (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                          dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                          omega) (by
                          intro xIdx yIdx
                          have hc := properSubEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                          dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                            externallyDependentWitnessCostBound] at hc ⊢
                          ring_nf at hc ⊢
                          omega)
                      simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                      omega
                    · by_cases hf8 : field = "GenericFunctionalDependence"
                      · subst field
                        have hr := resolveReport2Costed_cost_le thingNames x y
                          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                          (fun xIdx yIdx => genericFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                            omega) (by
                            intro xIdx yIdx
                            have hc := genericFunctionalDependenceEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                              externallyDependentWitnessCostBound] at hc ⊢
                            ring_nf at hc ⊢
                            omega)
                        simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                        omega
                      · by_cases hf9 : field = "GenericConstitutionalDependence"
                        · subst field
                          have hr := resolveReport2Costed_cost_le thingNames x y
                            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                            (fun xIdx yIdx => genericConstitutionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                              omega) (by
                              intro xIdx yIdx
                              have hc := genericConstitutionalDependenceEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                                externallyDependentWitnessCostBound] at hc ⊢
                              ring_nf at hc ⊢
                              omega)
                          simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                          omega
                        · by_cases hf10 : field = "Categorizes"
                          · subst field
                            have hr := resolveReport2Costed_cost_le thingNames x y
                              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                              (fun xIdx yIdx => categorizesEvidenceCosted worldNames thingNames tables xIdx yIdx w)
                              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                                omega) (by
                                intro xIdx yIdx
                                have hc := categorizesEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx w
                                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                                  externallyDependentWitnessCostBound] at hc ⊢
                                ring_nf at hc ⊢
                                omega)
                            simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
                            omega
                          · simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
  | ternary field x y z =>
      by_cases hf0 : field = "IsCompletelyCoveredBy"
      · subst field
        have hr := resolveReport3Costed_cost_le thingNames x y z
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx yIdx zIdx => completeCoverageEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx yIdx zIdx
            have hc := completeCoverageEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx zIdx w
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "IsPartitionedInto"
        · subst field
          have hr := resolveReport3Costed_cost_le thingNames x y z
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx yIdx zIdx => partitionEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx yIdx zIdx
              have hc := partitionEvidenceCosted_cost_le worldNames thingNames tables xIdx yIdx zIdx w
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
          omega
        · simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost, hf0, hf1]
  | quaternary field x y z u =>
      by_cases hf0 : field = "IndividualFunctionalDependence"
      · subst field
        have hr := resolveReport4Costed_cost_le thingNames x y z u
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx xTypeIdx yIdx yTypeIdx => individualFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
          (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
            dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
            omega) (by
            intro xIdx xTypeIdx yIdx yTypeIdx
            have hc := individualFunctionalDependenceEvidenceCosted_cost_le worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
            dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
              externallyDependentWitnessCostBound] at hc ⊢
            ring_nf at hc ⊢
            omega)
        simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
        omega
      · by_cases hf1 : field = "ComponentOf"
        · subst field
          have hr := resolveReport4Costed_cost_le thingNames x y z u
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx xTypeIdx yIdx yTypeIdx => componentOfEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
            (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
              dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
              omega) (by
              intro xIdx xTypeIdx yIdx yTypeIdx
              have hc := componentOfEvidenceCosted_cost_le worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
              dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                externallyDependentWitnessCostBound] at hc ⊢
              ring_nf at hc ⊢
              omega)
          simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
          omega
        · by_cases hf2 : field = "Constitution"
          · subst field
            have hr := resolveReport4Costed_cost_le thingNames x y z u
              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx xTypeIdx yIdx yTypeIdx => constitutionEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w)
              (derivedReportComponentCostBound worldNames.size thingNames.size tables) (by
                dsimp only [Complexity.Costed.tick, Complexity.Costed.pure, derivedReportComponentCostBound]
                omega) (by
                intro xIdx xTypeIdx yIdx yTypeIdx
                have hc := constitutionEvidenceCosted_cost_le worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
                dsimp only [derivedReportComponentCostBound, externallyDependentModeStatusCostBound,
                  externallyDependentWitnessCostBound] at hc ⊢
                ring_nf at hc ⊢
                omega)
            simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost]
            omega
          · simp [derivedAssertionEvidenceCosted, Complexity.Costed.charge_cost, hf0, hf1, hf2]

private theorem derivedAssertionEvidenceCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (derivedAssertionEvidenceCosted worldNames thingNames tables fact w).value.size ≤ 5 := by
  cases fact with
  | unary field x =>
      by_cases hf0 : field = "Quality"
      · subst field
        have hr := resolveReport1Costed_size_le thingNames x
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx => qualityEvidenceCosted worldNames.size thingNames tables xIdx w) 5 (by decide) (by
            intro xIdx
            have h := qualityEvidenceCosted_size worldNames.size thingNames tables xIdx w
            omega)
        simpa [derivedAssertionEvidenceCosted] using hr
      · by_cases hf1 : field = "ExternallyDependentMode"
        · subst field
          have hr := resolveReport1Costed_size_le thingNames x
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx => externalModeEvidenceCosted worldNames thingNames tables xIdx w) 5 (by decide) (by
              intro xIdx
              have h := externalModeEvidenceCosted_size_le worldNames thingNames tables xIdx w
              omega)
          simpa [derivedAssertionEvidenceCosted] using hr
        · by_cases hf2 : field = "NonEmptySet"
          · subst field
            have hr := resolveReport1Costed_size_le thingNames x
              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx => nonEmptySetEvidenceCosted worldNames thingNames tables xIdx w) 5 (by decide) (by
                intro xIdx
                have h := nonEmptySetEvidenceCosted_size worldNames thingNames tables xIdx w
                omega)
            simpa [derivedAssertionEvidenceCosted] using hr
          · by_cases hf3 : field = "QualityStructure"
            · subst field
              have hr := resolveReport1Costed_size_le thingNames x
                (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                (fun xIdx => qualityStructureEvidenceCosted worldNames thingNames tables xIdx w) 5 (by decide) (by
                  intro xIdx
                  have h := qualityStructureEvidenceCosted_size worldNames thingNames tables xIdx w
                  omega)
              simpa [derivedAssertionEvidenceCosted] using hr
            · by_cases hf4 : field = "SimpleQuality"
              · subst field
                have hr := resolveReport1Costed_size_le thingNames x
                  (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                  (fun xIdx => simpleQualityEvidenceCosted worldNames thingNames tables xIdx w) 5 (by decide) (by
                    intro xIdx
                    have h := simpleQualityEvidenceCosted_size worldNames thingNames tables xIdx w
                    omega)
                simpa [derivedAssertionEvidenceCosted] using hr
              · by_cases hf5 : field = "ComplexQuality"
                · subst field
                  have hr := resolveReport1Costed_size_le thingNames x
                    (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                    (fun xIdx => complexQualityEvidenceCosted worldNames thingNames tables xIdx w) 5 (by decide) (by
                      intro xIdx
                      have h := complexQualityEvidenceCosted_size worldNames thingNames tables xIdx w
                      omega)
                  simpa [derivedAssertionEvidenceCosted] using hr
                · by_cases hf6 : field = "SimpleQualityType"
                  · subst field
                    have hr := resolveReport1Costed_size_le thingNames x
                      (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                      (fun xIdx => simpleQualityTypeEvidenceCosted worldNames thingNames tables xIdx w) 5 (by decide) (by
                        intro xIdx
                        have h := simpleQualityTypeEvidenceCosted_size_le worldNames thingNames tables xIdx w
                        omega)
                    simpa [derivedAssertionEvidenceCosted] using hr
                  · by_cases hf7 : field = "ComplexQualityType"
                    · subst field
                      have hr := resolveReport1Costed_size_le thingNames x
                        (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                        (fun xIdx => complexQualityTypeEvidenceCosted worldNames thingNames tables xIdx w) 5 (by decide) (by
                          intro xIdx
                          have h := complexQualityTypeEvidenceCosted_size_le worldNames thingNames tables xIdx w
                          omega)
                      simpa [derivedAssertionEvidenceCosted] using hr
                    · by_cases hf8 : field = "QuaIndividual"
                      · subst field
                        have hr := resolveReport1Costed_size_le thingNames x
                          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                          (fun xIdx => quaIndividualEvidenceCosted worldNames.size thingNames tables xIdx w) 5 (by decide) (by
                            intro xIdx
                            have h := quaIndividualEvidenceCosted_size worldNames.size thingNames tables xIdx w
                            omega)
                        simpa [derivedAssertionEvidenceCosted] using hr
                      · simp [derivedAssertionEvidenceCosted, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
  | binary field x y =>
      by_cases hf0 : field = "ExternallyDependent"
      · subst field
        have hr := resolveReport2Costed_size_le thingNames x y
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx yIdx => externallyDependentEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
            intro xIdx yIdx
            have h := externallyDependentEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
            omega)
        simpa [derivedAssertionEvidenceCosted] using hr
      · by_cases hf1 : field = "ExistentialDependence"
        · subst field
          have hr := resolveReport2Costed_size_le thingNames x y
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx yIdx => existentialDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx) 5 (by decide) (by
              intro xIdx yIdx
              have h := existentialDependenceEvidenceCosted_size worldNames thingNames tables xIdx yIdx
              omega)
          simpa [derivedAssertionEvidenceCosted] using hr
        · by_cases hf2 : field = "UltimateBearerOf"
          · subst field
            have hr := resolveReport2Costed_size_le thingNames x y
              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx yIdx => ultimateBearerEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                intro xIdx yIdx
                have h := ultimateBearerEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
                omega)
            simpa [derivedAssertionEvidenceCosted] using hr
          · by_cases hf3 : field = "ExistentialIndependence"
            · subst field
              have hr := resolveReport2Costed_size_le thingNames x y
                (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                (fun xIdx yIdx => existentialIndependenceEvidenceCosted worldNames thingNames tables xIdx yIdx) 5 (by decide) (by
                  intro xIdx yIdx
                  have h := existentialIndependenceEvidenceCosted_size worldNames thingNames tables xIdx yIdx
                  omega)
              simpa [derivedAssertionEvidenceCosted] using hr
            · by_cases hf4 : field = "IsDisjointWith"
              · subst field
                have hr := resolveReport2Costed_size_le thingNames x y
                  (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                  (fun xIdx yIdx => disjointTypesEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                    intro xIdx yIdx
                    have h := disjointTypesEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
                    omega)
                simpa [derivedAssertionEvidenceCosted] using hr
              · by_cases hf5 : field = "SubsetOf"
                · subst field
                  have hr := resolveReport2Costed_size_le thingNames x y
                    (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                    (fun xIdx yIdx => subsetEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                      intro xIdx yIdx
                      have h := subsetEvidenceCosted_size_le worldNames thingNames tables xIdx yIdx w
                      omega)
                  simpa [derivedAssertionEvidenceCosted] using hr
                · by_cases hf6 : field = "ProperSubsetOf"
                  · subst field
                    have hr := resolveReport2Costed_size_le thingNames x y
                      (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                      (fun xIdx yIdx => properSubsetEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                        intro xIdx yIdx
                        have h := properSubsetEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
                        omega)
                    simpa [derivedAssertionEvidenceCosted] using hr
                  · by_cases hf7 : field = "ProperSub"
                    · subst field
                      have hr := resolveReport2Costed_size_le thingNames x y
                        (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                        (fun xIdx yIdx => properSubEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                          intro xIdx yIdx
                          have h := properSubEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
                          omega)
                      simpa [derivedAssertionEvidenceCosted] using hr
                    · by_cases hf8 : field = "GenericFunctionalDependence"
                      · subst field
                        have hr := resolveReport2Costed_size_le thingNames x y
                          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                          (fun xIdx yIdx => genericFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                            intro xIdx yIdx
                            have h := genericFunctionalDependenceEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
                            omega)
                        simpa [derivedAssertionEvidenceCosted] using hr
                      · by_cases hf9 : field = "GenericConstitutionalDependence"
                        · subst field
                          have hr := resolveReport2Costed_size_le thingNames x y
                            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                            (fun xIdx yIdx => genericConstitutionalDependenceEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                              intro xIdx yIdx
                              have h := genericConstitutionalDependenceEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
                              omega)
                          simpa [derivedAssertionEvidenceCosted] using hr
                        · by_cases hf10 : field = "Categorizes"
                          · subst field
                            have hr := resolveReport2Costed_size_le thingNames x y
                              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
                              (fun xIdx yIdx => categorizesEvidenceCosted worldNames thingNames tables xIdx yIdx w) 5 (by decide) (by
                                intro xIdx yIdx
                                have h := categorizesEvidenceCosted_size worldNames thingNames tables xIdx yIdx w
                                omega)
                            simpa [derivedAssertionEvidenceCosted] using hr
                          · simp [derivedAssertionEvidenceCosted, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
  | ternary field x y z =>
      by_cases hf0 : field = "IsCompletelyCoveredBy"
      · subst field
        have hr := resolveReport3Costed_size_le thingNames x y z
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx yIdx zIdx => completeCoverageEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w) 5 (by decide) (by
            intro xIdx yIdx zIdx
            have h := completeCoverageEvidenceCosted_size worldNames thingNames tables xIdx yIdx zIdx w
            omega)
        simpa [derivedAssertionEvidenceCosted] using hr
      · by_cases hf1 : field = "IsPartitionedInto"
        · subst field
          have hr := resolveReport3Costed_size_le thingNames x y z
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx yIdx zIdx => partitionEvidenceCosted worldNames thingNames tables xIdx yIdx zIdx w) 5 (by decide) (by
              intro xIdx yIdx zIdx
              have h := partitionEvidenceCosted_size worldNames thingNames tables xIdx yIdx zIdx w
              omega)
          simpa [derivedAssertionEvidenceCosted] using hr
        · simp [derivedAssertionEvidenceCosted, hf0, hf1]
  | quaternary field x y z u =>
      by_cases hf0 : field = "IndividualFunctionalDependence"
      · subst field
        have hr := resolveReport4Costed_size_le thingNames x y z u
          (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
          (fun xIdx xTypeIdx yIdx yTypeIdx => individualFunctionalDependenceEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w) 5 (by decide) (by
            intro xIdx xTypeIdx yIdx yTypeIdx
            have h := individualFunctionalDependenceEvidenceCosted_size worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
            omega)
        simpa [derivedAssertionEvidenceCosted] using hr
      · by_cases hf1 : field = "ComponentOf"
        · subst field
          have hr := resolveReport4Costed_size_le thingNames x y z u
            (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
            (fun xIdx xTypeIdx yIdx yTypeIdx => componentOfEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w) 5 (by decide) (by
              intro xIdx xTypeIdx yIdx yTypeIdx
              have h := componentOfEvidenceCosted_size worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
              omega)
          simpa [derivedAssertionEvidenceCosted] using hr
        · by_cases hf2 : field = "Constitution"
          · subst field
            have hr := resolveReport4Costed_size_le thingNames x y z u
              (fun _ => Complexity.Costed.tick (#[] : Array String) 1)
              (fun xIdx xTypeIdx yIdx yTypeIdx => constitutionEvidenceCosted worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w) 5 (by decide) (by
                intro xIdx xTypeIdx yIdx yTypeIdx
                have h := constitutionEvidenceCosted_size worldNames thingNames tables xIdx xTypeIdx yIdx yTypeIdx w
                omega)
            simpa [derivedAssertionEvidenceCosted] using hr
          · simp [derivedAssertionEvidenceCosted, hf0, hf1, hf2]

/-- An unknown assertion needs two explanatory rows and no model search.
The relation summary costs at most ten, its two text appends cost two, and
array initialization plus two writes/emissions cost five. -/
private def unreconstructedDerivedReportCosted (fact : NamedDerivedFact) :
    Complexity.Costed (Array String) := do
  let text := Complexity.Costed.pure "Could not reconstruct the asserted derived relation `"
  let text := text.appendString (namedDerivedFactSummaryCosted fact)
  let text ← text.appendString (.pure "` at the DSL level.")
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push text) 2
  Complexity.Costed.tick (out.push
    "Suggestion: check that all mentioned things are declared and that the relation has a registered diagnostic evaluator.") 2

private theorem unreconstructedDerivedReportCosted_value (fact : NamedDerivedFact) :
    (unreconstructedDerivedReportCosted fact).value =
      #[s!"Could not reconstruct the asserted derived relation `{namedDerivedFactSummary fact}` at the DSL level.",
        "Suggestion: check that all mentioned things are declared and that the relation has a registered diagnostic evaluator."] := by
  simp only [unreconstructedDerivedReportCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    Complexity.Costed.tick_value, namedDerivedFactSummary]
  rfl

private theorem unreconstructedDerivedReportCosted_cost_le (fact : NamedDerivedFact) :
    (unreconstructedDerivedReportCosted fact).cost ≤ 17 := by
  have h := namedDerivedFactSummaryCosted_cost_le fact
  simp only [unreconstructedDerivedReportCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
    Complexity.Costed.tick_cost]
  omega

private theorem unreconstructedDerivedReportCosted_size (fact : NamedDerivedFact) :
    (unreconstructedDerivedReportCosted fact).value.size = 2 := by
  rw [unreconstructedDerivedReportCosted_value]
  rfl

private def renderDerivedAssertionFailureSpec
    (worldNames thingNames : Array Name) (tables : FactTables)
    (failure : FailedDerivedAssertion) : Array String :=
  let fact := failure.fact
  let scope := failure.scope
  let w := failure.world
  if failure.reconstructed then
    #[
      s!"Counterexample assignment: w = {indexedName worldNames w}.",
      s!"Required but missing: {derivedAssertionRequiredMissingSpec worldNames thingNames tables fact w}",
      s!"Suggestion: {(derivedAssertionSuggestionCosted fact).value}",
      s!"Evidence: the assertion was written at `{namedScopeSummary scope}` and expands to world `{indexedName worldNames w}`."
    ] ++ derivedAssertionEvidenceSpec worldNames thingNames tables fact w
  else
    (unreconstructedDerivedReportCosted fact).value

/-- Construct the shared four-row preamble and append the selected evidence.
The world name is rendered once and reused. Every report component contributes
its executed cost, including fallback construction and any separate witness
searches. Output limiting happens afterwards and does not erase these costs. -/
private def renderDerivedAssertionFailureCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (failure : FailedDerivedAssertion) : Complexity.Costed (Array String) :=
  Complexity.Costed.charge 1 <| if failure.reconstructed then do
    let wn ← indexedNameCosted worldNames failure.world
    let assignment ← ((Complexity.Costed.pure "Counterexample assignment: w = ").appendString
      (.pure wn)).appendString (.pure ".")
    let missing ← (Complexity.Costed.pure "Required but missing: ").appendString
      (derivedAssertionRequiredMissingCosted worldNames thingNames tables failure.fact failure.world)
    let suggestion ← (Complexity.Costed.pure "Suggestion: ").appendString
      (derivedAssertionSuggestionCosted failure.fact)
    let scope ← namedScopeSummaryCosted failure.scope
    let header ← (((Complexity.Costed.pure "Evidence: the assertion was written at `").appendString
      (.pure scope)).appendString (.pure "` and expands to world `")).appendString
      (.pure wn) >>= fun text => (Complexity.Costed.pure text).appendString (.pure "`.")
    let out ← Complexity.Costed.tick (#[] : Array String) 1
    let out ← Complexity.Costed.tick (out.push assignment) 2
    let out ← Complexity.Costed.tick (out.push missing) 2
    let out ← Complexity.Costed.tick (out.push suggestion) 2
    let out ← Complexity.Costed.tick (out.push header) 2
    let evidence ← derivedAssertionEvidenceCosted worldNames thingNames tables failure.fact failure.world
    Complexity.Costed.appendArray out evidence
  else
    unreconstructedDerivedReportCosted failure.fact

private theorem renderDerivedAssertionFailureCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (failure : FailedDerivedAssertion) :
    (renderDerivedAssertionFailureCosted worldNames thingNames tables failure).value =
      renderDerivedAssertionFailureSpec worldNames thingNames tables failure := by
  cases hr : failure.reconstructed <;>
    simp [renderDerivedAssertionFailureCosted, renderDerivedAssertionFailureSpec, hr,
      Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.appendString_value,
      Complexity.Costed.appendArray_value, derivedAssertionRequiredMissingCosted_value,
      derivedAssertionEvidenceCosted_value,
      indexedNameCosted_value]
  all_goals rfl

/-- Four common rows plus at most five evidence rows. An unreconstructible
assertion has only two rows. This bound also covers unsupported fields and
out-of-range diagnostic coordinates. -/
private theorem renderDerivedAssertionFailureCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (failure : FailedDerivedAssertion) :
    (renderDerivedAssertionFailureCosted worldNames thingNames tables failure).value.size ≤ 9 := by
  have he := derivedAssertionEvidenceCosted_size_le
    worldNames thingNames tables failure.fact failure.world
  have hu := unreconstructedDerivedReportCosted_size failure.fact
  rw [renderDerivedAssertionFailureCosted_value]
  unfold renderDerivedAssertionFailureSpec
  split
  · rw [Array.size_append, ← derivedAssertionEvidenceCosted_value]
    change 4 + (derivedAssertionEvidenceCosted worldNames thingNames tables failure.fact failure.world).value.size ≤ 9
    omega
  · change (unreconstructedDerivedReportCosted failure.fact).value.size ≤ 9
    omega

/-- Whole-report bound in the primitive-call model. The two dispatchers add
72T+72 beyond their component bounds. Common text and suggestion selection
add at most 46, and copying at most five evidence rows adds 15. -/
def derivedAssertionReportCostBound (W T : Nat) (tables : FactTables) : Nat :=
  2 * derivedReportComponentCostBound W T tables + 72 * T + 133

private theorem renderDerivedAssertionFailureCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (failure : FailedDerivedAssertion) :
    (renderDerivedAssertionFailureCosted worldNames thingNames tables failure).cost ≤
      derivedAssertionReportCostBound worldNames.size thingNames.size tables := by
  have hm := derivedAssertionRequiredMissingCosted_cost_le
    worldNames thingNames tables failure.fact failure.world
  have he := derivedAssertionEvidenceCosted_cost_le
    worldNames thingNames tables failure.fact failure.world
  have hz := derivedAssertionEvidenceCosted_size_le
    worldNames thingNames tables failure.fact failure.world
  have hs := derivedAssertionSuggestionCosted_cost_le failure.fact
  have hu := unreconstructedDerivedReportCosted_cost_le failure.fact
  unfold renderDerivedAssertionFailureCosted
  rw [Complexity.Costed.charge_cost]
  unfold derivedAssertionReportCostBound
  split
  · simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.bind_value,
      Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
      Complexity.Costed.tick_cost, Complexity.Costed.tick_value,
      Complexity.Costed.appendArray_cost, indexedNameCosted_cost, namedScopeSummaryCosted_cost]
    omega
  · omega

/-!
## Public producers and complete bounds

The public functions compose selection, report construction, and output
limiting. Their ordinary results are projections of the counted execution.
The final bounds include all three stages, not just the selected predicate.
-/

/-- Select the first failed assertion, construct its report, and retain an
ordered prefix. Construction is charged even at budget zero. The prefix copy
adds four operations per retained row and four fixed operations. This is the
same output-boundary policy as specialized axiom diagnostics. -/
def derivedAssertionFailureBudgetedCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    Complexity.Costed (Option (Array String)) := do
  let failure ← firstDerivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables
  Complexity.Costed.charge 1 <| match failure with
  | none => .pure none
  | some failure => do
    let generated ← renderDerivedAssertionFailureCosted worldNames thingNames tables failure
    let kept ← Complexity.boundedEvidenceCosted budget generated
    .pure (some kept.items)

private theorem derivedAssertionFailureBudgetedCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionFailureBudgetedCosted budget worldNames thingNames namedFacts scopedFacts tables).value =
      (firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables).map
        (fun failure => (renderDerivedAssertionFailureSpec worldNames thingNames tables failure).extract 0 budget) := by
  simp only [derivedAssertionFailureBudgetedCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, firstDerivedAssertionFailureCosted_value]
  cases (firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables)
  all_goals simp [Complexity.Costed.bind_value, renderDerivedAssertionFailureCosted_value,
    Complexity.boundedEvidence_eq_prefix]

/-- Output-sensitive bound for assertion selection and complete diagnostics.
F counts named source facts; W and T count worlds and things. Stored derived
propositions occur in the predicate and report bounds. E is the number of
emitted rows, not the number of rows constructed before truncation. -/
def derivedAssertionFailureCostBound (W T F E : Nat) (tables : FactTables) : Nat :=
  F * (10 + (W + 1) * (namedDerivedPredicateCostBound W T tables + 36 * T + 24)) +
    derivedAssertionReportCostBound W T tables + 4 * E + 5

theorem derivedAssertionFailureBudgetedCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionFailureBudgetedCosted budget worldNames thingNames namedFacts scopedFacts tables).cost ≤
      derivedAssertionFailureCostBound worldNames.size thingNames.size namedFacts.size
        ((derivedAssertionFailureBudgetedCosted budget worldNames thingNames namedFacts scopedFacts tables).value.getD #[]).size
        tables := by
  have hselect := firstDerivedAssertionFailureCosted_cost_le
    worldNames thingNames namedFacts scopedFacts tables
  unfold derivedAssertionFailureBudgetedCosted derivedAssertionFailureCostBound
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.bind_value,
    Complexity.Costed.charge_cost, Complexity.Costed.charge_value]
  cases (firstDerivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).value with
  | none =>
      simp only [Complexity.Costed.pure_cost, Complexity.Costed.pure_value, Option.getD_none]
      omega
  | some failure =>
      have hr := renderDerivedAssertionFailureCosted_cost_le worldNames thingNames tables failure
      simp only [Complexity.Costed.bind_cost, Complexity.Costed.bind_value,
        Complexity.Costed.pure_cost, Complexity.Costed.pure_value, Option.getD_some,
        Complexity.boundedEvidenceCosted_value, Complexity.boundedEvidenceCosted_cost_eq_emitted]
      omega

theorem derivedAssertionFailureBudgetedCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    ((derivedAssertionFailureBudgetedCosted budget worldNames thingNames namedFacts scopedFacts tables).value.getD #[]).size ≤
      budget := by
  rw [derivedAssertionFailureBudgetedCosted_value]
  cases (firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables)
  all_goals simp [Array.size_extract]

/-- Nine rows suffice for every existing derived-assertion report: four
common rows and at most five evidence rows. The default cap therefore preserves
the full report, including for malformed diagnostic inputs. -/
def derivedAssertionFailureCosted
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    Complexity.Costed (Option (Array String)) :=
  derivedAssertionFailureBudgetedCosted 9 worldNames thingNames namedFacts scopedFacts tables

private theorem derivedAssertionFailureCosted_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).value =
      (firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables).map
        (renderDerivedAssertionFailureSpec worldNames thingNames tables) := by
  unfold derivedAssertionFailureCosted
  rw [derivedAssertionFailureBudgetedCosted_value]
  cases (firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables) with
  | none => rfl
  | some failure =>
      simp only [Option.map_some]
      apply congrArg some
      have hsize := renderDerivedAssertionFailureCosted_size_le worldNames thingNames tables failure
      rw [renderDerivedAssertionFailureCosted_value] at hsize
      apply Array.ext
      · simp [Array.size_extract, Nat.min_eq_right hsize]
      · intro i hi hj
        simp

/-- The production precheck erases the cost from its counted selection,
complete report construction, and output cap. It does not run another checker
or formatter with an unproved implementation connection. -/
def derivedAssertionFailure?
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Option (Array String) :=
  (derivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).value

private theorem derivedAssertionFailure_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables =
      (firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables).map
        (renderDerivedAssertionFailureSpec worldNames thingNames tables) :=
  derivedAssertionFailureCosted_value worldNames thingNames namedFacts scopedFacts tables

theorem derivedAssertionFailureCosted_cost_le
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).cost ≤
      derivedAssertionFailureCostBound worldNames.size thingNames.size namedFacts.size
        ((derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables).getD #[]).size tables :=
  derivedAssertionFailureBudgetedCosted_cost_le 9 worldNames thingNames namedFacts scopedFacts tables

/-- The UI fallback is constructed only when no failing assertion was retained.
Its single row costs one initialization and two write/emission operations;
the option match costs one in either branch. -/
def derivedAssertionAnalysisCosted
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    Complexity.Costed (Array String) := do
  let failure ← derivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables
  Complexity.Costed.charge 1 <| match failure with
  | some rows => .pure rows
  | none => .tick
      #["A user-written derived relation assertion failed, but the structured checker could not isolate a false asserted derived fact."] 3

def derivedAssertionAnalysis
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Array String :=
  (derivedAssertionAnalysisCosted worldNames thingNames namedFacts scopedFacts tables).value

theorem derivedAssertionAnalysisCosted_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionAnalysisCosted worldNames thingNames namedFacts scopedFacts tables).value =
      (derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables).getD
        #["A user-written derived relation assertion failed, but the structured checker could not isolate a false asserted derived fact."] := by
  unfold derivedAssertionAnalysisCosted derivedAssertionFailure?
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value]
  cases (derivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).value <;> rfl

theorem derivedAssertionAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionAnalysisCosted worldNames thingNames namedFacts scopedFacts tables).cost ≤
      (derivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).cost + 4 := by
  unfold derivedAssertionAnalysisCosted
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  cases (derivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).value
  all_goals dsimp only [Complexity.Costed.pure, Complexity.Costed.tick]
  all_goals omega

/-- Complete UI-analyzer bound, including its fallback. E counts the rows
returned to the caller; it is one when the UI fallback is used. -/
theorem derivedAssertionAnalysisCosted_cost_le_bound
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionAnalysisCosted worldNames thingNames namedFacts scopedFacts tables).cost ≤
      derivedAssertionFailureCostBound worldNames.size thingNames.size namedFacts.size
        (derivedAssertionAnalysis worldNames thingNames namedFacts scopedFacts tables).size tables + 4 := by
  have h0 := derivedAssertionAnalysisCosted_cost_le worldNames thingNames namedFacts scopedFacts tables
  have h1 := derivedAssertionFailureCosted_cost_le worldNames thingNames namedFacts scopedFacts tables
  have he :
      ((derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables).getD #[]).size ≤
        (derivedAssertionAnalysis worldNames thingNames namedFacts scopedFacts tables).size := by
    unfold derivedAssertionAnalysis
    rw [derivedAssertionAnalysisCosted_value]
    cases (derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables) <;> simp
  unfold derivedAssertionFailureCostBound at h1 ⊢
  omega

/-- Expanded polynomial for complete report construction. D counts stored
derived propositions; the other dimensions are worlds W and things T. -/
theorem derivedAssertionReportCostBound_eq (W T : Nat) (tables : FactTables) :
    derivedAssertionReportCostBound W T tables =
      112 * W * T ^ 2 + 200 * T ^ 2 + 214 * W * T +
        8 * T * tables.derivedProps.size + 866 * T + 184 * W + 519 := by
  unfold derivedAssertionReportCostBound derivedReportComponentCostBound
    externallyDependentModeStatusCostBound externallyDependentWitnessCostBound
  ring

/-- These bounds grow with model dimensions and stored derived propositions.
The statement concerns upper bounds, not exact counts: an added fact can
supply an earlier witness and reduce the work actually performed. -/
theorem derivedAssertionReportCostBound_mono
    {W₁ W₂ T₁ T₂ : Nat} (tables₁ tables₂ : FactTables)
    (hW : W₁ ≤ W₂) (hT : T₁ ≤ T₂)
    (hD : tables₁.derivedProps.size ≤ tables₂.derivedProps.size) :
    derivedAssertionReportCostBound W₁ T₁ tables₁ ≤
      derivedAssertionReportCostBound W₂ T₂ tables₂ := by
  have inner := Nat.mul_le_mul hT (show 56 * W₁ + 22 ≤ 56 * W₂ + 22 by omega)
  have mode := Nat.mul_le_mul hT
    (show 28 * W₁ + T₁ * (56 * W₁ + 22) + 6 ≤
      28 * W₂ + T₂ * (56 * W₂ + 22) + 6 by omega)
  have declared := Nat.mul_le_mul hT
    (show 4 * tables₁.derivedProps.size + 51 ≤ 4 * tables₂.derivedProps.size + 51 by omega)
  have external := Nat.mul_le_mul hT (show 60 * W₁ + 40 ≤ 60 * W₂ + 40 by omega)
  have functional := Nat.mul_le_mul hT (show 78 * T₁ + 100 ≤ 78 * T₂ + 100 by omega)
  have typehood := Nat.mul_le_mul hW (show 19 * T₁ + 62 ≤ 19 * T₂ + 62 by omega)
  dsimp only [derivedAssertionReportCostBound, derivedReportComponentCostBound,
    externallyDependentModeStatusCostBound, externallyDependentWitnessCostBound]
  omega

theorem derivedAssertionFailureCostBound_mono
    {W₁ W₂ T₁ T₂ F₁ F₂ E₁ E₂ : Nat} (tables₁ tables₂ : FactTables)
    (hW : W₁ ≤ W₂) (hT : T₁ ≤ T₂) (hF : F₁ ≤ F₂) (hE : E₁ ≤ E₂)
    (hD : tables₁.derivedProps.size ≤ tables₂.derivedProps.size) :
    derivedAssertionFailureCostBound W₁ T₁ F₁ E₁ tables₁ ≤
      derivedAssertionFailureCostBound W₂ T₂ F₂ E₂ tables₂ := by
  have hs := firstDerivedAssertionFailureCostBound_mono tables₁ tables₂ hF hW hT hD
  have hr := derivedAssertionReportCostBound_mono tables₁ tables₂ hW hT hD
  unfold derivedAssertionFailureCostBound
  omega

end LeanUfo.UFO.DSL
