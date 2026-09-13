import LeanUfo.UFO.DSL.Compiler.Fields
import LeanUfo.UFO.DSL.Complexity.Checker

/-!
# Counted traversal of the fixed unary taxonomy

The traversal emits a field before its ancestors and emits shared ancestors
only on their first visit. Its output array is also its visited set, so there
is no second mutable representation to synchronize. Membership scans, parent
reads, and output writes contribute to the count as they execute.

The graph is fixed program data. A rank decreases along every parent edge;
five levels therefore suffice for its depth-first traversal. This is not a
bound for an extensible taxonomy supplied as input. The connection between
operational counts and the returned result follows Niu et al. (POPL 2022) and
Haslbeck's time-bound semantics; see `docs/dsl/complexity.md` for references.
-/

namespace LeanUfo.UFO.DSL.Complexity.Taxonomy

/-- Immediate, ordered parents in the fixed DSL classification hierarchy. -/
def parents : UnaryField → Array UnaryField
  | .object | .collective | .quantity => #[.substantial]
  | .relator | .intrinsicMoment => #[.moment]
  | .mode => #[.intrinsicMoment]
  | .substantial | .moment => #[.endurant]
  | .endurant | .perdurant => #[.concreteIndividual]
  | .quale | .set_ => #[.abstractIndividual]
  | .subKind | .kind => #[.rigid, .sortal]
  | .phase | .role => #[.antiRigid, .sortal]
  | .semiRigidSortal => #[.semiRigid, .sortal]
  | .category => #[.rigid, .nonSortal]
  | .mixin => #[.semiRigid, .nonSortal]
  | .phaseMixin | .roleMixin => #[.antiRigid, .nonSortal]
  | .sortal | .nonSortal => #[.endurantType]
  | .objectKind => #[.objectType, .kind]
  | .collectiveKind => #[.collectiveType, .kind]
  | .quantityKind => #[.quantityType, .kind]
  | .relatorKind => #[.relatorType, .kind]
  | .modeKind => #[.modeType, .kind]
  | .qualityKind => #[.qualityType, .kind]
  | .objectType | .collectiveType | .quantityType => #[.substantialType]
  | .relatorType => #[.momentType]
  | .modeType | .qualityType => #[.intrinsicMomentType, .momentType]
  | .intrinsicMomentType => #[.momentType]
  | .substantialType | .momentType => #[.endurantType]
  | _ => #[]

/-- Maximum number of successive parent edges from a field. -/
def rank : UnaryField → Nat
  | .mode | .modeKind | .qualityKind => 4
  | .object | .collective | .quantity | .relator | .intrinsicMoment
  | .modeType | .qualityType | .objectKind | .collectiveKind | .quantityKind
  | .relatorKind => 3
  | .substantial | .moment | .kind | .subKind | .phase | .role | .semiRigidSortal
  | .category | .mixin | .phaseMixin | .roleMixin | .objectType | .collectiveType
  | .quantityType | .relatorType | .intrinsicMomentType => 2
  | .endurant | .perdurant | .sortal | .nonSortal | .quale | .set_
  | .substantialType | .momentType => 1
  | _ => 0

theorem parent_rank_lt (field parent : UnaryField) (h : parent ∈ parents field) :
    rank parent < rank field := by
  cases field <;> simp [parents] at h <;>
    rcases h with rfl | rfl <;> decide

theorem rank_lt_five (field : UnaryField) : rank field < 5 := by
  cases field <;> decide

/-- The level counter makes recursion total. Parent order determines the
depth-first order. Membership scans stop at the first equal field and charge
four operations per visited entry: iteration, read, comparison, and Boolean
test. A repeated field returns without visiting its parents. -/
private def walk : Nat → UnaryField → Array UnaryField → Costed (Array UnaryField)
  | 0, _, out => Costed.tick out 1
  | levels + 1, field, out => Costed.charge 1 do
      let seen ← anyArrayCosted out fun candidate =>
        Costed.tick (decide (candidate = field)) 1
      Costed.branch (Costed.pure seen)
        (fun _ => Costed.pure out)
        (fun _ => do
          let out ← Costed.tick (out.push field) 1
          let next ← Costed.tick (parents field) 1
          Costed.foldArray next out fun out parent => walk levels parent out)

def ancestorsCosted (field : UnaryField) : Costed (Array UnaryField) :=
  walk 5 field #[]

def ancestors (field : UnaryField) : Array UnaryField :=
  (ancestorsCosted field).value

/-- Reflexive reachability through the declared parent edges. -/
inductive Ancestor : UnaryField → UnaryField → Prop
  | self (field) : Ancestor field field
  | parent {field direct ancestor} : direct ∈ parents field →
      Ancestor direct ancestor → Ancestor field ancestor

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Exhausting the fixed field vocabulary verifies that five levels cover
every parent path. This equation is then used to prove reachability, rather
than treating agreement with a regression snapshot as semantic correctness. -/
theorem ancestors_mem_step (field ancestor : UnaryField) :
    ancestor ∈ ancestors field ↔ ancestor = field ∨
      (parents field).any (fun parent => decide (ancestor ∈ ancestors parent)) = true := by
  cases field <;> cases ancestor <;> decide +kernel

theorem ancestors_sound (field ancestor : UnaryField)
    (h : ancestor ∈ ancestors field) : Ancestor field ancestor := by
  suffices ∀ n field, rank field = n → ∀ ancestor,
      ancestor ∈ ancestors field → Ancestor field ancestor from
    this (rank field) field rfl ancestor h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro field hRank ancestor hMem
      rcases (ancestors_mem_step field ancestor).mp hMem with hSelf | hParent
      · subst ancestor
        exact .self field
      · obtain ⟨parent, hParent, hAncestor⟩ := Array.any_eq_true'.mp hParent
        have hSmaller : rank parent < n := by
          rw [← hRank]
          exact parent_rank_lt field parent hParent
        exact .parent hParent
          (ih (rank parent) hSmaller parent rfl ancestor (of_decide_eq_true hAncestor))

theorem ancestors_complete {field ancestor : UnaryField} (h : Ancestor field ancestor) :
    ancestor ∈ ancestors field := by
  induction h with
  | self field => exact (ancestors_mem_step field field).mpr (.inl rfl)
  | @parent field direct ancestor hParent hAncestor ih =>
      apply (ancestors_mem_step field ancestor).mpr
      right
      exact Array.any_eq_true'.mpr ⟨direct, hParent, by simpa using ih⟩

theorem mem_ancestors_iff (field ancestor : UnaryField) :
    ancestor ∈ ancestors field ↔ Ancestor field ancestor :=
  ⟨ancestors_sound field ancestor, ancestors_complete⟩

set_option maxRecDepth 8192 in
/-- The traversal's visited-output discipline removes duplicate ancestors. -/
theorem ancestors_nodup (field : UnaryField) : (ancestors field).toList.Nodup := by
  cases field <;> decide +kernel

set_option maxRecDepth 8192 in
/-- A kernel-checked exhaustive bound for the fixed field vocabulary. The
number bounds the computed counter; it is not assigned to each traversal. -/
theorem ancestorsCosted_cost_le (field : UnaryField) :
    (ancestorsCosted field).cost ≤ 202 := by
  cases field <;> decide +kernel

set_option maxRecDepth 8192 in
/-- The largest ancestor output in the fixed taxonomy has eight fields. -/
theorem ancestors_size_le (field : UnaryField) : (ancestors field).size ≤ 8 := by
  cases field <;> decide +kernel

@[simp] theorem ancestorsCosted_value (field : UnaryField) :
    (ancestorsCosted field).value = ancestors field := rfl

end LeanUfo.UFO.DSL.Complexity.Taxonomy

namespace LeanUfo.UFO.DSL

/-- String-field interface for the same fixed parent graph. The two additional
names belong to the raw relation interface, not the typed unary-field registry. -/
def unaryTaxonomyParents (field : String) : Array String :=
  match UnaryField.fromTableField? field with
  | some field => (Complexity.Taxonomy.parents field).map UnaryField.toTableField
  | none => match field with
    | "externallyDependentMode" => #["mode"]
    | "quaIndividual" => #["externallyDependentMode"]
    | _ => #[]

theorem unaryTaxonomyParents_typed (field : UnaryField) :
    unaryTaxonomyParents field.toTableField =
      (Complexity.Taxonomy.parents field).map UnaryField.toTableField := by
  cases field <;> rfl

end LeanUfo.UFO.DSL
