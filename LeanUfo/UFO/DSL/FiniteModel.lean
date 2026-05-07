import LeanUfo.UFO.DSL.Certification

/-!
# Finite reflective models for UFO §4

This file is the semantic middle layer for the finite DSL.

The important separation is:

* **DSL syntax** is only a user interface.  It names worlds and things and lists
  facts such as `Mark : ConcreteIndividual`, `Mark :: Person`, and
  `Employee ⊑ Person`.
* **Finite data** is the compiled representation below.  User names disappear
  here; worlds and things are represented by `Fin n` indices.
* **Semantic interpretation** is still the existing `UFOSignature4`.  The
  function `FiniteModel4.toUFOSignature4` compiles finite Boolean tables into
  the Prop-valued signature used by the trusted UFO axioms.
* **Certification** is the ordinary Lean proposition `UFOAxioms4 sig`.  The DSL
  proves it by computation for generated finite signatures; it does not replace
  or weaken the original axiom packages.

The finite backend uses a universal S5 accessibility relation.  This is enough
for the first DSL workflow and keeps the user syntax focused on ontology facts.
The structure still has an explicit `worldCount`, so adding an accessibility
table later is a local extension of this layer.
-/

namespace LeanUfo.UFO.DSL

/--
Finite data for a UFO model through the current §4 signature.

The first two parameters are positive by construction: a DSL model always has at
least one world and at least one thing.  Internally they become `Fin worldCount`
and `Fin thingCount`.

Most fields are primitive, user-controlled Boolean tables.  A few
definition-like predicates are kept as tables only because the surrounding
signature already exposes those slots; the semantic compiler may ignore those
tables and compute the corresponding Prop-valued relation instead.  In
particular, `Type_`, `Individual`, several dependence predicates, and §4
relations are derived during semantic compilation so the common model syntax
stays concise and cannot make those definitional axioms inconsistent by
accident.
-/
structure FiniteModel4 where
  worldCount : Nat
  thingCount : Nat
  worldPositive : 0 < worldCount
  thingPositive : 0 < thingCount

  /- §3.1 core relation supplied by `x :: T`. -/
  inst : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.1 specialization supplied by `T₁ ⊑ T₂`. -/
  sub : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.1 individual/type classification predicates supplied by `x : P`. -/
  concreteIndividual : Fin thingCount → Fin worldCount → Bool
  abstractIndividual : Fin thingCount → Fin worldCount → Bool
  endurant : Fin thingCount → Fin worldCount → Bool
  perdurant : Fin thingCount → Fin worldCount → Bool
  endurantType : Fin thingCount → Fin worldCount → Bool
  perdurantType : Fin thingCount → Fin worldCount → Bool

  /- §3.2 type metaproperties. -/
  rigid : Fin thingCount → Fin worldCount → Bool
  antiRigid : Fin thingCount → Fin worldCount → Bool
  semiRigid : Fin thingCount → Fin worldCount → Bool
  kind : Fin thingCount → Fin worldCount → Bool
  sortal : Fin thingCount → Fin worldCount → Bool
  nonSortal : Fin thingCount → Fin worldCount → Bool
  subKind : Fin thingCount → Fin worldCount → Bool
  phase : Fin thingCount → Fin worldCount → Bool
  role : Fin thingCount → Fin worldCount → Bool
  semiRigidSortal : Fin thingCount → Fin worldCount → Bool
  category : Fin thingCount → Fin worldCount → Bool
  mixin : Fin thingCount → Fin worldCount → Bool
  phaseMixin : Fin thingCount → Fin worldCount → Bool
  roleMixin : Fin thingCount → Fin worldCount → Bool

  /- §3.3 endurant-individual partition. -/
  substantial : Fin thingCount → Fin worldCount → Bool
  moment : Fin thingCount → Fin worldCount → Bool
  object : Fin thingCount → Fin worldCount → Bool
  collective : Fin thingCount → Fin worldCount → Bool
  quantity : Fin thingCount → Fin worldCount → Bool
  relator : Fin thingCount → Fin worldCount → Bool
  intrinsicMoment : Fin thingCount → Fin worldCount → Bool
  mode : Fin thingCount → Fin worldCount → Bool
  qualityKind : Fin thingCount → Fin worldCount → Bool

  /- §3.4 endurant type/kind refinements. -/
  substantialType : Fin thingCount → Fin worldCount → Bool
  momentType : Fin thingCount → Fin worldCount → Bool
  objectType : Fin thingCount → Fin worldCount → Bool
  collectiveType : Fin thingCount → Fin worldCount → Bool
  quantityType : Fin thingCount → Fin worldCount → Bool
  relatorType : Fin thingCount → Fin worldCount → Bool
  modeType : Fin thingCount → Fin worldCount → Bool
  qualityType : Fin thingCount → Fin worldCount → Bool
  objectKind : Fin thingCount → Fin worldCount → Bool
  collectiveKind : Fin thingCount → Fin worldCount → Bool
  quantityKind : Fin thingCount → Fin worldCount → Bool
  relatorKind : Fin thingCount → Fin worldCount → Bool
  modeKind : Fin thingCount → Fin worldCount → Bool

  /- §3.5 mereology. -/
  part : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  overlap : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  properPart : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.6 functional dependence. -/
  functionsAs : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  genericFunctionalDependence : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  individualFunctionalDependence :
    Fin thingCount → Fin thingCount → Fin thingCount → Fin thingCount → Fin worldCount → Bool
  componentOf :
    Fin thingCount → Fin thingCount → Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.7 existence and constitution. -/
  ex : Fin thingCount → Fin worldCount → Bool
  constitutedBy : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  genericConstitutionalDependence : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  constitution :
    Fin thingCount → Fin thingCount → Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.8 existential dependence. -/
  existentialDependence : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  existentialIndependence : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.9 inherence. -/
  inheresIn : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.10 externally dependent modes, relators, and qua individuals. -/
  externallyDependent : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  externallyDependentMode : Fin thingCount → Fin worldCount → Bool
  foundedBy : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  quaIndividualOf : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  quaIndividual : Fin thingCount → Fin worldCount → Bool
  mediates : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.11 characterization. -/
  characterization : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.12 qualities, quality spaces, and distance primitives. -/
  quale : Fin thingCount → Fin worldCount → Bool
  set_ : Fin thingCount → Fin worldCount → Bool
  setExtension : Fin thingCount → Fin worldCount → Set (Fin thingCount)
  qualityDomain : Fin thingCount → Fin worldCount → Bool
  qualityDimension : Fin thingCount → Fin worldCount → Bool
  associatedWith : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  intrinsicMomentType : Fin thingCount → Fin worldCount → Bool
  hasValue : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  tupleProjection :
    {n : Nat} → Fin thingCount → Fin n → Fin worldCount → Fin thingCount
  distance : Fin thingCount → Fin thingCount → Fin thingCount → Fin worldCount → Bool
  distanceZero : Fin thingCount → Fin worldCount → Bool
  distanceSum : Fin thingCount → Fin thingCount → Fin thingCount → Fin worldCount → Bool
  distanceGreaterEq : Fin thingCount → Fin thingCount → Fin worldCount → Bool

  /- §3.13 endurant/perdurant connection predicates. -/
  manifests : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  lifeOf : Fin thingCount → Fin thingCount → Fin worldCount → Bool
  meet : Fin thingCount → Fin thingCount → Fin worldCount → Bool

namespace FiniteModel4

/-- The internal world type of a finite model. -/
abbrev World (M : FiniteModel4) : Type := Fin M.worldCount

/-- The internal thing type of a finite model. -/
abbrev Thing (M : FiniteModel4) : Type := Fin M.thingCount

/-- Boolean-to-Prop coercion used uniformly for primitive finite tables. -/
def holds {α : Sort u} (p : α → Bool) (x : α) : Prop := p x = true

/--
Every generated model receives a universal S5 frame.

The accessibility relation is intentionally not part of the first user syntax:
for the current single-world and small finite examples, all worlds seeing all
worlds is enough.  The modal operators are still interpreted by the existing
S5 semantics; this is only a front-end default.
-/
def toS5Frame (M : FiniteModel4) : S5Frame :=
{ World := Fin M.worldCount
  R := fun _ _ => True
  refl := by intro _; trivial
  symm := by intro _ _ _; trivial
  trans := by intro _ _ _ _ _; trivial }

/-- A thing is a type exactly when it is possibly instantiated. -/
def typeSem (M : FiniteModel4) (x : Fin M.thingCount) (_w : Fin M.worldCount) : Prop :=
  ∃ (v : Fin M.worldCount) (y : Fin M.thingCount), M.inst y x v = true

/-- A thing is an individual exactly when it is never instantiated. -/
def individualSem (M : FiniteModel4) (x : Fin M.thingCount) (_w : Fin M.worldCount) : Prop :=
  ¬ ∃ (v : Fin M.worldCount) (y : Fin M.thingCount), M.inst y x v = true

/--
Compilation from finite data to the existing semantic signature.

Notice the direction of trust: all DSL-level data is erased into ordinary Lean
definitions over `Fin`; the target is exactly `UFOSignature4`, so all downstream
theorems continue to talk about the original UFO semantics.
-/
def toUFOSignature4 (M : FiniteModel4) : UFOSignature4 :=
{ F := M.toS5Frame
  Thing := Fin M.thingCount
  thing_nonempty := ⟨⟨0, M.thingPositive⟩⟩

  Type_ := M.typeSem
  Individual := M.individualSem
  Inst := fun y x w => M.inst y x w = true
  Sub := fun x y w => M.sub x y w = true

  ConcreteIndividual := fun x w => M.concreteIndividual x w = true
  AbstractIndividual := fun x w => M.abstractIndividual x w = true
  Endurant := fun x w => M.endurant x w = true
  Perdurant := fun x w => M.perdurant x w = true
  EndurantType := fun x w => M.endurantType x w = true
  PerdurantType := fun x w => M.perdurantType x w = true

  Rigid := fun x w => M.rigid x w = true
  AntiRigid := fun x w => M.antiRigid x w = true
  SemiRigid := fun x w => M.semiRigid x w = true
  Kind := fun x w => M.kind x w = true
  Sortal := fun x w => M.sortal x w = true
  NonSortal := fun x w => M.nonSortal x w = true
  SubKind := fun x w => M.subKind x w = true
  Phase := fun x w => M.phase x w = true
  Role := fun x w => M.role x w = true
  SemiRigidSortal := fun x w => M.semiRigidSortal x w = true
  Category := fun x w => M.category x w = true
  Mixin := fun x w => M.mixin x w = true
  PhaseMixin := fun x w => M.phaseMixin x w = true
  RoleMixin := fun x w => M.roleMixin x w = true

  Substantial := fun x w => M.substantial x w = true
  Moment := fun x w => M.moment x w = true
  Object := fun x w => M.object x w = true
  Collective := fun x w => M.collective x w = true
  Quantity := fun x w => M.quantity x w = true
  Relator := fun x w => M.relator x w = true
  IntrinsicMoment := fun x w => M.intrinsicMoment x w = true
  Mode := fun x w => M.mode x w = true
  QualityKind := fun x w => M.qualityKind x w = true

  SubstantialType := fun x w => M.substantialType x w = true
  MomentType := fun x w => M.momentType x w = true
  ObjectType := fun x w => M.objectType x w = true
  CollectiveType := fun x w => M.collectiveType x w = true
  QuantityType := fun x w => M.quantityType x w = true
  RelatorType := fun x w => M.relatorType x w = true
  ModeType := fun x w => M.modeType x w = true
  QualityType := fun x w => M.qualityType x w = true
  ObjectKind := fun x w => M.objectKind x w = true
  CollectiveKind := fun x w => M.collectiveKind x w = true
  QuantityKind := fun x w => M.quantityKind x w = true
  RelatorKind := fun x w => M.relatorKind x w = true
  ModeKind := fun x w => M.modeKind x w = true

  /-
  Mereology is user-controlled finite data.  This means a DSL model may specify
  non-trivial `Part`, `Overlap`, and `ProperPart` facts.  Certification then has
  to check the §3.5 constraints: parthood must be reflexive, antisymmetric, and
  transitive; overlap must match common parthood; and proper parthood must be
  strict parthood.
  -/
  Part := fun x y w => M.part x y w = true
  Overlap := fun x y w => M.overlap x y w = true
  ProperPart := fun x y w => M.properPart x y w = true

  FunctionsAs := fun x y w => M.functionsAs x y w = true
  /-
  The following §3.6 relations are definition-like in the current axioms, so
  the finite compiler derives them from the primitive tables.  This lets the
  user specify `FunctionsAs` and mereology while keeping the dependent
  functional-composition predicates coherent by construction.
  -/
  GenericFunctionalDependence := fun x' y' w =>
    ∀ x : Fin M.thingCount,
      (M.inst x x' w = true ∧ M.functionsAs x x' w = true) →
        ∃ y : Fin M.thingCount,
          y ≠ x ∧ M.inst y y' w = true ∧ M.functionsAs y y' w = true
  IndividualFunctionalDependence := fun x x' y y' w =>
    (∀ z : Fin M.thingCount,
      (M.inst z x' w = true ∧ M.functionsAs z x' w = true) →
        ∃ q : Fin M.thingCount,
          q ≠ z ∧ M.inst q y' w = true ∧ M.functionsAs q y' w = true) ∧
    M.inst x x' w = true ∧ M.inst y y' w = true ∧
    (M.functionsAs x x' w = true → M.functionsAs y y' w = true)
  ComponentOf := fun x x' y y' w =>
    M.properPart x y w = true ∧
    ((∀ z : Fin M.thingCount,
      (M.inst z x' w = true ∧ M.functionsAs z x' w = true) →
        ∃ q : Fin M.thingCount,
          q ≠ z ∧ M.inst q y' w = true ∧ M.functionsAs q y' w = true) ∧
    M.inst x x' w = true ∧ M.inst y y' w = true ∧
    (M.functionsAs x x' w = true → M.functionsAs y y' w = true))

  Ex := fun x w => M.ex x w = true
  ConstitutedBy := fun x y w => M.constitutedBy x y w = true
  /- §3.7 generic constitution predicates are also definition-like. -/
  GenericConstitutionalDependence := fun x' y' w =>
    ∀ x : Fin M.thingCount,
      M.inst x x' w = true →
        ∃ y : Fin M.thingCount, M.inst y y' w = true ∧ M.constitutedBy x y w = true
  Constitution := fun x x' y y' w =>
    M.inst x x' w = true ∧ M.inst y y' w = true ∧
    (∀ z : Fin M.thingCount,
      M.inst z x' w = true →
        ∃ q : Fin M.thingCount, M.inst q y' w = true ∧ M.constitutedBy z q w = true) ∧
    M.constitutedBy x y w = true

  /- §3.8 dependence predicates are derived from the existence table. -/
  ExistentialDependence := fun x y w =>
    Frame.Box (F := M.toS5Frame)
      (fun w' => M.ex x w' = true → M.ex y w' = true)
      w
  ExistentialIndependence := fun x y w =>
    ¬ Frame.Box (F := M.toS5Frame)
        (fun w' => M.ex x w' = true → M.ex y w' = true)
        w ∧
    ¬ Frame.Box (F := M.toS5Frame)
        (fun w' => M.ex y w' = true → M.ex x w' = true)
        w

  InheresIn := fun x y w => M.inheresIn x y w = true

  /-
  §3.10 starts with definition-like relator predicates.  The finite data still
  contains tables for these relations so existing generated structures have a
  uniform shape.  The semantic compiler, however, interprets the first two by
  their Prop-level definitions:

  * `ExternallyDependent` is the §3.10 right-hand side built from existential
    dependence and inherence.
  * `ExternallyDependentMode` is exactly a mode with some external dependency.
  * `QuaIndividual` is derived from `QuaIndividualOf`, matching axiom (a74).

  `QuaIndividualOf` remains a primitive table in this first backend because its
  definition uses `FoundationOf`, a definite description over `FoundedBy`.  The
  generated certificate still checks axiom (a73), so invalid `QuaIndividualOf`
  facts are rejected by `certify`.
  -/
  ExternallyDependent := fun x y w =>
    (Frame.Box (F := M.toS5Frame)
      (fun w' => M.ex x w' = true → M.ex y w' = true)
      w) ∧
    ∀ z : Fin M.thingCount,
      M.inheresIn x z w = true →
        (¬ Frame.Box (F := M.toS5Frame)
            (fun w' => M.ex y w' = true → M.ex z w' = true)
            w ∧
         ¬ Frame.Box (F := M.toS5Frame)
            (fun w' => M.ex z w' = true → M.ex y w' = true)
            w)
  ExternallyDependentMode := fun x w =>
    M.mode x w = true ∧
    ∃ y : Fin M.thingCount,
      (Frame.Box (F := M.toS5Frame)
        (fun w' => M.ex x w' = true → M.ex y w' = true)
        w) ∧
      ∀ z : Fin M.thingCount,
        M.inheresIn x z w = true →
          (¬ Frame.Box (F := M.toS5Frame)
              (fun w' => M.ex y w' = true → M.ex z w' = true)
              w ∧
           ¬ Frame.Box (F := M.toS5Frame)
              (fun w' => M.ex z w' = true → M.ex y w' = true)
              w)
  FoundedBy := fun x y w => M.foundedBy x y w = true
  QuaIndividualOf := fun x y w => M.quaIndividualOf x y w = true
  QuaIndividual := fun x w =>
    ∃ y : Fin M.thingCount, M.quaIndividualOf x y w = true
  Mediates := fun x y w => M.mediates x y w = true

  Characterization := fun x y w => M.characterization x y w = true

  Quale := fun x w => M.quale x w = true
  Set_ := fun x w => M.set_ x w = true
  SetExtension := M.setExtension
  QualityDomain := fun x w => M.qualityDomain x w = true
  QualityDimension := fun x w => M.qualityDimension x w = true
  AssociatedWith := fun x y w => M.associatedWith x y w = true
  IntrinsicMomentType := fun x w => M.intrinsicMomentType x w = true
  HasValue := fun x y w => M.hasValue x y w = true
  TupleProjection := fun x i w => M.tupleProjection x i w
  Distance := fun x y z w => M.distance x y z w = true
  DistanceZero := fun x w => M.distanceZero x w = true
  DistanceSum := fun x y z w => M.distanceSum x y z w = true
  DistanceGreaterEq := fun x y w => M.distanceGreaterEq x y w = true

  Manifests := fun x y w => M.manifests x y w = true
  LifeOf := fun x y w => M.lifeOf x y w = true
  Meet := fun x y w => M.meet x y w = true

  /-
  §4 relations are derived from their axiom right-hand sides.  This is the
  semantic operation requested by the `derive_relations` DSL directive.
  -/
  IsDisjointWith := fun t t' w =>
    M.typeSem t w ∧ M.typeSem t' w ∧
      ¬ ∃ x : Fin M.thingCount, M.inst x t w = true ∧ M.inst x t' w = true
  IsCompletelyCoveredBy := fun t t' t'' w =>
    ∀ x : Fin M.thingCount, M.inst x t w = true →
      M.inst x t' w = true ∨ M.inst x t'' w = true
  IsPartitionedInto := fun t t' t'' w =>
    (∀ x : Fin M.thingCount, M.inst x t w = true →
      M.inst x t' w = true ∨ M.inst x t'' w = true) ∧
    (M.typeSem t' w ∧ M.typeSem t'' w ∧
      ¬ ∃ x : Fin M.thingCount, M.inst x t' w = true ∧ M.inst x t'' w = true)
  Categorizes := fun t1 t2 w =>
    M.typeSem t1 w ∧
      ∀ t3 : Fin M.thingCount, M.inst t3 t1 w = true → M.sub t3 t2 w = true }

/--
User-facing certification predicate for a finite model.

This is intentionally just the original axiom package applied to the compiled
signature.  Keeping the type this direct makes generated certificates useful in
ordinary downstream Lean proofs.
-/
def Certified (M : FiniteModel4) : Prop :=
  UFOAxioms4 M.toUFOSignature4

end FiniteModel4

end LeanUfo.UFO.DSL
