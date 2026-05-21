# DSL Syntax Reference

[Docs home](../README.md) · [Project README](../../README.md)

## Model Command

```lean
ufo_model ModelName : UFO where
  worlds actual possible
  things Person Student Alice

  given actual:
    Role(Student)
    Student ⊑ Person
    Object(Alice)
    Alice :: Student

  given everywhere:
    ObjectKind(Person)

  derive_relations
  certify
```

Use `certify_fresh` when you want to force fresh per-axiom Boolean check
theorems instead of allowing parent-certificate reuse in an extension:

```lean
ufo_model ModelName : UFO where
  worlds actual
  things Person Alice

  given actual:
    ObjectKind(Person)
    Object(Alice)
    Alice :: Person

  derive_relations
  certify_fresh
```

In the current implementation, ordinary `certify` may reuse a parent's stored
check theorem when an extension compiles to exactly the same source as the
parent, or when the registered finite-table footprint for that axiom is
unchanged. `certify_fresh` forces fresh check theorem generation.

Reuse is still Lean-checked. The generated child theorem first proves that the
child checker result equals the parent checker result; if Lean cannot check
that equality, the command falls back to a fresh checker proof.

## Model Extension

A model can extend a model that was elaborated earlier in the same module or
imported from another module. This example starts with a car as a physical
object, then adds a window and a body as proper parts. The body is included
because the encoded UFO mereology includes strong supplementation: if the
window is a proper part of the car, the car must also have another part that
does not overlap the window.

```lean
ufo_model CarBase : UFO where
  worlds actual
  things PhysicalObject Car

  given actual:
    ObjectKind(PhysicalObject)
    Object(Car)
    Car :: PhysicalObject

  derive_relations
  certify

ufo_model CarWithWindow : UFO extends CarBase : UFO where
  things Window Body

  given actual:
    Window :: PhysicalObject
    Body :: PhysicalObject
    Object(Window)
    Object(Body)
    Part(Window, Car)
    Part(Body, Car)
    Overlap(Window, Car)
    Overlap(Car, Window)
    Overlap(Body, Car)
    Overlap(Car, Body)

    ProperPart(Window, Car)
    ProperPart(Body, Car)

  derive_relations
  certify

export_certificate CarWithWindow
```

The child model reuses the parent's declared worlds, things, facts, and
product-family witnesses, then adds its own things and facts before compilation.
It cannot add worlds yet. This avoids changing the meaning of parent
`given everywhere:` facts; the added-world scoping policy is intentionally left
for a later design step.

Across modules, import the parent model's module before writing the child:

```lean
import MyModels.CarBase

open LeanUfo.UFO.DSL

ufo_model CarWithWindow : UFO extends CarBase : UFO where
  -- add the child things and facts here
  derive_relations
  certify
```

Use `certify_fresh` for the same model shape when you explicitly want to bypass
reuse and regenerate all checker proofs:

```lean
ufo_model CarWithWindowFresh : UFO extends CarBase : UFO where
  things Window Body

  given actual:
    Window :: PhysicalObject
    Body :: PhysicalObject
    Object(Window)
    Object(Body)
    Part(Window, Car)
    Part(Body, Car)
    Overlap(Window, Car)
    Overlap(Car, Window)
    Overlap(Body, Car)
    Overlap(Car, Body)

    ProperPart(Window, Car)
    ProperPart(Body, Car)

  derive_relations
  certify_fresh
```

An extension with no additions is treated as an exact alias and can reuse the
parent's stored checks:

```lean
ufo_model CarBaseAlias : UFO extends CarBase : UFO where
  derive_relations
  certify
```

Every certified model exposes reusable certificate artifacts:

```lean
#check CarBase.source
#check CarBase.checked_ax1
#check CarBase.certificateManifest
#check CarBase.certificateManifest.toJson
```

Use `export_certificate` to mark a model for manifest export:

```lean
export_certificate CarBase
```

The marker emits `CarBase.exportRequested : Bool := true`. It is metadata for
the Lake exporter, not proof evidence.

Export and validation are ordinary Lake workflows:

```bash
lake build LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension
lake exe export-certificates --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension --out certificates/
lake exe validate-certificate certificates/CarBase.certificate.json --structure-only
lake exe validate-certificate certificates/CarWithWindow.certificate.json --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension
```

`--structure-only` checks just the JSON manifest shape. The default validation
path requires `--module`: it rebuilds the module, checks the named Lean theorem
declarations at their expected types, and compares regenerated SHA-256 source
and finite-model digests.

Additional concrete reuse examples cover role extension and mode/inherence
extension:

```text
LeanUfo/UFO/DSL/ConcreteExamples/ReuseRoleExtension.lean
LeanUfo/UFO/DSL/ConcreteExamples/ReuseModeExtension.lean
```

## Facts

The DSL keeps UFO notation for instantiation and specialization:

```lean
Alice :: Person
Student ⊑ Person
```

Unary predicates use call syntax:

```lean
Object(Alice)
ObjectKind(Person)
Moment(ColorMode)
Perdurant(Process)
```

Binary relations use call syntax:

```lean
Part(Wheel, Car)
ProperPart(Wheel, Car)
Overlap(LeftHalf, WholeCar)
InheresIn(ColorMode, Apple)
FoundedBy(EnrollmentRole, EnrollmentEvent)
ConstitutedBy(Statue, Clay)
```

Selected ternary and higher-arity relations also use call syntax:

```lean
Distance(RedValue, BlueValue, ColorDistance)
DistanceSum(ShortDistance, MediumDistance, LongDistance)
IsPartitionedInto(Person, Student, NonStudent)
TupleProjection(ColorTuple, 0, HueValue)
```

## Scope

```lean
given actual:
  Object(Alice)
```

adds a fact at one world.

```lean
given everywhere:
  ObjectKind(Person)
```

adds the fact at every declared world.

## Derived Relations

Some relations can be asserted in `derive_relations`, but their truth is still
computed from the finite model semantics. Assertions are checked, not used to
override the compiler.

Current supported derived assertions include:

- `IsDisjointWith(Person, Organization)`
- `IsCompletelyCoveredBy(Person, Student, NonStudent)`
- `IsPartitionedInto(Person, Student, NonStudent)`
- `Categorizes(EmploymentCategory, Employee)`

The compiler also computes definition-like predicates such as `Type`,
`Individual`, `UltimateBearerOf`, `ExistentialDependence`,
`ExternallyDependentMode`, and selected quality/set predicates.

## Quality And Distance Primitives

The current surface supports primitive finite facts for quality/set examples:

```lean
Quale(RedValue)
Set(ColorSpace)
MemberOf(RedValue, ColorSpace)
QualityDomain(ColorDomain)
QualityDimension(HueDimension)
AssociatedWith(HueDimension, ColorQuality)
TupleProjection(ColorTuple, 0, HueValue)
Distance(RedValue, BlueValue, ColorDistance)
DistanceZero(ZeroDistance)
DistanceGreaterEq(LongDistance, ShortDistance)
DistanceSum(ShortDistance, MediumDistance, LongDistance)
```

Product-family witnesses for axiom (a99) are written outside `given` blocks:

```lean
product_family ColorSpace for ColorQuality:
  dimensions HueSpace SaturationSpace BrightnessSpace
  types Hue Saturation Brightness
```

The witness supplies the finite `ys`/`zs` family used by the reflective checker.
Richer §3.12 models can still require low-level tuple, membership,
`AssociatedWith`, and `Characterization` facts to make such a family
semantically active.

[Docs home](../README.md) · [Project README](../../README.md)
