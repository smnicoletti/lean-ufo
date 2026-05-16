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
