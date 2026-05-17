import LeanUfo.UFO.DSL.Syntax

/-!
# Reuse model extension example

This file exercises the incremental-certificate surface syntax with a small
car scenario.  The child model adds a window and body as proper parts of the
car, while certificate generation reuses only the parent checks whose finite
checker inputs are unchanged.

The extension does not add worlds: child facts are compiled against the
parent's world set, which avoids changing the meaning of parent `everywhere`
facts.
-/

open LeanUfo.UFO.DSL

ufo_model CarBase : UFO where
  worlds actual
  things PhysicalObject Car
  given actual:
    Car :: PhysicalObject
    Object(Car)
    ObjectKind(PhysicalObject)
  derive_relations
  certify

export_certificate CarBase

ufo_model CarWithWindow : UFO extends CarBase : UFO where
  things Window Body
  given actual:
    Window :: PhysicalObject
    Body :: PhysicalObject
    Object(Window)
    Object(Body)
    Part(PhysicalObject, PhysicalObject)
    Part(Car, Car)
    Part(Window, Window)
    Part(Body, Body)
    Part(Window, Car)
    Part(Body, Car)
    Overlap(PhysicalObject, PhysicalObject)
    Overlap(Car, Car)
    Overlap(Window, Window)
    Overlap(Body, Body)
    Overlap(Window, Car)
    Overlap(Car, Window)
    Overlap(Body, Car)
    Overlap(Car, Body)
    ProperPart(Window, Car)
    ProperPart(Body, Car)
  derive_relations
  certify

export_certificate CarWithWindow

/-
The same source can be certified with `certify_fresh` when a developer wants to
force fresh checker proofs instead of allowing parent-certificate reuse.
-/
ufo_model CarWithWindowFresh : UFO extends CarBase : UFO where
  things Window Body
  given actual:
    Window :: PhysicalObject
    Body :: PhysicalObject
    Object(Window)
    Object(Body)
    Part(PhysicalObject, PhysicalObject)
    Part(Car, Car)
    Part(Window, Window)
    Part(Body, Body)
    Part(Window, Car)
    Part(Body, Car)
    Overlap(PhysicalObject, PhysicalObject)
    Overlap(Car, Car)
    Overlap(Window, Window)
    Overlap(Body, Body)
    Overlap(Window, Car)
    Overlap(Car, Window)
    Overlap(Body, Car)
    Overlap(Car, Body)
    ProperPart(Window, Car)
    ProperPart(Body, Car)
  derive_relations
  certify_fresh

/-
An exact-source extension alias demonstrates the surface form used by
incremental certification.  Because it adds no facts or things, ordinary
`certify` can reuse the parent's stored checker theorems.
-/
ufo_model CarBaseAlias : UFO extends CarBase : UFO where
  derive_relations
  certify
