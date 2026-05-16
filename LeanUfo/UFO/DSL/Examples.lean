import LeanUfo.UFO.DSL.ConcreteExamples.Minimal
import LeanUfo.UFO.DSL.ConcreteExamples.Company
import LeanUfo.UFO.DSL.ConcreteExamples.Role
import LeanUfo.UFO.DSL.ConcreteExamples.WoodenTable
import LeanUfo.UFO.DSL.ConcreteExamples.SchoolRoles
import LeanUfo.UFO.DSL.ConcreteExamples.FlowerPropertyChange
import LeanUfo.UFO.DSL.ConcreteExamples.RedirectedWalk
import LeanUfo.UFO.DSL.ConcreteExamples.UltimateBearer
import LeanUfo.UFO.DSL.ConcreteExamples.StudentEnrollmentMode
import LeanUfo.UFO.DSL.ConcreteExamples.GrantGoal
import LeanUfo.UFO.DSL.ConcreteExamples.ColorSpaceProductFamily
import LeanUfo.UFO.DSL.ConcreteExamples.ConceptEvolution

/-!
# Concrete DSL examples

This module is only an index, so opening `LeanUfo.UFO.DSL.Examples` does not
force readers to inspect generated finite tables or backend proof terms.

The checked concrete examples intentionally use the lightweight surface style:
they state leaf classifications such as `Object`, `ObjectKind`, `Role`, and
`QuantityKind`, while the DSL compiler inserts deterministic taxonomy ancestors
before certification.

`ConceptEvolution.lean` is included with the same example collection, but it is
documentation-only: it records the Section 4.5 higher-order pattern that needs
a level-aware DSL extension before it can be certified faithfully.

The user-facing examples live in:

* `LeanUfo/UFO/DSL/ConcreteExamples/Minimal.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/Company.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/Role.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/WoodenTable.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/SchoolRoles.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/FlowerPropertyChange.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/RedirectedWalk.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/UltimateBearer.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/StudentEnrollmentMode.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/GrantGoal.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/ColorSpaceProductFamily.lean`
* `LeanUfo/UFO/DSL/ConcreteExamples/ConceptEvolution.lean`
-/
