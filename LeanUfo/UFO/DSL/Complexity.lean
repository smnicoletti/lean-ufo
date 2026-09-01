import LeanUfo.UFO.DSL.Complexity.CostModel
import LeanUfo.UFO.DSL.Complexity.Metrics
import LeanUfo.UFO.DSL.Complexity.Tables
import LeanUfo.UFO.DSL.Complexity.Closure
import LeanUfo.UFO.DSL.Complexity.Compiler
import LeanUfo.UFO.DSL.Complexity.Checker
import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Complexity.Theorems

/-!
# Operational complexity guarantees

This is the public import for the DSL cost development. The files follow the
order in which a model is processed:

* `CostModel` defines computations that return both a value and a cost;
* `Metrics` defines the independently sized parts of source and compiled input;
* `Tables` and `Closure` cover the main finite data structures and reachability;
* `Compiler`, `Checker`, and `Diagnostics` bound the three executable stages;
* `Theorems` combines those local results into end-to-end statements.

Keeping these modules together prevents complexity claims from being confused
with semantic correctness proofs in `Checker/Soundness.lean`. The ordinary
production functions are erasures of the counted functions: erasure discards
the cost field and retains exactly the computed value.
-/
