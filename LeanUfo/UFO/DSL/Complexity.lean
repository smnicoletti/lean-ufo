import LeanUfo.UFO.DSL.Complexity.CostModel
import LeanUfo.UFO.DSL.Complexity.Metrics
import LeanUfo.UFO.DSL.Complexity.Tables
import LeanUfo.UFO.DSL.Complexity.Closure
import LeanUfo.UFO.DSL.Complexity.Taxonomy
import LeanUfo.UFO.DSL.Complexity.Compiler
import LeanUfo.UFO.DSL.Complexity.Checker
import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Complexity.Diagnostics.ProductFamily
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Unique
import LeanUfo.UFO.DSL.Complexity.Theorems
import LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions

/-!
# Operational complexity guarantees

This is the public import for the DSL cost development. The files follow the
order in which a model is processed:

* `CostModel` defines computations that return both a value and a cost;
* `Metrics` defines the independently sized parts of source and compiled input;
* `Tables` and `Closure` cover the main finite data structures and reachability;
* `Taxonomy` proves and counts traversal of the fixed unary parent graph;
* `Compiler`, `Checker`, and `Diagnostics` bound the three executable stages;
  `Diagnostics/ProductFamily` validates supplied axiom 99 witnesses with
  concrete table-query costs and a checker-condition correspondence theorem;
  `Diagnostics/Unique` proves the result and linear bound of the search for
  exactly one witness, with an early exit at the second match;
* `Theorems` collects the stage bounds and their sum. Source-to-model
  correspondence remains an open obligation in the behavior contract.
* The imported `Diagnostic.DerivedAssertions` module provides the operational
  selection, report, and output bounds for the pre-certification assertion path.
  Its proofs stay beside the executable functions they describe.

Keeping these modules together prevents complexity claims from being confused
with semantic correctness proofs in `Checker/Soundness.lean`. The ordinary
production functions are erasures of the counted functions: erasure discards
the cost field and retains exactly the computed value.
-/
