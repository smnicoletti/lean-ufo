import LeanUfo.UFO.DSL.Complexity.CostModel
import LeanUfo.UFO.DSL.Complexity.Metrics
import LeanUfo.UFO.DSL.Complexity.Tables
import LeanUfo.UFO.DSL.Complexity.Closure
import LeanUfo.UFO.DSL.Complexity.Taxonomy
import LeanUfo.UFO.DSL.Complexity.Compiler
import LeanUfo.UFO.DSL.Compiler.VerifiedModel
import LeanUfo.UFO.DSL.Complexity.Checker
import LeanUfo.UFO.DSL.Complexity.Queries
import LeanUfo.UFO.DSL.Complexity.Frontend
import LeanUfo.UFO.DSL.Complexity.Reuse
import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Complexity.Diagnostics.ProductFamily
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Unique
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Formula
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Reports
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Paths
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Source
import LeanUfo.UFO.DSL.Complexity.Theorems
import LeanUfo.UFO.DSL.Complexity.Certification
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
  `Queries` proves full value/cost correspondence between selected checker
  calls and the concrete table evaluator on the source-produced model;
  `Frontend` proves checked-field driver erasure and bounds its branch costs,
  and composes the per-field and outer drivers with the actual precheck and
  command-only policy. It also proves the assertion and final-report drivers'
  erasure and control bounds, and composes failure-report analyzer/output costs.
  `Reuse` bounds the executed planner's source and table comparisons and
  proves that erasure preserves its candidate-parent selection. Its source
  bound uses the actual parent compiler output and includes stored family slots;
  `Diagnostics/ProductFamily` validates supplied axiom 99 witnesses with
  concrete table-query costs and a checker-condition correspondence theorem;
  `Diagnostics/Unique` proves the result and linear bound of the search for
  exactly one witness, with an early exit at the second match;
  `Diagnostics/Formula` bounds diagnostic evaluation, failure minimization, and
  successful context by formula size, quantifier depth, and input metrics;
  `Diagnostics/Reports` composes generic report bounds through assignment
  search, source evidence, text, registry selection, and retained output;
  `Diagnostics/Paths` proves that paths returned from compiled first-hop
  tables follow actual model edges and have the requested endpoints, and that
  every reachable pair returns a path within the existing traversal limit;
  `Diagnostics/Source` derives the stored-proposition size from compilation
  and bounds derived-assertion diagnostics in the explicit source size;
* `Theorems` collects the stage bounds and the source-linked sum for one
  compiler, model-construction, and aggregate-checker sequence;
  `Certification` composes actual source-linked operands with proof preparation,
  retries, registry traversal, derived assertions, and selected failure analysis.
  It provides multivariate, scalar, and fixed-registry workflow bounds, with
  diagnostic output and excluded Lean proof work stated separately.
  `Compiler.VerifiedModel` proves consistency of a successful source result's
  dimensions, expanded facts, and tables. Successful name resolution supplies
  the coordinate bounds needed for sparse/dense lookup agreement.
  `Complexity.Compiler` bounds construction and the resulting model size
  using the actual compiler output.
* The imported `Diagnostic.DerivedAssertions` module provides the operational
  selection, report, and output bounds for the pre-certification assertion path.
  Its proofs stay beside the executable functions they describe.

Keeping these modules together prevents complexity claims from being confused
with semantic correctness proofs in `Checker/Soundness.lean`. The ordinary
production functions use direct cost erasure or a proved native substitution
to that erasure. Erasure discards the cost field and retains the computed value.
The substitution keeps kernel proof reduction compact while native execution
uses the counted algorithm.
-/
