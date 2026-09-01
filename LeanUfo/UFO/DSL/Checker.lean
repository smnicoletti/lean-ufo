import LeanUfo.UFO.DSL.Checker.Basic
import LeanUfo.UFO.DSL.Checker.Axioms
import LeanUfo.UFO.DSL.Checker.Soundness

/-!
# Reflective checker

This is the public import for the executable checker and its correctness proof.
The implementation is split by responsibility:

* `Checker/Basic.lean` defines finite, short-circuiting quantifiers, which stop
  as soon as one item determines the result, and common derived predicates;
* `Checker/Axioms.lean` computes the Boolean result of each UFO axiom;
* `Checker/Soundness.lean` connects each Boolean result to the corresponding
  proposition in the semantic UFO kernel.

This last connection is often called **reflection**: Lean evaluates a Boolean
program and then uses a proved theorem to turn `true` into a proposition. It
lets generated certificates perform computation without trusting that
computation as a new axiom.
-/
