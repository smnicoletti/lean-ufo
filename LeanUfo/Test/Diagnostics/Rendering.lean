import LeanUfo.UFO.DSL.Syntax

/-!
Diagnostic rendering smoke marker.

The executable test runner performs string-level checks against expected failure
output.  This module stays cheap so default `lake test` does not certify a model;
semantic rendering fixtures are run in the full test profile.
-/
