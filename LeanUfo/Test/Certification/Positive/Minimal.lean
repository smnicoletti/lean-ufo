import LeanUfo.UFO.DSL.Syntax

/-!
Self-contained minimal positive fixture for the test suite.

This mirrors the user-facing minimal example without importing it, so the test
suite does not depend on example files.
-/

open LeanUfo.UFO.DSL

ufo_model TestMinimalCommand : UFO where
  worlds actual
  things K I
  given actual:
    I :: K
    Object(I)
    ObjectKind(K)
  derive_relations
  certify
