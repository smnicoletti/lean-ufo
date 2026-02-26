import LeanUfo.UFO.Models.Model3_1
import LeanUfo.UFO.Models.Model3_2

/--
Consistency checkpoint for UFO subsection 3.1 (relative to Lean):

There exists a `UFOModel3_1`, hence axioms (a1)–(a17) are jointly satisfiable.
-/
theorem consistent_3_1 : Nonempty (UFOModel3_1.{0,0}) :=
  ⟨Model3_1.model3_1⟩

/--
Consistency checkpoint for UFO subsection 3.2 (relative to Lean):

There exists a `UFOModel3_2`, hence axioms (a1)–(a33) and the structural
assumptions required for (t16) are jointly satisfiable.
-/
theorem consistent_3_2 : Nonempty (UFOModel3_2.{0,0}) :=
  ⟨Model3_2.model3_2⟩
