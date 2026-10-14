import LeanUfo.UFO.DSL.Syntax

/-!
Syntax smoke test for the mixed DSL surface.

Instantiation and specialization keep their UFO notation, while unary
predicates and ordinary relations use call syntax.
-/

open LeanUfo.UFO.DSL

ufo_model PredicateCallSyntaxExample : UFO where
  worlds actual
  things KindA IndividualA
  given actual:
    ObjectKind(KindA)
    Object(IndividualA)
    IndividualA :: KindA
    KindA ⊑ KindA
    Part(IndividualA, IndividualA)
    Overlap(IndividualA, IndividualA)
  derive_relations
  certify
