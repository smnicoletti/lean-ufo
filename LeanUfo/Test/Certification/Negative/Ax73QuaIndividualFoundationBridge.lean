import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax73 fixture.

`Q` is explicitly a qua individual of `B`, and the prerequisite foundation
axioms are satisfied: `Q` is an externally dependent mode with a unique
perdurant foundation.  The first failure is the foundation-based
`QuaIndividualOf` definition, because the required overlap witness `Q` inheres
in `Bearer`, not in `B`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx73QuaIndividualFoundationBridge : UFO where
  worlds actual fOnly bearerOnly
  things MK K Q B Bearer F
  given everywhere:
    ModeKind(MK)
    ObjectKind(K)
    Mode(Q)
    Object(B)
    Object(Bearer)
    Perdurant(F)
    Q :: MK
    B :: K
    Bearer :: K
    InheresIn(Q, Bearer)
    FoundedBy(Q, F)
    QuaIndividualOf(Q, B)
  given actual:
    Ex(Q)
    Ex(F)
    Ex(Bearer)
  given fOnly:
    Ex(F)
  given bearerOnly:
    Ex(Bearer)
  derive_relations
  certify
