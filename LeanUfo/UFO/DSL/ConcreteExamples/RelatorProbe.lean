import LeanUfo.UFO.DSL.Syntax

/-!
Certified nonempty-relator example.

`RelatorInstance` has two qua-individual proper parts. Each qua individual
inheres in a different bearer, while both share `Foundation`. Their identical
existence profiles provide the mutual existential dependence required by
(a79), and the two bearer links provide the mediation facts required by (a80).

The two qua individuals use the opposite bearer as their external-dependence
target. Their actual-world existence witnesses dependence, while the two
bearer-only worlds witness independence between the distinct bearers.

A measured fresh build of this example took about 22 minutes because
certification checks the complete axiom package over three worlds and ten
things. It is therefore a standalone selected test rather than part of the
examples aggregate or positive seed. Subsequent builds reuse Lean's compiled
artifact.
-/

open LeanUfo.UFO.DSL

ufo_model RelatorProbe : UFO where
  worlds actual bearerAOnly bearerBOnly
  things RelatorType ModeType ObjectType EventType
    RelatorInstance QuaA QuaB BearerA BearerB Foundation

  given everywhere:
    RelatorKind(RelatorType)
    ModeKind(ModeType)
    ObjectKind(ObjectType)
    PerdurantType(EventType)

    Relator(RelatorInstance)
    Mode(QuaA)
    Mode(QuaB)
    Object(BearerA)
    Object(BearerB)
    Perdurant(Foundation)

    RelatorInstance :: RelatorType
    QuaA :: ModeType
    QuaB :: ModeType
    BearerA :: ObjectType
    BearerB :: ObjectType
    Foundation :: EventType

    Part(QuaA, RelatorInstance)
    Part(QuaB, RelatorInstance)
    ProperPart(QuaA, RelatorInstance)
    ProperPart(QuaB, RelatorInstance)

    Overlap(QuaA, RelatorInstance)
    Overlap(RelatorInstance, QuaA)
    Overlap(QuaB, RelatorInstance)
    Overlap(RelatorInstance, QuaB)

    InheresIn(RelatorInstance, BearerA)
    InheresIn(QuaA, BearerA)
    InheresIn(QuaB, BearerB)

    FoundedBy(RelatorInstance, Foundation)
    FoundedBy(QuaA, Foundation)
    FoundedBy(QuaB, Foundation)

    QuaIndividualOf(QuaA, BearerA)
    QuaIndividualOf(QuaB, BearerB)

    Mediates(RelatorInstance, BearerA)
    Mediates(RelatorInstance, BearerB)

  given actual:
    Ex(RelatorInstance)
    Ex(QuaA)
    Ex(QuaB)
    Ex(BearerA)
    Ex(BearerB)
    Ex(Foundation)

  given bearerAOnly:
    Ex(BearerA)

  given bearerBOnly:
    Ex(BearerB)

  derive_relations
  certify
