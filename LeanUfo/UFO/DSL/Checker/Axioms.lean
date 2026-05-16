import LeanUfo.UFO.DSL.Checker.Steps

/-!
# Boolean checks for reflective finite-model certification

These explicit Boolean finite-model checks mirror the corresponding UFO axioms
over the compiled finite tables and derived finite predicates.  Generated DSL
certificates use these checkers through reusable soundness theorems.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

def impliesB (p q : Bool) : Bool :=
  !p || q

def iffB (p q : Bool) : Bool :=
  (p && q) || (!p && !q)

def typeB (M : FiniteModel4) (x : Fin M.thingCount) (_w : Fin M.worldCount) : Bool :=
  anyWorlds M fun v => anyThings M fun y => M.inst y x v

def individualB (M : FiniteModel4) (x : Fin M.thingCount) (_w : Fin M.worldCount) : Bool :=
  !(anyWorlds M fun v => anyThings M fun y => M.inst y x v)

def subDefB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  typeB M x w && typeB M y w &&
    decide (∀ w' : Fin M.worldCount, ∀ z : Fin M.thingCount,
      M.inst z x w' = true → M.inst z y w' = true)

def boxExImpB
    (M : FiniteModel4) (x y : Fin M.thingCount) (_w : Fin M.worldCount) : Bool :=
  decide (∀ w' : Fin M.worldCount, M.ex x w' = true → M.ex y w' = true)

def externallyDependentB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    ((∀ w' : Fin M.worldCount, M.ex x w' = true → M.ex y w' = true) ∧
      ∀ z : Fin M.thingCount,
        M.inheresIn x z w = true →
          ((∃ w' : Fin M.worldCount, M.ex y w' = true ∧ M.ex z w' = false) ∧
           ∃ w' : Fin M.worldCount, M.ex z w' = true ∧ M.ex y w' = false))

def externallyDependentModeB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (M.mode x w = true ∧
      ∃ y : Fin M.thingCount,
        (∀ w' : Fin M.worldCount, M.ex x w' = true → M.ex y w' = true) ∧
          ∀ z : Fin M.thingCount,
            M.inheresIn x z w = true →
              ((∃ w' : Fin M.worldCount, M.ex y w' = true ∧ M.ex z w' = false) ∧
               ∃ w' : Fin M.worldCount, M.ex z w' = true ∧ M.ex y w' = false))

def existsUniqueFoundedByB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ y : Fin M.thingCount,
      M.foundedBy x y w = true ∧
        ∀ z : Fin M.thingCount, M.foundedBy x z w = true → z = y)

def sameFoundationB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  anyThings M fun u => M.foundedBy x u w && M.foundedBy y u w

def existsUniqueInstInheresB
    (M : FiniteModel4) (z t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ y : Fin M.thingCount,
      M.inst y t w = true ∧ M.inheresIn z y w = true ∧
        ∀ y' : Fin M.thingCount,
          M.inst y' t w = true ∧ M.inheresIn z y' w = true → y' = y)

/-!
`ax68` is about `UltimateBearerOf`, whose definition uses the inductive
transitive closure `MomentOf`. The terminal-direct predicates cover the
one-step bearer case, and the reachability predicates below implement the
bounded finite closure used by the checker-backed `ax68` certificate.
-/

def terminalDirectBearerB
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.inheresIn m b w && !(M.moment b w) &&
    (allThings M fun z => !(M.inheresIn b z w))

def existsUniqueTerminalDirectBearerB
    (M : FiniteModel4) (m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ b : Fin M.thingCount,
      terminalDirectBearerB M m b w = true ∧
        ∀ z : Fin M.thingCount, M.inheresIn m z w = true → z = b)

def reachableInheresInFuel
    (M : FiniteModel4) : Nat → Fin M.thingCount → Fin M.thingCount → Fin M.worldCount → Bool
  | 0, _m, _b, _w => false
  | fuel + 1, m, b, w =>
      M.inheresIn m b w ||
        (anyThings M fun y => M.inheresIn m y w && reachableInheresInFuel M fuel y b w)

def reachableInheresInVia
    (M : FiniteModel4) (pivots : List (Fin M.thingCount))
    (m b : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  match pivots with
  | [] => decide (m = b) || M.inheresIn m b w
  | List.cons pivot pivots =>
      reachableInheresInVia M pivots m b w ||
        (reachableInheresInVia M pivots m pivot w &&
          reachableInheresInVia M pivots pivot b w)

def reachableInheresInB
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  reachableInheresInVia M (List.finRange M.thingCount) m b w

def ultimateBearerOfB
    (M : FiniteModel4) (b m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  !(M.moment b w) && reachableInheresInB M m b w

def existsUniqueUltimateBearerB
    (M : FiniteModel4) (m : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ b : Fin M.thingCount,
      ultimateBearerOfB M b m w = true ∧
        ∀ b' : Fin M.thingCount, ultimateBearerOfB M b' m w = true → b' = b)

def checkAx68Closure
    (M : FiniteModel4) : Bool :=
  allThings M fun m =>
    allWorlds M fun w =>
      impliesB (M.moment m w) (existsUniqueUltimateBearerB M m w)

def checkAx1 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (typeB M x w) (anyWorlds M fun v => anyThings M fun y => M.inst y x v)

def checkAx2 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (individualB M x w)
        (allWorlds M fun v => !(anyThings M fun y => M.inst y x v))

def checkAx3 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.inst x y w) (typeB M x w || individualB M x w)

def checkAx4 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      allThings M fun y =>
        allThings M fun z =>
          !(typeB M x w && M.inst x y w && M.inst y z w)

def checkAx5 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (M.sub x y w) (subDefB M x y w)

def checkAx6 (M : FiniteModel4) : Bool :=
  allThings M fun t1 =>
    allThings M fun t2 =>
      allThings M fun x =>
        allWorlds M fun w =>
          impliesB
            (M.inst x t1 w && M.inst x t2 w && !(M.sub t1 t2 w) && !(M.sub t2 t1 w))
            ((anyThings M fun t3 =>
              M.sub t1 t3 w && M.sub t2 t3 w && M.inst x t3 w) ||
             (anyThings M fun t3 =>
              M.sub t3 t1 w && M.sub t3 t2 w && M.inst x t3 w))

def checkAx7 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.concreteIndividual x w) (individualB M x w)

def checkAx8 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.abstractIndividual x w) (individualB M x w)

def checkAx9 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.concreteIndividual x w) (!(M.abstractIndividual x w))

def checkAx10 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (individualB M x w) (M.concreteIndividual x w || M.abstractIndividual x w)

def checkAx11 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.endurant x w) (M.concreteIndividual x w)

def checkAx12 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.perdurant x w) (M.concreteIndividual x w)

def checkAx13 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.endurant x w) (!(M.perdurant x w))

def checkAx14 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (M.concreteIndividual x w) (M.endurant x w || M.perdurant x w)

def checkAx15 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.endurantType x w) (typeB M x w)

def checkAx16 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.perdurantType x w) (typeB M x w)

def checkAx17 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.endurantType x w) (!(M.perdurantType x w))

def checkAx18 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.rigid t w)
        (M.endurantType t w &&
          allThings M fun x =>
            impliesB
              (anyWorlds M fun v => M.inst x t v)
              (allWorlds M fun v => M.inst x t v))

def checkAx19 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.antiRigid t w)
        (M.endurantType t w &&
          allThings M fun x =>
            impliesB
              (anyWorlds M fun v => M.inst x t v)
              (anyWorlds M fun v => !(M.inst x t v)))

def checkAx20 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.semiRigid t w)
        (M.endurantType t w && !(M.rigid t w) && !(M.antiRigid t w))

def checkAx21 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.endurant x w)
        (anyThings M fun k => M.kind k w && (allWorlds M fun v => M.inst x k v))

def checkAx22 (M : FiniteModel4) : Bool :=
  allThings M fun k =>
    allThings M fun x =>
      allWorlds M fun w =>
        impliesB (M.kind k w && M.inst x k w)
          (!(anyWorlds M fun v =>
            anyThings M fun z =>
              M.kind z v && M.inst x z v && decide (z ≠ k)))

def checkAx23 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.sortal t w)
        (M.endurantType t w &&
          anyThings M fun k =>
            M.kind k w &&
              (allWorlds M fun v =>
                allThings M fun x =>
                  impliesB (M.inst x t v) (M.inst x k v)))

def checkAx24 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.nonSortal t w) (M.endurantType t w && !(M.sortal t w))

def checkAx25 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun t =>
      !(M.kind t w && M.subKind t w)

def checkAx26 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.kind t w || M.subKind t w) (M.rigid t w && M.sortal t w)

def checkAx27 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun t =>
      !(M.phase t w && M.role t w)

def checkAx28 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.phase t w || M.role t w) (M.antiRigid t w && M.sortal t w)

def checkAx29 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.semiRigidSortal t w) (M.semiRigid t w && M.sortal t w)

def checkAx30 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.category t w) (M.rigid t w && M.nonSortal t w)

def checkAx31 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.mixin t w) (M.semiRigid t w && M.nonSortal t w)

def checkAx32 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun t =>
      !(M.phaseMixin t w && M.roleMixin t w)

def checkAx33 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.phaseMixin t w || M.roleMixin t w) (M.antiRigid t w && M.nonSortal t w)

def checkAxInstEndurant (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allThings M fun x =>
      allWorlds M fun w =>
        impliesB (M.endurantType t w && M.inst x t w) (M.endurant x w)

def checkAxSubKindSortal (M : FiniteModel4) : Bool :=
  allThings M fun a =>
    allThings M fun k =>
      allWorlds M fun w =>
        impliesB (M.sub a k w && M.kind k w) (M.sortal a w)

def checkAxNonSortalUp (M : FiniteModel4) : Bool :=
  allThings M fun a =>
    allThings M fun b =>
      allWorlds M fun w =>
        impliesB (M.nonSortal a w && M.sub a b w) (M.nonSortal b w)

def checkAxKindStable (M : FiniteModel4) : Bool :=
  allThings M fun k =>
    allWorlds M fun w =>
      allWorlds M fun v =>
        impliesB (M.kind k w) (M.kind k v)

def qualityB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ t : Fin M.thingCount,
      (M.qualityKind t w = true ∧ M.inst x t w = true) ∧
        ∀ t' : Fin M.thingCount,
          M.qualityKind t' w = true ∧ M.inst x t' w = true → t' = t)

def qualityStructureB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ t : Fin M.thingCount,
      (M.qualityType t w = true ∧ M.associatedWith x t w = true) ∧
        ∀ t' : Fin M.thingCount,
          M.qualityType t' w = true ∧ M.associatedWith x t' w = true → t' = t)

def simpleQualityB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  qualityB M x w && (allThings M fun y => !(M.inheresIn y x w))

def complexQualityB (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  qualityB M x w && !(simpleQualityB M x w)

def simpleQualityTypeB (M : FiniteModel4) (t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.qualityType t w &&
    (allThings M fun x => impliesB (M.inst x t w) (simpleQualityB M x w))

def complexQualityTypeB (M : FiniteModel4) (t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.qualityType t w &&
    (allThings M fun x => impliesB (M.inst x t w) (complexQualityB M x w))

def nonEmptySetB (M : FiniteModel4) (s : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  anyThings M fun x => M.memberOf x s w

def properSubsetB (M : FiniteModel4) (s t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  (allThings M fun x => impliesB (M.memberOf x s w) (M.memberOf x t w)) &&
    (anyThings M fun x => M.memberOf x t w && !(M.memberOf x s w))

def existsUniqueQualityStructureMemberB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ s : Fin M.thingCount,
      (qualityStructureB M s w = true ∧ M.memberOf x s w = true) ∧
        ∀ s' : Fin M.thingCount,
          qualityStructureB M s' w = true ∧ M.memberOf x s' w = true → s' = s)

def existsUniqueHasValueB
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide
    (∃ y : Fin M.thingCount,
      M.hasValue x y w = true ∧
        ∀ y' : Fin M.thingCount, M.hasValue x y' w = true → y' = y)

def checkAx34 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (M.substantial x w || M.moment x w) (M.endurant x w)

def checkAx35 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      !(M.substantial x w && M.moment x w)

def checkAx36 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (M.object x w || M.collective x w || M.quantity x w) (M.substantial x w)

def checkAx37 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      !(M.object x w && M.collective x w)

def checkAx38 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      !(M.object x w && M.quantity x w)

def checkAx39 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      !(M.collective x w && M.quantity x w)

def checkAx40 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (M.relator x w || M.intrinsicMoment x w) (M.moment x w)

def checkAx41 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      !(M.relator x w && M.intrinsicMoment x w)

def checkAx42 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (M.mode x w || qualityB M x w) (M.intrinsicMoment x w)

def checkAx43 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      !(M.mode x w && qualityB M x w)

def typeByInstancesB
    (M : FiniteModel4)
    (typePred leafPred : Fin M.thingCount → Fin M.worldCount → Bool) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (typePred t w)
        (typeB M t w &&
          (allWorlds M fun v =>
            allThings M fun x =>
              impliesB (M.inst x t v) (leafPred x v)))

def checkAx44 (M : FiniteModel4) : Bool :=
  typeByInstancesB M M.endurantType M.endurant &&
  typeByInstancesB M M.perdurantType M.perdurant &&
  typeByInstancesB M M.substantialType M.substantial &&
  typeByInstancesB M M.momentType M.moment &&
  typeByInstancesB M M.objectType M.object &&
  typeByInstancesB M M.collectiveType M.collective &&
  typeByInstancesB M M.quantityType M.quantity &&
  typeByInstancesB M M.relatorType M.relator &&
  typeByInstancesB M M.modeType M.mode &&
  typeByInstancesB M M.qualityType (qualityB M)

def kindByTypeB
    (M : FiniteModel4)
    (kindPred typePred : Fin M.thingCount → Fin M.worldCount → Bool) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (kindPred t w) (typePred t w && M.kind t w)

def checkAx45 (M : FiniteModel4) : Bool :=
  kindByTypeB M M.objectKind M.objectType &&
  kindByTypeB M M.collectiveKind M.collectiveType &&
  kindByTypeB M M.quantityKind M.quantityType &&
  kindByTypeB M M.relatorKind M.relatorType &&
  kindByTypeB M M.modeKind M.modeType &&
  kindByTypeB M M.qualityKind M.qualityType

def specificEndurantKindB (M : FiniteModel4) (k : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.objectKind k w || M.collectiveKind k w || M.quantityKind k w ||
    M.relatorKind k w || M.modeKind k w || M.qualityKind k w

def checkAx46 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.endurant x w)
        (anyWorlds M fun v =>
          anyThings M fun k =>
            specificEndurantKindB M k v && M.inst x k v)

def checkAx47 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      M.part x x w

def checkAx48 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.part x y w && M.part y x w) (decide (x = y))

def checkAx49 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun z =>
        allWorlds M fun w =>
          impliesB (M.part x y w && M.part y z w) (M.part x z w)

def checkAx50 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (M.overlap x y w)
          (anyThings M fun z => M.part z x w && M.part z y w)

def checkAx51 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (!(M.part y x w))
          (anyThings M fun z => M.part z y w && !(M.overlap z x w))

def checkAx52 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (M.properPart x y w) (M.part x y w && !(M.part y x w))

def genericFunctionalDependenceB
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  allThings M fun x =>
    impliesB (M.inst x x' w && M.functionsAs x x' w)
      (anyThings M fun y =>
        decide (y ≠ x) && M.inst y y' w && M.functionsAs y y' w)

def individualFunctionalDependenceB
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  genericFunctionalDependenceB M x' y' w &&
    M.inst x x' w && M.inst y y' w &&
      impliesB (M.functionsAs x x' w) (M.functionsAs y y' w)

def checkAx53 (M : FiniteModel4) : Bool :=
  allThings M fun x' =>
    allThings M fun y' =>
      allWorlds M fun w =>
        iffB (genericFunctionalDependenceB M x' y' w)
          (genericFunctionalDependenceB M x' y' w)

def checkAx54 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun x' =>
      allThings M fun y =>
        allThings M fun y' =>
          allWorlds M fun w =>
            iffB (individualFunctionalDependenceB M x x' y y' w)
              (individualFunctionalDependenceB M x x' y y' w)

def checkAx55 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun x' =>
      allThings M fun y =>
        allThings M fun y' =>
          allWorlds M fun w =>
            iffB (M.properPart x y w && individualFunctionalDependenceB M x x' y y' w)
              (M.properPart x y w && individualFunctionalDependenceB M x x' y y' w)

def checkAx56 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.constitutedBy x y w)
          (iffB (M.endurant x w) (M.endurant y w) &&
           iffB (M.perdurant x w) (M.perdurant y w))

def checkAx57 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun x' =>
        allThings M fun y' =>
          allWorlds M fun w =>
            impliesB
              (M.constitutedBy x y w && M.inst x x' w && M.inst y y' w &&
                M.kind x' w && M.kind y' w)
              (decide (x' ≠ y'))

def genericConstitutionalDependenceB
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  allThings M fun x =>
    impliesB (M.inst x x' w)
      (anyThings M fun y => M.inst y y' w && M.constitutedBy x y w)

def constitutionB
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  M.inst x x' w && M.inst y y' w &&
    genericConstitutionalDependenceB M x' y' w && M.constitutedBy x y w

def checkAx58 (M : FiniteModel4) : Bool :=
  allThings M fun x' =>
    allThings M fun y' =>
      allWorlds M fun w =>
        iffB (genericConstitutionalDependenceB M x' y' w)
          (genericConstitutionalDependenceB M x' y' w)

def checkAx59 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun x' =>
      allThings M fun y =>
        allThings M fun y' =>
          allWorlds M fun w =>
            iffB (constitutionB M x x' y y' w)
              (constitutionB M x x' y y' w)

def checkAx60 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.perdurant x w && M.constitutedBy x y w)
          (allWorlds M fun v => impliesB (M.ex x v) (M.constitutedBy x y v))

def checkAx61 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.constitutedBy x y w) (!(M.constitutedBy y x w))

def checkAx62 (M : FiniteModel4) : Bool :=
  allThings M fun _x =>
    allWorlds M fun _w =>
      true

def existentialDependenceB
    (M : FiniteModel4) (x y : Fin M.thingCount) (_w : Fin M.worldCount) : Bool :=
  allWorlds M fun v => impliesB (M.ex x v) (M.ex y v)

def existentialIndependenceB
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  !(existentialDependenceB M x y w) && !(existentialDependenceB M y x w)

def checkAx63 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (existentialDependenceB M x y w) (existentialDependenceB M x y w)

def checkAx64 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (existentialIndependenceB M x y w) (existentialIndependenceB M x y w)

def checkAx65 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.inheresIn x y w) (existentialDependenceB M x y w)

def checkAx66 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.inheresIn x y w)
          (M.moment x w && (typeB M y w || M.concreteIndividual y w))

def checkAx67 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun z =>
        allWorlds M fun w =>
          impliesB (M.inheresIn x y w && M.inheresIn x z w) (decide (y = z))

def checkAx68 (M : FiniteModel4) : Bool :=
  checkAx68Closure M

def checkAx69 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (externallyDependentB M x y w) (externallyDependentB M x y w)

def checkAx70 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (externallyDependentModeB M x w) (externallyDependentModeB M x w)

def checkAx71 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.foundedBy x y w)
          ((externallyDependentModeB M x w || M.relator x w) && M.perdurant y w)

def checkAx72 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (externallyDependentModeB M x w) (existsUniqueFoundedByB M x w)

def checkAx73 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (M.quaIndividualOf x y w)
          (allThings M fun z =>
            iffB (M.overlap z x w)
              (externallyDependentModeB M z w &&
                M.inheresIn z y w &&
                sameFoundationB M z x w))

def checkAx77 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.relator x w) (existsUniqueFoundedByB M x w)

def checkAx74 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (anyThings M fun y => M.quaIndividualOf x y w)
        (anyThings M fun y => M.quaIndividualOf x y w)

def checkAx75 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (anyThings M fun y => M.quaIndividualOf x y w)
        (externallyDependentModeB M x w)

def checkAx76 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun y' =>
        allWorlds M fun w =>
          impliesB (M.quaIndividualOf x y w && M.quaIndividualOf x y' w)
            (decide (y = y'))

def checkAx78 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.relator x w && M.part y x w) (sameFoundationB M x y w)

def checkAx79 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (M.relator x w)
        ((anyThings M fun y => M.properPart y x w) &&
          (allThings M fun y =>
            allThings M fun z =>
              impliesB (M.properPart y x w && M.properPart z x w)
                ((anyThings M fun q => M.quaIndividualOf y q w) &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)) &&
          (allThings M fun y =>
            allThings M fun z =>
              impliesB
                (M.properPart y x w &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)
                (M.properPart z x w)))

def checkAx80 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (M.mediates x y w)
          (M.relator x w && M.endurant y w &&
            (anyThings M fun z => M.quaIndividualOf z y w && M.part z x w))

def checkAxQuaIndividualOfEndurant (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.quaIndividualOf x y w) (M.endurant y w)

def checkAx81 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allThings M fun m =>
      allWorlds M fun w =>
        impliesB (M.characterization t m w)
          (M.endurantType t w &&
            M.momentType m w &&
            (allThings M fun x =>
              impliesB (M.inst x t w)
                (anyThings M fun y => M.inst y m w && M.inheresIn y x w)) &&
            (allThings M fun z =>
              impliesB (M.inst z m w) (existsUniqueInstInheresB M z t w)))

def checkAx82 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allThings M fun q =>
      allWorlds M fun w =>
        impliesB (M.characterization t q w && M.qualityType q w)
          (allThings M fun x =>
            impliesB (M.inst x q w) (existsUniqueInstInheresB M x t w))

def checkAx83 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.quale x w) (M.abstractIndividual x w)

def checkAx84 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.set_ x w) (M.abstractIndividual x w)

def checkAx85 (M : FiniteModel4) : Bool :=
  allWorlds M fun w =>
    allThings M fun x =>
      !(M.quale x w && M.set_ x w)

def checkAx86 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (qualityStructureB M x w) (M.set_ x w && nonEmptySetB M x w)

def checkAx87 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (M.quale x w) (existsUniqueQualityStructureMemberB M x w)

def checkAx88 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      iffB (qualityStructureB M x w) (M.qualityDomain x w || M.qualityDimension x w)

def checkAx89 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (M.qualityDomain x w) (!(M.qualityDimension x w))

def checkAx90 (M : FiniteModel4) : Bool :=
  allThings M fun s =>
    allThings M fun t =>
      allThings M fun s' =>
        allThings M fun t' =>
          allWorlds M fun w =>
            impliesB (M.associatedWith s t w && M.associatedWith s' t' w &&
              (M.sub t' t w && !(M.sub t t' w))) (properSubsetB M s' s w)

def checkAx91 (M : FiniteModel4) : Bool :=
  allThings M fun t =>
    allWorlds M fun w =>
      iffB (M.qualityType t w)
        (M.intrinsicMomentType t w &&
          decide
            (∃ x : Fin M.thingCount,
              (qualityStructureB M x w = true ∧ M.associatedWith x t w = true) ∧
                ∀ x' : Fin M.thingCount,
                  qualityStructureB M x' w = true ∧ M.associatedWith x' t w = true → x' = x))

def checkAx92 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.hasValue x y w) (qualityB M x w && M.quale y w)

def checkAx93 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (qualityB M x w) (existsUniqueHasValueB M x w)

def checkAx94 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.hasValue x y w)
          (anyThings M fun t =>
            anyThings M fun s =>
              M.inst x t w && M.associatedWith s t w && M.memberOf y s w)

def checkAx95 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.associatedWith x y w)
          (iffB (M.qualityDimension x w) (simpleQualityTypeB M y w))

def checkAx96 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.associatedWith x y w)
          (iffB (M.qualityDomain x w) (complexQualityTypeB M y w))

def checkAx97 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun z =>
        allThings M fun Y =>
          allThings M fun Z =>
            allWorlds M fun w =>
              impliesB
                (complexQualityB M x w && M.inst y Y w && M.inst z Z w &&
                  M.inheresIn y x w && M.inheresIn z x w && decide (Y = Z))
                (decide (y = z))

def checkAx98 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allWorlds M fun w =>
      impliesB (complexQualityB M x w)
        (allThings M fun y =>
          impliesB (M.inheresIn y x w) (simpleQualityB M y w))

def productFamilyDimensions
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount) :
    Fin pf.dimensionThings.size → Fin thingCount :=
  fun i => pf.dimensionThings[i]

def productFamilyTypes
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount) :
  Fin pf.dimensionThings.size → Fin thingCount :=
  fun i =>
    let hidx : i.val < pf.typeThings.size := by
      rw [← pf.sameSize]
      exact i.isLt
    pf.typeThings[i.val]'hidx

def productFamilyWitnessProp
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Prop :=
  pf.domain = x ∧ pf.qualityType = t ∧ pf.world = w ∧
    (∀ p : Fin M.thingCount,
      M.memberOf p x w = true →
        ∀ i : Fin pf.dimensionThings.size,
          M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w = true) ∧
    (∀ i : Fin pf.dimensionThings.size,
      M.associatedWith (productFamilyDimensions pf i) (productFamilyTypes pf i) w = true ∧
        M.characterization t (productFamilyTypes pf i) w = true) ∧
    (∀ u : Fin M.thingCount,
      M.characterization t u w = true →
        ∃ i : Fin pf.dimensionThings.size, u = productFamilyTypes pf i)

def allProductFamilyIndices
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount)
    (p : Fin pf.dimensionThings.size → Bool) : Bool :=
  decide (∀ i : Fin pf.dimensionThings.size, p i = true)

def anyProductFamilyIndices
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount)
    (p : Fin pf.dimensionThings.size → Bool) : Bool :=
  decide (∃ i : Fin pf.dimensionThings.size, p i = true)

def anyProductFamilyWitness
    (M : FiniteModel4)
    (p : (pf : ProductFamilyWitness M.thingCount M.worldCount) → Bool) : Bool :=
  decide (∃ i : Fin M.productFamilies.size, p (M.productFamilies[i]) = true)

def productFamilyEntryB
    (M : FiniteModel4) (x t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  anyProductFamilyWitness M fun pf =>
    decide (pf.domain = x ∧ pf.qualityType = t ∧ pf.world = w)

def checkAx99WitnessEntriesPresent (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun t =>
      allWorlds M fun w =>
        impliesB
          (M.qualityDomain x w && M.associatedWith x t w)
          (productFamilyEntryB M x t w)

def productFamilyWitnessB
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) : Bool :=
  decide (pf.domain = x) && decide (pf.qualityType = t) && decide (pf.world = w) &&
    (allThings M fun p =>
      impliesB (M.memberOf p x w)
        (allProductFamilyIndices pf fun i =>
          M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w)) &&
    (allProductFamilyIndices pf fun i =>
      M.associatedWith (productFamilyDimensions pf i) (productFamilyTypes pf i) w &&
        M.characterization t (productFamilyTypes pf i) w) &&
    (allThings M fun u =>
      impliesB (M.characterization t u w)
        (anyProductFamilyIndices pf fun i => decide (u = productFamilyTypes pf i)))

def ax99Finite (M : FiniteModel4) : Prop :=
  ∀ (x t : Fin M.thingCount) (w : Fin M.worldCount),
    (M.qualityDomain x w = true ∧ M.associatedWith x t w = true) →
      ∃ i : Fin M.productFamilies.size,
        productFamilyWitnessProp M (M.productFamilies[i]) x t w

def checkAx99 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun t =>
      allWorlds M fun w =>
        impliesB (M.qualityDomain x w && M.associatedWith x t w)
          (anyProductFamilyWitness M fun pf => productFamilyWitnessB M pf x t w)

def checkAx100 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun r =>
        allWorlds M fun w =>
          impliesB (M.distance x y r w)
            (M.quale x w && M.quale y w &&
              (anyThings M fun z => M.memberOf x z w && M.memberOf y z w))

def checkAx101 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.quale x w && M.quale y w)
          (decide
            (∃ r : Fin M.thingCount,
              M.distance x y r w = true ∧
                ∀ r' : Fin M.thingCount, M.distance x y r' w = true → r' = r))

def checkAx102 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.manifests x y w) (M.perdurant x w && M.endurant y w)

def checkAx103 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        iffB (M.lifeOf x y w)
          (M.perdurant x w && M.endurant y w &&
            (allThings M fun z =>
              iffB (M.overlap z x w) (M.perdurant z w && M.manifests z y w)))

def checkAx104 (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allWorlds M fun w =>
        impliesB (M.meet x y w) (M.perdurant x w && M.perdurant y w)

def checkAx105 (_M : FiniteModel4) : Bool := true

def checkAx106 (_M : FiniteModel4) : Bool := true

def checkAx107 (_M : FiniteModel4) : Bool := true

def checkAx108 (_M : FiniteModel4) : Bool := true

def checkAxDistanceIdentity (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun r =>
        allWorlds M fun w =>
          impliesB (decide (x = y) && M.distance x y r w) (M.distanceZero r w)

def checkAxDistanceSymmetry (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun r =>
        allWorlds M fun w =>
          impliesB (M.distance x y r w) (M.distance y x r w)

def checkAxDistanceTriangle (M : FiniteModel4) : Bool :=
  allThings M fun x =>
    allThings M fun y =>
      allThings M fun z =>
        allThings M fun r0 =>
          allThings M fun r1 =>
            allThings M fun r2 =>
              allThings M fun s =>
                allWorlds M fun w =>
                  impliesB
                    (M.distance x y r0 w && M.distance y z r1 w &&
                      M.distance x z r2 w && M.distanceSum r0 r1 s w)
                    (M.distanceGreaterEq s r2 w)

def checkAx1_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx1 M)

def checkAx2_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx2 M)

def checkAx3_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx3 M)

def checkAx4_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx4 M)

def checkAx5_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx5 M)

def checkAx6_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx6 M)

def checkAx7_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx7 M)

def checkAx8_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx8 M)

def checkAx9_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx9 M)

def checkAx10_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx10 M)

def checkAx11_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx11 M)

def checkAx12_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx12 M)

def checkAx13_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx13 M)

def checkAx14_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx14 M)

def checkAx15_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx15 M)

def checkAx16_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx16 M)

def checkAx17_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx17 M)

def checkAx18_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx18 M)

def checkAx19_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx19 M)

def checkAx20_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx20 M)

def checkAx21_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx21 M)

def checkAx22_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx22 M)

def checkAx23_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx23 M)

def checkAx24_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx24 M)

def checkAx25_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx25 M)

def checkAx26_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx26 M)

def checkAx27_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx27 M)

def checkAx28_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx28 M)

def checkAx29_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx29 M)

def checkAx30_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx30 M)

def checkAx31_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx31 M)

def checkAx32_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx32 M)

def checkAx33_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx33 M)

def checkAxInstEndurant_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxInstEndurant M)

def checkAxSubKindSortal_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxSubKindSortal M)

def checkAxNonSortalUp_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxNonSortalUp M)

def checkAxKindStable_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxKindStable M)

def checkAx34_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx34 M)

def checkAx35_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx35 M)

def checkAx36_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx36 M)

def checkAx37_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx37 M)

def checkAx38_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx38 M)

def checkAx39_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx39 M)

def checkAx40_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx40 M)

def checkAx41_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx41 M)

def checkAx42_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx42 M)

def checkAx43_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx43 M)

def checkAx44_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx44 M)

def checkAx45_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx45 M)

def checkAx46_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx46 M)

def checkAx47_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx47 M)

def checkAx48_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx48 M)

def checkAx49_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx49 M)

def checkAx50_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx50 M)

def checkAx51_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx51 M)

def checkAx52_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx52 M)

def checkAx53_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx53 M)

def checkAx54_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx54 M)

def checkAx55_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx55 M)

def checkAx56_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx56 M)

def checkAx57_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx57 M)

def checkAx58_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx58 M)

def checkAx59_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx59 M)

def checkAx60_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx60 M)

def checkAx61_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx61 M)

def checkAx62_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx62 M)

def checkAx63_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx63 M)

def checkAx64_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx64 M)

def checkAx65_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx65 M)

def checkAx66_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx66 M)

def checkAx67_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx67 M)

def checkAx68_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx68 M)

def checkAx69_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx69 M)

def checkAx70_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx70 M)

def checkAx71_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx71 M)

def checkAx72_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx72 M)

def checkAx73_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx73 M)

def checkAx77_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx77 M)

def checkAx74_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx74 M)

def checkAx75_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx75 M)

def checkAx76_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx76 M)

def checkAx78_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx78 M)

def checkAx79_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx79 M)

def checkAx80_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx80 M)

def checkAxQuaIndividualOfEndurant_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxQuaIndividualOfEndurant M)

def checkAx81_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx81 M)

def checkAx82_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx82 M)

def checkAx83_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx83 M)

def checkAx84_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx84 M)

def checkAx85_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx85 M)

def checkAx86_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx86 M)

def checkAx87_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx87 M)

def checkAx88_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx88 M)

def checkAx89_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx89 M)

def checkAx90_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx90 M)

def checkAx91_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx91 M)

def checkAx92_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx92 M)

def checkAx93_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx93 M)

def checkAx94_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx94 M)

def checkAx95_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx95 M)

def checkAx96_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx96 M)

def checkAx97_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx97 M)

def checkAx98_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx98 M)

def checkAx99_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx99 M)

def checkAx100_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx100 M)

def checkAx101_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx101 M)

def checkAx102_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx102 M)

def checkAx103_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx103 M)

def checkAx104_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx104 M)

def checkAx105_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx105 M)

def checkAx106_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx106 M)

def checkAx107_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx107 M)

def checkAx108_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAx108 M)

def checkAxDistanceIdentity_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxDistanceIdentity M)

def checkAxDistanceSymmetry_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxDistanceSymmetry M)

def checkAxDistanceTriangle_S (M : FiniteModel4) : Stepped Bool :=
  Stepped.axiomEnvelope M (checkAxDistanceTriangle M)

def checkAxiomsPilot (M : FiniteModel4) : Bool :=
  checkAx1 M && checkAx2 M && checkAx3 M && checkAx4 M && checkAx5 M &&
    checkAx6 M && checkAx7 M && checkAx8 M && checkAx9 M && checkAx10 M &&
    checkAx11 M && checkAx12 M && checkAx13 M && checkAx14 M && checkAx15 M &&
    checkAx16 M && checkAx17 M && checkAx18 M && checkAx19 M && checkAx20 M &&
    checkAx21 M && checkAx22 M && checkAx23 M && checkAx24 M && checkAx25 M &&
    checkAx26 M && checkAx27 M && checkAx28 M && checkAx29 M && checkAx30 M &&
    checkAx31 M && checkAx32 M && checkAx33 M && checkAxInstEndurant M &&
    checkAxSubKindSortal M && checkAxNonSortalUp M && checkAxKindStable M &&
    checkAx34 M && checkAx35 M && checkAx36 M && checkAx37 M && checkAx38 M &&
    checkAx39 M && checkAx40 M && checkAx41 M && checkAx42 M && checkAx43 M &&
    checkAx44 M && checkAx45 M && checkAx46 M &&
    checkAx47 M && checkAx48 M && checkAx49 M && checkAx50 M &&
    checkAx51 M && checkAx52 M &&
    checkAx53 M && checkAx54 M && checkAx55 M &&
    checkAx56 M && checkAx57 M && checkAx58 M && checkAx59 M && checkAx60 M &&
    checkAx61 M && checkAx62 M && checkAx63 M && checkAx64 M &&
    checkAx65 M && checkAx66 M && checkAx67 M && checkAx68 M &&
    checkAx69 M && checkAx70 M && checkAx71 M && checkAx72 M && checkAx73 M &&
    checkAx74 M && checkAx75 M && checkAx76 M && checkAx77 M && checkAx78 M &&
    checkAx79 M && checkAx80 M && checkAxQuaIndividualOfEndurant M &&
    checkAx81 M && checkAx82 M

def checkAxiomsPilot_S (M : FiniteModel4) : Stepped Bool :=
  { value := checkAxiomsPilot M
    steps := 89 * Stepped.polyEnvelope M + 88 }

def checkAxioms4Checks (M : FiniteModel4) : List Bool := [
  checkAx1 M, checkAx2 M, checkAx3 M, checkAx4 M, checkAx5 M,
  checkAx6 M, checkAx7 M, checkAx8 M, checkAx9 M, checkAx10 M,
  checkAx11 M, checkAx12 M, checkAx13 M, checkAx14 M, checkAx15 M,
  checkAx16 M, checkAx17 M, checkAx18 M, checkAx19 M, checkAx20 M,
  checkAx21 M, checkAx22 M, checkAx23 M, checkAx24 M, checkAx25 M,
  checkAx26 M, checkAx27 M, checkAx28 M, checkAx29 M, checkAx30 M,
  checkAx31 M, checkAx32 M, checkAx33 M, checkAxInstEndurant M,
  checkAxSubKindSortal M, checkAxNonSortalUp M, checkAxKindStable M,
  checkAx34 M, checkAx35 M, checkAx36 M, checkAx37 M, checkAx38 M,
  checkAx39 M, checkAx40 M, checkAx41 M, checkAx42 M, checkAx43 M,
  checkAx44 M, checkAx45 M, checkAx46 M,
  checkAx47 M, checkAx48 M, checkAx49 M, checkAx50 M,
  checkAx51 M, checkAx52 M,
  checkAx53 M, checkAx54 M, checkAx55 M,
  checkAx56 M, checkAx57 M, checkAx58 M, checkAx59 M, checkAx60 M,
  checkAx61 M, checkAx62 M, checkAx63 M, checkAx64 M,
  checkAx65 M, checkAx66 M, checkAx67 M, checkAx68 M,
  checkAx69 M, checkAx70 M, checkAx71 M, checkAx72 M, checkAx73 M,
  checkAx74 M, checkAx75 M, checkAx76 M, checkAx77 M, checkAx78 M,
  checkAx79 M, checkAx80 M, checkAxQuaIndividualOfEndurant M,
  checkAx81 M, checkAx82 M,
  checkAx83 M, checkAx84 M, checkAx85 M, checkAx86 M, checkAx87 M,
  checkAx88 M, checkAx89 M, checkAx90 M, checkAx91 M, checkAx92 M,
  checkAx93 M, checkAx94 M, checkAx95 M, checkAx96 M, checkAx97 M,
  checkAx98 M, checkAx99 M, checkAx100 M, checkAx101 M,
  checkAxDistanceIdentity M, checkAxDistanceSymmetry M, checkAxDistanceTriangle M,
  checkAx102 M, checkAx103 M, checkAx104 M,
  checkAx105 M, checkAx106 M, checkAx107 M, checkAx108 M
]

def checkAxioms4 (M : FiniteModel4) : Bool :=
  (checkAxioms4Checks M).all id

def checkAxioms4_S (M : FiniteModel4) : Stepped Bool :=
  { value := checkAxioms4 M
    steps := 116 * Stepped.polyEnvelope M + 115 }

end Checker
end LeanUfo.UFO.DSL
