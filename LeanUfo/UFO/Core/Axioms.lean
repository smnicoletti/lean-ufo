import LeanUfo.UFO.Core.Signature
import LeanUfo.UFO.Modal.Basics
import LeanUfo.UFO.Modal.FirstOrder

universe u v

variable (Sig : UFOSignature)

open UFOSignature

/--
Axiom (a1):

Type(x) ↔ ◇(∃ y, y :: x)

A Thing x is a Type at world w
iff x is possibly instantiated.
-/
def ax_a1 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Type_ x w ↔
      S5Frame.Dia
        (fun w' => ∃ y : Sig.Thing, Sig.Inst y x w')
        w

/--
Axiom (a2):

Individual(x) ↔ □(¬∃ y, y :: x)

A Thing x is an Individual at world w
iff in every accessible world, nothing instantiates x.
-/
def ax_a2 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Individual x w ↔
      S5Frame.Box
        (fun w' => ¬ ∃ y : Sig.Thing, Sig.Inst y x w')
        w

/--
Axiom (a3):

x :: y → (Type(x) ∨ Individual(x))

If x instantiates y at world w,
then x is either a Type or an Individual at w.
-/
def ax_a3 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Inst x y w →
      (Sig.Type_ x w ∨ Sig.Individual x w)


/--
Axiom (a4):

¬∃ x y z, (Type(x) ∧ x :: y ∧ y :: z)

At no world w do there exist x, y, z such that
x is a Type at w, x instantiates y at w,
and y instantiates z at w.
-/
def ax_a4 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ (x y z : Sig.Thing),
        Sig.Type_ x w ∧
        Sig.Inst x y w ∧
        Sig.Inst y z w


/--
Axiom (t1):

Individual(x) ∨ Type(x)

Every Thing is either an Individual or a Type
at each world.
-/
def ax_t1 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Individual x w ∨ Sig.Type_ x w


/--
Axiom (t2):

¬∃ x, (Individual(x) ∧ Type(x))

No Thing is both an Individual and a Type
at any world.
-/
def ax_t2 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ (x : Sig.Thing),
        Sig.Individual x w ∧ Sig.Type_ x w


/--
A UFO model is a UFOSignature satisfying axioms
(a1)–(a4) and (t1)–(t2).
-/
structure UFOModel extends UFOSignature where
  ax1 : ax_a1 toUFOSignature
  ax2 : ax_a2 toUFOSignature
  ax3 : ax_a3 toUFOSignature
  ax4 : ax_a4 toUFOSignature
  t1  : ax_t1 toUFOSignature
  t2  : ax_t2 toUFOSignature
