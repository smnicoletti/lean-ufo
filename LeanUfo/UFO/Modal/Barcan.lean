import LeanUfo.UFO.Modal.Basics
import LeanUfo.UFO.Modal.FirstOrder

universe u v

variable {F : S5Frame}
variable (D : Type v)

/--
Barcan Formula (constant-domain version):

    □ (∀ x, φ x) → ∀ x, □ (φ x)

If it is necessary that every individual satisfies φ,
then for each individual x, it is necessary that φ holds of x.
-/

theorem barcan
  (φ : D → F.World → Prop)
  (w : F.World) :
  (□[F] (∀₀[D] φ)) w →
  (∀₀[D] (fun x => (□[F] (φ x)))) w :=
by
  intro h
  intro d
  intro v
  intro hv
  exact (h v hv) d

theorem converse_barcan
  (φ : D → F.World → Prop)
  (w : F.World) :
  ForallD D (fun x => S5Frame.Box (F := F) (φ x)) w →
  S5Frame.Box (F := F) (ForallD D φ) w :=
by
  intro h
  intro v
  intro r
  intro d
  exact h d v r
