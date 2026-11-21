import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)

omit [NumberField E] [IsCMField E] in
theorem ln_std (n : ℕ) : (⟨stdLat E n⟩ : GenLat E n).Ln = stdLat E n := inf_idem _

omit [NumberField E] [IsCMField E] in

theorem detSet_scale {n : ℕ} (M M' : Submodule (𝓞 E) (Fin n → E)) (a : E)
    (h : ∀ v, v ∈ M' ↔ ∃ w ∈ M, v = a • w) : detSet M' = (fun d => a ^ n * d) '' detSet M := by
  have key : ∀ w : Fin n → Fin n → E, Matrix.det (Matrix.of fun i j => (a • w j) i) =
      a ^ n * Matrix.det (Matrix.of fun i j => w j i) := by
    intro w
    have : (Matrix.of fun i j => (a • w j) i) = a • (Matrix.of fun i j => w j i) := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin]
  ext d
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hw' using fun i => (h (v i)).1 (hv i)
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    have : v = fun j => a • w j := funext hw'
    subst this
    exact (key w).symm
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨fun j => a • w j, fun i => (h _).2 ⟨w i, hw i, rfl⟩, (key w).symm⟩




end GlobalTheory.BetaCounterexample
