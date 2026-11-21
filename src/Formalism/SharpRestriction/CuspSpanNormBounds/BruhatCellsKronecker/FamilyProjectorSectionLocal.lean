import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section Loc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem umat_mem (g : Formalism.REAL.UJ ε) : umat g ∈ UJset ε := g.2

def homOf (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ) :
    Formalism.REAL.UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (umat g)
  map_one' := h.1.1
  map_mul' a b := h.1.2 _ (umat_mem a) _ (umat_mem b)

theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val


theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have : star z = (starRingEnd ℂ) z := rfl
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem schur_abs {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) (x y : H) :
    Integrable (fun g : Formalism.REAL.UJ ε => ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2) (Formalism.REAL.muG ε) ∧
      ∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨hi, he⟩ := hd.2 x y x y
  have hfun : (fun g : Formalism.REAL.UJ ε => coefOn σ x y g * star (coefOn σ x y g)) =
      fun g : Formalism.REAL.UJ ε => ((‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    exact mul_star_eq _
  rw [hfun] at hi he
  refine ⟨?_, ?_⟩
  · exact hi.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)
  · rw [integral_complex_ofReal] at he
    have h2 : ((∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    exact_mod_cast h2

theorem fdegOf_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : ‖w‖ = 1) : fdegOf (Formalism.REAL.muG ε) σ w = d := by
  unfold fdegOf
  have h := (schur_abs hd w w).2
  have h' : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / d := by
    have : (fun g : Formalism.REAL.UJ ε => ‖coefOn σ w w g‖ ^ 2) = fun g : Formalism.REAL.UJ ε => ‖⟪w, σ (umat g) w⟫_ℂ‖ ^ 2 := rfl
    rw [this, h, hw]
    norm_num
  rw [h', hw]
  have := hd.1
  field_simp

end Loc



end Formalism.MainNotions.BridgeLemma

end
