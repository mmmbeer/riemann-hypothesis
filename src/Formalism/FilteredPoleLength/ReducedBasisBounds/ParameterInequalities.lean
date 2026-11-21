import Mathlib

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset Matrix
open scoped RealInnerProductSpace BigOperators

def CompletingSquare : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (q : ℝ), 0 < q → ∀ χ : V,
      (∀ u : V, -(B χ χ / 2) / q ≤ B χ u + q * (B u u / 2)) ∧
      B χ ((-(1 / q)) • χ) + q * (B ((-(1 / q)) • χ) ((-(1 / q)) • χ) / 2) = -(B χ χ / 2) / q

def PackingCount : Prop :=
  ∀ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin n))) (δ R : ℝ), 0 < δ → δ ≤ R →
    (∀ x ∈ P, ‖x‖ ≤ R) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) →
    (P.card : ℝ) ≤ (3 * R / δ) ^ n

def DetPerturbation : Prop :=
  ∀ (𝕜 : Type) [NormedField 𝕜] (i : ℕ) (κ : Type) [Fintype κ] (w : κ → Fin i → 𝕜)
    (σ₀ : Fin i → κ) (ε : Fin i → κ → 𝕜) (Δmax : ℝ),
    (∀ σ : Fin i → κ, ‖(Matrix.of fun a j => w (σ j) a).det‖ ≤ Δmax) →
    ‖(Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det -
        (Matrix.of fun a j => w (σ₀ j) a).det‖ ≤
      ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax

def DetPerturbNumeric : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ - 1 ≤ 1 / 2

def CauchyBinetMax : Prop :=
  ∀ (i N r : ℕ) (M : Matrix (Fin i) (Fin N) ℂ), M * Mᴴ = 1 → N ≤ r →
    ∃ s : Fin i → Fin N, StrictMono s ∧ (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(M.submatrix id s).det‖

def ParameterInequalities : Prop :=
  ∀ (q RR PP DF M0 T g0 Cd : ℝ), 1 ≤ RR → 1 ≤ PP → 1 ≤ DF → 0 ≤ M0 → 0 ≤ T → 0 ≤ g0 →
    (M0 < PP → RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → DF * M0 < q) ∧
    (0 < q → T * g0 * RR * PP * DF ^ 2 ≤ q → T * (RR * PP * DF ^ 2 / q) * g0 ≤ 1) ∧
    (0 < q → 2 * Cd ≤ RR * PP → 2 * Cd * DF ^ 2 / q ≤ RR * PP * DF ^ 2 / q)

end Formalism.LatticeBaseChangeAlt
