import Formalism.GL3MeanSquares.QuadraticFormLowerBound

namespace Formalism.HermitianLattices.FormalDegreeBoundsAlt

open Finset MeasureTheory Filter Topology
open Formalism.LogVandermondeBounds.StandardLattice
open scoped ComplexOrder

noncomputable def cbW {N i : ℕ} (hi : i ≤ N) (U : Matrix (Fin N) (Fin N) ℂ)
    (S : {S : Finset (Fin N) // S.card = i}) : ℝ :=
  ‖(U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det‖ ^ 2

noncomputable def sh (u : ℝ) : ℝ := if u = 0 then 1 else Real.sinh u / u

def UnitaryConjugateDiagonalMoments : Prop :=
  ∀ (N i : ℕ) (hi : i ≤ N) (U : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℝ),
    U ∈ Matrix.unitaryGroup (Fin N) ℂ →
    let X : Matrix (Fin N) (Fin N) ℂ := U * Matrix.diagonal (fun s => ((x s : ℝ) : ℂ)) * U.conjTranspose
    let trA : ℝ := ∑ a : Fin i, (X (Fin.castLE hi a) (Fin.castLE hi a)).re
    (∑ S : {S : Finset (Fin N) // S.card = i}, cbW hi U S) = 1 ∧
    (∑ S : {S : Finset (Fin N) // S.card = i}, cbW hi U S * ∑ s ∈ S.1, x s) = trA ∧
    (∑ S : {S : Finset (Fin N) // S.card = i}, cbW hi U S * (∑ s ∈ S.1, x s) ^ 2) =
      trA ^ 2 + ∑ a, ∑ b ∈ univ.filter (fun b : Fin N => b.val < i ∧ i ≤ a.val), ‖X a b‖ ^ 2

noncomputable def cloudV (c Δ : ℝ) : ℕ → ℝ := fun l => c - 4 * Δ * l

noncomputable def wordU (c Δ : ℝ) (δ : ℕ → ℕ) : ℕ → ℝ := fun l => cloudV c Δ l - 1 / 2 - (δ l : ℝ) * Δ

noncomputable def colU (k : ℕ) (c Δ : ℝ) (δ : ℕ → ℕ) (u0 uk : ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then u0 else if i = k - 1 then uk else wordU c Δ δ (i - 1)

def VandermondeVariationExplicit : Prop :=
  ∀ (k : ℕ) (c Δ u0 uk : ℝ) (δ δ' : ℕ → ℕ), 2 ≤ k → 0 < Δ → (∀ l, δ l ≤ 1) → (∀ l, δ' l ≤ 1) →
    4 * (k : ℝ) * Δ ≤ u0 - cloudV c Δ 0 →
    (uk = cloudV c Δ (k - 2) - 1 / 2 ∨ ∀ l, l < k - 2 → 4 * (k : ℝ) * Δ ≤ cloudV c Δ l - 1 / 2 - Δ - uk) →
    |Real.log (vandN (colU k c Δ δ u0 uk) k) - Real.log (vandN (colU k c Δ δ' u0 uk) k)| ≤
      (k : ℝ) * (1 + Real.log k) + 2

end Formalism.HermitianLattices.FormalDegreeBoundsAlt
