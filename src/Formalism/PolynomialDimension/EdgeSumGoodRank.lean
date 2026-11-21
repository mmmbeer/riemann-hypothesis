import Mathlib
import Formalism.PolynomialDimension.StatementNum
import Formalism.PolynomialDimension.FrameSum
import Formalism.SubspaceCounting.Statement

noncomputable section

open scoped BigOperators TensorProduct
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

def ShareProd : Prop :=
  ∀ (J : ℕ) (κ : Fin J → ℝ) (n d : Fin J → ℕ), (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) →
    (∀ j, (1 - κ j) * (d j : ℝ) ≤ n j) →
      (1 - ∑ j, κ j) * ((∏ j, d j : ℕ) : ℝ) ≤ ((∏ j, n j : ℕ) : ℝ)

def MultinomialKLog : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (c k : ℕ) (α : Fin c → ℕ) (a : ℝ), 5 ≤ p → c ≤ k → 1 ≤ a →
    ((∑ i, α i : ℕ) : ℝ) ≤ 2 * a →
      (padicValNat p ((∑ i, α i).factorial / ∏ i, (α i).factorial) : ℝ) ≤ k * Real.logb p a

def dd {K σ : Type} [Field K] (x : σ) (m : ℕ) (f : MvPolynomial σ K) : MvPolynomial σ K :=
  C ((m.factorial : K)⁻¹) * (⇑(pderiv x))^[m] f

def EdgeSumGoodRank : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (B : Type) [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B]
      (M : ℕ) (n : Fin M → ℕ) (β : ∀ e : Fin M, (Fin (n e) → O) →ₗ[O] Module.Dual O B) (D c : ℕ), D < c →
      (∀ (e : Fin M) (x : Fin (n e) → O), (∃ i, ¬ π ∣ x i) →
        ∃ G : B, ¬ π ^ (D + 1) ∣ β e x G ∧ ∀ e', e' ≠ e → ∀ y : Fin (n e') → O, π ^ c ∣ β e' y G) →
        Formalism.G0.GoodRank π (LinearMap.lsum O (fun e : Fin M => Fin (n e) → O) O β) (∑ e, n e) D

end Formalism.CountingSumsFrames
