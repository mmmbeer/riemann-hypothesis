import Formalism.GaussJetBounds.GenLogInverse

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def UWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (τ : Type w) [Finite τ] [DecidableEq τ] (p : τ → τ)
    (g : τ → MvPowerSeries τ K), (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) →
    ∀ U : MvPowerSeries τ K, Integral U →
    ∀ (ι : Type v) [Fintype ι] (M : τ → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ (sig : ι → ℝ), (∀ i, 0 ≤ sig i) →
      WtGe ‖(l : K)‖ (fun i => rho l + sig i) 0
        (MvPowerSeries.subst (fun x => (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i :
          MvPowerSeries ι K)) (MvPowerSeries.subst g U))

def RCoreA : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) [Fintype ι] (sig : ι → ℝ) (κ : ι →₀ ℕ) (a : ℕ), 1 ≤ a →
      (∀ i, κ i ≤ a) → ∀ (B U : MvPowerSeries ι K), MvPowerSeries.constantCoeff B = 0 →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) n
        (MvPowerSeries.coeff n B)) →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) 0 n (MvPowerSeries.coeff n U)) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (U * mvExp B)‖ ≤
        ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) * (gam l - sig i)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
