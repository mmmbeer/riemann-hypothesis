import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementM

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

def ThmSUniform : Prop :=
  ∀ (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [CompleteSpace K0] (p : ℕ)
    (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, BetaHyp p F be →
    ∃ c : K0, ‖c‖ ≤ 1 ∧ σ (σ c) = c ∧ Simeq be (Gser p c (σ c)) ∧
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K)
      (ν r0 r1 : ℕ) [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) →
    ∀ (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K) (μ : PowerSeries K)
      (U0 Φ : MvPowerSeries (Bool × EV ν r0 r1) K),
      ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (MvPowerSeries.map j be)) →
      InClass (p : K) (hhS p (uS (j c) (j (σ c))))
        (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x) (mvExp (-Φ) * U0))

def GcIsBeta : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ c : K, ‖c‖ ≤ 1 → σ (σ c) = c → BetaHyp p F (Gser p c (σ c))

def GcUnique : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ c d : K, σ (σ c) = c → σ (σ d) = d → Simeq (Gser p c (σ c)) (Gser p d (σ d)) → c = d

def LogCoord : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ) (ϖ : K) (μ : PowerSeries K), 2 ≤ p → (p : K) ≠ 0 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X →
    (PowerSeries.subst (PowerSeries.C ϖ * μ) (lgF K p) : PowerSeries K) =
      PowerSeries.C ϖ * PowerSeries.X

end Formalism.InvariantFactorPaths.G7
