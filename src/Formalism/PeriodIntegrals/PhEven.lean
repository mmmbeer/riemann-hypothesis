import Formalism.PeriodIntegrals.AddIntG

noncomputable section

namespace PI.PhEven

open PI.AddIntG

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def ePhi {p : ℕ} [Fact p.Prime] (l s : PowerSeries ℂ_[p]) (ep : ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ep⁻¹ * PowerSeries.coeff (n + 1)
    (PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * l) s)

def ph {p : ℕ} [Fact p.Prime] (l s : PowerSeries ℂ_[p]) (ep : ℂ_[p]) : PowerSeries ℂ_[p] := -logMv (ePhi l s ep)

def WqEven : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    W.a₁ = 0 → W.a₃ = 0 → IsWq W wq → ∀ n, Odd n → PowerSeries.coeff n wq = 0

end PI.PhEven

end
