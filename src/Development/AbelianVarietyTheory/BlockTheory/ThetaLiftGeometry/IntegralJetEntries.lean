import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries

def JetsIntegral {σ : Type} {l : ℕ} [Fact l.Prime] (F : MvPowerSeries σ ℂ_[l]) : Prop :=
  ∀ a : σ →₀ ℕ, ‖(a.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff a F‖ ≤ 1

def IsRBasis (D : D7) {l : ℕ} [Fact l.Prime] (ρ : D.host.E → ℂ_[l]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (g : Matrix (Fin N) (Fin N) ℂ_[l]) : Prop :=
  g.det ≠ 0 ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range fun a : Fin N => fun k => g k a) =
      Submodule.span 𝓞_ℂ_[l] ((fun (x : Fin N → D.host.E) k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))

open Classical in

def coordCh (D : D7) {l : ℕ} [Fact l.Prime] {N N' : ℕ} (s : D.what₂.Tau → ℂ_[l])
    (g : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[l]) (g' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[l])
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[l] :=
  if tauPl D x.1 = k.1 then s k.1 * g' k.1 k.2.1 x.2.2 * ((g k.1)⁻¹) x.2.1 k.2.2 else 0

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries
