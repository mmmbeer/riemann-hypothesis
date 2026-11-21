import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VandermondeConjugatePrimes

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section Beta

variable {l : ℕ} [Fact l.Prime]

def zOf (l : ℕ) [Fact l.Prime] {σ : Type} (k : σ) : MvPowerSeries σ ℂ_[l] :=
  PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries σ ℂ_[l]) (logF l)

end Beta

def embAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (x : Fin N → D.host.E) : Fin N → ℂ_[l] × ℂ_[l] :=
  fun k => (lamC lam (embT D τ (x k)), lamC lam (embT D τ (D.host.conj (x k))))

def latAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → ℂ_[l] × ℂ_[l]) :=
  closure (embAt D lam τ '' (L : Set (Fin N → D.host.E)))

def colMat {l : ℕ} [Fact l.Prime] {N : ℕ} (b : Fin N → Fin N → ℂ_[l] × ℂ_[l]) : Matrix (Fin N) (Fin N) ℂ_[l] :=
  Matrix.of fun k a => (b a k).1

open Classical in

def chgO (D : D7) {l : ℕ} [Fact l.Prime] {N N' : ℕ} (c0 : D.what₂.Tau → ℂ_[l])
    (b : D.what₂.Tau → Fin N → Fin N → ℂ_[l] × ℂ_[l]) (b' : D.what₂.Tau → Fin N' → Fin N' → ℂ_[l] × ℂ_[l])
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × Formalism.MainNotions.G.HH D) × Fin N × Fin N') : ℂ_[l] :=
  if tauPl D x.1 = k.1 then c0 k.1 * colMat (b' k.1) k.2.1 x.2.2 * (colMat (b k.1))⁻¹ x.2.1 k.2.2 else 0

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def KerTie {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ)
    {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) (i : ℕ) : Prop :=
  liftTie D (tor0 D cc δ) (B.eNat χ) O i

end GlobalTheory.IndefiniteRowSideFullHecke.VandermondeConjugatePrimes
