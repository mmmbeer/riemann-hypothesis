import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DualBasesOfSeries

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta
open Classical

def IntJets {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α : σ →₀ ℕ, ‖(α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F‖ ≤ 1

abbrev Var (D : D7) (N N' : ℕ) : Type := (Bool × HH D) × Fin N × Fin N'

def beForm (D : D7) {p : ℕ} [Fact p.Prime] (N N' : ℕ) (u' : HH D → ℂ_[p]) : MvPowerSeries (Var D N N') ℂ_[p] :=
  ∑ t : HH D, MvPowerSeries.C (u' t) * ∑ a : Fin N, ∑ b : Fin N',
    (MvPowerSeries.X ((false, t), a, b) : MvPowerSeries (Var D N N') ℂ_[p]) * MvPowerSeries.X ((true, t), a, b)

def HasShape (D : D7) {p : ℕ} [Fact p.Prime] {N N' : ℕ} (S : ℂ_[p]) (u' : HH D → ℂ_[p])
    (Θ : MvPowerSeries (Var D N N') ℂ_[p]) : Prop :=
  ∃ sg : MvPowerSeries (Var D N N') ℂ_[p], IntJets sg ∧
    Θ = expMv (-(MvPowerSeries.C S * beForm D N N' u')) * sg

abbrev Amb (D : D7) (p : ℕ) [Fact p.Prime] : Type := D.what₂.Tau → ℂ_[p] × ℂ_[p]

def embA (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.E) : Amb D p :=
  fun τ => (tauEmb D lam τ a, tauEmb D lam τ (D.host.conj a))

def KerTie (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (idl : D.Dt ⧸ D.UO → IdE D)
    (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ, ∀ i < D.R.m, liftTie D (tor0 D cc δ) (B.eNat (chiRec D idl)) (O u μ) i

def ShapeD {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = D.host.d →
    ∃ (S : ℂ_[D.what₂.places.resChar w]) (u' : HH D → ℂ_[D.what₂.places.resChar w]),
      ‖S‖ ^ 2 ≤ (D.host.d : ℝ) ∧ (∀ t, ‖u' t‖ ≤ 1) ∧
      ∀ u μ, LevFree Dx u μ w → ∀ i < D.R.m,
        ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), HasShape D S u' (E.Th u μ w i c c')

end GlobalTheory.IndefiniteRowSideFullHecke.DualBasesOfSeries
