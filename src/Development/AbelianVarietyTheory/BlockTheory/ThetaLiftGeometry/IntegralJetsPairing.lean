import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing

def HasIntJets {σ : Type} {p : ℕ} [Fact p.Prime] (f : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α : σ →₀ ℕ, ‖(α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α f‖ ≤ 1

def pairForm (D : D7) {p : ℕ} [Fact p.Prime] (N N' : ℕ) (u' : HH D → ℂ_[p]) :
    MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p] :=
  ∑ t : HH D, MvPowerSeries.C (u' t) *
    ∑ a : Fin N, ∑ b : Fin N', MvPowerSeries.X (((false, t), a, b) : (Bool × HH D) × Fin N × Fin N') *
      MvPowerSeries.X (((true, t), a, b) : (Bool × HH D) × Fin N × Fin N')

def DualBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Bool × HH D → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  (∀ s, TaylorLogMetric.LocBasisW D (TaylorLogMetric.tauEmb D lam (tauPl D s)) L (P s)) ∧
  ∀ (t : HH D) (a a' : Fin N),
    ∑ k, P (false, t) k a * D.host.conj (P (true, t) k a') = if a = a' then 1 else 0

def IsLineGen (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (c : D.what₂.Tau → ℂ)
    (g : Bool × HH D → ℂ_[p]) : Prop :=
  ∀ s, ∃ ε : ℂ_[p], ‖ε‖ = 1 ∧ g s = ε * TaylorLogMetric.lamC lam (c (tauPl D s))

open Classical in

def chgCoef (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ} (g : Bool × HH D → ℂ_[p])
    (P : Bool × HH D → Matrix (Fin N) (Fin N) D.host.E) (P' : Bool × HH D → Matrix (Fin N') (Fin N') D.host.E)
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  if tauPl D x.1 = k.1 then
    g x.1 * TaylorLogMetric.tauEmb D lam (tauPl D x.1) (P' x.1 k.2.1 x.2.2) *
      TaylorLogMetric.tauEmb D lam (tauPl D x.1) ((P x.1)⁻¹ x.2.1 k.2.2)
  else 0

def SeriesTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∃ g : Bool × HH D → ℂ_[D.what₂.places.resChar w], IsLineGen D (E.lam w) O.dgen g ∧
    ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ (P : Bool × HH D → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
        (P' : Bool × HH D → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E),
        DualBases D (E.lam w) (O.lat i c).1 P ∧ DualBases D (E.lam w) (O.lat (i + 1) c').1 P' ∧
        E.Th u μ w i c c' = linAt (chgCoef D (E.lam w) g P P') (TaylorLogMetric.pSer D (E.lam w) (O.Th i c c'))

def Shape {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∃ S : ℂ_[D.what₂.places.resChar w], ‖S‖ ≤ Real.sqrt (D.what₂.places.resChar w : ℝ) ∧
    ∃ u' : HH D → ℂ_[D.what₂.places.resChar w], (∀ t, ‖u' t‖ ≤ 1) ∧
      ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
        ∃ sg' : MvPowerSeries ((Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w],
          HasIntJets sg' ∧
          E.Th u μ w i c c' =
            TaylorLogMetric.expMv (-(MvPowerSeries.C S * pairForm D (D.R.N i) (D.R.N (i + 1)) u')) * sg'

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing
