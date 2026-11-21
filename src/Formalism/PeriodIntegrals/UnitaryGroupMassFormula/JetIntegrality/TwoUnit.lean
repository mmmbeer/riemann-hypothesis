import Mathlib
import Formalism.PeriodIntegrals.JetsPhW

noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

def Dv {p : ℕ} [Fact p.Prime] {σ : Type*} (v : PowerSeries ℂ_[p]) (i : σ)
    (f : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v * MvPowerSeries.pderiv ℂ_[p] i f

def psi {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.subst ex ph

def IntP {p : ℕ} [Fact p.Prime] (g : PowerSeries ℂ_[p]) : Prop :=
  ∀ n, IsIntP (PowerSeries.coeff n g)

def Chain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst s g) =
      MvPowerSeries.pderiv ℂ_[p] i s * PowerSeries.subst s (dX g)

def DChain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (l v g : PowerSeries ℂ_[p]) (s : MvPowerSeries σ ℂ_[p])
    (c : ℂ_[p]), v * dX l = 1 → MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv ℂ_[p] i s =
      MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX l) →
    Dv v i (PowerSeries.subst s g) = MvPowerSeries.C c * PowerSeries.subst s (dX g)

def PdSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX g)

def PdNe : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i j : σ) (g : PowerSeries ℂ_[p]), j ≠ i →
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) g) = 0

def DSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v g : PowerSeries ℂ_[p]),
    Dv v i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (v * dX g)

def Ev0 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.constantCoeff (PowerSeries.subst s g) = PowerSeries.constantCoeff g

def JetD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (n : ℕ),
    jet ex ph n = PowerSeries.constantCoeff ((dX (A := ℂ_[p]))^[n] (psi ex ph))

def LogDer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → MvPowerSeries.constantCoeff f = 0 → IntegralMv (expMv f) → IntegralMv (Dv v i f)

def Dint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → IntegralMv f → IntegralMv (Dv v i f)

abbrev lX {p : ℕ} [Fact p.Prime] {σ : Type*} (l : PowerSeries ℂ_[p]) (j : σ) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) l

def Rw3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    cubeE l ex ph =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

def TwoUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ‖(2 : ℂ_[p])‖ = 1

end PI.JetsPhW.W
