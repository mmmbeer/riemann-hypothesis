import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.FormalGroupJets

open Formalism.MainNotions.FormalGroupJets

namespace Formalism.MainNotions.Ext

end Formalism.MainNotions.Ext

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def BiaddOfCube : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    Simeq (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2))

def AddIntG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    (ModelOverW g.lam g.abelian₂ g.C → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))

end Formalism.MainNotions.Ext

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

def OkpInertG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → p ≠ 2 → (Ideal.span {(p : 𝓞 K)}).IsPrime →
    closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) = W2pair p

end Formalism.MainNotions.Ext
