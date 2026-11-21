import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

noncomputable section

namespace GlobalTheory.ThStr

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField Classical

variable {l : ℕ} [Fact l.Prime]

def laS (l : ℕ) [Fact l.Prime] (d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

def laAt {d : ℕ} {κ : Type} (ι : ZMod d → κ) (s : ZMod d) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun r : ZMod d => (MvPowerSeries.X (ι r) : MvPowerSeries κ ℂ_[l])) (laS l d s)

def parDeg {d : ℕ} (par : Bool) (n : ZMod d →₀ ℕ) : ℕ :=
  n.sum fun s k => if decide (Even s.val) = par then k else 0

def cobdry {d : ℕ} (par : Bool) (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (Bool × ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (false, r)) s + laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])
      else laAt (fun r => (false, r)) s) be -
    MvPowerSeries.subst (fun s : ZMod d => (laAt (fun r => (false, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])) be -
    MvPowerSeries.subst (fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l]) else laAt (fun r => (false, r)) s) be

structure IsBe (d : ℕ) (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop where
  coef : CoefWf be
  inv : ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be
  bideg : ∀ n, MvPowerSeries.coeff n be ≠ 0 →
    parDeg true n ≠ 0 ∧ parDeg false n ≠ 0 ∧ ¬ (parDeg true n = 1 ∧ parDeg false n = 1)
  cob : ∀ par, IntegralW (expMv (cobdry par be))

end GlobalTheory.ThStr
