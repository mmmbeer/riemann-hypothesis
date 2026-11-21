import Mathlib

noncomputable section

open Classical

namespace PI.FunEqAll

def JetTdeg {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.sum (fun _ k => k)

def jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((l ^ 2) ^ e) then (((l : ℂ_[l]) ^ e)⁻¹) else 0

def zL (l d : ℕ) [Fact l.Prime] (s : ZMod d) : MvPowerSeries (ZMod d × Unit) ℂ_[l] :=
  jetLogG l d (s, ())

end PI.FunEqAll
