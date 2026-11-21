import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.FlagModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {c : Com D} {s s' : PiLocalization₂ D}

theorem inFlag_one : s.InFlag 1 := ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩


theorem ch_ne_zero (κ : GA D s.V) : s.ch κ ≠ 0 := Lev.levChi_ne_zero _ _

theorem ch_mul {κ κ' : GA D s.V} (h : s.InFlag κ) (h' : s.InFlag κ') : s.ch (κ * κ') = s.ch κ * s.ch κ' := by
  unfold PiLocalization₂.ch Lev.levChi
  rw [map_mul, Lev.levFn_flag_mul h.2 h'.2, Units.val_mul]

theorem ch_one : s.ch 1 = 1 := by
  have h := ch_mul (s := s) inFlag_one inFlag_one
  rw [mul_one] at h
  exact (mul_eq_left₀ (ch_ne_zero _)).1 h.symm

theorem rTup_eq_one {j : ℕ} (hs : s.Is c j) (hP : c.P.H = ⊥) {κ : GA D s.V} (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    rTup s.β s.L (Lev.finE s.V κ) = 1 := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hb : s.L.P.H = ⊥ := by rw [hL]; exact hP
  have h : rTup s.β s.L (Lev.finE s.V κ) ∈ s.L.P.H := hκ.2.2
  rw [hb] at h
  exact Subgroup.mem_bot.1 h








end GlobalTheory.ChainOnto.FlagModel

end
