import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.WittLeviObjects
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ChangeOfVariables
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DetNorm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DensityConstant

noncomputable section

namespace PI.IwaMeasEx

open MeasureTheory NumberField Matrix
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

section Sizes

variable {I : AutInst} {J : ℕ}

open Classical in

def tBlk (Fr : WittFrame I J) (c : Composition J) (m : I.GA) (i : Fin c.length) : ℝ :=
  (if h : IsUnit (Fr.blkF c m i).det then Formalism.L2.S.S7.GLOne.nrmF I h.unit else 0) *
    ∏ v, ‖(Fr.blkV c m v i).det‖ ^ 2

def eExp (I : AutInst) (c : Composition J) : Fin c.length → ℝ := fun i => 2 * (c.blocksFun i : ℝ) * I.f

def dInv (Fr : WittFrame I J) (c : Composition J) (m : I.GA) : ℝ :=
  cn_dens c.blocksFun (I.n - 2 * J) I.f (chv (eExp I c) (tBlk Fr c m))

end Sizes

structure IwaMeas (X : CData) {J : ℕ} (D : BaseDatum X.I J) (c : Composition J) where
  μP : Measure X.I.GA
  μK : Measure X.I.GA
  μN : Measure X.I.GA
  μM : Measure X.I.GA
  cIw : ℝ≥0∞
  cIw_ne_zero : cIw ≠ 0
  cIw_ne_top : cIw ≠ ⊤
  μK_univ : μK Set.univ = 1
  μK_supp : μK (D.kZero : Set X.I.GA)ᶜ = 0
  intF : ∀ Φ : X.I.GA → ℝ≥0∞, Measurable Φ →
    ∫⁻ x, Φ x ∂(X.I.muA X.μf) = cIw * ∫⁻ p, (∫⁻ k, Φ (p * k) ∂μK) ∂μP
  parabolicMeasure_map_mul_left : ∀ γ ∈ PPF X.I (D.toWittFrame.flag c), μP.map (fun p => γ * p) = μP
  μN_supp : μN (D.toWittFrame.uniA c : Set X.I.GA)ᶜ = 0
  μM_supp : μM (D.toWittFrame.leviA c : Set X.I.GA)ᶜ = 0
  decomp : ∀ g : X.I.GA → ℝ≥0∞, Measurable g →
    ∫⁻ p, g p ∂μP = ∫⁻ m, (∫⁻ n, g (n * m) ∂μN) * ENNReal.ofReal (dInv D.toWittFrame c m) ∂μM
  FN : Set X.I.GA
  FM : Set X.I.GA
  Om : Set X.I.GA
  FN_meas : MeasurableSet FN
  FM_meas : MeasurableSet FM
  Om_meas : MeasurableSet Om
  Om_fd : IsFundamentalDomain (PPF X.I (D.toWittFrame.flag c)) Om μP
  Om_spec : ∀ n ∈ D.toWittFrame.uniA c, ∀ m ∈ D.toWittFrame.leviA c, n * m ∈ Om ↔ n ∈ FN ∧ m ∈ FM
  VM : ℝ≥0∞
  levi : ∀ Φ : (Fin c.length → ℝ) → ℝ≥0∞, Measurable Φ →
    ∫⁻ m in FM, Φ (tBlk D.toWittFrame c m) ∂μM = VM * ∫⁻ t in posO c.length, Φ t * ∏ i, ENNReal.ofReal (t i)⁻¹
  levi_size_measurable : Measurable (tBlk D.toWittFrame c)

end PI.IwaMeasEx

namespace PI.IwaFinBase

open NumberField Matrix
open Formalism.MainNotions.S Formalism.L2.S.S7.WittLeviSubgroups

end PI.IwaFinBase

end
