import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIsotropicFixesVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XZeroColumnLattice

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
open GlobalTheory.FinPlLoc

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.LeviKeep

variable {D : D7}

theorem latV_mono {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) :
    latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨α, hα, hα', r⟩
  exact ⟨α, hα, fun w hw => hα' w fun h => hw (h ▸ hv), r⟩

end GlobalTheory.FinPl.LeviKeep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitLast

variable {D : D7}

theorem proj_mem_adelic_lattice_of_mono {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) {LW : Lat W} {LW₀ : Lat W₀} {v : Pl D}
    (hm : MonoAt d LW LW₀ v) {y : Fin W.rank → AE D} (hy : y ∈ latA W LW (· = v)) :
    d.p0 *ᵥ y ∈ latA W₀ LW₀ (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin W.rank → AE D := fun k => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x k) with hu
    have hu' : u ∈ latV W LW (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hg : (fun k => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x k)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • u := by
      funext k
      simp only [hu, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have heq : d.p0 *ᵥ (((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • u) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.p0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rw [hg, heq]
    exact VacFlat.smul_mem_latA ha (((hm u).1 hu').2.2)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.SplitLast

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatUnitPf

theorem idAt_mul_idOff {D : D7} (P : Pl D → Prop) (a b : AE D) (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) : a * b = 0 := by
  have h1 : a * b ∈ idAt D P := Ideal.mul_mem_right _ _ ha
  have h2 : a * b ∈ idOff D P := Ideal.mul_mem_left _ _ hb
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at h1
  rw [idOff, Ideal.mem_iInf] at h2
  obtain ⟨hinf, hfin⟩ := h1
  rw [RingHom.mem_ker] at hinf
  apply GlobalTheory.LatVac.eq_zero_of_parts
  · exact hinf
  · apply GlobalTheory.SelfDualAt.eq_zero_of_compFin
    intro w
    by_cases hw : P w
    · have := h2 ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this
    · have := hfin ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this

theorem psiE_add {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) : psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  unfold psiE; rw [map_add, AddChar.map_add_eq_mul]

end GlobalTheory.FinPl.FlatUnitPf

end
end
