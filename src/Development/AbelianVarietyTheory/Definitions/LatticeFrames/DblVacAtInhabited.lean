import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsParamVecOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisPoleLEZeroOfLt

noncomputable section

namespace GlobalTheory.Core.Rk.SW.Model

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw

variable {D : D7}


theorem exists_split (D : D7) : ∃ q : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q := by
  have h2 : ¬ IsUnit (2 : 𝓞 D.host.F) := fun h => by
    have h' := h.map (Algebra.norm ℤ)
    rw [show (2 : 𝓞 D.host.F) = algebraMap ℤ _ 2 by simp, Algebra.norm_algebraMap] at h'
    have h3 := (isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 D.host.F)).ne').1 h'
    exact absurd (Int.isUnit_iff.1 h3) (by decide)
  obtain ⟨M, hM, hle⟩ := exists_max_ideal_of_mem_nonunits h2
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, GlobalTheory.Core.Rk.IP.Model.isSplit_two _ hle⟩
  rw [h, Ideal.mem_bot] at hle
  exact two_ne_zero hle








end GlobalTheory.Core.Rk.SW.Model

end
