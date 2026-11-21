import Mathlib
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.KernelSt
import Development.AbelianVarietyTheory.BlockTheory.ClassSums.StabilizerKernelSums
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RowsCongrOfTrivialAtLevel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionFixesLevelVectorUpToUnit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.IndefiniteRowSideFullHecke.StabilizerKernelSums
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.KernelCompare

variable {D : D7} {S T : HSp D}

theorem isTh_uVec (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) {f : WO S T → ℂ} (hf : C.IsTh f) :
    C.IsTh (C.uVec Lv hn f) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  exact finsum_induction C.IsTh h0 (fun x y hx hy => (h1 x y hx hy).1)
    fun c => (h2 _ ((h2 f hf).2.1 _)).1 _

end GlobalTheory.Ker.KernelCompare
