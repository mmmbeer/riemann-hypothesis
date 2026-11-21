import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCVPosIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts

section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs
open GroundTheory.Automorphic.Reduction (adelicBorel posIdele diagUnits coe_diagUnits)
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.SiegelConj

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

def scal (s : ℝ) : Ad E := 1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E (fun _ => (s : ℂ))

variable {E}

variable {n : ℕ}

end GlobalTheory.CompanionTheory.SiegelConj

end
end

section
noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open GroundTheory.Automorphic.Reduction (maxCompact)

namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.CompanionTheory.PiVec

end
end
