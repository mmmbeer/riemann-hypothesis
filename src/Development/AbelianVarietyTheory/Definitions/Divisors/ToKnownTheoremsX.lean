import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointDimensionLtProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower

section
namespace GlobalTheory.CovHt

structure HypothesesY : Prop where

  alt : GlobalTheory.Published.RegularAlteration

  dem : GlobalTheory.Published.DemaillyRegularisation

  mat : GlobalTheory.Published.MatrixLemma

  sieg : GlobalTheory.Published.AbsoluteSiegel

  perfd : GlobalTheory.Published.PrismaticDieudonnePerfd

example (h : HypothesesY) : GlobalTheory.Published.RegularAlteration ∧ GlobalTheory.Published.PrismaticDieudonnePerfd := ⟨h.alt, h.perfd⟩

end GlobalTheory.CovHt
end

section
namespace GlobalTheory.CovTop

structure HypothesesXH : Prop where

  toClassicalTheoremsX : HypothesesX

  mb : GlobalTheory.Published.MoretBaillyModel

  arr : GlobalTheory.Published.ArithRiemannRoch

  cube : GlobalTheory.Published.CubeTheorem

  dual : GlobalTheory.Published.DualAbelianScheme

  logres : GlobalTheory.Published.AnalyticLogResolution

  andim : GlobalTheory.Published.AnalyticSetDimension

  conj : GlobalTheory.Published.ConjugateFiltration

  ray : GlobalTheory.Published.RaynaudExtension

  orth : GlobalTheory.Published.GrothendieckOrthogonality

  y : GlobalTheory.CovHt.HypothesesY

  btd : GlobalTheory.Published.BarsottiTateDieudonne

instance : Coe HypothesesXH HypothesesX := ⟨HypothesesXH.toClassicalTheoremsX⟩

theorem HypothesesXH.ks (h : HypothesesXH) : GlobalTheory.Published.ToroidalForFanKS := h.toClassicalTheoremsX.ks

theorem HypothesesXH.lie (h : HypothesesXH) : GlobalTheory.Published.SemiAbelianLieSeminegative := h.toClassicalTheoremsX.lie

theorem HypothesesXH.sep (h : HypothesesXH) : GlobalTheory.Published.PointSeparationPair := h.toClassicalTheoremsX.sep

end GlobalTheory.CovTop
end
