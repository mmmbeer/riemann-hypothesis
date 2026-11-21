import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.Abs

def rho : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))

def orthogonalHaarMeasure : Measure (GL (Fin 2) ℝ) :=
  ENNReal.ofReal (4 * Real.pi)⁻¹ •
    (Measure.map (fun θ => GL2LocalData.kR θ false) rho + Measure.map (fun θ => GL2LocalData.kR θ true) rho)

def mKv (v : Pl) : Measure (GL (Fin 2) (Qv v)) :=
  (LFS.hG (GP.psiF v) (GL2LocalData.K2 (Qv v)))⁻¹ • (LFS.hG (GP.psiF v)).restrict (GL2LocalData.K2 (Qv v))

end GlobalTheory.CompanionTheory.GL2Factorization.Abs
