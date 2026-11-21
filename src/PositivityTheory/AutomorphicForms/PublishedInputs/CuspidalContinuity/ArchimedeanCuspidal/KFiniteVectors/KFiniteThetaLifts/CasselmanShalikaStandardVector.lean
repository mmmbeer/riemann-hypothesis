import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.BaseChangeAssembly
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.PureTh

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3.R (G2 Jd md KA Set0 Coord LInv)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable (K : Type) [Field K] [NumberField K]

def SPHB : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl), Th.Unr c v → ∃ Wt, Th.StdTh c v Wt

def CasselmanShalikaStandardVector : Prop := Module.finrank ℚ K = 2 → ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), v ∉ D.bad →
  Th.Unr c v → ∀ Wt, Th.StdTh c v Wt → ∀ s : ℂ, 0 < s.re →
    zU (GP.sph D v) Wt s = GP.sph D v 1 * lfV DK c v s ∧
    zU (GL2LocalData.dW3 (GP.sph D v)) (GL2LocalData.dW2 Wt) s = GP.sph D v 1 * lfV DK c⁻¹ v s

def THETAB : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (e : Pl → ℂ), (∀ v, InThE c v (Wtf v) (e v)) →
  (∃ S0 : Finset Pl, ∀ v ∉ S0, Th.Unr c v ∧ Th.StdTh c v (Wtf v)) → ∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 (thR n t) Wtf)

end Ad3.K.QuadraticBaseChangeGL3
