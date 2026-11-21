import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteGlobalStability.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection
open scoped NumberField.AdeleRing ValuativeRel ENNReal
open Ad3 Ad3.K Ad3.K.GPK

namespace GlobalTheory.CompanionTheory.GPKIntB

variable {K : Type} [Field K] [NumberField K]

def cU (a : (InfiniteAdeleRing K)ˣ) : ℂˣ :=
  Units.map (InfinitePlace.Completion.extensionEmbedding (wC K)).toMonoidHom
    (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completion) (wC K)) a)

open scoped Classical in

def Qf (D : DatK K) (S : Finset (PlK K)) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℂ :=
  ∏ᶠ v : PlK K, if v ∈ S then 1 else sph D v (dg 1 1 (finUnitAt v b))

section Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def tauL (W : GL (Fin 3) F → ℂ) (t : Fˣ) : ℝ≥0∞ :=
  (∫⁻ u, ‖W (mm t u)‖ₑ ∂haarIntegers F) * ENNReal.ofReal ((modulus (t : F) : ℝ) ^ (-(5 / 2 : ℝ)))

end Loc

end GlobalTheory.CompanionTheory.GPKIntB
