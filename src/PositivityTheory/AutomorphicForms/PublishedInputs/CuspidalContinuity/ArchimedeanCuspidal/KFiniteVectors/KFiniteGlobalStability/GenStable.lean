import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.GPK

variable {K : Type} [Field K] [NumberField K]

variable (K) in

def wC : InfinitePlace K := Classical.arbitrary _

def gCx (g : G3K K) : GL (Fin 3) ℂ :=
  Units.map (InfinitePlace.Completion.extensionEmbedding (wC K)).mapMatrix.toMonoidHom (Reduction.infAt (wC K) g)

abbrev psiF (v : PlK K) : AddChar (Kv K v) Circle := localAdelicChar K v

abbrev sph (D : DatK K) (v : PlK K) : GL (Fin 3) (Kv K v) → ℂ := sphW (psiF v) (D.ν v)

def pw (Wi : GL (Fin 3) ℂ → ℂ) (Wf : ∀ v : PlK K, GL (Fin 3) (Kv K v) → ℂ) (g : G3K K) : ℂ :=
  Wi (gCx g) * ∏ᶠ v, Wf v (Reduction.finAt v g)

structure Loc (D : DatK K) where
  VF : ∀ v : PlK K, Submodule ℂ (GL (Fin 3) (Kv K v) → ℂ)
  hF : ∀ v, WhF (psiF v) (D.ν v) (VF v)
  sp : ∀ v, v ∉ D.bad → sph D v ∈ VF v
  VC : Submodule ℂ (GL (Fin 3) ℂ → ℂ)
  E : Fin 3 → Fin 3 → Module.End ℂ VC
  E' : Fin 3 → Fin 3 → Module.End ℂ VC
  hC : WhC D.k VC E E'

variable {D : DatK K}

structure IsFac (L : Loc D) (Wi : GL (Fin 3) ℂ → ℂ) (Wf : ∀ v : PlK K, GL (Fin 3) (Kv K v) → ℂ) : Prop where
  inf : Wi ∈ L.VC
  fin : ∀ v, Wf v ∈ L.VF v
  ae : ∃ S : Finset (PlK K), ∀ v ∉ S, Wf v = sph D v

def Gen (L : Loc D) : Set (G3K K → ℂ) := {W | ∃ Wi Wf, IsFac L Wi Wf ∧ W = pw Wi Wf}

def VA (L : Loc D) : Submodule ℂ (G3K K → ℂ) := Submodule.span ℂ (Gen L)

variable (K) in

def VorS (W : G3K K → ℂ) : Prop :=
  Summable (fun a : Kˣ => W (diaK (K := K) (dg a 1 1))) ∧
    (∀ b : Kˣ, Integrable (fun u => W (diaK (K := K) (dg 1 1 b) * cyc u)) (adeleMeasure K)) ∧
    Summable (fun b : Kˣ => ∫ u, W (diaK (K := K) (dg 1 1 b) * cyc u) ∂adeleMeasure K)

abbrev ιK (a : Kˣ) : IdeleGroup K := Units.map (algebraMap K 𝔸[K]).toMonoidHom a

def κC : ℂ := 2

def GenStable : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, ∀ h, (fun g => W (g * h)) ∈ Gen L

end Ad3.K.GPK
