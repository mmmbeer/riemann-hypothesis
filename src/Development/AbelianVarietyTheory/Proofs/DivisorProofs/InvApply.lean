import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PoleFactor

open IsDedekindDomain
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def unipR (x : Matrix (Fin n) (Fin 1) E) : Subgroup (HA R σ J) :=
  Subgroup.closure {g | let m : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (HA.mat R σ J g).1 - 1
    m * x.map (inclR (F := F) R) = 0 ∧ (cT (σ : E →+* E) x * J).map (inclR (F := F) R) * m = 0 ∧
    ∀ z : Fin n → E, (cT (σ : E →+* E) x * J) *ᵥ z = 0 →
      ∃ c : Fin 1 → R ⊗[F] E, m *ᵥ (fun i => inclR (F := F) R (z i)) = x.map (inclR (F := F) R) *ᵥ c}

open Formalism.UG (bc)

variable (F E) in

def latHt (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → Fv F v ⊗[F] E) : ℝ :=
  sInf {r : ℝ | ∃ l : (Fv F v ⊗[F] E)ˣ, (fun i => ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * z i) ∈ latLoc F L v ∧
    r = (GlobalTheory.Doubling.absEv F E v l : ℝ)}

variable (F E) in

def archHt (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (z : Fin n → w.Completion ⊗[F] E) : ℝ :=
  ‖(∑ i, Algebra.norm w.Completion (((((bc (compInf F E w) a)⁻¹ : GL (Fin n) (w.Completion ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) *ᵥ z) i))‖

open Classical in

def haarFin (L : Submodule (𝓞 E) (Fin n → E)) (x : Matrix (Fin n) (Fin 1) E) (v : HeightOneSpectrum (𝓞 F)) :
    Measure (unipR (Fv F v) σ J x) :=
  if h : IsCompact (((stabLoc σ J L v).subgroupOf (unipR (Fv F v) σ J x)) : Set (unipR (Fv F v) σ J x)) ∧
      (interior (((stabLoc σ J L v).subgroupOf (unipR (Fv F v) σ J x)) : Set (unipR (Fv F v) σ J x))).Nonempty then
    Measure.haarMeasure ⟨⟨_, h.1⟩, h.2⟩
  else 0

open Classical in

def haarArch (x : Matrix (Fin n) (Fin 1) E) (w : InfinitePlace F) : Measure (unipR w.Completion σ J x) :=
  if h : Nonempty (TopologicalSpace.PositiveCompacts (unipR w.Completion σ J x)) then Measure.haarMeasure h.some else 0

end GlobalTheory.PoleFactor
