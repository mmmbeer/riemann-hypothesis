import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneSubOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetEqSumIndicatorOfPeriodic
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry

section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil

namespace GlobalTheory.TypeTwo.FullRank

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k]

def IsDens (ν : Measure k) {n j : ℕ} (μ : rkSB k n j j →ₗ[ℂ] ℂ) (ρ : Matrix (Fin n) (Fin j) k → ℂ) : Prop :=
  (∀ x : Matrix (Fin n) (Fin j) k, x.rank = j → ∀ᶠ y in nhds x, ρ y = ρ x) ∧
    ∀ Φ : rkSB k n j j, μ Φ = ∫ x, ρ x * Φ.1 x ∂(volM ν (Fin n) (Fin j))

end GlobalTheory.TypeTwo.FullRank
end
end

section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.TypeTwo.FullRank ValuativeRel Matrix
open scoped Topology

noncomputable section

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat

namespace GlobalTheory.TypeTwo.FullRank.DensEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballLat (m c : Type) (s : kˣ) : AddSubgroup (Matrix m c k) where
  carrier := {z | ∀ i l, z i l ∈ cball s}
  add_mem' ha hb i l := add_mem_cball (ha i l) (hb i l)
  zero_mem' i l := by simp [cball]
  neg_mem' ha i l := neg_mem_cball (ha i l)

end GlobalTheory.TypeTwo.FullRank.DensEx

namespace GlobalTheory.TypeTwo.FullRank.DensEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Rank
variable {n j : ℕ}

end Rank

theorem valuation_det_of_mem_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k} (hg : g ∈ KO k m) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) =
      algebraMap 𝒪[k] k ((Matrix.GeneralLinearGroup.det u : 𝒪[k]ˣ) : 𝒪[k]) := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [this]
  exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 (Units.isUnit _)

end GlobalTheory.TypeTwo.FullRank.DensEx

namespace GlobalTheory.TypeTwo.FullRank.DensEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Meas
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

end Meas

section Ext
variable {n j : ℕ}

open Classical in

def extByZero (μ : rkSB k n j j →ₗ[ℂ] ℂ) (f : Matrix (Fin n) (Fin j) k → ℂ) : ℂ :=
  if h : f ∈ rkSB k n j j then μ ⟨f, h⟩ else 0

end Ext

section Meas2
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

end Meas2

end GlobalTheory.TypeTwo.FullRank.DensEx

namespace GlobalTheory.TypeTwo.FullRank.DensEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

end GlobalTheory.TypeTwo.FullRank.DensEx

namespace GlobalTheory.TypeTwo.FullRank

end GlobalTheory.TypeTwo.FullRank
end
end
