import Mathlib

noncomputable section

open ValuativeRel

namespace PositivityTheory.Lbc

variable (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]

def normU : Eˣ →* Fˣ := Units.map (Algebra.norm F : E →* F)

def OU (K : Type) [Field K] [ValuativeRel K] : Subgroup Kˣ :=
  (Units.map (valuation K).toMonoidWithZeroHom.toMonoidHom).ker

def incU : Fˣ →* Eˣ := Units.map (algebraMap F E : F →* E)

def ramIdx : ℕ := ((incU F E).range ⊔ OU E).index

variable {F E}

def IsGen (σ : E ≃ₐ[F] E) : Prop := ∀ τ : E ≃ₐ[F] E, ∃ k : ℕ, τ = σ ^ k

variable (F E)

def LocalUnitNormIndex : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → ((OU E).map (normU F E)).relIndex (OU F) = ramIdx F E

end PositivityTheory.Lbc
