import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev

noncomputable section

namespace GlobalTheory.ThK.DescB.PlaneTwo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n₁ n₂ : ℕ}

def xTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Fin n → E := H₁.ι *ᵥ H₂.x

def yTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Fin n → E := H₁.ι *ᵥ H₂.y

def ιTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Matrix (Fin n) (Fin n₂) E := H₁.ι * H₂.ι

variable (σ) in

def unipTwo (Y : Spc F E n) (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Subgroup (UA σ Y.J) :=
  Subgroup.closure {u | mat u *ᵥ incV F H₁.x = incV F H₁.x ∧ mat u *ᵥ incV F (xTwo H₁ H₂) = incV F (xTwo H₁ H₂) ∧
    ∀ z, ∃ a b : AE F E, mat u *ᵥ (incM F (ιTwo H₁ H₂) *ᵥ z) =
      incM F (ιTwo H₁ H₂) *ᵥ z + a • incV F H₁.x + b • incV F (xTwo H₁ H₂)}

end GlobalTheory.ThK.DescB.PlaneTwo

end
