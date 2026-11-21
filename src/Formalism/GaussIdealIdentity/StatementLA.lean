import Mathlib

open scoped InnerProductSpace Pointwise

noncomputable section

namespace Formalism.DV

def GramDet : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (d : ℕ) (e F : Fin d → V),
    Pairwise (fun σ τ => ⟪e σ, e τ⟫_ℂ = 0) → (∀ σ, e σ ≠ 0) →
    let Z : Submodule ℂ V := Submodule.span ℂ (Set.range e)
    letI : FiniteDimensional ℂ Z := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
    let pr : V → V := fun v => Z.starProjection v
    let G : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun a b => ⟪pr (F a), pr (F b)⟫_ℂ
    let C : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun σ a => ⟪e σ, F a⟫_ℂ
    G.det = ((‖C.det‖ ^ 2 / ∏ σ, ‖e σ‖ ^ 2 : ℝ) : ℂ)

def gaussIdeal (σ O : Type) [CommRing O] [IsLocalRing O] : Ideal (MvPolynomial σ O) :=
  Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O)

def GaussDVR : Prop :=
  ∀ (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O],
    (gaussIdeal σ O).IsPrime ∧
    ∀ [(gaussIdeal σ O).IsPrime],
      IsDiscreteValuationRing (Localization.AtPrime (gaussIdeal σ O)) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime (gaussIdeal σ O)) =
        Ideal.map (algebraMap O (Localization.AtPrime (gaussIdeal σ O))) (IsLocalRing.maximalIdeal O)

def GaussLength : Prop :=
  ∀ (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [(gaussIdeal σ O).IsPrime] (N : Type) [AddCommGroup N] [Module O N],
    Module.length (Localization.AtPrime (gaussIdeal σ O))
        (TensorProduct O (Localization.AtPrime (gaussIdeal σ O)) N) = Module.length O N

end Formalism.DV
