import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

namespace ReciprocityTheory.CA.PS

open IsLocalRing MvPowerSeries

universe u v

structure IsCNL (A : Type*) [CommRing A] : Prop where
  noeth : IsNoetherianRing A
  loc : IsLocalRing A
  complete : IsAdicComplete (maximalIdeal A) A

noncomputable def relEmbDim (O : Type*) [CommRing O] [IsLocalRing O] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra O A] : ℕ :=
  ((maximalIdeal A).map
    (Ideal.Quotient.mk ((maximalIdeal O).map (algebraMap O A)))).spanFinrank

def PresentationStatement : Prop :=
  ∀ (O : Type u) [CommRing O], IsCNL O → ∀ [IsLocalRing O] (A : Type v) [CommRing A], IsCNL A →
    ∀ [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)],
    Function.Surjective (ResidueField.map (algebraMap O A)) →
    (∃ φ : MvPowerSeries (Fin (relEmbDim O A)) O →ₐ[O] A, Function.Surjective φ) ∧
    ∀ (a : ℕ) (φ : MvPowerSeries (Fin a) O →ₐ[O] A), Function.Surjective φ → relEmbDim O A ≤ a

end ReciprocityTheory.CA.PS
