import Formalism.WachLatticeTwists.DenseTopActions.Statement
import Formalism.WachLatticeTwists.SandwichH1Classes.HypothesisWGivesUnitCongruence

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
open scoped TensorProduct

section named

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {W : NData S ι pr D} {ℓ : ℕ} [Fact ℓ.Prime] {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC]
  [Algebra ℤ_[ℓ] WC] {jS : As →+* (ι → A)} {jA : As →+* AA} {io : AA →+* WC} {φ : WC →+* WC}
  {Gg : Type} [Group Gg] {H : Subgroup Gg} {act : Gg →* (WC ≃+* WC)} {r : ℕ}
  {ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]}

def OLin (C : Cmp W jS jA io φ H act ρ) (EO : O → Matrix (Fin r) (Fin r) ℤ_[ℓ]) : Prop :=
  ∀ (o : O) (x : ι → D), C.cmp ((fun _ => algebraMap O A o : ι → A) • x)
    = C.cmp x ᵥ* (EO o).map (algebraMap ℤ_[ℓ] WC)

end named

end Formalism.RepresentationBoundsCohomology.JW
