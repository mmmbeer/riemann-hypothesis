import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChTor

def ChartPt (p : ℕ) {O : Type} [CommRing O] {d : ℕ} {G : Over (Sp O)}
    (x : ∀ m : ℕ, algOver O (JetR O (Fin 1 × Fin d) m) ⟶ G) (c : Fin d → O) (P : algOver O O ⟶ G) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (ψ : JetR O (Fin 1 × Fin d) k →ₐ[O] O ⧸ Ideal.span {((p : O) ^ n)}),
    (∀ i, ψ (zR k ((0 : Fin 1), i)) = Ideal.Quotient.mk _ (c i)) ∧
    algOverHom (Ideal.Quotient.mkₐ O (Ideal.span {((p : O) ^ n)})) ≫ P = algOverHom ψ ≫ x k

abbrev Pts {C : Type} [Field C] (A : Over (Sp C)) : Type := (Over.mk (𝟙 (Sp C)) : Over (Sp C)) ⟶ A

end GlobalTheory.ChTor
