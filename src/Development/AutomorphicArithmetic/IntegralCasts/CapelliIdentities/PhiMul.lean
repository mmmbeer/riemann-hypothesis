import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

open TensorProduct Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.Qf14.phi_mul
    {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {E : Type} [Field E] [Algebra Qp E]
    (x y : E ⊗[Qp] B) :
    φVB PD (LL := E) (V := E) (x * y) =
      φVB PD (LL := E) (V := E) x * φVB PD (LL := E) (V := E) y := by
  have h : ∀ z : E ⊗[Qp] B,
      φVB PD (LL := E) (V := E) z = Algebra.TensorProduct.map (AlgHom.id E E) PD.φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  exact (h (x * y)).trans ((map_mul _ x y).trans (congrArg₂ (· * ·) (h x).symm (h y).symm))
