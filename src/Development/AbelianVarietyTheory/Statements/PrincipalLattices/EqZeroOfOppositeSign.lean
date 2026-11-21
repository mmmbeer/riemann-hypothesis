import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTypeModel

open PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.PureTypeModel.exists_isTypeFn (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty := by
  classical
  let n : (E →+* ℂ) → ℕ := fun τ => if τ H.rt = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (n τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have hcard : ∀ τ, Nat.card {i // (e.symm i).1 = τ} = n τ := by
    intro τ
    rw [Nat.card_congr ((e.symm.subtypeEquiv (p := fun i => (e.symm i).1 = τ)
      (q := fun s => s.1 = τ) (fun i => Iff.rfl)).trans (Equiv.sigmaSubtype τ)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    simp [n, h]
  · rw [hcard]
    simp [n, h]



section Linear

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

end Linear



section Mixed

open HostModel PeriodNonempty
open scoped TensorProduct


def scale (H : Host E) (s t : ℝ) : ℝ ⊗[ℤ] HypLattice H →ₗ[ℝ] ℝ ⊗[ℤ] HypLattice H :=
  s • (LinearMap.inl ℤ _ _ ∘ₗ LinearMap.fst ℤ _ _).baseChange ℝ + t • (LinearMap.inr ℤ _ _ ∘ₗ LinearMap.snd ℤ _ _).baseChange ℝ

theorem scale_tmul (s t r : ℝ) (u : HypLattice H) :
    scale H s t (r ⊗ₜ u) = s • r ⊗ₜ (u.1, 0) + t • r ⊗ₜ (0, u.2) := by simp [scale]

theorem scale_scale {s t : ℝ} (h : s * t = 1) (x) : scale H s t (scale H t s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul r u =>
    rw [scale_tmul, map_add, map_smul, map_smul, scale_tmul, scale_tmul]
    simp only [Prod.mk_zero_zero, TensorProduct.tmul_zero, smul_zero, add_zero, zero_add, smul_smul, h, mul_comm t s,
      one_smul, ← TensorProduct.tmul_add, Prod.mk_add_mk]

theorem form_scale {s t : ℝ} (h : s * t = 1) (x y) :
    (hypForm H).baseChange ℝ (scale H s t x) (scale H s t y) = (hypForm H).baseChange ℝ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul r' v =>
      simp [scale_tmul]
      linear_combination ((ConjDual.toDual H u.2 v.1 : ℤ) - (ConjDual.toDual H v.2 u.1 : ℤ) : ℝ) * r * r' * h


end Mixed

end GlobalTheory.PureTypeModel
