import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

def leftMul (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) :
    Matrix (Fin a) (Fin b) R ≃ₗ[R] Matrix (Fin a) (Fin b) R where
  toFun x := Jiᵀ * x
  invFun y := Jᵀ * y
  map_add' := Matrix.mul_add _
  map_smul' c x := Matrix.mul_smul _ c x
  left_inv x := by
    change Jᵀ * (Jiᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    change Jiᵀ * (Jᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, mul_eq_one_comm.1 h1, Matrix.transpose_one, Matrix.one_mul]

theorem gen_supp (f : R) (g : Matrix (Fin a) (Fin a) R) :
    (∀ i j, f * (g - 1) i j = (g - 1) i j) ↔ (1 - f) • g = (1 - f) • (1 : Matrix (Fin a) (Fin a) R) := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  constructor <;> intro h <;> linear_combination -h

theorem gen_cont [TopologicalSpace R] [IsTopologicalRing R] (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) :
    Continuous (leftMul (b := b) J Ji h1) ∧ Continuous (leftMul (b := b) J Ji h1).symm :=
  ⟨continuous_const.matrix_mul continuous_id, continuous_const.matrix_mul continuous_id⟩

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) : SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (e + HeisenbergWeilMatrices.cj D e) g :=
  gen_supp _ _

theorem suppAt_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (V : HSp D)
    (g : GA D V) : SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (HeisenbergWeilMatrices.idemFin D v) g := by
  rw [suppAt_iff', he.sum]

end GlobalTheory.DualPairCompare

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

instance topRing (D : D7) : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _

theorem gramInv_mul (A : HSp D) : HeisenbergWeilMatrices.gramInvA A * HeisenbergWeilMatrices.gramA A = 1 := by
  unfold HeisenbergWeilMatrices.gramInvA HeisenbergWeilMatrices.gramA
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne A))]
  exact Matrix.map_one _ (incA D).map_zero (incA D).map_one

def coordUp (A B : HSp D) : HeisenbergWeilMatrices.WA A B ≃ₗ[AE D] WA A B :=
  leftMul (HeisenbergWeilMatrices.gramA A) (HeisenbergWeilMatrices.gramInvA A) (gramInv_mul A)

theorem cont_up (A B : HSp D) : Continuous (coordUp A B) ∧ Continuous (coordUp A B).symm :=
  gen_cont _ _ (gramInv_mul A)

structure IsCoord {V W A B : HSp D} (φ : HeisenbergWeilMatrices.WA A B ≃ₗ[AE D] WA V W) : Prop where
  cont : Continuous φ
  cont_symm : Continuous φ.symm
  herm : ∀ x y, hHom V W (φ y) (φ x) = HeisenbergWeilMatrices.herm x y
  rat : ∀ x, φ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B
  inf : ∀ x, (φ x).map (infPart D) = 0 ↔ x.map (infPart D) = 0
  fin : ∀ x, (φ x).map (finPart D) = 0 ↔ x.map (finPart D) = 0

end GlobalTheory.DualPairCompare

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke

section Gen
variable {M N : Type} [AddCommGroup M] [TopologicalSpace M] [AddCommGroup N] [TopologicalSpace N]

def SmoothAlong (Z : M → Prop) (f : M → ℂ) : Prop :=
  ∀ (k : ℕ) (L : (Fin k → ℝ) →+ M), Continuous L → (∀ t, Z (L t)) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

theorem gen_smooth_iff {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (Z : M → Prop)
    (r : P →+ M) (hr : Continuous r) (hZ : ∀ p, Z (r p)) (co : M →+ P) (hc : Continuous co)
    (h3 : ∀ z, Z z → r (co z) = z) (f : M → ℂ) :
    SmoothAlong Z f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + r p) := by
  constructor
  · intro h w
    let e : P ≃L[ℝ] (Fin (Module.finrank ℝ P) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := (h _ (r.comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom) (hr.comp e.symm.continuous)
      (fun t => hZ _) w).comp e.contDiff
    convert this using 2 with p
    exact congrArg (fun q => f (w + r q)) (e.symm_apply_apply p).symm
  · intro h k L hL h0 w
    have := (h w).comp ((co.comp L).toRealLinearMap (hc.comp hL)).contDiff
    convert this using 2 with t
    exact congrArg (fun q => f (w + q)) (h3 _ (h0 t)).symm





omit [TopologicalSpace M] [TopologicalSpace N] in
theorem gen_quasi (φ : M ≃+ N) (S : AddSubgroup M) (S' : AddSubgroup N) (hS : ∀ x, φ x ∈ S' ↔ x ∈ S)
    (κ : M → M → ℂ) (κ' : N → N → ℂ) (hκ : ∀ x y, κ' (φ x) (φ y) = κ x y) (f : N → ℂ) :
    (∀ γ ∈ S', ∀ w, f (γ + w) = κ' γ w * f w) ↔ ∀ γ ∈ S, ∀ w, (f ∘ φ) (γ + w) = κ γ w * (f ∘ φ) w := by
  simp only [φ.surjective.forall, hS, hκ, Function.comp_apply, map_add]



end Gen

def realMat (D : D7) (m n : ℕ) :
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) →+ Matrix (Fin m) (Fin n) (AE D) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q =>
    Matrix.ext fun i j => (realPtHom D).map_add (p i j) (q i j)

theorem continuous_realMat (D : D7) (m n : ℕ) : Continuous (realMat D m n) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))

theorem exists_coMat (D : D7) (m n : ℕ) : ∃ co : Matrix (Fin m) (Fin n) (AE D) →+
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)), Continuous co ∧
    (∀ z, (z - realMat D m n (co z)).map (infPart D) = 0) ∧ ∀ z, z.map (finPart D) = 0 → realMat D m n (co z) = z := by
  obtain ⟨co, h1, h2, h3⟩ := exists_co D
  exact ⟨AddMonoidHom.mk' (fun z i j => co (z i j)) fun z w => funext₂ fun i j => co.map_add _ _,
    continuous_pi fun i => continuous_pi fun j => h1.comp ((continuous_apply j).comp (continuous_apply i)),
    fun z => Matrix.ext fun i j => h2 (z i j),
    fun z hz => Matrix.ext fun i j => h3 (z i j) (congrFun₂ hz i j)⟩

theorem smoothAlong_iff {m n : ℕ} (f : Matrix (Fin m) (Fin n) (AE D) → ℂ) :
    SmoothAlong (fun z => z.map (finPart D) = 0) f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + realMat D m n p) := by
  obtain ⟨co, c1, -, c3⟩ := exists_coMat D m n
  exact gen_smooth_iff (fun z : Matrix (Fin m) (Fin n) (AE D) => z.map (finPart D) = 0) (realMat D m n) (continuous_realMat D m n)
    (fun p => Matrix.ext fun i j => finPart_realPt D (p i j)) co c1 c3 f

theorem continuous_cA (D : D7) : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap



end GlobalTheory.DualPairCompare

end
end
