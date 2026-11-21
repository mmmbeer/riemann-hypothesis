import Mathlib
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.DSExist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualChoice

section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

structure Fam (n : ℕ) where
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)

attribute [instance] Fam.nH Fam.iH Fam.cH

def Ineq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam lam' : Fin n → ℝ), vNormSq ε (lowK ε lam) ≠ vNormSq ε (lowK ε lam') →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      IsDS ε lam' σ' → ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)

def ToSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ + Pi.single s 1) → IsDS ε (μ + Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ + Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ

def OfSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ + Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ + Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g *ᵥ xI i))

def ToSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ - Pi.single s 1) → IsDS ε (μ - Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ - Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ

def OfSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ - Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ - Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g⁻¹ *ᵥ xI i))

def NormNe : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ), IsHCParam μ → ∀ s s' : Fin n, s ≠ s' →
    vNormSq ε (lowK ε (μ + Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ + Pi.single s' 1)) ∧
    vNormSq ε (lowK ε (μ - Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ - Pi.single s' 1))




end PI.ZuckTensorWork
end
end

section
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

section Eq
variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]

def cjEquivInv (U : Cj A ≃ₗᵢ[ℂ] Cj B) : A ≃ₗᵢ[ℂ] B where
  toFun x := Cj.un (U (Cj.mk x))
  invFun y := Cj.un (U.symm (Cj.mk y))
  left_inv x := by
    show Cj.un (U.symm (U (Cj.mk x))) = x
    rw [U.symm_apply_apply]; rfl
  right_inv y := by
    show Cj.un (U (U.symm (Cj.mk y))) = y
    rw [U.apply_symm_apply]; rfl
  map_add' x y := by
    show Cj.un (U (Cj.mk x + Cj.mk y)) = _
    rw [map_add]; rfl
  map_smul' c x := by
    have e : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
      show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
      rw [Complex.conj_conj]
    show Cj.un (U (Cj.mk (c • x))) = c • Cj.un (U (Cj.mk x))
    rw [e, map_smul, Cj.un_smul, Complex.conj_conj]
  norm_map' x := U.norm_map (Cj.mk x)

end Eq

end PI.ZuckTensorWork
end
end

section
open Matrix Finset
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

variable {n : ℕ}










end PI.ZuckTensorWork
end
end

section
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

section Mat
variable {n : ℕ}

theorem revM_eq_submatrix (g : Matrix (Fin n) (Fin n) ℂ) :
    revM g = g.submatrix (Fin.revPerm : Fin n ≃ Fin n) (Fin.revPerm : Fin n ≃ Fin n) := by
  ext i j; simp [revM, Fin.revPerm_apply]

theorem revM_revM (g : Matrix (Fin n) (Fin n) ℂ) : revM (revM g) = g := by
  ext i j; simp [revM]


theorem revM_mul (a b : Matrix (Fin n) (Fin n) ℂ) : revM (a * b) = revM a * revM b := by
  rw [revM_eq_submatrix, revM_eq_submatrix, revM_eq_submatrix, Matrix.submatrix_mul_equiv]

theorem revM_one : revM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [revM_eq_submatrix, Matrix.submatrix_one_equiv]


theorem revM_conjTranspose (g : Matrix (Fin n) (Fin n) ℂ) : (revM g)ᴴ = revM gᴴ := by
  unfold revM; rw [Matrix.conjTranspose_submatrix]

theorem revM_diagonal (d : Fin n → ℂ) : revM (diagonal d) = diagonal (d ∘ Fin.rev) := by
  rw [revM_eq_submatrix, Matrix.submatrix_diagonal_equiv]
  congr 1

theorem revM_Jm (ε : Fin n → Bool) : revM (Jm ε) = Jm (revE ε) := by
  unfold Jm; rw [revM_diagonal]; rfl









end Mat

section Conj
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Cj.mk_smul (c : ℂ) (x : H) : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
  show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
  rw [Complex.conj_conj]

theorem Cj.continuous_mk : Continuous (Cj.mk : H → Cj H) := continuous_id



variable {n : ℕ}














end Conj

section Wt
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}







end Wt





end PI.ZuckTensorWork
end
end

section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

namespace SqInt

variable {n : ℕ}

theorem revM_mul (A B : Matrix (Fin n) (Fin n) ℂ) : revM (A * B) = revM A * revM B := by
  unfold revM
  exact (Matrix.submatrix_mul_equiv A B Fin.rev Fin.revPerm Fin.rev).symm

theorem revM_one : revM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  simp [revM, Matrix.one_apply]

theorem revM_revM (A : Matrix (Fin n) (Fin n) ℂ) : revM (revM A) = A := by
  ext i j
  simp [revM]

theorem revM_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) : revM Aᴴ = (revM A)ᴴ := by
  unfold revM
  exact (Matrix.conjTranspose_submatrix A Fin.rev Fin.rev).symm

theorem revM_Jm (ε : Fin n → Bool) : revM (Jm ε) = Jm (revE ε) := by
  unfold revM Jm revE
  exact Matrix.submatrix_diagonal _ Fin.rev Fin.rev_injective

theorem inUJ_rev (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (h : inUJ ε g) :
    inUJ (revE ε) (revM g) := by
  unfold inUJ at *
  rw [← revM_Jm, ← revM_conjTranspose, ← revM_mul, ← revM_mul, h]

def revHom : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun := revM
  map_one' := revM_one
  map_mul' := revM_mul

theorem mem_fwd (ε : Fin n → Bool) (g : UJ (revE ε)) :
    Units.map (revHom (n := n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ∈ UJ ε := by
  show inUJ ε (revM (umat g))
  have h := inUJ_rev (revE ε) (g.2 : inUJ (revE ε) (umat g))
  rwa [revE_revE] at h

theorem mem_bwd (ε : Fin n → Bool) (g : UJ ε) :
    Units.map (revHom (n := n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ∈ UJ (revE ε) := by
  show inUJ (revE ε) (revM (umat g))
  exact inUJ_rev ε (g.2 : inUJ ε (umat g))

def phiE (ε : Fin n → Bool) : UJ (revE ε) ≃* UJ ε where
  toFun g := ⟨Units.map revHom (g : (Matrix (Fin n) (Fin n) ℂ)ˣ), mem_fwd ε g⟩
  invFun g := ⟨Units.map revHom (g : (Matrix (Fin n) (Fin n) ℂ)ˣ), mem_bwd ε g⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    exact revM_revM (umat g)
  right_inv g := by
    apply Subtype.ext; apply Units.ext
    exact revM_revM (umat g)
  map_mul' g h := by
    apply Subtype.ext; apply Units.ext
    exact revM_mul (umat g) (umat h)

theorem phiE_cont (ε : Fin n → Bool) : Continuous (phiE ε) := by
  rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
  show Continuous (fun g : UJ (revE ε) => (coeMatrixAlt (revE ε) g).submatrix Fin.rev Fin.rev)
  exact (continuous_coeMatrix (revE ε)).matrix_submatrix Fin.rev Fin.rev

theorem phiE_symm_cont (ε : Fin n → Bool) : Continuous (phiE ε).symm := by
  rw [(isClosedEmbeddingMatrix n (revE ε)).1.isInducing.continuous_iff]
  show Continuous (fun g : UJ ε => (coeMatrixAlt ε g).submatrix Fin.rev Fin.rev)
  exact (continuous_coeMatrix ε).matrix_submatrix Fin.rev Fin.rev

end SqInt

open SqInt in
theorem square_integrable_conj : SqIntConj := by
  intro n ε H _ _ σ hs v w
  have hmap : (Measure.map (phiE ε) (muG (revE ε))).IsHaarMeasure :=
    (phiE ε).isHaarMeasure_map (muG (revE ε)) (phiE_cont ε) (phiE_symm_cont ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map (phiE ε) (muG (revE ε))) (muG ε)
  have h1 : MemLp (coefOn (ε := ε) σ (Cj.un v) (Cj.un w)) 2 (Measure.map (phiE ε) (muG (revE ε))) := by
    rw [heq, ENNReal.smul_def]
    exact (hs _ _).smul_measure ENNReal.coe_ne_top
  have h2 := (memLp_map_measure_iff h1.1 (phiE_cont ε).measurable.aemeasurable).1 h1
  have e : coefOn (ε := revE ε) (sigC σ) v w = star (coefOn (ε := ε) σ (Cj.un v) (Cj.un w) ∘ phiE ε) := by
    funext g
    show ⟪w, cjOp (σ (revM (umat g))) v⟫_ℂ = star ⟪Cj.un w, σ (revM (umat g)) (Cj.un v)⟫_ℂ
    rw [Cj.inner_def, cjOp_apply]
    exact (inner_conj_symm _ _).symm
  rw [e]
  exact h2.star

end PI.ZuckTensorWork
end
end

section
namespace PI.ZuckTensorWork
open PI.ZuckTensor


end PI.ZuckTensorWork
end
