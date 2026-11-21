import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureTensorDecompositionLocal
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import GroundTheory.HeightsAndTheta.Theta.WeilBox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
import BuildAid.ForwardExisting

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GroundTheory.Heights₂.Theta
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.BigCell.PhdSupp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def flat (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) : (Fin 2 × Fin 2 → F) → ℂ :=
  fun X => Φ (Matrix.of fun i j => X (i, j))

def entHomeo : (Fin 2 × Fin 2 → F) ≃ₜ Matrix (Fin 2) (Fin 2) F where
  toFun X := Matrix.of fun i j => X (i, j)
  invFun A := fun ij => A ij.1 ij.2
  left_inv X := rfl
  right_inv A := rfl
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    exact continuous_apply (i, j)
  continuous_invFun := by
    refine continuous_pi fun ij => ?_
    exact (continuous_apply ij.2).comp (continuous_apply ij.1)

theorem flat_mem {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} (h : SB2 Φ) :
    flat Φ ∈ schwartzBruhatPi F (Fin 2 × Fin 2) :=
  ⟨h.1.comp_continuous entHomeo.continuous, h.2.comp_homeomorph entHomeo⟩

variable [MeasurableSpace F] [BorelSpace F]

end GlobalTheory.CompanionTheory.BigCell.PhdSupp

namespace GlobalTheory.CompanionTheory.BigCell

end GlobalTheory.CompanionTheory.BigCell
end
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GroundTheory.Heights₂.Theta
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.PureTensorFourier

open GlobalTheory.CompanionTheory.BigCell.PhdSupp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def mat (X : Fin 2 × Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => X (i, j)

theorem mem_pi_of_mem {f : (Fin 2 → F) → ℂ} (h : f ∈ GodementSectionLocal.schwartzBruhat2 F) :
    f ∈ schwartzBruhatPi F (Fin 2) :=
  ⟨h.1, h.2⟩

theorem pFT_eq_sum (ψ : AddChar F Circle) (hψ : Continuous ψ)
    (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) {n : ℕ} (Φ₁ : Fin n → Matrix (Fin 2) (Fin 2) F → ℂ)
    (Φ₂ : Fin n → (Fin 2 → F) → ℂ) (h₂ : ∀ i, Φ₂ i ∈ GodementSectionLocal.schwartzBruhat2 F)
    (hΦ : ∀ A y, Φ (cat3 A y) = ∑ i, Φ₁ i A * Φ₂ i y)
    (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) :
    pFT ψ Φ A ξ = ∑ i, Φ₁ i A * fourierPi ψ (Φ₂ i) (-ξ) := by
  have hint : ∀ i, Integrable (fun y => Φ₁ i A * (Φ₂ i y * (ψ (y ⬝ᵥ (-ξ)) : ℂ))) (selfDualPi (Fin 2) ψ) :=
    fun i => (integrable_mul_char_of_mem_schwartzBruhatPi hψ (mem_pi_of_mem (h₂ i)) (-ξ)).const_mul _
  have hpt : ∀ y : Fin 2 → F, Φ (cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) =
      ∑ i, Φ₁ i A * (Φ₂ i y * (ψ (y ⬝ᵥ (-ξ)) : ℂ)) := by
    intro y
    have hd : y ⬝ᵥ (-ξ) = -(ξ 0 * y 0 + ξ 1 * y 1) := by
      simp [dotProduct, Fin.sum_univ_two]
      ring
    rw [hΦ, Finset.sum_mul, hd]
    exact Finset.sum_congr rfl fun i _ => by ring
  change ∫ y, Φ (cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂selfDualPi (Fin 2) ψ = _
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem a3 : A3 := by
  intro F _ _ _ _ _ _ ψ hψ n Φ Φ₁ Φ₂ h₁ h₂ hΦ
  refine ⟨fun A ξ => ?_, fun A ξ => ?_⟩
  · rw [pFT_eq_sum ψ hψ.1 Φ Φ₁ Φ₂ h₂ hΦ A ξ]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    change ∫ x, Φ₂ i x * (ψ (x ⬝ᵥ (-ξ)) : ℂ) ∂selfDualPi (Fin 2) ψ =
      ∫ x, Φ₂ i x * (ψ (-(x 0 * ξ 0 + x 1 * ξ 1)) : ℂ) ∂selfDualPi (Fin 2) ψ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hd : x ⬝ᵥ (-ξ) = -(x 0 * ξ 0 + x 1 * ξ 1) := by
      simp [dotProduct, Fin.sum_univ_two]
    simp only [hd]
  · have hdot : ∀ X : Fin 2 × Fin 2 → F,
        X ⬝ᵥ (fun p : Fin 2 × Fin 2 => A p.1 p.2) = ∑ i, ∑ j, X (i, j) * A i j := by
      intro X
      simp only [dotProduct]
      exact Fintype.sum_prod_type _
    have hint : ∀ i, Integrable (fun X : Fin 2 × Fin 2 → F =>
        Φ₁ i (Matrix.of fun a b => X (a, b)) * (ψ (∑ a, ∑ b, X (a, b) * A a b) : ℂ) * Φ₂ i (-ξ))
        (Measure.pi fun _ => selfDualMeasure ψ) := by
      intro i
      have h := integrable_mul_char_of_mem_schwartzBruhatPi hψ.1 (flat_mem (h₁ i))
        (fun p : Fin 2 × Fin 2 => A p.1 p.2)
      simp only [hdot] at h
      exact h.mul_const _
    have hpt : ∀ X : Fin 2 × Fin 2 → F,
        Φ (cat3 (Matrix.of fun a b => X (a, b)) (-ξ)) * (ψ (∑ a, ∑ b, X (a, b) * A a b) : ℂ) =
        ∑ i, Φ₁ i (Matrix.of fun a b => X (a, b)) * (ψ (∑ a, ∑ b, X (a, b) * A a b) : ℂ) *
          Φ₂ i (-ξ) := by
      intro X
      rw [hΦ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold dFT matrixFourierTransposeInv
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => hint i]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _

end GlobalTheory.CompanionTheory.PureTensorFourier
end
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.FourierPlane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ft2 (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) (ξ : Fin 2 → F) : ℂ :=
  ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ

theorem integral_plane_measure_eq_prod (ψ : AddChar F Circle) (f : (Fin 2 → F) → ℂ) :
    ∫ y, f y ∂LFS.vol2 ψ =
      ∫ p : F × F, f ![p.1, p.2] ∂(selfDualMeasure ψ).prod (selfDualMeasure ψ) :=
  ((measurePreserving_finTwoArrow (selfDualMeasure ψ)).symm.integral_comp' f).symm

theorem inv_one {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {f : F → ℂ}
    (hf : f ∈ schwartzBruhat F) (z : F) :
    Integrable (fun u => localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ)) (selfDualMeasure ψ) ∧
      ∫ u, localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ) ∂selfDualMeasure ψ = f z := by
  have hT := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ hψ1 hf
  have hI := integrable_mul_char_of_mem_schwartzBruhat (selfDualMeasure ψ) hψ hT (-z)
  have e : (fun u => localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ)) =
      fun u => (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ)) (-u) := by
    funext u
    simp only [neg_mul_neg]
  rw [e]
  refine ⟨hI.comp_neg, ?_⟩
  rw [integral_neg_eq_self (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ))]
  have h := localFourier_localFourier_selfDual hψ hψ1 hf (-z)
  rw [neg_neg] at h
  exact h

theorem fourier_plane_product_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) {n : ℕ} {f g : Fin n → F → ℂ}
    (hf : ∀ i, f i ∈ schwartzBruhat F) (hg : ∀ i, g i ∈ schwartzBruhat F) (ξ : Fin 2 → F) :
    ft2 ψ (fun y => ∑ i, f i (y 0) * g i (y 1)) ξ =
      ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) := by
  have e : ∀ p : F × F, (∑ i, f i p.1 * g i p.2) * (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) =
      ∑ i, (f i p.1 * (ψ (p.1 * -ξ 0) : ℂ)) * (g i p.2 * (ψ (p.2 * -ξ 1) : ℂ)) := by
    intro p
    have hc : (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) = (ψ (p.1 * -ξ 0) : ℂ) * (ψ (p.2 * -ξ 1) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold ft2
  rw [integral_plane_measure_eq_prod]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e]
  rw [integral_finsetSum _ fun i _ => Integrable.mul_prod
    (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hf i) (-ξ 0))
    (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hg i) (-ξ 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_prod_mul (fun x => f i x * (ψ (x * -ξ 0) : ℂ)) (fun x => g i x * (ψ (x * -ξ 1) : ℂ))

theorem inv_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {f g : Fin n → F → ℂ}
    (hf : ∀ i, f i ∈ schwartzBruhat F) (hg : ∀ i, g i ∈ schwartzBruhat F) (z : Fin 2 → F) :
    ∫ ξ : Fin 2 → F, (∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)) * (ψ (ξ 0 * z 0 + ξ 1 * z 1) : ℂ) ∂LFS.vol2 ψ =
      ∑ i, f i (z 0) * g i (z 1) := by
  have e : ∀ p : F × F, (∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-p.2)) * (ψ (p.1 * z 0 + p.2 * z 1) : ℂ) =
      ∑ i, (localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) * (ψ (p.1 * z 0) : ℂ)) *
        (localFourier (selfDualMeasure ψ) ψ (g i) (-p.2) * (ψ (p.2 * z 1) : ℂ)) := by
    intro p
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_plane_measure_eq_prod]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e]
  rw [integral_finsetSum _ fun i _ => Integrable.mul_prod
    (inv_one hψ hψ1 (hf i) (z 0)).1 (inv_one hψ hψ1 (hg i) (z 1)).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_prod_mul (fun u => localFourier (selfDualMeasure ψ) ψ (f i) (-u) * (ψ (u * z 0) : ℂ))
    (fun u => localFourier (selfDualMeasure ψ) ψ (g i) (-u) * (ψ (u * z 1) : ℂ)),
    (inv_one hψ hψ1 (hf i) (z 0)).2, (inv_one hψ hψ1 (hg i) (z 1)).2]

omit [MeasurableSpace F] [BorelSpace F] in

theorem pure_mem {a b : F → ℂ} (ha : a ∈ schwartzBruhat F) (hb : b ∈ schwartzBruhat F) :
    (fun x : Fin 2 → F => a (x 0) * b (x 1)) ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine GodementSectionLocal.mem_schwartzBruhat2.2
    ⟨(ha.1.comp_continuous (continuous_apply 0)).mul (hb.1.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro
    ((ha.2.isCompact.prod hb.2.isCompact).image (Homeomorph.finTwoArrow (X := F)).symm.continuous) fun x hx => ?_
  by_contra hne
  refine hx ⟨(x 0, x 1), ⟨subset_tsupport _ fun h => hne ?_, subset_tsupport _ fun h => hne ?_⟩, ?_⟩
  · simp [h]
  · simp [h]
  · ext j
    fin_cases j <;> simp

omit [MeasurableSpace F] [BorelSpace F] in

theorem reflect_mem {a : F → ℂ} (ha : a ∈ schwartzBruhat F) : (fun x => a (-x)) ∈ schwartzBruhat F :=
  ⟨ha.1.comp_continuous continuous_neg, ha.2.comp_homeomorph (Homeomorph.neg F)⟩

omit [MeasurableSpace F] [BorelSpace F] in

theorem exists_pure {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) :
    ∃ (n : ℕ) (f g : Fin n → F → ℂ), (∀ i, f i ∈ schwartzBruhat F) ∧ (∀ i, g i ∈ schwartzBruhat F) ∧
      φ = fun y => ∑ i, f i (y 0) * g i (y 1) := by
  have hl : IsLocallyConstant fun p : F × F => φ ((Homeomorph.finTwoArrow (X := F)).symm p) :=
    hφ.1.comp_continuous (Homeomorph.finTwoArrow (X := F)).symm.continuous
  have hc : HasCompactSupport fun p : F × F => φ ((Homeomorph.finTwoArrow (X := F)).symm p) :=
    hφ.2.comp_homeomorph (Homeomorph.finTwoArrow (X := F)).symm
  obtain ⟨n, f, g, hf, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hl hc
  refine ⟨n, f, g, hf, hg, ?_⟩
  funext y
  rw [← hfg]
  congr 1
  ext j
  fin_cases j <;> rfl

theorem fourier_inversion_plane_explicit : ForS fun F _ _ _ _ _ _ ψ => ∀ φ : (Fin 2 → F) → ℂ,
    φ ∈ GodementSectionLocal.schwartzBruhat2 F →
    (fun ξ : Fin 2 → F => ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) ∈
        GodementSectionLocal.schwartzBruhat2 F ∧
      ∀ z : Fin 2 → F, ∫ ξ : Fin 2 → F, (∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) *
        (ψ (ξ 0 * z 0 + ξ 1 * z 1) : ℂ) ∂LFS.vol2 ψ = φ z := by
  intro F _ _ _ _ _ _ ψ hstd φ hφ
  have hψ : Continuous ψ := hstd.1
  have hψ1 : ψ ≠ 1 := hstd.2.1
  obtain ⟨n, f, g, hf, hg, rfl⟩ := exists_pure hφ
  have e : (fun ξ : Fin 2 → F => ∫ y, (∑ i, f i (y 0) * g i (y 1)) *
      (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) =
      fun ξ => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) :=
    funext fun ξ => fourier_plane_product_sum hψ hf hg ξ
  refine ⟨?_, fun z => ?_⟩
  · rw [e]
    have : (fun ξ : Fin 2 → F => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)) =
        ∑ i, fun ξ : Fin 2 → F => localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
          localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) := by
      funext ξ
      simp
    rw [this]
    exact Submodule.sum_mem _ fun i _ => pure_mem
      (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hf i)))
      (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hg i)))
  · have := inv_sum hψ hψ1 hf hg z
    simp only [← congrFun e] at this
    exact this

end GlobalTheory.CompanionTheory.FourierPlane
end
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.PFTBound

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem exists_entry_bound {s : Set (Matrix (Fin 2) (Fin 2) F)} (hs : IsCompact s) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ A ∈ s, ∀ i j, (modulus (A i j) : ℝ) ≤ R := by
  have hc : Continuous (fun A : Matrix (Fin 2) (Fin 2) F =>
      ∑ i, ∑ j, (modulus (A i j) : ℝ)) := by
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact NNReal.continuous_coe.comp (continuous_modulus.comp (continuous_id.matrix_elem i j))
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun A hA i j => ?_⟩
  have h1 : (modulus (A i j) : ℝ) ≤ ∑ j, (modulus (A i j) : ℝ) :=
    Finset.single_le_sum (f := fun j => (modulus (A i j) : ℝ))
      (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j, (modulus (A i j) : ℝ) ≤ ∑ i, ∑ j, (modulus (A i j) : ℝ) :=
    Finset.single_le_sum (f := fun i => ∑ j, (modulus (A i j) : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ i)
  have h3 := hC A hA
  exact (h1.trans h2).trans ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
    (h3.trans (le_max_left _ _))))

theorem exists_mx_bound {s : Set (Fin 2 → F)} (hs : IsCompact s) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ ξ ∈ s, mx ξ ≤ R := by
  have hc : Continuous (fun ξ : Fin 2 → F => mx ξ) := by
    unfold mx
    exact (NNReal.continuous_coe.comp (continuous_modulus.comp (continuous_apply 0))).max
      (NNReal.continuous_coe.comp (continuous_modulus.comp (continuous_apply 1)))
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun ξ hξ =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans ((hC ξ hξ).trans (le_max_left _ _)))⟩

theorem ftN_mem (ψ : AddChar F Circle) (hψ : IsStd ψ) {φ : (Fin 2 → F) → ℂ}
    (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) :
    ftN ψ φ ∈ GodementSectionLocal.schwartzBruhat2 F := by
  have h := (GlobalTheory.CompanionTheory.FourierPlane.fourier_inversion_plane_explicit F ψ hψ φ hφ).1
  have e : ftN ψ φ = fun ξ : Fin 2 → F =>
      ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ := by
    funext ξ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_comm (x 0), mul_comm (x 1)]
  rw [e]
  exact h

end D

theorem pFT_continuous_bounded : ForS fun F _ _ _ _ _ _ ψ => ∀ Φ ∈ LFS.SB F,
    Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) ∧
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C ∧
      (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R) := by
  intro F _ _ _ _ _ _ ψ hψ Φ hΦ
  obtain ⟨n, Φ₁, Φ₂, h₁, h₂, hs⟩ := GlobalTheory.CompanionTheory.PureTensor.k2pt F ψ hψ Φ hΦ
  have hsum : ∀ A ξ, pFT ψ Φ A ξ = ∑ i, Φ₁ i A * ftN ψ (Φ₂ i) ξ :=
    (GlobalTheory.CompanionTheory.PureTensorFourier.a3 F ψ hψ n Φ Φ₁ Φ₂ h₁ h₂ hs).1
  have hg : ∀ i, IsLocallyConstant (ftN ψ (Φ₂ i)) ∧ HasCompactSupport (ftN ψ (Φ₂ i)) :=
    fun i => GodementSectionLocal.mem_schwartzBruhat2.1 (ftN_mem ψ hψ (h₂ i))
  have hc₁ : ∀ i, Continuous (Φ₁ i) := fun i => (h₁ i).1.continuous
  have hc₂ : ∀ i, Continuous (ftN ψ (Φ₂ i)) := fun i => (hg i).1.continuous
  refine ⟨?_, ?_⟩
  · have e : (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) =
        fun q => ∑ i, Φ₁ i q.1 * ftN ψ (Φ₂ i) q.2 := funext fun q => hsum q.1 q.2
    rw [e]
    exact continuous_finset_sum _ fun i _ =>
      ((hc₁ i).comp continuous_fst).mul ((hc₂ i).comp continuous_snd)
  · choose B₁ hB₁ using fun i => (hc₁ i).bounded_above_of_compact_support (h₁ i).2
    choose B₂ hB₂ using fun i => (hc₂ i).bounded_above_of_compact_support (hg i).2
    choose R₁ hR₁ hR₁' using fun i => exists_entry_bound (h₁ i).2.isCompact
    choose R₂ hR₂ hR₂' using fun i => exists_mx_bound (hg i).2.isCompact
    have hB₁0 : ∀ i, 0 ≤ B₁ i := fun i => (norm_nonneg _).trans (hB₁ i 0)
    have hB₂0 : ∀ i, 0 ≤ B₂ i := fun i => (norm_nonneg _).trans (hB₂ i 0)
    refine ⟨∑ i, B₁ i * B₂ i, ∑ i, (R₁ i + R₂ i),
      Finset.sum_nonneg fun i _ => mul_nonneg (hB₁0 i) (hB₂0 i), fun A ξ => ⟨?_, fun hne => ?_⟩⟩
    · rw [hsum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hB₁ i A) (hB₂ i ξ) (norm_nonneg _) (hB₁0 i)
    · rw [hsum] at hne
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hA : Φ₁ i A ≠ 0 := left_ne_zero_of_mul hi
      have hξ : ftN ψ (Φ₂ i) ξ ≠ 0 := right_ne_zero_of_mul hi
      have hle : R₁ i + R₂ i ≤ ∑ i, (R₁ i + R₂ i) :=
        Finset.single_le_sum (f := fun i => R₁ i + R₂ i)
          (fun i _ => add_nonneg (hR₁ i) (hR₂ i)) (Finset.mem_univ i)
      refine ⟨fun a b => ?_, ?_⟩
      · have := hR₁' i A (subset_tsupport _ hA) a b
        linarith [hR₂ i]
      · have := hR₂' i ξ (subset_tsupport _ hξ)
        linarith [hR₁ i]

end GlobalTheory.CompanionTheory.PFTBound
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_continuous_bounded_support : ForS fun F _ _ _ _ _ _ ψ => ∀ Φ ∈ LFS.SB F, Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) ∧
  ∃ C R : ℝ, 0 ≤ C ∧ ∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C ∧
    (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PFTBound.pFT_continuous_bounded
end
