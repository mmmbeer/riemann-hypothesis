import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCentreLawZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DivAbsBig

theorem exists_idele_absE_gt_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ) := by
  intro F E _ _ _ _ _
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨b, h2⟩ : ∃ b : w.Completion, ‖b‖ = 2 := by
    refine ⟨_, (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))).trans ?_⟩
    show w (2 : F) = 2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.apply, map_ofNat]
    norm_num
  have hne : b ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; norm_num at h2
  let a : (w.Completion)ˣ := Units.mk0 b hne
  let y : (w.Completion ⊗[F] E)ˣ := Units.map (algebraMap w.Completion (w.Completion ⊗[F] E)).toMonoidHom a
  refine ⟨GlobalTheory.Doubling.ideleAtInf F E w y, ?_⟩
  rw [GlobalTheory.Doubling.absE_ideleAtInf, GlobalTheory.Doubling.absEw_apply]
  change 1 < ((‖Algebra.norm w.Completion (algebraMap w.Completion (w.Completion ⊗[F] E) b)‖₊ ^ w.mult : ℝ≥0) : ℝ)
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, NNReal.coe_pow, coe_nnnorm, norm_pow, h2, ← pow_mul]
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  have hm : 0 < w.mult := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact one_lt_pow₀ (by norm_num) (Nat.mul_ne_zero hn.ne' hm.ne')

end GlobalTheory.DivAbsBig

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.DescB.PrimeSplit

open Matrix GlobalTheory.LeviLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem skew_gram (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (ι : Matrix (Fin n) (Fin n₁) E) :
    ∀ k l, σ ((ιᵀ * J * ι.map σ) l k) = -(ιᵀ * J * ι.map σ) k l := by
  intro k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, Finset.sum_mul]
  simp only [hJ]
  refine Finset.sum_comm.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

theorem skew_sp (hσ : ∀ x, σ (σ x) = x) (B : Base F E) {d d₁ p : ℕ} {W : Spc F E d} (hW : ∀ i j, σ (W.J j i) = -W.J i j)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B W (sp 0) i₀ i₁)
    (hiso : ∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) :
    ∀ j ≤ p, ∀ k l, σ ((sp j).J l k) = -(sp j).J k l := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [← hH.gram]
    exact skew_gram hσ hW H'.ι
  | succ j ih =>
    intro hj
    rw [← (hiso j (by omega)).2.2.2.2.2.1]
    exact skew_gram hσ (ih (by omega)) (pl j).ι

end GlobalTheory.ThK.DescB.PrimeSplit

namespace GlobalTheory.ThK.DescB.PrimeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def lawFn (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

theorem norm_lawFn (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ‖lawFn χ z t‖ = (absE F E t : ℝ) ^ z := by
  rw [lawFn, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]

theorem lawFn_ne (α β : Chr F E) {z z' : ℝ} (hz : z < z') {t : (AE F E)ˣ} (ht : 1 < (absE F E t : ℝ)) :
    lawFn α z t ≠ lawFn β z' t := fun e => by
  have h := congrArg norm e
  rw [norm_lawFn, norm_lawFn] at h
  exact (Real.rpow_lt_rpow_of_exponent_lt ht hz).ne h

theorem isLevi_one {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H : Plane E d d₁) :
    IsLevi (σ := σ) (W := W) (W₁ := W₁) H 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat]

theorem isLevi_mul {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {t s : (AE F E)ˣ}
    {m m' : UA σ W.J} (h : IsLevi (W₁ := W₁) H t 1 m) (h' : IsLevi (W₁ := W₁) H s 1 m') :
    IsLevi (W₁ := W₁) H (t * s) 1 (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (1 : UA σ W₁.J) = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]
  · rw [e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [e, Matrix.mul_assoc, h'.2.2, e1, Matrix.mul_one]
    simpa [e1] using h.2.2

end GlobalTheory.ThK.DescB.PrimeSplit

namespace GlobalTheory.ThK.DescB.PrimeSplit

open GlobalTheory.LeviLine

end GlobalTheory.ThK.DescB.PrimeSplit

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviUniqueCartan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n' : ℕ}

theorem det_ne_zero_of_isCartan {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (e : E →+* ℂ) (θ : Matrix (Fin n) (Fin n) ℂ)
    (h : IsCartan (Complex.I • J.map e) θ) : J.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hx : star (fun i => e (v i)) ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa using this
  have hpos := h.2.2 _ hx
  have hz : (Complex.I • J.map e) *ᵥ star (star (fun i => e (v i))) = 0 := by
    rw [star_star, Matrix.smul_mulVec]
    have : J.map e *ᵥ (fun i => e (v i)) = 0 := by
      funext i
      have := RingHom.map_mulVec e J v i
      rw [hJv] at this
      simpa [Function.comp_def] using this.symm
    rw [this, smul_zero]
  rw [hz] at hpos
  simp at hpos

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : σ (form σ J a b) = -form σ J b a := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem incV_add (a b : Fin n' → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul (s : E) (a : Fin n' → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV]

theorem incV_mulVec {k : ℕ} (M : Matrix (Fin n') (Fin k) E) (u : Fin k → E) :
    incV F (M *ᵥ u) = incM F M *ᵥ incV F u := by
  funext i
  exact RingHom.map_mulVec (inclR (F := F) (AF F)) M u i

theorem incV_single (j : Fin n') : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [incV]
  · simp [incV, Pi.single_apply, hk]

theorem levi_unique {σ : E →ₐ[F] E} (B : Base F E) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (Y.J j i) = -Y.J i j) (hP : IsIsoPlane σ B H Y Y₁)
    (t : (AE F E)ˣ) (h₁ : UA σ Y₁.J) (m m' : UA σ Y.J)
    (hm : IsLevi (W₁ := Y₁) H t h₁ m) (hm' : IsLevi (W₁ := Y₁) H t h₁ m') : m = m' := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, -, hcart⟩ := hP
  subst hn
  have hadd : ∀ a b c, form σ Y.J (a + b) c = form σ Y.J a c + form σ Y.J b c := fun a b c => by
    simp [form, add_dotProduct]
  have hsmul : ∀ (s : E) a c, form σ Y.J (s • a) c = s * form σ Y.J a c := fun s a c => by
    simp [form, smul_dotProduct]
  have hzero : ∀ c, form σ Y.J 0 c = 0 := fun c => by simp [form]
  have hyx : form σ Y.J H.y H.x = -1 := by
    have := form_swap σ hσ Y.J hJ H.x H.y
    rw [hxy, map_one] at this
    linear_combination this
  have hdet : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact det_ne_zero_of_isCartan _ _ _ (hcart w)
  let Φ : E × (Fin n₁ → E) × E →ₗ[E] (Fin (n₁ + 2) → E) :=
    (LinearMap.smulRight LinearMap.id H.x).comp (LinearMap.fst E E ((Fin n₁ → E) × E)) +
    (Matrix.mulVecLin H.ι).comp ((LinearMap.fst E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E))) +
    (LinearMap.smulRight LinearMap.id H.y).comp ((LinearMap.snd E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E)))
  have hΦ : ∀ s u r, Φ (s, u, r) = s • H.x + H.ι *ᵥ u + r • H.y := fun s u r => by
    simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, u, r⟩ h
    rw [hΦ] at h
    have e1 := congrArg (fun z => form σ Y.J z H.y) h
    simp only [hadd, hsmul, hxy, hyy, (horth u).2, hzero] at e1
    have hs : s = 0 := by simpa using e1
    subst hs
    have e2 := congrArg (fun z => form σ Y.J z H.x) h
    simp only [hadd, hsmul, hxx, hyx, (horth u).1, hzero] at e2
    have hr : r = 0 := by simpa using e2
    subst hr
    have hu0 : H.ι *ᵥ u = 0 := by simpa using h
    have hu : u ᵥ* Y₁.J = 0 := by
      rw [← hgram, Matrix.mul_assoc, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu0, Matrix.zero_vecMul]
    have : u = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hne, hu⟩)
    subst this
    rfl
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hinj
  have key : ∀ z, mat m *ᵥ incV F z = mat m' *ᵥ incV F z := by
    intro z
    obtain ⟨⟨s, u, r⟩, rfl⟩ := hsurj z
    rw [hΦ, incV_add, incV_add, incV_smul, incV_smul, incV_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hm.1, hm.2.1, hm.2.2, hm'.1, hm'.2.1, hm'.2.2]
  have hmat : mat m = mat m' := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [incV_single, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    simpa using this
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUniqueCartan

end
end

section
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DescB.GenGrowth

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_block {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) ℂ) (π : Matrix (Fin n₁) (Fin n) ℂ) (h : π * ι = 1)
    (Z : Matrix (Fin n₁) (Fin n₁) ℂ) :
    NormedSpace.exp (ι * Z * π) = (1 - ι * π) + ι * NormedSpace.exp Z * π := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  haveI : CompleteSpace (Matrix (Fin n₁) (Fin n₁) ℂ) := FiniteDimensional.complete ℝ _
  have h' : ∀ {k : ℕ} (X : Matrix (Fin n₁) (Fin k) ℂ), π * (ι * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  let f : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => p.2 • (1 - ι * π) + ι * p.1 * π
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h', Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero,
          add_zero, zero_add, sub_zero, smul_smul, smul_sub]
        module
      map_zero' := by simp
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul, Matrix.mul_add, Matrix.add_mul]; abel }
  have hf : Continuous f :=
    (continuous_snd.smul continuous_const).add ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const)
  have e := NormedSpace.map_exp f hf (Z, 0)
  have e1 : f (Z, 0) = ι * Z * π := by simp [f]
  rw [e1] at e
  refine e.symm.trans ?_
  show (NormedSpace.exp ((Z, 0) : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ)).2 • (1 - ι * π) +
    ι * (NormedSpace.exp ((Z, 0) : Matrix (Fin n₁) (Fin n₁) ℂ × ℂ)).1 * π = _
  have a1 := NormedSpace.map_exp (RingHom.fst (Matrix (Fin n₁) (Fin n₁) ℂ) ℂ) continuous_fst (Z, 0)
  have a2 := NormedSpace.map_exp (RingHom.snd (Matrix (Fin n₁) (Fin n₁) ℂ) ℂ) continuous_snd (Z, 0)
  exact congrArg₂ (· + ·) ((congrArg (· • (1 - ι * π)) (a2.trans NormedSpace.exp_zero)).trans (one_smul _ _))
    (congrArg (ι * · * π) a1)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_proj (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) :
    ∃ π : Matrix (Fin n₁) (Fin n) E, π * H.ι = 1 ∧ H.ιᵀ * W.J = W₁.J * π.map σ ∧
      ∀ (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi (W₁ := W₁) H 1 h₁ m → mat m = incM F (1 - H.ι * π) + incM F H.ι * mat h₁ * incM F π := by
  choose α β z hz using fun j : Fin n => GlobalTheory.UnipCocptForm.decomp σ W.J W₁.J H.x H.y H.ι hsk hσ h.1 h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 hd (Pi.single j 1)
  let π : Matrix (Fin n₁) (Fin n) E := Matrix.of fun i j => z j i
  have e : (1 : Matrix (Fin n) (Fin n) E) = Matrix.vecMulVec H.x α + Matrix.vecMulVec H.y β + H.ι * π := by
    ext i j
    have := congrFun (hz j) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Matrix.mulVec, dotProduct] at this
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, π, Matrix.of_apply, Matrix.one_apply, this]
    ring
  have hv : ∀ v a : Fin n → E, (∀ u, form σ W.J (H.ι *ᵥ u) v = 0) →
      H.ιᵀ * W.J * (Matrix.vecMulVec v a).map σ = 0 := fun v a hv => by
    ext i j
    have := hv (Pi.single i 1)
    rw [Matrix.mulVec_single_one] at this
    simp only [form, dotProduct, Matrix.mulVec, Matrix.col, Matrix.transpose_apply,
      Finset.mul_sum] at this
    rw [Finset.sum_comm] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, Matrix.transpose_apply,
      Matrix.zero_apply, ← mul_assoc, ← Finset.sum_mul]
    simp only [← mul_assoc, ← Finset.sum_mul] at this
    rw [this, zero_mul]
  have e2 : H.ιᵀ * W.J = W₁.J * π.map σ := by
    have e3 := congrArg (fun X : Matrix (Fin n) (Fin n) E => H.ιᵀ * W.J * X.map σ) e
    simp only [Matrix.map_add _ (map_add σ), Matrix.mul_add, hv _ _ fun u => (h.2.2.2.2.1 u).1,
      hv _ _ fun u => (h.2.2.2.2.1 u).2, zero_add, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one] at e3
    rw [e3, Matrix.map_mul, ← Matrix.mul_assoc, h.2.2.2.2.2]
  have e4 : π * H.ι = 1 := by
    have e5 : W₁.J * (π * H.ι).map σ = W₁.J * (1 : Matrix (Fin n₁) (Fin n₁) E).map σ := by
      rw [Matrix.map_mul, ← Matrix.mul_assoc, ← e2, h.2.2.2.2.2, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one]
    have hu : IsUnit W₁.J := (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ hd)
    exact Matrix.map_injective (Function.LeftInverse.injective hσ) (hu.mul_left_cancel e5)
  refine ⟨π, e4, e2, fun h₁ m hm => ?_⟩
  obtain ⟨ax, ay, aι⟩ := hm
  simp only [inv_one, Units.val_one, map_one, one_smul] at ax ay
  have hvv : ∀ v a : Fin n → E, incM F (Matrix.vecMulVec v a) = Matrix.vecMulVec (incV F v) (incV F a) := fun v a =>
    Matrix.ext fun i j => map_mul (inclR (F := F) (AF F)) _ _
  have e6 : 1 - H.ι * π = Matrix.vecMulVec H.x α + Matrix.vecMulVec H.y β := by rw [sub_eq_iff_eq_add]; exact e
  have e7 : (1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.vecMulVec (incV F H.x) (incV F α) +
      Matrix.vecMulVec (incV F H.y) (incV F β) + incM F H.ι * incM F π := by
    have := congrArg (incM F) e
    rw [← hvv, ← hvv]
    simpa only [incM, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using this
  have e8 : incM F (1 - H.ι * π) = Matrix.vecMulVec (incV F H.x) (incV F α) +
      Matrix.vecMulVec (incV F H.y) (incV F β) := by
    rw [e6, ← hvv, ← hvv]; exact Matrix.map_add _ (map_add _) _ _
  rw [e8, ← aι]
  conv_lhs => rw [← Matrix.mul_one (mat m), e7]
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, ax, ay, Matrix.mul_assoc]

theorem isRealLine_conj {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

theorem isRealLine_block (h : IsCMExt F E σ) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} {π : Matrix (Fin n₁) (Fin n) E} (h1 : π * ι = 1)
    (h2 : (ι.map σ)ᵀ * J = J₁ * π) (h3 : J * ι = (π.map σ)ᵀ * J₁) (M : GAd σ J₁ → GAd σ J)
    (hM : ∀ x, (matHom _ σ J (M x)).1 = adMat F (1 - ι * π) + adMat F ι * (matHom _ σ J₁ x).1 * adMat F π)
    {γ : ℝ → GAd σ J₁} (hγ : IsRealLine σ J₁ γ) : IsRealLine σ J fun t => M (γ t) := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hone : adMat F (1 - ι * π) + adMat F ι * (1 : Matrix (Fin n₁) (Fin n₁) (AF F ⊗[F] E)) * adMat F π = 1 := by
    rw [Matrix.mul_one, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), sub_add_cancel,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ {R : Type} [CommRing R] (φ : AF F ⊗[F] E →+* R) (x : GAd σ J₁), (matHom _ σ J₁ x).1.map φ = 1 →
      (matHom _ σ J (M x)).1.map φ = 1 := fun φ x hx => by
    rw [hM, GlobalTheory.EmbHeight.map_aff, hx, ← Matrix.map_one φ (map_zero _) (map_one _), ← GlobalTheory.EmbHeight.map_aff, hone,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hs : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), ((X.map σ)ᵀ).map τ.1 = (X.map τ.1)ᴴ := fun X =>
    Matrix.ext fun i j => h.2.2.2 τ.1 (X j i)
  have g1 : π.map τ.1 * ι.map τ.1 = 1 := by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have g2 : (ι.map τ.1)ᴴ * J.map τ.1 = J₁.map τ.1 * π.map τ.1 := by rw [← hs, ← Matrix.map_mul, h2, Matrix.map_mul]
  have g3 : J.map τ.1 * ι.map τ.1 = (π.map τ.1)ᴴ * J₁.map τ.1 := by rw [← hs, ← Matrix.map_mul, h3, Matrix.map_mul]
  refine ⟨w, τ, ι.map τ.1 * Z * π.map τ.1, ?_, fun t => ?_⟩
  · calc _ = (π.map τ.1)ᴴ * Zᴴ * ((ι.map τ.1)ᴴ * J.map τ.1) + (J.map τ.1 * ι.map τ.1) * Z * π.map τ.1 := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (π.map τ.1)ᴴ * (Zᴴ * J₁.map τ.1 + J₁.map τ.1 * Z) * π.map τ.1 := by
          rw [g2, g3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨projArch σ J w (M (γ t)), GAd_ext σ J (fun u => ?_) fun v => ?_, ?_⟩
    · by_cases e : u = w
      · subst e; simp
      · rw [projArch_embArch_ne σ J e]
        have : projArch σ J₁ u (γ t) = 1 := by rw [e1, projArch_embArch_ne σ J₁ e]
        exact Subtype.ext (Units.ext (key (compInf F E u) (γ t) (congrArg (fun z => z.1.1) this)))
    · have : proj σ J₁ v (γ t) = 1 := by rw [e1]; simp
      rw [show proj σ J v (embArch σ J w (projArch σ J w (M (γ t)))) = 1 by simp]
      exact Subtype.ext (Units.ext (key (compFin F E v) (γ t) (congrArg (fun z => z.1.1) this)))
    · let φ := (infEmb τ).comp (compInf F E w)
      have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
        change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
        simp
      have h4 : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), (adMat F X).map φ = X.map τ.1 := fun X =>
        Matrix.ext fun i j => h0 _
      have h5 : (matHom _ σ J₁ (γ t)).1.map φ = NormedSpace.exp (t • Z) := by
        rw [← e2, ← projArch_embArch_self σ J₁ w y, ← e1]; rfl
      show (matHom _ σ J (M (γ t))).1.map φ = _
      rw [hM, GlobalTheory.EmbHeight.map_aff, h4, h4, h4, h5, ← Matrix.smul_mul, ← Matrix.mul_smul, exp_block _ _ g1,
        Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]

omit [NumberField E] in

theorem foldr_lineDer_hom {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    (M : GAd σ J₁ →* GAd σ J) (a : GAd σ J) (f : GAd σ J → ℂ) (l : List (ℝ → GAd σ J₁)) :
    l.foldr lineDer (fun x => f (M x * a)) =
      fun x => (l.map fun γ t => a⁻¹ * M (γ t) * a).foldr lineDer f (M x * a) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.foldr_cons]
    funext g
    simp only [lineDer]
    congr 1
    funext t
    simp [mul_assoc]

theorem one_mem_kInf {n : ℕ} (Y : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    (1 : UA σ Y.J) ∈ KInf σ Y τ := by
  have h1 : mat (1 : UA σ Y.J) = 1 := rfl
  refine ⟨?_, fun w => ?_⟩
  · show At (evI F) (mat (1 : UA σ Y.J) - 1)
    rw [h1, sub_self]
    unfold At
    simp
  · rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _

theorem growth_block (h : IsCMExt F E σ) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} {π : Matrix (Fin n₁) (Fin n) E} (h1 : π * ι = 1)
    (h2 : (ι.map σ)ᵀ * J = J₁ * π) (h3 : J * ι = (π.map σ)ᵀ * J₁) (M : GAd σ J₁ →* GAd σ J)
    (hM : ∀ x, (matHom _ σ J (M x)).1 = adMat F (1 - ι * π) + adMat F ι * (matHom _ σ J₁ x).1 * adMat F π)
    (a : GAd σ J) {f : GAd σ J → ℂ} {N : ℕ} (hN : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ C : ℝ, ∀ g, ‖l.foldr lineDer f g‖ ≤ C * (height σ J g : ℝ) ^ N)
    (l : List (ℝ → GAd σ J₁)) (hl : ∀ γ ∈ l, IsRealLine σ J₁ γ) :
    ∃ C : ℝ, ∀ x, ‖l.foldr lineDer (fun x => f (M x * a)) x‖ ≤ C * (height σ J₁ x : ℝ) ^ N := by
  obtain ⟨K, hK⟩ := GlobalTheory.EmbHeight.exists_heightGL_aff_le F (adMat F (1 - ι * π)) (adMat F ι) (adMat F π)
  have hK' : ∀ x, height σ J (M x) ≤ K * height σ J₁ x := fun x =>
    hK _ _ (hM x) (by rw [← map_inv, ← map_inv, ← map_inv]; exact hM x⁻¹)
  obtain ⟨C, hC⟩ := hN (l.map fun γ t => a⁻¹ * M (γ t) * a) (by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hγ'
    exact isRealLine_conj h (isRealLine_block h h1 h2 h3 M hM (hl γ hγ)) a)
  refine ⟨max C 0 * ((K : ℝ) * (height σ J a : ℝ)) ^ N, fun x => ?_⟩
  rw [foldr_lineDer_hom M a f l]
  have hh : (height σ J (M x * a) : ℝ) ≤ ((K : ℝ) * (height σ J a : ℝ)) * (height σ J₁ x : ℝ) := by
    have := (height_mul_le σ J (M x) a).trans (mul_le_mul' (hK' x) le_rfl)
    rw [mul_right_comm] at this
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ (height σ J (M x * a) : ℝ) := by positivity
  refine (hC _).trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg h0 N)).trans ?_)
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hh N) (le_max_right _ _)

omit [NumberField F] [NumberField E] in

theorem gram_rel (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} {π : Matrix (Fin n₁) (Fin n) E} (hsk : ∀ i j, σ (J j i) = -J i j)
    (hsk₁ : ∀ i j, σ (J₁ j i) = -J₁ i j) (p2 : ιᵀ * J = J₁ * π.map σ) (c : E) :
    (ι.map σ)ᵀ * (c • J.map σ) = (c • J₁.map σ) * π ∧ (c • J.map σ) * ι = (π.map σ)ᵀ * (c • J₁.map σ) := by
  have hmm : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), (X.map σ).map σ = X := fun X => Matrix.ext fun i j => hσ _
  constructor
  · have := congrArg (fun X : Matrix (Fin n₁) (Fin n) E => X.map σ) p2
    simp only [Matrix.map_mul, hmm] at this
    rw [Matrix.mul_smul, Matrix.smul_mul, ← this]; rfl
  · have := congrArg Matrix.transpose p2
    have t1 : J.map σ = -Jᵀ := Matrix.ext fun i j => hsk j i
    have t2 : J₁.map σ = -J₁ᵀ := Matrix.ext fun i j => hsk₁ j i
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_smul, Matrix.smul_mul, t1, t2, Matrix.neg_mul, Matrix.mul_neg, this]

theorem exists_hom_move (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E)
    {c : E} (hc : c ≠ 0) (M₀ : UA σ J₁ →* UA σ J) :
    ∃ M : GAd σ (c • J₁.map σ) →* GAd σ (c • J.map σ),
      (∀ x, (toGAd hσ J hc).symm (M x) = M₀ ((toGAd hσ J₁ hc).symm x)) ∧
      (∀ x, (matHom _ σ _ (M x)).1 = mat (M₀ ((toGAd hσ J₁ hc).symm x))) ∧
      ∀ x, (matHom _ σ _ x).1 = mat ((toGAd hσ J₁ hc).symm x) :=
  ⟨(toGAd hσ J hc).toMonoidHom.comp (M₀.comp (toGAd hσ J₁ hc).symm.toMonoidHom),
    fun _ => (toGAd hσ J hc).symm_apply_apply _, fun _ => rfl, fun _ => rfl⟩

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      ∃ N : ℕ, ∀ l : List (ℝ → GAd σ (c • Y₁.J.map σ)), (∀ γ ∈ l, IsRealLine σ (c • Y₁.J.map σ) γ) →
        ∃ C : ℝ, ∀ x, ‖l.foldr lineDer (fun x => g ((toGAd hσ Y₁.J hc).symm x)) x‖ ≤ C * (height σ (c • Y₁.J.map σ) x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hsk hP c hc _ fa hfa h _ _ g hg
  have hd : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact GlobalTheory.LeviUniqueCartan.det_ne_zero_of_isCartan _ _ _ (hP.2.2.2.2.2.2.2 w)
  have hH := GlobalTheory.ThK.GLTwo.IsIsoPlane.isHypPlane hP
  obtain ⟨M₀, -, hM₀, -⟩ := hH.exists_leviHom hσ hsk hd
  obtain ⟨π, p1, p2, p3⟩ := exists_proj hσ hH hsk hd
  obtain ⟨q2, q3⟩ := gram_rel hσ hsk (hH.skew hσ hsk) p2 c
  obtain ⟨N, hN⟩ := (hfa ⊥ fun x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one]; exact one_mem_kInf Y B.emb).growth
  obtain ⟨M, m1, m2, m3⟩ := exists_hom_move hσ Y.J Y₁.J hc M₀
  refine ⟨N, fun l hl => ?_⟩
  have hgf : (fun x => g ((toGAd hσ Y₁.J hc).symm x)) = fun x => fa ((toGAd hσ Y.J hc).symm (M x * toGAd hσ Y.J hc h)) :=
    funext fun x => by rw [hg _ _ (hM₀ _), map_mul, m1, MulEquiv.symm_apply_apply]
  have hM : ∀ x, (matHom _ σ _ (M x)).1 =
      adMat F (1 - P.ι * π) + adMat F P.ι * (matHom _ σ _ x).1 * adMat F π := fun x => by
    rw [m2, m3, p3 _ _ (hM₀ _)]
    rfl
  rw [hgf]
  exact growth_block (f := fun x => fa ((toGAd hσ Y.J hc).symm x)) hB.cm p1 q2 q3 M hM (toGAd hσ Y.J hc h) hN l hl

end GlobalTheory.ThK.DescB.GenGrowth

end
end

section
noncomputable section

namespace GlobalTheory.ThK.DescB.LeviFirst

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.LeviLine
open GlobalTheory.Doubling (absE)
open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gram_skew {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (hJ : ∀ i j, σ (J j i) = -J i j) (i j : Fin n₁) :
    σ ((ιᵀ * J * ι.map σ) j i) = -(ιᵀ * J * ι.map σ) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, sigma_invol hcm, hJ,
    Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.ThK.DescB.LeviFirst

namespace GlobalTheory.ThK.DescB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

end GlobalTheory.ThK.DescB

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.CentreTwoExists

open GlobalTheory.LeviLine Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_levi_of_unit (hcm : IsCMExt F E σ) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hskew : ∀ i j, σ (Y.J j i) = -Y.J i j) (hxx' : form σ Y.J H.x H.x = 0) (hyy' : form σ Y.J H.y H.y = 0)
    (hxy' : form σ Y.J H.x H.y = 1)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) (t : (AE F E)ˣ) :
    ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H t 1 m := by
  set c : AE F E →+* AE F E := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hcdef
  have hc : ∀ r, c (c r) = r := cA_invol hcm
  have hJ : ∀ i j, c (incM F Y.J j i) = -incM F Y.J i j := by
    intro i j
    change cA σ (inclR (F := F) (AF F) (Y.J j i)) = -inclR (F := F) (AF F) (Y.J i j)
    rw [cA_inclR, hskew i j, map_neg]
  have hxx : sf c (incM F Y.J) (incV F H.x) (incV F H.x) = 0 := by rw [sf_inc, hxx', map_zero]
  have hyy : sf c (incM F Y.J) (incV F H.y) (incV F H.y) = 0 := by rw [sf_inc, hyy', map_zero]
  have hxy : sf c (incM F Y.J) (incV F H.x) (incV F H.y) = 1 := by rw [sf_inc, hxy', map_one]
  have hyx : sf c (incM F Y.J) (incV F H.y) (incV F H.x) = -1 := by rw [sf_skew c _ hc hJ, hxy, map_one]
  have hts : (t : AE F E) * c (c (↑t⁻¹ : AE F E)) = 1 := by rw [hc, Units.mul_inv]
  have hst : c (↑t⁻¹ : AE F E) * c (t : AE F E) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  let L := levi c (incM F Y.J) (incV F H.x) (incV F H.y)
  let g : GL (Fin n) (AE F E) :=
    ⟨L t (c ↑t⁻¹), L ↑t⁻¹ (c t), by
      rw [levi_mul hc hJ hxx hyy hxy, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levi_one],
      by rw [levi_mul hc hJ hxx hyy hxy, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levi_one]⟩
  have hg : g ∈ UG (cA σ) (incM F Y.J) := levi_unitary hc hJ hxx hyy hxy hts hst
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
  · change L t (c ↑t⁻¹) *ᵥ incV F H.x = _
    rw [levi_mulVec, hxx, hxy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) *ᵥ incV F H.y = c ↑t⁻¹ • incV F H.y
    rw [levi_mulVec, hyy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) * incM F H.ι = incM F H.ι * (1 : Matrix (Fin n₁) (Fin n₁) (AE F E))
    rw [Matrix.mul_one]
    refine ext_mulVec_single fun k => ?_
    have hcol : incM F H.ι *ᵥ Pi.single k 1 = incV F (H.ι *ᵥ Pi.single k 1) := by
      ext i
      simp [mulVec_single_one, incM, incV]
    rw [← mulVec_mulVec, hcol]
    exact levi_mulVec_of_orth _ _ _ _ (by rw [sf_inc, (horth _).1, map_zero]) (by rw [sf_inc, (horth _).2, map_zero])


end GlobalTheory.ThK.DescB.CentreTwoExists

namespace GlobalTheory.ThK.DescB

open GlobalTheory.ThK.DescB.CentreTwoExists Matrix

end GlobalTheory.ThK.DescB

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Gen

variable {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def fR (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

theorem fR_add_left (u u' v : Fin n → R) : fR c J (u + u') v = fR c J u v + fR c J u' v := by
  simp [fR, add_dotProduct]

theorem fR_sub_left (u u' v : Fin n → R) : fR c J (u - u') v = fR c J u v - fR c J u' v := by
  simp [fR, sub_dotProduct]

theorem fR_smul_left (r : R) (u v : Fin n → R) : fR c J (r • u) v = r * fR c J u v := by
  simp [fR, smul_dotProduct]

theorem fR_add_right (u v v' : Fin n → R) : fR c J u (v + v') = fR c J u v + fR c J u v' := by
  have h : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_add, dotProduct_add]

theorem fR_sub_right (u v v' : Fin n → R) : fR c J u (v - v') = fR c J u v - fR c J u v' := by
  have h : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_sub, dotProduct_sub]

theorem fR_smul_right (r : R) (u v : Fin n → R) : fR c J u (r • v) = c r * fR c J u v := by
  have h : (fun i => c ((r • v) i)) = c r • fun i => c (v i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fR_skew (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (u v : Fin n → R) :
    c (fR c J u v) = -fR c J v u := by
  simp only [fR, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem fR_mulVec (A : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    fR c J (A *ᵥ u) (A *ᵥ v) = u ⬝ᵥ (Aᵀ * J * A.map c) *ᵥ (fun i => c (v i)) := by
  have h : (fun i => c ((A *ᵥ v) i)) = A.map c *ᵥ fun i => c (v i) := by
    funext i; exact RingHom.map_mulVec c A v i
  simp only [fR, h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Aᵀ, Matrix.vecMul_transpose]

theorem eq_of_form (M N : Matrix (Fin n) (Fin n) R)
    (h : ∀ u v : Fin n → R, u ⬝ᵥ M *ᵥ (fun i => c (v i)) = u ⬝ᵥ N *ᵥ (fun i => c (v i))) : M = N := by
  ext i j
  have hs : (fun k => c ((Pi.single j (1 : R) : Fin n → R) k)) = Pi.single j 1 := by
    funext k; by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [Matrix.mulVec_single_one] using this

theorem eq_of_mulVec (M N : Matrix (Fin n) (Fin n) R) (h : ∀ u, M *ᵥ u = N *ᵥ u) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

def lev (x y : Fin n → R) (t s : R) : Matrix (Fin n) (Fin n) R :=
  1 + (t - 1) • vecMulVec x (J *ᵥ fun i => c (y i)) - (s - 1) • vecMulVec y (J *ᵥ fun i => c (x i))

variable {c J}
variable {x y : Fin n → R} (hxx : fR c J x x = 0) (hyy : fR c J y y = 0) (hxy : fR c J x y = 1)
  (hyx : fR c J y x = -1)
include hxx hyy hxy hyx

end Gen

end GlobalTheory.AdelicPlaneLevi

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem sigma_invol {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem fR_inc (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → E) :
    fR (cA σ).toRingHom (incM F J) (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  simp [fR, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_incl]

end Main

end GlobalTheory.AdelicPlaneLevi

end
end

section
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev gm {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p : GAd σ J) : Matrix (Fin n) (Fin n) (AE F E) := (matHom _ σ J p).1

theorem gm_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : gm (1 : GAd σ J) = 1 := by
  simp only [gm, map_one, Units.val_one]

theorem gm_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p q : GAd σ J) : gm (p * q) = gm p * gm q := by
  simp only [gm, map_mul, Units.val_mul]

theorem gm_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p : GAd σ J) : gm p⁻¹ * gm p = 1 := by
  simp only [gm, map_inv]; exact Units.inv_mul _

theorem fR_gm (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (p : GAd σ (c • J.map σ)) (u v : Fin n → AE F E) :
    fR (cA σ).toRingHom (incM F J) (gm p *ᵥ u) (gm p *ᵥ v) = fR (cA σ).toRingHom (incM F J) u v := by
  have hU : (gm p)ᵀ * incM F J * (gm p).map (cA σ).toRingHom = incM F J :=
    ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ J hc).symm p).2
  rw [fR_mulVec, hU]; rfl

theorem mul_fR_eq_one (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} (hc : c ≠ 0)
    {x y : Fin n → E} (hxy : form σ J x y = 1) (p : GAd σ (c • J.map σ)) {t : AE F E}
    (ht : gm p *ᵥ incV F x = t • incV F x) : t * fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y) = 1 := by
  have h := fR_gm hσ J hc p (incV F x) (incV F y)
  rw [ht, fR_smul_left, fR_inc, hxy, map_one] at h
  exact h

def stab (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (x y : Fin n → E) (hxy : form σ J x y = 1) : Subgroup (GAd σ (c • J.map σ)) where
  carrier := {p | ∃ t : AE F E, gm p *ᵥ incV F x = t • incV F x}
  one_mem' := ⟨1, by rw [gm_one, Matrix.one_mulVec, one_smul]⟩
  mul_mem' := by
    rintro p q ⟨t, ht⟩ ⟨s, hs⟩
    refine ⟨s * t, ?_⟩
    rw [gm_mul, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul, ht, smul_smul]
  inv_mem' := by
    rintro p ⟨t, ht⟩
    refine ⟨fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y), ?_⟩
    have e := mul_fR_eq_one hσ hc hxy p ht
    have h1 : incV F x = t • (gm p⁻¹ *ᵥ incV F x) := by
      rw [← Matrix.mulVec_smul, ← ht, Matrix.mulVec_mulVec, gm_inv_mul, Matrix.one_mulVec]
    generalize fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y) = s at e ⊢
    calc gm p⁻¹ *ᵥ incV F x = (t * s) • (gm p⁻¹ *ᵥ incV F x) := by rw [e, one_smul]
      _ = s • (t • (gm p⁻¹ *ᵥ incV F x)) := by rw [smul_smul, mul_comm]
      _ = s • incV F x := by rw [← h1]

theorem mem_stab {hσ : ∀ x, σ (σ x) = x} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} {hc : c ≠ 0}
    {x y : Fin n → E} {hxy : form σ J x y = 1} {p : GAd σ (c • J.map σ)} :
    p ∈ stab hσ J hc x y hxy ↔ ∃ t : AE F E, gm p *ᵥ incV F x = t • incV F x := Iff.rfl

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local instance topRingAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_gm {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous (gm : GAd σ J → Matrix (Fin n) (Fin n) (AE F E)) :=
  Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous

def tv {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) {J' : Matrix (Fin n) (Fin n) E} (p : GAd σ J') : AE F E :=
  fR (cA σ).toRingHom (incM F J) (gm p *ᵥ incV F x) (incV F y)

theorem continuous_tv {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (J' : Matrix (Fin n) (Fin n) E) :
    Continuous (tv (σ := σ) J x y (J' := J')) :=
  ((continuous_gm J').matrix_mulVec continuous_const).dotProduct continuous_const

variable {hσ : ∀ x, σ (σ x) = x} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} {hc : c ≠ 0}
    {x y : Fin n → E} {hxy : form σ J x y = 1}

theorem gm_x {p : GAd σ (c • J.map σ)} (hp : p ∈ stab hσ J hc x y hxy) : gm p *ᵥ incV F x = tv J x y p • incV F x := by
  obtain ⟨t, ht⟩ := hp
  rw [tv, ht, fR_smul_left, fR_inc, hxy, map_one, mul_one]

theorem isUnit_tv {p : GAd σ (c • J.map σ)} (hp : p ∈ stab hσ J hc x y hxy) : IsUnit (tv (σ := σ) J x y p) :=
  ⟨⟨_, _, mul_fR_eq_one hσ hc hxy p (gm_x hp), by rw [mul_comm]; exact mul_fR_eq_one hσ hc hxy p (gm_x hp)⟩, rfl⟩

variable (hσ J hc x y hxy) in

def tHom : stab hσ J hc x y hxy →* AE F E where
  toFun p := tv J x y p.1
  map_one' := by
    show fR _ _ (gm (1 : GAd σ (c • J.map σ)) *ᵥ _) _ = 1
    rw [gm_one, Matrix.one_mulVec, fR_inc, hxy, map_one]
  map_mul' p q := by
    show fR _ _ (gm (p.1 * q.1) *ᵥ _) _ = tv J x y p.1 * tv J x y q.1
    rw [gm_mul, ← Matrix.mulVec_mulVec, gm_x q.2, Matrix.mulVec_smul, gm_x p.2, smul_smul, fR_smul_left, fR_inc, hxy,
      map_one, mul_one, mul_comm]

variable (hσ J hc x y hxy) in

def tUnits : stab hσ J hc x y hxy →* (AE F E)ˣ := IsUnit.liftRight (tHom hσ J hc x y hxy) fun p => isUnit_tv p.2

theorem gm_x_units (p : stab hσ J hc x y hxy) : gm p.1 *ᵥ incV F x = (tUnits hσ J hc x y hxy p : AE F E) • incV F x := gm_x p.2

theorem continuous_tUnits : Continuous (tUnits hσ J hc x y hxy) := by
  refine Units.continuous_iff.2 ⟨(continuous_tv J x y _).comp continuous_subtype_val, ?_⟩
  have e : (fun p => ((tUnits hσ J hc x y hxy p)⁻¹ : (AE F E)ˣ).1) = fun p => tv J x y (p⁻¹ : stab hσ J hc x y hxy).1 := by
    funext p; rw [← map_inv]; rfl
  rw [e]
  exact (continuous_tv J x y _).comp (continuous_subtype_val.comp continuous_inv)

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fR_mulVec_rect {R : Type} [CommRing R] (cc : R →+* R) {a b : ℕ} (J : Matrix (Fin a) (Fin a) R)
    (X : Matrix (Fin a) (Fin b) R) (u v : Fin b → R) :
    fR cc J (X *ᵥ u) (X *ᵥ v) = fR cc (Xᵀ * J * X.map cc) u v := by
  have h : (fun i => cc ((X *ᵥ v) i)) = X.map cc *ᵥ fun i => cc (v i) := by
    funext i; exact RingHom.map_mulVec cc X v i
  simp only [fR, h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Xᵀ, Matrix.vecMul_transpose]

theorem fR_mulVec_left {R : Type} [CommRing R] (cc : R →+* R) {a b : ℕ} (J : Matrix (Fin a) (Fin a) R)
    (X : Matrix (Fin a) (Fin b) R) (z : Fin b → R) (v : Fin a → R) :
    fR cc J (X *ᵥ z) v = z ⬝ᵥ (Xᵀ * J) *ᵥ (fun i => cc (v i)) := by
  simp only [fR]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z Xᵀ, Matrix.vecMul_transpose]

theorem tr_mul_mulVec_eq_zero {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin n₁) E} {v : Fin n → E}
    (h : ∀ u, form σ J (ι *ᵥ u) v = 0) : (ιᵀ * J) *ᵥ (fun i => σ (v i)) = 0 := by
  funext i
  have := h (Pi.single i 1)
  rw [Matrix.mulVec_single_one] at this
  rw [← Matrix.mulVec_mulVec]
  exact this

theorem cA_incV {n : ℕ} (v : Fin n → E) : (fun i => (cA σ).toRingHom (incV F v i)) = incV F (fun i => σ (v i)) := by
  funext i; exact cA_incl σ (v i)

theorem fR_incM_left {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin n₁) E} {v : Fin n → E}
    (h : ∀ u, form σ J (ι *ᵥ u) v = 0) (z : Fin n₁ → AE F E) :
    fR (cA σ).toRingHom (incM F J) (incM F ι *ᵥ z) (incV F v) = 0 := by
  rw [fR_mulVec_left, cA_incV]
  have e : (incM F ι)ᵀ * incM F J = incM F (ιᵀ * J) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e, ← GlobalTheory.UnipCocptForm.incV_mulVec, tr_mul_mulVec_eq_zero h]
  simp [incV, dotProduct]

theorem mulVec_eq_zero_of_tr {n n₁ : ℕ} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {A : Matrix (Fin n₁) (Fin n) E} (hd : J₁.det ≠ 0)
    (hA : ιᵀ * J = J₁ * A.map σ) {v : Fin n → E} (h : ∀ u, form σ J (ι *ᵥ u) v = 0) : A *ᵥ v = 0 := by
  have e := tr_mul_mulVec_eq_zero h
  rw [hA, ← Matrix.mulVec_mulVec] at e
  have e2 : A.map σ *ᵥ (fun i => σ (v i)) = fun i => σ ((A *ᵥ v) i) := by
    funext i; exact (RingHom.map_mulVec (σ : E →+* E) A v i).symm
  rw [e2] at e
  have e3 := Matrix.eq_zero_of_mulVec_eq_zero hd e
  funext i
  have := congrFun e3 i
  simp only [Pi.zero_apply] at this ⊢
  rw [← hσ ((A *ᵥ v) i), this, map_zero]

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def hm {n n₁ : ℕ} (A : Matrix (Fin n₁) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) {J' : Matrix (Fin n) (Fin n) E}
    (p : GAd σ J') : Matrix (Fin n₁) (Fin n₁) (AE F E) :=
  incM F A * gm p * incM F ι

theorem incM_one' {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp only [incM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_mul'' {a b d : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin d) E) :
    incM F (X * Y) = incM F X * incM F Y := by
  simp only [incM, Matrix.map_mul]

variable {hσ : ∀ x, σ (σ x) = x} {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {c : E} {hc : c ≠ 0}
  {hxy : form σ W.J H.x H.y = 1}

theorem fR_basic (hσ' : ∀ x, σ (σ x) = x) (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) :
    fR (cA σ).toRingHom (incM F W.J) (incV F H.x) (incV F H.x) = 0 ∧
    fR (cA σ).toRingHom (incM F W.J) (incV F H.y) (incV F H.x) = -1 ∧
    (∀ r, (cA σ).toRingHom ((cA σ).toRingHom r) = r) ∧
    ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := by
  have hcc : ∀ r, (cA σ).toRingHom ((cA σ).toRingHom r) = r := cA_cA σ hσ'
  have hJ : ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := fun i j => by
    change cA σ (inclR (F := F) (AF F) (W.J j i)) = -inclR (F := F) (AF F) (W.J i j)
    rw [cA_incl, hsk, map_neg]
  refine ⟨by rw [fR_inc, hH.2.1, map_zero], ?_, hcc, hJ⟩
  have := fR_skew (cA σ).toRingHom (incM F W.J) hcc hJ (incV F H.x) (incV F H.y)
  rw [fR_inc, hH.2.2.2.1, map_one, map_one] at this
  linear_combination this

theorem decomp (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ)
    {p : GAd σ (c • W.J.map σ)} (hp : p ∈ stab hσ W.J hc H.x H.y hxy) (z : Fin n₁ → AE F E) :
    fR (cA σ).toRingHom (incM F W.J) (gm p *ᵥ (incM F H.ι *ᵥ z)) (incV F H.x) = 0 ∧
      ∃ a : AE F E, gm p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (hm A H.ι p *ᵥ z) + a • incV F H.x := by
  obtain ⟨hxx, hyx, -, -⟩ := fR_basic hσ hH hsk
  have hox : ∀ w, fR (cA σ).toRingHom (incM F W.J) (incM F H.ι *ᵥ w) (incV F H.x) = 0 :=
    fR_incM_left fun u => (hH.2.2.2.2.1 u).1
  have h0 : fR (cA σ).toRingHom (incM F W.J) (gm p *ᵥ (incM F H.ι *ᵥ z)) (incV F H.x) = 0 := by
    have e1 := fR_gm hσ W.J hc p (incM F H.ι *ᵥ z) (incV F H.x)
    rw [gm_x hp, fR_smul_right, hox] at e1
    exact (((isUnit_tv hp).map (cA σ).toRingHom).mul_right_eq_zero).1 e1
  refine ⟨h0, ?_⟩
  obtain ⟨α, β, w, hv⟩ := hH.decompA hσ hsk hd (gm p *ᵥ (incM F H.ι *ᵥ z))
  have hβ : β = 0 := by
    rw [hv, fR_add_left, fR_add_left, fR_smul_left, fR_smul_left, hxx, hyx, hox] at h0
    linear_combination -h0
  have hAx : incM F A *ᵥ incV F H.x = 0 := by
    rw [← GlobalTheory.UnipCocptForm.incV_mulVec, mulVec_eq_zero_of_tr hσ hd hA2 fun u => (hH.2.2.2.2.1 u).1]
    funext i; simp [incV]
  have hAι : incM F A * incM F H.ι = 1 := by rw [← incM_mul'', hA1, incM_one']
  have hw : hm A H.ι p *ᵥ z = w := by
    rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, hβ, zero_smul, add_zero, Matrix.mulVec_add,
      Matrix.mulVec_smul, hAx, smul_zero, zero_add, Matrix.mulVec_mulVec, hAι, Matrix.one_mulVec]
  refine ⟨α, ?_⟩
  rw [hw, hv, hβ, zero_smul, add_zero, add_comm]

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {hσ : ∀ x, σ (σ x) = x} {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {c : E} {hc : c ≠ 0}
  {hxy : form σ W.J H.x H.y = 1}

theorem A_facts (hσ' : ∀ x, σ (σ x) = x) (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ) :
    incM F A *ᵥ incV F H.x = 0 ∧ incM F A * incM F H.ι = 1 := by
  refine ⟨?_, by rw [← incM_mul'', hA1, incM_one']⟩
  rw [← GlobalTheory.UnipCocptForm.incV_mulVec, mulVec_eq_zero_of_tr hσ' hd hA2 fun u => (hH.2.2.2.2.1 u).1]
  funext i; simp [incV]

theorem hm_one {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) {J' : Matrix (Fin n) (Fin n) E} :
    hm A H.ι (1 : GAd σ J') = 1 := by
  rw [hm, gm_one, Matrix.mul_one, ← incM_mul'', hA1, incM_one']

theorem hm_mul (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ)
    {p q : GAd σ (c • W.J.map σ)} (hp : p ∈ stab hσ W.J hc H.x H.y hxy) (hq : q ∈ stab hσ W.J hc H.x H.y hxy) :
    hm A H.ι (p * q) = hm A H.ι p * hm A H.ι q := by
  obtain ⟨hAx, hAι⟩ := A_facts hσ hH hd hA1 hA2
  refine eq_of_mulVec _ _ fun z => ?_
  obtain ⟨a, ha⟩ := (decomp hH hsk hd hA1 hA2 hq z).2
  obtain ⟨b, hb⟩ := (decomp hH hsk hd hA1 hA2 hp (hm A H.ι q *ᵥ z)).2
  rw [← Matrix.mulVec_mulVec, hm, gm_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha,
    Matrix.mulVec_add, hb, Matrix.mulVec_smul, gm_x hp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hAx, Matrix.mulVec_smul, hAx, Matrix.mulVec_mulVec, hAι, Matrix.one_mulVec]
  simp

theorem gram_inc (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) :
    (incM F H.ι)ᵀ * incM F W.J * (incM F H.ι).map (cA σ).toRingHom = incM F W₁.J := by
  have e : (incM F H.ι).map (cA σ).toRingHom = incM F (H.ι.map σ) := by
    ext i j; exact cA_incl σ (H.ι i j)
  have e2 : (incM F H.ι)ᵀ = incM F H.ιᵀ := rfl
  rw [e, e2, ← incM_mul'', ← incM_mul'', hH.2.2.2.2.2]

theorem hm_unitary (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ)
    {p : GAd σ (c • W.J.map σ)} (hp : p ∈ stab hσ W.J hc H.x H.y hxy) :
    (hm A H.ι p)ᵀ * incM F W₁.J * (hm A H.ι p).map (cA σ).toRingHom = incM F W₁.J := by
  obtain ⟨hxx, -, hcc, hJ⟩ := fR_basic hσ hH hsk
  refine eq_of_form (cA σ).toRingHom _ _ fun u v => ?_
  rw [← fR_mulVec]
  change _ = fR (cA σ).toRingHom (incM F W₁.J) u v
  rw [← gram_inc hH, ← fR_mulVec_rect, ← fR_mulVec_rect]
  obtain ⟨hu0, a, ha⟩ := decomp hH hsk hd hA1 hA2 hp u
  obtain ⟨hv0, b, hb⟩ := decomp hH hsk hd hA1 hA2 hp v
  have hu : incM F H.ι *ᵥ (hm A H.ι p *ᵥ u) = gm p *ᵥ (incM F H.ι *ᵥ u) - a • incV F H.x := by rw [ha]; abel
  have hv : incM F H.ι *ᵥ (hm A H.ι p *ᵥ v) = gm p *ᵥ (incM F H.ι *ᵥ v) - b • incV F H.x := by rw [hb]; abel
  have hxv : fR (cA σ).toRingHom (incM F W.J) (incV F H.x) (gm p *ᵥ (incM F H.ι *ᵥ v)) = 0 := by
    have := fR_skew (cA σ).toRingHom (incM F W.J) hcc hJ (gm p *ᵥ (incM F H.ι *ᵥ v)) (incV F H.x)
    rw [hv0, map_zero] at this
    linear_combination this
  rw [hu, hv, fR_sub_left, fR_sub_right, fR_sub_right, fR_smul_left, fR_smul_right, fR_smul_left, fR_smul_right, hu0,
    hxv, hxx, fR_gm hσ W.J hc p]
  ring

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local instance topRingAE' : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

variable (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) {c : E} (hc : c ≠ 0)
  (hxy : form σ W.J H.x H.y = 1)

def piU (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    (A : Matrix (Fin n₁) (Fin n) E) (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ) :
    stab hσ W.J hc H.x H.y hxy →* UA σ W₁.J where
  toFun p := ⟨⟨hm A H.ι p.1, hm A H.ι (p⁻¹).1,
    by rw [← hm_mul hH hsk hd hA1 hA2 p.2 (p⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, hm_one hA1],
    by rw [← hm_mul hH hsk hd hA1 hA2 (p⁻¹).2 p.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, hm_one hA1]⟩,
    hm_unitary hH hsk hd hA1 hA2 p.2⟩
  map_one' := Subtype.ext (Units.ext (hm_one hA1))
  map_mul' p q := Subtype.ext (Units.ext (hm_mul hH hsk hd hA1 hA2 p.2 q.2))

theorem continuous_piU (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    (A : Matrix (Fin n₁) (Fin n) E) (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ) :
    Continuous (piU hσ W W₁ H hc hxy hH hsk hd A hA1 hA2) := by
  have hg : Continuous fun p : stab hσ W.J hc H.x H.y hxy => hm A H.ι p.1 :=
    (continuous_const.matrix_mul ((continuous_gm _).comp continuous_subtype_val)).matrix_mul continuous_const
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hg, ?_⟩) _
  exact hg.comp continuous_inv

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

theorem exists_stab_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (X' Y' : Matrix (Fin n) (Fin (r + 1)) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) →
      ∃ (P : Subgroup (GAd σ (c₀ • W.J.map σ))) (π : P →* GAd σ (c₀ • W₁.J.map σ)) (T : P →* (AE F E)ˣ),
        (∀ p, p ∈ P ↔ ∃ t : AF F ⊗[F] E, (matHom _ σ _ p).1 *ᵥ (fun i => inclR (F := F) (AF F) (H.x i)) = t • fun i => inclR (F := F) (AF F) (H.x i)) ∧
        (∀ p : P, ∃ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∃ m, IsLevi (W₁ := W₁) H (T p) 1 m ∧
          (p : GAd σ (c₀ • W.J.map σ)) = u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M (π p)) ∧
        (∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∀ t m y, IsLevi (W₁ := W₁) H t 1 m →
          u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ P) ∧
        Continuous π ∧ Continuous T ∧
        ∃ A : Matrix (Fin n₁) (Fin n) E, A * H.ι = 1 ∧ ∀ p : P, (matHom _ σ _ (π p)).1 =
          GlobalTheory.SiegelSet.adMat F A * (matHom _ σ _ (p : GAd σ (c₀ • W.J.map σ))).1 * GlobalTheory.SiegelSet.adMat F H.ι := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hW₁ hW M hM r X' Y' hwitt hX0
  have hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hgram⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hW₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  obtain ⟨A, hA1, hA2, -⟩ := GlobalTheory.ThK.DescB.GenGrowth.exists_proj hσ hH hsk hd
  let πU := piU hσ W W₁ H hc₀ hxy hH hsk hd A hA1 hA2
  let π : stab hσ W.J hc₀ H.x H.y hxy →* GAd σ (c₀ • W₁.J.map σ) :=
    (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).toMonoidHom.comp πU
  let T := tUnits hσ W.J hc₀ H.x H.y hxy
  have h0 : 0 < r + 1 := Nat.succ_pos r
  have hX : ∀ k, X' k ⟨0, h0⟩ = H.x k := hX0
  have hfix : ∀ g : UA σ W.J, g ∈ GlobalTheory.ThK.unip σ W H → mat g *ᵥ incV F H.x = incV F H.x := by
    intro g hg
    refine Subgroup.closure_induction (fun g hg => hg.1) (Matrix.one_mulVec _) (fun a b _ _ ha hb => ?_)
      (fun a _ ha => ?_) hg
    · change (mat a * mat b) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, hb, ha]
    · have e : mat a⁻¹ * mat a = 1 := by change mat (a⁻¹ * a) = 1; rw [inv_mul_cancel]; rfl
      conv_lhs => rw [← ha, Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  refine ⟨stab hσ W.J hc₀ H.x H.y hxy, π, T, fun p => Iff.rfl, fun p => ?_, fun u hu t m y hml => ?_, ?_,
    continuous_tUnits, A, hA1, fun p => rfl⟩
  · obtain ⟨m, hml⟩ := GlobalTheory.ThK.DescB.CentreTwoExists.exists_levi_of_unit hcm W W₁ H hsk hxx hyy hxy horth (T p)
    let h := πU p
    let q : UA σ W.J := m * M h
    let g0 : UA σ W.J := (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm p.1
    have hmq : mat q *ᵥ incV F H.x = (T p : AE F E) • incV F H.x := by
      change (mat m * mat (M h)) *ᵥ _ = _
      have e1 := (hM h).1
      simp only [Units.val_one, one_smul] at e1
      rw [← Matrix.mulVec_mulVec, e1, hml.1]
    have hqι : mat q * incM F H.ι = incM F H.ι * mat h := by
      change (mat m * mat (M h)) * incM F H.ι = incM F H.ι * mat h
      have e2 := hml.2.2
      rw [show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.mul_one] at e2
      rw [Matrix.mul_assoc, (hM h).2.2, ← Matrix.mul_assoc, e2]
    have hqq : mat q⁻¹ * mat q = 1 := by change mat (q⁻¹ * q) = 1; rw [inv_mul_cancel]; rfl
    have hhh : mat h * mat h⁻¹ = 1 := by change mat (h * h⁻¹) = 1; rw [mul_inv_cancel]; rfl
    have hmem : g0 * q⁻¹ ∈ GlobalTheory.ThK.unip σ W H := by
      refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
      · have e : mat (g0 * q⁻¹) *ᵥ (mat q *ᵥ incV F H.x) = (T p : AE F E) • incV F H.x := by
          change (gm p.1 * mat q⁻¹) *ᵥ _ = _
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hqq, Matrix.mul_one]
          exact gm_x_units p
        rw [hmq, Matrix.mulVec_smul] at e
        have := congrArg (fun w => ((T p)⁻¹ : (AE F E)ˣ).1 • w) e
        simpa only [smul_smul, Units.inv_mul, one_smul] using this
      · obtain ⟨a, ha⟩ := (decomp hH hsk hd hA1 hA2 p.2 (mat h⁻¹ *ᵥ z)).2
        refine ⟨a, ?_⟩
        have e : incM F H.ι *ᵥ z = mat q *ᵥ (incM F H.ι *ᵥ (mat h⁻¹ *ᵥ z)) := by
          symm
          rw [Matrix.mulVec_mulVec, hqι, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (mat h), hhh, Matrix.one_mulVec]
        conv_lhs => rw [e]
        change (gm p.1 * mat q⁻¹) *ᵥ _ = _
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hqq, Matrix.mul_one, ha,
          show hm A H.ι p.1 = mat h from rfl, Matrix.mulVec_mulVec _ (mat h), hhh, Matrix.one_mulVec]
    refine ⟨GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (g0 * q⁻¹),
      (GlobalTheory.ThK.GLTwo.IsHypPlane.mem_unip_iff hσ hH hsk hd hc₀ hwitt h0 hX _).1 hmem, m, hml, ?_⟩
    have e1 : GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M (π p) = GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M h) := by
      simp only [GlobalTheory.ThK.CuspTransfer.emb, π, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.symm_apply_apply]
      rfl
    have e2 : g0 * q⁻¹ * m * M h = g0 := by
      rw [mul_assoc, show m * M h = q from rfl, inv_mul_cancel_right]
    rw [e1, ← map_mul, ← map_mul, e2]
    exact (MulEquiv.apply_symm_apply _ _).symm
  · have hu' : (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm u ∈ GlobalTheory.ThK.unip σ W H :=
      (GlobalTheory.ThK.GLTwo.IsHypPlane.mem_unip_iff hσ hH hsk hd hc₀ hwitt h0 hX _).2 (by rwa [MulEquiv.apply_symm_apply])
    have ux := hfix _ hu'
    refine (mem_stab).2 ⟨t.1, ?_⟩
    rw [gm_mul, gm_mul]
    have e1 := (hM ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm y)).1
    simp only [Units.val_one, one_smul] at e1
    change (gm u * mat m * mat (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm y))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, hml.1, Matrix.mulVec_smul]
    exact congrArg _ ux
  · exact (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ W₁.J hc₀).1.comp (continuous_piU hσ W W₁ H hc₀ hxy hH hsk hd A hA1 hA2)

end GlobalTheory.StabLine
end
end
end
end
end
end
end
end

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_plane_stabilizer_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (X' Y' : Matrix (Fin n) (Fin (r + 1)) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) →
      ∃ (P : Subgroup (GAd σ (c₀ • W.J.map σ))) (π : P →* GAd σ (c₀ • W₁.J.map σ)) (T : P →* (AE F E)ˣ),
        (∀ p, p ∈ P ↔ ∃ t : AF F ⊗[F] E, (matHom _ σ _ p).1 *ᵥ (fun i => inclR (F := F) (AF F) (H.x i)) = t • fun i => inclR (F := F) (AF F) (H.x i)) ∧
        (∀ p : P, ∃ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∃ m, IsLevi (W₁ := W₁) H (T p) 1 m ∧
          (p : GAd σ (c₀ • W.J.map σ)) = u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M (π p)) ∧
        (∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∀ t m y, IsLevi (W₁ := W₁) H t 1 m →
          u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ P) ∧
        Continuous π ∧ Continuous T ∧
        ∃ A : Matrix (Fin n₁) (Fin n) E, A * H.ι = 1 ∧ ∀ p : P, (matHom _ σ _ (π p)).1 =
          GlobalTheory.SiegelSet.adMat F A * (matHom _ σ _ (p : GAd σ (c₀ • W.J.map σ))).1 * GlobalTheory.SiegelSet.adMat F H.ι := by
  atlas_forward_decl GlobalTheory.StabLine.exists_stab_decomp
end
