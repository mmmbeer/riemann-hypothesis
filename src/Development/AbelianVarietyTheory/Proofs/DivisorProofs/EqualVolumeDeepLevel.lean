import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StrongApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImage
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentSingleAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFullLevelGroupIffCongruenceLcm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThree
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevelGroup_data_same_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, ∃ Y : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y.Ψ = (U.X k).Ψ ∧ Y.p0 = (U.X k).p0 ∧ Y.Gm = (U.X k).Gm ∧ Y.Λ = (U.X k).Λ ∧ Y.ξ0 = (U.X k).ξ0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y ∧ GlobalTheory.EqCovol.IsSelfDualTr Y ∧ GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol Y := by
  first | exact @GlobalTheory.EqCovol.exists_levGrp_covol | exact GlobalTheory.EqCovol.exists_levGrp_covol | (intros; apply GlobalTheory.EqCovol.exists_levGrp_covol <;> assumption)
end

section
section
noncomputable section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ENNReal Matrix nonZeroDivisors

namespace GlobalTheory.EqCovol.Transport

open GlobalTheory.CovolConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Frames

variable {Ψ : Finset (E →+* ℂ)} {G G' : Matrix (Fin r) (Fin r) E} {u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}

omit [IsCMField E] [NumberField E] in
theorem gram_mul' {τ : E →+* ℂ} {v : Matrix (Fin r) (Fin r) ℂ}
    (hu : gram τ G' v = G.map τ) (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G' (v * x) = gram τ G x := by
  rw [CovolConj.gram_eq] at hu
  rw [CovolConj.gram_eq, CovolConj.gram_eq, Matrix.transpose_mul, Matrix.map_mul, ← hu]
  simp only [Matrix.mul_assoc]

omit [IsCMField E] [NumberField E] in
theorem det_ne' {τ : E →+* ℂ} (hG : G.det ≠ 0)
    {v : Matrix (Fin r) (Fin r) ℂ} (hu : gram τ G' v = G.map τ) : v.det ≠ 0 := by
  intro h
  rw [CovolConj.gram_eq] at hu
  have h2 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul] at h2
  have h3 : τ G.det = (G.map τ).det := RingHom.map_det τ G
  exact hG ((map_eq_zero τ).1 (h3.trans h2.symm))

omit [IsCMField E] [NumberField E] in
theorem dmin_umul (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G' (umul u x) τ i = dmin G x τ i :=
  congrArg (fun M => lminor M i) (gram_mul' (hu τ.1 τ.2) (mat x τ))

omit [IsCMField E] [NumberField E] in
theorem umul_mem_GG (hG : G.det ≠ 0) (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) (p : ℕ) (x : Frame Ψ r) :
    umul u x ∈ GG Ψ G' p ↔ x ∈ GG Ψ G p := by
  refine forall_congr' fun τ => and_congr ?_ ?_
  · have : mat (umul u x) τ = u τ.1 * mat x τ := rfl
    rw [this, Matrix.det_mul]
    exact ⟨right_ne_zero_of_mul, mul_ne_zero (det_ne' hG (hu τ.1 τ.2))⟩
  · simp only [dmin_umul hu]

omit [IsCMField E] [NumberField E] in
theorem umul_inj' (hG : G.det ≠ 0) (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) {x y : Frame Ψ r}
    (h : umul u x = umul u y) : x = y := by
  funext τ
  have h1 : u τ.1 * mat x τ = u τ.1 * mat y τ := congrFun h τ
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne' hG (hu τ.1 τ.2))
  have := congrArg (fun M => (u τ.1)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  exact this

omit [IsCMField E] [NumberField E] in
theorem umul_surj (hG : G.det ≠ 0) (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) (x : Frame Ψ r) :
    ∃ y, x = umul u y := by
  refine ⟨umul (fun τ => (u τ)⁻¹) x, funext fun τ => ?_⟩
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne' hG (hu τ.1 τ.2))
  exact (Matrix.mul_nonsing_inv_cancel_left _ (mat x τ) hd).symm

omit [IsCMField E] [NumberField E] in
theorem umul_lact' {γ γ' : GL (Fin r) E}
    (h : ∀ τ ∈ Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) (x : Frame Ψ r) :
    umul u (lact γ x) = lact γ' (umul u x) := by
  funext τ
  show u τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (u τ.1 * mat x τ)
  rw [← Matrix.mul_assoc, h τ.1 τ.2, Matrix.mul_assoc]

end Frames

def ratio (X Y : Data E r) : E := X.κ0 / Y.κ0

theorem cc_κ (X : Data E r) : cc X.κ0 = -X.κ0 := by
  have h := X.ξ0_im
  unfold cc at h ⊢
  rcases X.κ0_xi with e | e <;> simp [e, h, map_ofNat]

theorem κ_ne (X : Data E r) : X.κ0 ≠ 0 := by
  have h := X.ξ0_ne
  rcases X.κ0_xi with e | e <;> simp [e, h]

theorem ratio_ne (X Y : Data E r) : ratio X Y ≠ 0 := div_ne_zero (κ_ne X) (κ_ne Y)

theorem cc_ratio (X Y : Data E r) : cc (ratio X Y) = ratio X Y := by
  have h := cc_κ X
  have h' := cc_κ Y
  unfold cc at h h' ⊢
  rw [ratio, map_div₀, h, h', neg_div_neg_eq]

theorem ξ_mul_ratio (X Y : Data E r) : Y.ξ0 * ratio X Y = X.ξ0 ∨ Y.ξ0 * ratio X Y = -X.ξ0 := by
  have h := Y.ξ0_ne
  unfold ratio
  rcases X.κ0_xi with e | e <;> rcases Y.κ0_xi with e' | e' <;> rw [e, e']
  · left; field_simp
  · right; field_simp
  · right; field_simp
  · left; field_simp

theorem re_κ (X : Data E r) (τ : E →+* ℂ) : (τ X.κ0).re = 0 := by
  have h := IsCMField.complexEmbedding_complexConj E τ X.κ0
  have h' := cc_κ X
  unfold cc at h'
  rw [h', map_neg] at h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem exists_sq (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) {τ : E →+* ℂ} (hτ : τ ∈ X.Ψ) :
    ∃ t : ℝ, t ≠ 0 ∧ (t : ℂ) * t * τ (ratio X Y) = 1 := by
  have h1 := X.κ0_sign ⟨τ, hτ⟩
  have h2 := Y.κ0_sign ⟨τ, hΨ ▸ hτ⟩
  dsimp only at h1 h2
  have e1 : τ X.κ0 = (τ X.κ0).im * Complex.I := by
    apply Complex.ext <;> simp [re_κ]
  have e2 : τ Y.κ0 = (τ Y.κ0).im * Complex.I := by
    apply Complex.ext <;> simp [re_κ]
  have hp : 0 < (τ Y.κ0).im / (τ X.κ0).im := div_pos_of_neg_of_neg h2 h1
  refine ⟨Real.sqrt ((τ Y.κ0).im / (τ X.κ0).im), (Real.sqrt_pos.2 hp).ne', ?_⟩
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le, ratio, map_div₀]
  have n1 : ((τ X.κ0).im : ℂ) ≠ 0 := by exact_mod_cast h1.ne
  have n2 : ((τ Y.κ0).im : ℂ) ≠ 0 := by exact_mod_cast h2.ne
  generalize (τ X.κ0).im = a at *
  generalize (τ Y.κ0).im = b at *
  rw [e1, e2]
  push_cast
  field_simp

omit [IsCMField E] [NumberField E] in
theorem gram_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : E) (t : ℝ) (Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ (c • G) ((t : ℂ) • Q) = ((t : ℂ) * t * τ c) • gram τ G Q := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem herm_smul (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm (c • G) x y = c * herm G x y := by
  simp only [herm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem trace_ratio (X Y : Data E r) (a : E) :
    (∃ n : ℤ, Algebra.trace ℚ E (-Y.ξ0 * (ratio X Y * a)) = n) ↔ ∃ n : ℤ, Algebra.trace ℚ E (-X.ξ0 * a) = n := by
  rcases ξ_mul_ratio X Y with e | e
  · rw [← e]; ring_nf
  · have : -Y.ξ0 * (ratio X Y * a) = -(-X.ξ0 * a) := by linear_combination (-a) * e
    rw [this, map_neg]
    exact ⟨fun ⟨n, h⟩ => ⟨-n, by push_cast; linarith⟩, fun ⟨n, h⟩ => ⟨-n, by push_cast; linarith⟩⟩

theorem exists_similitude (H : Host E) (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) (hp : X.p0 = Y.p0)
    (hX : IsSelfDualTr X) (hY : IsSelfDualTr Y) :
    ∃ P : GL (Fin r) E, ratio X Y • X.Gm = P.1ᵀ * Y.Gm * P.1.map cc := by
  haveI := H.unram
  have hb := inv_ne_zero (mul_ne_zero
    ((FractionalIdeal.spanSingleton_ne_zero_iff (R := 𝓞 E) (P := E)).2 Y.ξ0_ne) (coe_different_ne_zero (E := E)))
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := Y.Gm) (G' := ratio X Y • X.Gm)
    (L := Y.Λ) (L' := X.Λ) (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt hb
    (GlobalTheory.SelfDualGenus.cc_mem_inv_mul_different Y.ξ0_im) Y.Gm_herm
    (fun a b => by
      have h1 := cc_ratio X Y
      have h2 := X.Gm_herm a b
      unfold cc at h1 h2 ⊢
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h1, h2])
    Y.Gm_det
    (by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ (ratio_ne X Y)) X.Gm_det)
    ⟨Y.Λ_fg, Y.Λ_span⟩ ⟨X.Λ_fg, X.Λ_span⟩
    (fun x => by
      rw [← mem_smul_hermDual_iff hb, ← traceFormDual_eq Y.ξ0_ne]
      exact hY x)
    (fun x => by
      rw [← mem_smul_hermDual_iff hb, ← traceFormDual_eq Y.ξ0_ne, mem_traceFormDual]
      simp only [EFf, herm_smul, trace_ratio]
      exact hX x)
    (GlobalTheory.Published.Landherr.congr_of_signature (X.Ψ : Set (E →+* ℂ))
      (fun τ => by
        by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
        · exact Or.inr h
        · exact Or.inl ((X.cmType τ).2 h))
      fun τ hτ => ⟨X.p0, by rw [hp]; exact Y.signature ⟨τ, hΨ ▸ hτ⟩, by
        obtain ⟨Q, hQ, e⟩ := X.signature ⟨τ, hτ⟩
        obtain ⟨t, ht, h⟩ := exists_sq X Y hΨ hτ
        refine ⟨(t : ℂ) • Q, ?_, ?_⟩
        · rw [Matrix.det_smul]
          exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht)) hQ
        · rw [gram_smul, h, one_smul]; exact e⟩)
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hP0, hP⟩

def latMap (P : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : Submodule (𝓞 E) (Fin r → E) :=
  Λ.map ((Matrix.mulVecLin P.1).restrictScalars (𝓞 E))

omit [IsCMField E] [NumberField E] in
theorem mulVec_inj (P : GL (Fin r) E) {x y : Fin r → E} (h : P.1 *ᵥ x = P.1 *ᵥ y) : x = y := by
  have := congrArg (fun v => (P⁻¹).1 *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this

omit [IsCMField E] [NumberField E] in
theorem mulVec_surj (P : GL (Fin r) E) : Function.Surjective fun x : Fin r → E => P.1 *ᵥ x := fun x =>
  ⟨(P⁻¹).1 *ᵥ x, by simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩

omit [IsCMField E] [NumberField E] in
theorem mem_latMap (P : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Fin r → E) :
    P.1 *ᵥ x ∈ latMap P Λ ↔ x ∈ Λ :=
  ⟨fun ⟨_, hy, e⟩ => mulVec_inj P e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [IsCMField E] [NumberField E] in
theorem latMap_smul (P : GL (Fin r) E) (I : Ideal (𝓞 E)) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    I • latMap P Λ = latMap P (I • Λ) := (Submodule.map_smul'' _ _ _).symm

omit [IsCMField E] [NumberField E] in
theorem conj_mulVec (P γ : GL (Fin r) E) (x : Fin r → E) :
    γ.1 *ᵥ (P.1 *ᵥ x) = P.1 *ᵥ ((P⁻¹ * γ * P).1 *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

omit [IsCMField E] [NumberField E] in
theorem cong_iff (P γ : GL (Fin r) E) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) :
    (∀ x ∈ latMap P Λ', ∃ y ∈ latMap P Λ, γ.1 *ᵥ x - x = n • y) ↔
      ∀ x ∈ Λ', ∃ y ∈ Λ, (P⁻¹ * γ * P).1 *ᵥ x - x = n • y := by
  rw [(mulVec_surj P).forall]
  refine forall_congr' fun x => imp_congr (mem_latMap P _ x) ?_
  rw [(mulVec_surj P).exists]
  refine exists_congr fun y => and_congr (mem_latMap P _ y) ?_
  rw [conj_mulVec, ← Matrix.mulVec_sub, ← Matrix.mulVec_smul]
  exact ⟨mulVec_inj P, fun h => by rw [h]⟩

section Move

variable (X Y : Data E r) (P : GL (Fin r) E) (hP : ratio X Y • X.Gm = P.1ᵀ * Y.Gm * P.1.map cc)

include hP in
theorem herm_P (x y : Fin r → E) : herm Y.Gm (P.1 *ᵥ x) (P.1 *ᵥ y) = ratio X Y * herm X.Gm x y := by
  rw [GlobalTheory.SelfDualGenus.herm_mulVec, ← hP, herm_smul]

include hP in
theorem isUStab_iff (γ : GL (Fin r) E) :
    IsUStab Y.Gm (latMap P X.Λ) γ ↔ IsUStab X.Gm X.Λ (P⁻¹ * γ * P) := by
  refine and_congr ?_ ?_
  · rw [(mulVec_surj P).forall]
    refine forall_congr' fun x => ?_
    rw [(mulVec_surj P).forall]
    refine forall_congr' fun y => ?_
    rw [conj_mulVec P γ x, conj_mulVec P γ y, herm_P X Y P hP, herm_P X Y P hP, mul_right_inj' (ratio_ne X Y)]
  · rw [(mulVec_surj P).forall]
    refine forall_congr' fun x => ?_
    rw [conj_mulVec, mem_latMap, mem_latMap]

include hP in

theorem exists_isom (hΨ : X.Ψ = Y.Ψ) : ∃ u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ,
    (∀ τ ∈ X.Ψ, gram τ Y.Gm (u τ) = X.Gm.map τ) ∧
    ∀ γ : GL (Fin r) E, ∀ τ ∈ X.Ψ, u τ * (P⁻¹ * γ * P).1.map τ = γ.1.map τ * u τ := by
  choose! t ht using fun τ (hτ : τ ∈ X.Ψ) => exists_sq X Y hΨ hτ
  refine ⟨fun τ => (t τ : ℂ) • P.1.map τ, fun τ hτ => ?_, fun γ τ _ => ?_⟩
  · have h1 := gram_smul τ Y.Gm 1 (t τ) (P.1.map τ)
    have h2 : (P.1.map τ).map (starRingEnd ℂ) = (P.1.map cc).map τ := by
      ext a b
      exact (IsCMField.complexEmbedding_complexConj E τ _).symm
    rw [one_smul, map_one, mul_one] at h1
    rw [h1, CovolConj.gram_eq, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← hP]
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [← mul_assoc, (ht τ hτ).2, one_mul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul]
    congr 3
    group

include hP in
theorem transv_conj (ξ : Fin r → E) (α : E) :
    transvMat Y.Gm (P.1 *ᵥ ξ) α * P.1 = P.1 * transvMat X.Gm ξ (α * ratio X Y) := by
  have key : ∀ (G : Matrix (Fin r) (Fin r) E) (ξ x : Fin r → E) (α : E),
      transvMat G ξ α *ᵥ x = x + (α * herm G x ξ) • ξ := by
    intro G ξ x α
    funext a
    simp only [transvMat, herm, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key, key,
    herm_P X Y P hP, Matrix.mulVec_add, Matrix.mulVec_smul, mul_assoc]

theorem exists_den : ∃ d : 𝓞 E, d ≠ 0 ∧
    ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((d : E) * (ratio X Y * herm X.Gm x y)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (ratio X Y)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := by simpa using hb0
  refine ⟨b * X.den, mul_ne_zero hb0 X.den_ne, fun x hx y hy => ?_⟩
  have : ((b * X.den : 𝓞 E) : E) * (ratio X Y * herm X.Gm x y) =
      algebraMap (𝓞 E) E a * ((X.den : E) * herm X.Gm x y) := by
    rw [← e]
    show algebraMap (𝓞 E) E (b * X.den) * _ = _ * (algebraMap (𝓞 E) E X.den * _)
    rw [map_mul]
    field_simp
  rw [this]
  exact a.isIntegral_coe.mul (X.Λ_int x hx y hy)

variable (hΨ : X.Ψ = Y.Ψ) (hp : X.p0 = Y.p0)

def move : Data E r where
  Ψ := X.Ψ
  cmType := X.cmType
  Gm := Y.Gm
  Gm_herm := Y.Gm_herm
  Gm_det := Y.Gm_det
  p0 := X.p0
  p0_le := X.p0_le
  signature τ := by rw [hp]; exact Y.signature ⟨τ.1, hΨ ▸ τ.2⟩
  Λ := latMap P X.Λ
  Λ_fg := X.Λ_fg.map _
  Λ_span := by
    have : (latMap P X.Λ : Set (Fin r → E)) = Matrix.mulVecLin P.1 '' (X.Λ : Set (Fin r → E)) := rfl
    rw [this, Submodule.span_image, X.Λ_span, Submodule.map_top, LinearMap.range_eq_top]
    exact mulVec_surj P
  den := (exists_den X Y).choose
  den_ne := (exists_den X Y).choose_spec.1
  Λ_int := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := (exists_den X Y).choose_spec.2 x hx y hy
    rwa [← herm_P X Y P hP] at this
  Γ := X.Γ.comap (MulAut.conj P).symm.toMonoidHom
  Γ_stab γ hγ := (isUStab_iff X Y P hP γ).2 (X.Γ_stab _ hγ)
  Γ_index := by
    classical
    obtain ⟨S, hS⟩ := X.Γ_index
    refine ⟨S.image fun s => P * s * P⁻¹, fun γ hγ => ?_⟩
    obtain ⟨s, hs, h⟩ := hS _ ((isUStab_iff X Y P hP γ).1 hγ)
    refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
    show P⁻¹ * _ * P ∈ X.Γ
    convert h using 1
    group
  Γ_free γ hγ x hx b hb h := by
    obtain ⟨u, hu, hc⟩ := exists_isom X Y P hP hΨ
    obtain ⟨y, rfl⟩ := umul_surj X.Gm_det hu x
    rw [← umul_rmul, ← umul_lact' (hc γ)] at h
    have := X.Γ_free _ hγ y ((umul_mem_GG X.Gm_det hu _ y).1 hx) b hb (umul_inj' X.Gm_det hu h)
    have h2 : P⁻¹ * γ * P = 1 := this
    calc γ = P * (P⁻¹ * γ * P) * P⁻¹ := by group
      _ = 1 := by rw [h2]; group
  χ _ _ := 1
  χ_mul := by simp
  χ_add := by simp
  χ_fin _ := ⟨1, one_pos, by simp⟩
  ξ0 := Y.ξ0
  ξ0_im := Y.ξ0_im
  ξ0_ne := Y.ξ0_ne
  κ0 := Y.κ0
  κ0_xi := Y.κ0_xi
  κ0_sign τ := Y.κ0_sign ⟨τ.1, hΨ ▸ τ.2⟩
  m := X.m
  m_pos := X.m_pos
  transv := by
    rintro _ ⟨ξ, hξ, rfl⟩ h0 s hs hi
    change herm Y.Gm (P.1 *ᵥ ξ) (P.1 *ᵥ ξ) = 0 at h0
    rw [herm_P X Y P hP, mul_eq_zero, or_iff_right (ratio_ne X Y)] at h0
    obtain ⟨γ, hγ, e⟩ := X.transv ξ hξ h0 s hs hi
    refine ⟨P * γ * P⁻¹, ?_, ?_⟩
    · show P⁻¹ * _ * P ∈ X.Γ
      convert hγ using 1
      group
    · have h1 := transv_conj X Y P hP ξ ((X.m : E) * s * Y.κ0)
      rw [mul_assoc _ Y.κ0, ratio, mul_div_cancel₀ _ (κ_ne Y), ← e] at h1
      rw [Units.val_mul, Units.val_mul, ← h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rfl

theorem mem_move (γ : GL (Fin r) E) : γ ∈ (move X Y P hP hΨ hp).Γ ↔ P⁻¹ * γ * P ∈ X.Γ := Iff.rfl

theorem isLevGrp_move {H : Host E} (l : Level H) (h : IsLevGrp l X) : IsLevGrp l (move X Y P hP hΨ hp) := by
  intro γ
  rw [mem_move, h]
  refine and_congr (isUStab_iff X Y P hP γ).symm (and_congr ?_ (cong_iff P γ _ _ _).symm)
  refine (cong_iff P γ _ _ _).symm.trans ?_
  rw [← latMap_smul]
  rfl

theorem isSelfDualTr_move (h : IsSelfDualTr X) : IsSelfDualTr (move X Y P hP hΨ hp) := by
  intro x
  obtain ⟨x, rfl⟩ := mulVec_surj P x
  show P.1 *ᵥ x ∈ latMap P X.Λ ↔ ∀ y ∈ latMap P X.Λ, ∃ n : ℤ,
    Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm (P.1 *ᵥ x) y) = n
  rw [mem_latMap, h x]
  refine Iff.trans ?_ (mulVec_surj P).forall.symm
  refine forall_congr' fun y => imp_congr (mem_latMap P _ y).symm ?_
  rw [herm_P X Y P hP, trace_ratio]

theorem covol_move : GlobalTheory.TrueCx.covol (move X Y P hP hΨ hp) = GlobalTheory.TrueCx.covol X := by
  obtain ⟨u, hu, hc⟩ := exists_isom X Y P hP hΨ
  have ho := GlobalTheory.TrueCx.isOrth_x0F X
  generalize x0F X = x0 at ho
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  set Z := move X Y P hP hΨ hp with hZ
  have hcpt : ∀ z : V (nd X), rmul (umul u x0) (nmat X z) = umul u (cpt X x0 z) := fun z => (umul_rmul _ _).symm
  have hO : OmF Z (umul u x0) = OmF X x0 := by
    refine Set.ext fun z : V (nd X) => ?_
    show rmul (umul u x0) (nmat X z) ∈ GG X.Ψ Y.Gm X.p0 ↔ cpt X x0 z ∈ X.dom
    rw [hcpt]
    exact umul_mem_GG X.Gm_det hu _ _
  have hD : densF Z (umul u x0) = densF X x0 := by
    refine funext fun z : V (nd X) => ?_
    show ∏ τ : X.Ψ, ∏ i : Fin r, ‖dmin Y.Gm (rmul (umul u x0) (nmat X z)) τ i.castSucc‖ ^ (-2 : ℤ) = _
    simp only [hcpt, dmin_umul hu, densF]
  have hmu : muF Z (umul u x0) = muF X x0 := by
    exact congrArg₂ (fun (O : Set (V (nd X))) (D : V (nd X) → ℝ) =>
      (volume.restrict O).withDensity fun z => ENNReal.ofReal (D z)) hO hD
  have ho' : IsOrth Z (umul u x0) := fun τ => (gram_mul' (hu τ.1 τ.2) (mat x0 τ)).trans (ho τ)
  have hF' : IsFundSet Z (umul u x0) FF := by
    refine ⟨hF.1, hF.2.1.trans hO.ge, ?_, ?_⟩
    · intro (z : V (nd X)) hz (z' : V (nd X)) hz' γ hγ (b : Frame X.Ψ r) hb h
      replace h : rmul (umul u x0) (nmat X z') = lact γ (rmul (rmul (umul u x0) (nmat X z)) b) := h
      rw [hcpt, hcpt] at h
      have h' : umul u (cpt X x0 z') = umul u (lact (P⁻¹ * γ * P) (rmul (cpt X x0 z) b)) := by
        rw [umul_lact' (hc γ), umul_rmul]; exact h
      exact hF.2.2.1 z hz z' hz' _ hγ b hb (umul_inj' X.Gm_det hu h')
    · have : ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ Z.Γ, ∃ b ∈ Bor X.Ψ r,
          rmul (umul u x0) (nmat X z) = lact γ (rmul (rmul (umul u x0) (nmat X z')) b) := ?_
      · rw [← hmu] at this
        exact this
      filter_upwards [hF.2.2.2] with z hz
      obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
      have e : P⁻¹ * (P * γ * P⁻¹) * P = γ := by group
      refine ⟨z', hz', P * γ * P⁻¹, (mem_move X Y P hP hΨ hp _).2 (by rwa [e]), b, hb, ?_⟩
      rw [hcpt, hcpt]
      have := umul_lact' (hc (P * γ * P⁻¹)) (rmul (cpt X x0 z') b)
      rw [e, ← h, umul_rmul] at this
      exact this
  rw [(GlobalTheory.TrueCx.covol_eq Z ho' hF').2, (GlobalTheory.TrueCx.covol_eq X ho hF).2]
  exact congrArg (fun m : Measure (V (nd X)) => GlobalTheory.TrueCx.flagConst r ^ X.Ψ.card * (m FF).toReal) hmu

end Move

end GlobalTheory.EqCovol.Transport

open GlobalTheory.EqCovol.Transport in

theorem GlobalTheory.EqCovol.exists_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → ∃ Y'' : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y''.Ψ = Y.Ψ ∧ Y''.Gm = Y.Gm ∧ Y''.ξ0 = Y.ξ0 ∧ Y''.p0 = Y.p0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y'' ∧ GlobalTheory.EqCovol.IsSelfDualTr Y'' ∧ GlobalTheory.TrueCx.covol Y'' = GlobalTheory.TrueCx.covol Y' := by
  intro E _ _ _ H l r Y Y' _ hΨ hp _ _ hl hY hY'
  obtain ⟨P, hP⟩ := exists_similitude H Y' Y hΨ hp hY' hY
  exact ⟨move Y' Y P hP hΨ hp, hΨ, rfl, rfl, hp, isLevGrp_move Y' Y P hP hΨ hp l hl,
    isSelfDualTr_move Y' Y P hP hΨ hp hY', covol_move Y' Y P hP hΨ hp⟩
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → ∃ Y'' : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y''.Ψ = Y.Ψ ∧ Y''.Gm = Y.Gm ∧ Y''.ξ0 = Y.ξ0 ∧ Y''.p0 = Y.p0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y'' ∧ GlobalTheory.EqCovol.IsSelfDualTr Y'' ∧ GlobalTheory.TrueCx.covol Y'' = GlobalTheory.TrueCx.covol Y' := by
  atlas_forward_decl GlobalTheory.EqCovol.exists_transport
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors Matrix

noncomputable section

namespace GlobalTheory.EqCovol.IsoPlane

open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem selfD_of_isSelfDualTr {r : ℕ} (Y : Data E r) (h : IsSelfDualTr Y) : GlobalTheory.SW.SelfD Y Y.Λ := by
  refine ⟨Y.Λ_fg, fun x => (h x).trans (forall₂_congr fun y _ => ?_)⟩
  rw [GlobalTheory.ThFr.EF_def]
  rcases Y.κ0_xi with hk | hk
  · rw [hk, show (2 * Y.ξ0) / 2 = Y.ξ0 by ring]
  · have e : -(-(2 * Y.ξ0) / 2) * herm Y.Gm x y = -(-Y.ξ0 * herm Y.Gm x y) := by ring
    rw [hk, e, map_neg]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [hn, Int.cast_neg]⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩

def hypG : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem hypG_herm (a b : Fin 2) : cc (hypG (E := E) a b) = hypG b a := by
  fin_cases a <;> fin_cases b <;> simp [hypG, cc]

theorem hypG_det : (hypG (E := E)).det ≠ 0 := by
  simp [hypG, Matrix.det_fin_two_of]

theorem herm_hypG (x y : Fin 2 → E) : herm hypG x y = x 0 * cc (y 1) + x 1 * cc (y 0) := by
  simp [herm, hypG, Fin.sum_univ_two]

def hypLat (J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 2 → E) :=
  ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).comap (LinearMap.proj 0) ⊓
    (J : Submodule (𝓞 E) E).comap (LinearMap.proj 1)

theorem mem_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} {x : Fin 2 → E} :
    x ∈ hypLat J ↔ x 0 ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ∧ x 1 ∈ J := Iff.rfl

theorem isLattice_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (hypLat J) := by
  classical
  constructor
  · refine Submodule.FG.of_le ((Submodule.fg_span_singleton (Pi.single 0 1 : Fin 2 → E)).sup
      ((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map
        (LinearMap.single (𝓞 E) (fun _ : Fin 2 => E) 1))) fun x hx => ?_
    obtain ⟨h0, h1⟩ := mem_hypLat.1 hx
    let z : 𝓞 E := ⟨x 0, mem_one_fractionalIdeal_iff.1 h0⟩
    refine Submodule.mem_sup.2 ⟨z • Pi.single 0 1, Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _),
      Pi.single 1 (x 1), ⟨x 1, h1, rfl⟩, ?_⟩
    funext i
    fin_cases i
    · simp [Algebra.smul_def]; rfl
    · simp
  · obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (mt FractionalIdeal.coeToSubmodule_eq_bot.1 hJ0)
    have e0 : (Pi.single 0 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
    have e1' : (Pi.single 1 j : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by simpa using hj⟩)
    have e1 : (Pi.single 1 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) := by
      have := Submodule.smul_mem _ j⁻¹ e1'
      rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hj0] at this
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → E) + v 1 • Pi.single 1 1 := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ e0) (Submodule.smul_mem _ _ e1)

theorem modular_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) (hJc : ∀ z ∈ J, cc z ∈ J)
    (x : Fin 2 → E) : x ∈ hypLat J ↔ ∀ y ∈ hypLat J, herm hypG x y ∈ J := by
  constructor
  · intro hx y hy
    obtain ⟨hx0, hx1⟩ := mem_hypLat.1 hx
    obtain ⟨hy0, hy1⟩ := mem_hypLat.1 hy
    rw [herm_hypG]
    refine (J : Submodule (𝓞 E) E).add_mem ?_ ?_
    · simpa using FractionalIdeal.mul_mem_mul hx0 (hJc _ hy1)
    · have : cc (y 0) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
        mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hy0))
      simpa using FractionalIdeal.mul_mem_mul hx1 this
  · intro h
    have h1 : x 1 ∈ J := by
      have := h (Pi.single 0 1) (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
      simpa [herm_hypG, cc] using this
    have h0 : ∀ j ∈ J, x 0 * j ∈ J := fun j hj => by
      have := h (Pi.single 1 (cc j)) (mem_hypLat.2 ⟨by simp, by simpa using hJc j hj⟩)
      simpa [herm_hypG, cc] using this
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J ≤ J := by
      refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact (J : Submodule (𝓞 E) E).smul_mem a (h0 j hj)
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) ≤ 1 := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0)
          = J⁻¹ * (FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J) := by
            rw [mul_left_comm, inv_mul_cancel₀ hJ0, mul_one]
        _ ≤ J⁻¹ * J := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hJ0
    exact ⟨hle1 (FractionalIdeal.mem_spanSingleton_self _ _), h1⟩

theorem hypG_signature (τ : E →+* ℂ) : ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
    gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn 1 (a : ℕ) : ℝ) : ℂ) := by
  refine ⟨!![1, 1; 1 / 2, -1 / 2], by simp [Matrix.det_fin_two_of]; norm_num, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, hypG, sgn, Fin.sum_univ_two, map_ofNat] <;> norm_num

theorem iso_rank_two (H : Host E) (Y : Data E 2) (hp : Y.p0 = 1) (hY : IsSelfDualTr Y) :
    ∃ z : Fin 2 → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  haveI := H.unram
  obtain ⟨J, hJ0, hJc, hJ⟩ := GlobalTheory.Ker.OntoLat.exists_valueIdeal Y
  have HN := GlobalTheory.QNorm.hasseNormSt
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ (Y.Ψ : Set (E →+* ℂ)) ∨ ComplexEmbedding.conjugate τ ∈ (Y.Ψ : Set (E →+* ℂ)) := by
    intro τ
    by_cases h : ComplexEmbedding.conjugate τ ∈ Y.Ψ
    · exact Or.inr h
    · exact Or.inl ((Y.cmType τ).mpr h)
  have hs : ∀ τ ∈ (Y.Ψ : Set (E →+* ℂ)), ∃ p : ℕ,
      (∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ Y.Gm Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ hτ
    obtain ⟨Q, hQ, hg⟩ := Y.signature ⟨τ, hτ⟩
    rw [hp] at hg
    exact ⟨1, ⟨Q, hQ, hg⟩, hypG_signature τ⟩
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := Y.Gm) (G' := hypG) (L := Y.Λ)
    (L' := hypLat J) (GlobalTheory.LocalQuad.landherr_of_hasseNormSt HN) HN hJ0 hJc Y.Gm_herm hypG_herm Y.Gm_det
    hypG_det ⟨Y.Λ_fg, Y.Λ_span⟩ (isLattice_hypLat hJ0) (hJ Y.Λ (selfD_of_isSelfDualTr Y hY))
    (modular_hypLat hJ0 hJc) (GlobalTheory.Published.Landherr.congr_of_signature _ hΨ hs)
  refine ⟨P *ᵥ Pi.single 0 1, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [GlobalTheory.SelfDualGenus.herm_mulVec, ← hPG, herm_hypG]
    simp

end GlobalTheory.EqCovol.IsoPlane

namespace GlobalTheory.EqCovol

theorem exists_isotropic_of_isSelfDualTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ)
    (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  intro E _ _ _ H r Y h1 h2 hY
  by_cases hr : 3 ≤ r
  · obtain ⟨cu⟩ := GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt E r 1 Y h1 (by omega) (by omega)
    exact ⟨cu.e 0, cu.ind.ne_zero 0, cu.iso 0 0⟩
  · obtain rfl : r = 2 := by omega
    exact IsoPlane.iso_rank_two H Y (by omega) hY

end GlobalTheory.EqCovol
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ) (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y → ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  atlas_forward_decl GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_fullLevelGroup_iff_congruence_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (r : ℕ) (Y : Data E r), GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsSelfDualTr Y → ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧ ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M' • y := by
  first | exact @GlobalTheory.EqCovol.mem_iff_congr_lcm | exact GlobalTheory.EqCovol.mem_iff_congr_lcm | (intros; apply GlobalTheory.EqCovol.mem_iff_congr_lcm <;> assumption)
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Matrix Polynomial

namespace GlobalTheory.UnitaryCongruenceDetAny

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M G Λ γ hM hG hfg hspan hst hcong
  classical
  obtain ⟨hherm, -⟩ := hst
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ Λ, A *ᵥ x ∈ Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots,
      IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply GlobalTheory.UnitaryCongruenceDet.isIntegral_of_left_eigen A Λ hfg hspan hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := GlobalTheory.UnitaryCongruenceDet.prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _

  set z₀ : E := (g.det - 1) / (M : E) with hz₀
  have hφz : φ z₀ = z := by
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, hφdet]
    field_simp
    ring
  have hz₀int : IsIntegral ℤ z₀ := by
    have h1 : IsIntegral ℤ (φ z₀) := by rw [hφz]; exact hz
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 h1

  have hcc := GlobalTheory.UnitaryCongruenceDet.det_mul_cc_det G g hG hherm
  have hnorm : ∀ ψ : E →+* ℂ, ‖ψ g.det‖ = 1 := by
    intro ψ
    have h1 := congrArg ψ hcc
    rw [map_mul, map_one, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj] at h1
    have h2 : Complex.normSq (ψ g.det) = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h2.trans (one_pow 2).symm)

  have hsmall : ∀ ψ : E →+* ℂ, ‖ψ z₀‖ < 1 := by
    intro ψ
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    calc ‖ψ g.det - 1‖ ≤ ‖ψ g.det‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm, norm_one]; norm_num
      _ < M := by linarith
  have hz0 : z₀ = 0 := by
    by_contra hne
    let α : 𝓞 E := ⟨z₀, hz₀int⟩
    have hα : α ≠ 0 := by
      intro h; apply hne
      have := congrArg (fun a : 𝓞 E => (a : E)) h
      exact this
    obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hα
    exact absurd hσ (not_le.2 (hsmall σ))
  have : g.det - 1 = 0 := by
    have h := hz0
    rw [hz₀, div_eq_zero_iff] at h
    exact h.resolve_right hME
  exact sub_eq_zero.1 this

end GlobalTheory.UnitaryCongruenceDetAny
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  atlas_forward_decl GlobalTheory.UnitaryCongruenceDetAny.det_eq_one
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

theorem exists_data_of_le_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 →
    ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  intro E _ _ _ r X Δ hle hidx
  classical
  have hT : ∃ T : Finset (GL (Fin r) E), ∀ g ∈ X.Γ, ∃ t ∈ T, t⁻¹ * g ∈ Δ := by
    letI := Subgroup.fintypeOfIndexNeZero hidx
    refine ⟨Finset.univ.image
      (fun q : X.Γ ⧸ Δ.subgroupOf X.Γ => ((Quotient.out q : X.Γ) : GL (Fin r) E)), ?_⟩
    intro g hg
    set q : X.Γ ⧸ Δ.subgroupOf X.Γ := QuotientGroup.mk (⟨g, hg⟩ : X.Γ) with hq
    refine ⟨((Quotient.out q : X.Γ) : GL (Fin r) E),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : ((Quotient.out q : X.Γ) : X.Γ ⧸ Δ.subgroupOf X.Γ) = QuotientGroup.mk (⟨g, hg⟩ : X.Γ) :=
      QuotientGroup.out_eq' q
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  obtain ⟨T, hT⟩ := hT
  obtain ⟨S, hS⟩ := X.Γ_index
  refine ⟨{ X with
    Γ := Δ
    Γ_stab := fun γ hγ => X.Γ_stab γ (hle hγ)
    Γ_index := ⟨(S ×ˢ T).image (fun p => p.1 * p.2), by
      intro γ hγ
      obtain ⟨s, hs, h1⟩ := hS γ hγ
      obtain ⟨t, ht, h2⟩ := hT _ h1
      refine ⟨s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩
      rw [mul_inv_rev, mul_assoc]
      exact h2⟩
    Γ_free := fun γ hγ => X.Γ_free γ (hle hγ)
    χ_mul := fun la γ hγ γ' hγ' => X.χ_mul la γ (hle hγ) γ' (hle hγ')
    χ_add := fun la la' γ hγ => X.χ_add la la' γ (hle hγ)
    χ_fin := fun la => by
      obtain ⟨n, hn, h⟩ := X.χ_fin la
      exact ⟨n, hn, fun γ hγ => h γ (hle hγ)⟩
    m := X.m * (Δ.relIndex X.Γ).factorial
    m_pos := Nat.mul_pos X.m_pos (Nat.factorial_pos _)
    transv := by
      intro ξ hξ hiso s hs hint
      obtain ⟨γ, hγ, hmat⟩ := X.transv ξ hξ hiso s hs hint
      refine ⟨γ ^ (Δ.relIndex X.Γ).factorial,
        (Subgroup.mem_inf.mp (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx hγ
          (fun k hk hk' => Nat.dvd_factorial hk hk'))).1, ?_⟩
      rw [Units.val_pow_eq_pow_val, hmat, TransvectionPeriodicity.transvMat_pow X.Gm hiso]
      congr 1
      push_cast
      ring }, rfl, rfl, rfl, rfl⟩

end GlobalTheory.EqCovol
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 → ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  atlas_forward_decl GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero
end

section
section
namespace GlobalTheory

open Subgroup

theorem relIndex_cocycle_of_ne_zero {A : Type} [Group A] (X Y Z : Subgroup A)
    (hXY : X.relIndex Y ≠ 0) (hYX : Y.relIndex X ≠ 0) (hYZ : Y.relIndex Z ≠ 0)
    (hZY : Z.relIndex Y ≠ 0) (hXZ : X.relIndex Z ≠ 0) (hZX : Z.relIndex X ≠ 0) :
    Y.relIndex X * Z.relIndex Y * X.relIndex Z = X.relIndex Y * Y.relIndex Z * Z.relIndex X := by
  have a1 := relIndex_inf_mul_relIndex Y Z X
  have a2 := relIndex_inf_mul_relIndex Z Y X
  have b1 := relIndex_inf_mul_relIndex Z X Y
  have b2 := relIndex_inf_mul_relIndex X Z Y
  have c1 := relIndex_inf_mul_relIndex X Y Z
  have c2 := relIndex_inf_mul_relIndex Y X Z
  rw [inf_comm Z Y] at a2
  rw [inf_comm Y X] at c2
  rw [inf_comm X Z] at b2
  rw [inf_comm Z Y] at b2
  rw [inf_comm Y X] at a2
  rw [inf_comm X Z] at c2
  have ha : (Y ⊓ Z).relIndex X ≠ 0 := relIndex_inf_ne_zero hYX hZX
  have hb : (Z ⊓ X).relIndex Y ≠ 0 := relIndex_inf_ne_zero hZY hXY
  have hc : (X ⊓ Y).relIndex Z ≠ 0 := relIndex_inf_ne_zero hXZ hYZ
  have hpY : Y.relIndex (Z ⊓ X) ≠ 0 := by
    intro h; apply ha; rw [← a1, h, zero_mul]
  have hpZ : Z.relIndex (X ⊓ Y) ≠ 0 := by
    intro h; apply hb; rw [← b1, h, zero_mul]
  have hpX : X.relIndex (Y ⊓ Z) ≠ 0 := by
    intro h; apply hc; rw [← c1, h, zero_mul]
  have hP : 0 < Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) := by
    positivity
  apply Nat.eq_of_mul_eq_mul_left hP
  calc Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) *
        (Y.relIndex X * Z.relIndex Y * X.relIndex Z)
      = (Z.relIndex (X ⊓ Y) * Y.relIndex X) * (X.relIndex (Y ⊓ Z) * Z.relIndex Y) *
        (Y.relIndex (Z ⊓ X) * X.relIndex Z) := by ring
    _ = (Y.relIndex (Z ⊓ X) * Z.relIndex X) * (Z.relIndex (X ⊓ Y) * X.relIndex Y) *
        (X.relIndex (Y ⊓ Z) * Y.relIndex Z) := by rw [a2, b2, c2, a1, b1, c1]
    _ = _ := by ring

theorem map_conj_mul {A : Type} [Group A] (K : Subgroup A) (x y : A) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem relIndex_map_conj {A : Type} [Group A] (H L : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).relIndex (L.map (MulAut.conj g).toMonoidHom) =
      H.relIndex L :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem map_conj_one {A : Type} [Group A] (K : Subgroup A) :
    K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext x; simp

theorem relIndex_conj_pow_succ {A : Type} [Group A] (K : Subgroup A) (g : A) (i : ℕ) :
    (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ i)).toMonoidHom) =
      (K.map (MulAut.conj g).toMonoidHom).relIndex K ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom) =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  rw [pow_succ, map_conj_mul, relIndex_map_conj, relIndex_map_conj]
  exact ⟨rfl, rfl⟩

theorem relIndex_conj_pow_induction {A : Type} [Group A] (K : Subgroup A) (g : A)
    (ha : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0)
    (hb : K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0) (i : ℕ) :
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K ≠ 0 ∧
    K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) ≠ 0 ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K *
        (K.relIndex (K.map (MulAut.conj g).toMonoidHom)) ^ i =
      K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) *
        ((K.map (MulAut.conj g).toMonoidHom).relIndex K) ^ i := by
  induction i with
  | zero =>
    rw [pow_zero, map_conj_one]
    simp
  | succ i ih =>
    obtain ⟨hu, hv, hi⟩ := ih
    obtain ⟨sa, sb⟩ := relIndex_conj_pow_succ K g i
    set B := K.map (MulAut.conj (g ^ i)).toMonoidHom
    set C := K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom
    set a := (K.map (MulAut.conj g).toMonoidHom).relIndex K
    set b := K.relIndex (K.map (MulAut.conj g).toMonoidHom)
    have hCB : C.relIndex B ≠ 0 := by rw [sa]; exact ha
    have hBC : B.relIndex C ≠ 0 := by rw [sb]; exact hb
    have hCK : C.relIndex K ≠ 0 := relIndex_ne_zero_trans hCB hu
    have hKC : K.relIndex C ≠ 0 := relIndex_ne_zero_trans hv hBC
    have coc := relIndex_cocycle_of_ne_zero K B C hv hu hBC hCB hKC hCK
    rw [sa, sb] at coc
    refine ⟨hCK, hKC, ?_⟩
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hv)
    calc C.relIndex K * b ^ (i + 1) * K.relIndex B
        = b * K.relIndex B * C.relIndex K * b ^ i := by ring
      _ = B.relIndex K * a * K.relIndex C * b ^ i := by rw [coc]; ring
      _ = a * K.relIndex C * (B.relIndex K * b ^ i) := by ring
      _ = K.relIndex C * a ^ (i + 1) * K.relIndex B := by rw [hi]; ring

theorem relIndex_conj_eq_of_pow_eq : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 →
    K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 →
    (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  intro A _ K g n hn ha hb heq
  obtain ⟨hu, _, hi⟩ := relIndex_conj_pow_induction K g ha hb n
  rw [heq] at hi hu
  have hpow := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hu) hi
  exact (Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp hn) hpow).symm

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n → (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 → K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 → (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) → (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  atlas_forward_decl GlobalTheory.relIndex_conj_eq_of_pow_eq
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UTrans GlobalTheory.UTrans.StrongApprox GlobalTheory.AdLat
open scoped TensorProduct ENNReal

namespace GlobalTheory.EqCovol.SameSpace

theorem mem_map_conj {A : Type} [Group A] (K : Subgroup A) (h k : A) :
    k ∈ K.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * k * h ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hk
    exact ⟨_, hk, by simp [mul_assoc]⟩

section Abstract

variable {R : Type} [CommRing R] {n : ℕ} {σ : R →+* R} {G : Matrix (Fin n) (Fin n) R}

theorem hf_eq (x y : Fin n → R) : hf σ G x y = x ⬝ᵥ (G *ᵥ fun i => σ (y i)) := by
  simp only [hf, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem isU_iff {γ : Matrix (Fin n) (Fin n) R} : IsU σ G γ ↔ γᵀ * G * γ.map σ = G := by
  have key : ∀ x y, hf σ G (γ *ᵥ x) (γ *ᵥ y) = hf σ (γᵀ * G * γ.map σ) x y := fun x y => by
    have : (fun i => σ ((γ *ᵥ y) i)) = γ.map σ *ᵥ fun i => σ (y i) :=
      funext fun i => RingHom.map_mulVec σ γ y i
    rw [hf_eq, hf_eq, this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]
  refine ⟨fun h => ?_, fun h x y => by rw [key, h]⟩
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [key] at this
  simpa [hf, Pi.single_apply, apply_ite σ] using this

theorem isU_mul {a b : Matrix (Fin n) (Fin n) R} (ha : IsU σ G a) (hb : IsU σ G b) : IsU σ G (a * b) :=
  fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, ha, hb]

theorem isU_inv {a : GL (Fin n) R} (ha : IsU σ G a.1) : IsU σ G (a⁻¹).1 := fun x y => by
  rw [← ha, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]

theorem isU_pow {a : GL (Fin n) R} (ha : IsU σ G a.1) (k : ℕ) : IsU σ G (a ^ k).1 := by
  induction k with
  | zero => intro x y; simp
  | succ k ih => rw [pow_succ, Units.val_mul]; exact isU_mul ih ha

theorem det_mul_det (hG : IsUnit G.det) {a : Matrix (Fin n) (Fin n) R} (ha : IsU σ G a) :
    a.det * σ a.det = 1 := by
  have e := congrArg det (isU_iff.1 ha)
  rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e
  refine hG.mul_right_cancel ?_
  linear_combination e

theorem det_conj (h k : GL (Fin n) R) : (h⁻¹ * k * h).1.det = k.1.det := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]

variable (σ G) in

def cong (H : AddSubgroup (Fin n → R)) (M : ℕ) : Subgroup (GL (Fin n) R) where
  carrier := {k | IsU σ G k.1 ∧ k.1.det = 1 ∧ (k⁻¹).1 ∈ stab H ∧ ∃ B ∈ stab H, k.1 = 1 + (M : R) • B}
  one_mem' := ⟨fun x y => by simp, by simp, by simpa using one_mem _, 0, zero_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, B, hB, e⟩ ⟨hb1, hb2, hb3, C, hC, e'⟩
    refine ⟨isU_mul ha1 hb1, by rw [Units.val_mul, det_mul, ha2, hb2, mul_one], ?_,
      B + C + (M : R) • (B * C), add_mem (add_mem hB hC) (natCast_smul_mem _ (mul_mem hB hC)), ?_⟩
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact mul_mem hb3 ha3
    · rw [Units.val_mul, e, e']
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_add]
      abel
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, B, hB, e⟩
    refine ⟨isU_inv ha1, ?_, ?_, -((a⁻¹).1 * B), neg_mem (mul_mem ha3 hB), ?_⟩
    · have := congrArg det a.inv_mul
      rwa [det_mul, ha2, mul_one, det_one] at this
    · rw [inv_inv, e]; exact add_mem (one_mem _) (natCast_smul_mem _ hB)
    · rw [← a.inv_mul, e, mul_add, mul_one, Matrix.mul_smul, smul_neg, add_neg_cancel_right]

theorem mem_cong {H : AddSubgroup (Fin n → R)} {M : ℕ} {k : GL (Fin n) R} : k ∈ cong σ G H M ↔
    IsU σ G k.1 ∧ k.1.det = 1 ∧ (k⁻¹).1 ∈ stab H ∧ ∃ B ∈ stab H, k.1 = 1 + (M : R) • B := Iff.rfl

theorem conj_mem_cong {H H' : AddSubgroup (Fin n → R)} {M : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (hH : ∀ A ∈ stab H', (h⁻¹).1 * A * h.1 ∈ stab H) {k : GL (Fin n) R} (hk : k ∈ cong σ G H' M) :
    h⁻¹ * k * h ∈ cong σ G H M := by
  obtain ⟨h1, h2, h3, B, hB, e⟩ := hk
  refine ⟨isU_mul (isU_mul (isU_inv hh) h1) hh, by rw [det_conj, h2], ?_, _, hH B hB, ?_⟩
  · have : (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h := by group
    rw [this]; exact hH _ h3
  · rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul, Matrix.mul_smul,
      Matrix.smul_mul]

theorem conj_mem_stab {H H' : AddSubgroup (Fin n → R)} {h : GL (Fin n) R}
    (h1 : ∀ z ∈ H, h.1 *ᵥ z ∈ H') (h2 : ∀ z ∈ H', (h⁻¹).1 *ᵥ z ∈ H) :
    ∀ A ∈ stab H', (h⁻¹).1 * A * h.1 ∈ stab H := fun A hA z hz => by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact h2 _ (hA _ (h1 z hz))

theorem map_conj_cong {H H' : AddSubgroup (Fin n → R)} {M : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (hH : h.1.mulVec '' H = H') : (cong σ G H M).map (MulAut.conj h).toMonoidHom = cong σ G H' M := by
  have h1 : ∀ z ∈ H, h.1 *ᵥ z ∈ H' := fun z hz => by
    rw [← SetLike.mem_coe, ← hH]; exact ⟨z, hz, rfl⟩
  have h2 : ∀ z ∈ H', (h⁻¹).1 *ᵥ z ∈ H := fun z hz => by
    rw [← SetLike.mem_coe, ← hH] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec]
  ext k
  rw [mem_map_conj]
  refine ⟨fun hk => ?_, conj_mem_cong hh (conj_mem_stab h1 h2)⟩
  have := conj_mem_cong (isU_inv hh) (conj_mem_stab (h := h⁻¹) h2 (by simpa using h1)) hk
  simpa [mul_assoc] using this

theorem cong_le_map_conj {H : AddSubgroup (Fin n → R)} {M a b : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (ha : (a : R) • (h⁻¹).1 ∈ stab H) (hb : (b : R) • h.1 ∈ stab H) :
    cong σ G H (M * a * b) ≤ (cong σ G H M).map (MulAut.conj h).toMonoidHom := by
  have key : ∀ k ∈ cong σ G H (M * a * b), ∃ C ∈ stab H, (h⁻¹ * k * h).1 = 1 + (M : R) • C := by
    rintro k ⟨-, -, -, B, hB, e⟩
    refine ⟨_, mul_mem (mul_mem ha hB) hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Nat.cast_mul]
    congr 2
    ring
  intro k hk
  rw [mem_map_conj]
  refine ⟨isU_mul (isU_mul (isU_inv hh) hk.1) hh, by rw [det_conj, hk.2.1], ?_, key k hk⟩
  obtain ⟨C, hC, e⟩ := key _ (inv_mem hk)
  have : (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h := by group
  rw [this, e]
  exact add_mem (one_mem _) (natCast_smul_mem _ hC)

theorem cong_mul_le {H : AddSubgroup (Fin n → R)} {M a : ℕ} : cong σ G H (M * a) ≤ cong σ G H M := by
  rintro k ⟨h1, h2, h3, B, hB, e⟩
  exact ⟨h1, h2, h3, _, natCast_smul_mem a hB, by rw [e, smul_smul, Nat.cast_mul]⟩

theorem exists_det_one_conj_eq (hG : IsUnit G.det) {g : GL (Fin n) R} (hg : IsU σ G g.1) :
    ∃ s : GL (Fin n) R, IsU σ G s.1 ∧ s.1.det = 1 ∧ ∀ k, (g ^ n)⁻¹ * k * g ^ n = s⁻¹ * k * s := by
  have hd := det_mul_det hG hg
  let z : GL (Fin n) R := ⟨σ g.1.det • 1, g.1.det • 1, by simp [smul_smul, mul_comm, hd],
    by simp [smul_smul, mul_comm, hd]⟩
  have hz : ∀ k, z * k = k * z := fun k => Units.ext (by simp [z])
  have hd' : σ g.1.det * σ (σ g.1.det) = 1 := by rw [← map_mul, hd, map_one]
  refine ⟨z * g ^ n, isU_mul (isU_iff.2 ?_) (isU_pow hg n), ?_, fun k => ?_⟩
  · have : (σ g.1.det • (1 : Matrix (Fin n) (Fin n) R)).map σ = σ (σ g.1.det) • 1 := by
      ext i j; simp [one_apply, apply_ite σ]
    simp [z, this, smul_smul, mul_comm, hd']
  · rw [Units.val_mul, det_mul, Units.val_pow_eq_pow_val, det_pow]
    simp [z, ← mul_pow, mul_comm, hd]
  · rw [_root_.mul_inv_rev, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc k, ← hz k, mul_assoc z,
      inv_mul_cancel_left]

end Abstract

section Adelic

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def embGL : GL (Fin n) E →* GL (Fin n) (RA F E) := GeneralLinearGroup.map (emb F)

theorem embGL_val (γ : GL (Fin n) E) : (embGL F γ).1 = (emb F).mapMatrix γ.1 := rfl

theorem emb_injective : Function.Injective (emb F : E →+* RA F E) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h => by
    have : (0 : v.adicCompletion F) = 1 := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
    exact zero_ne_one this⟩⟩
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

variable {F} (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

def sgA : RA F E →+* RA F E := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom

theorem isU_emb {γ : Matrix (Fin n) (Fin n) E} :
    IsU (sgA c) ((emb F).mapMatrix G) ((emb F).mapMatrix γ) ↔ IsU (c : E →+* E) G γ := by
  have e : ((emb F).mapMatrix γ)ᵀ * (emb F).mapMatrix G * ((emb F).mapMatrix γ).map (sgA c) =
      (emb F).mapMatrix (γᵀ * G * γ.map (c : E →+* E)) := by
    rw [map_mul, map_mul]; rfl
  rw [isU_iff, isU_iff, e]
  exact (Matrix.map_injective (emb_injective F)).eq_iff

variable [NumberField E] {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
  (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)

include hL hsp in

theorem embGL_mem_cong {M : ℕ} (hM : 0 < M) (γ : GL (Fin n) E) :
    embGL F γ ∈ cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M ↔
      IsU (c : E →+* E) G γ.1 ∧ γ.1.det = 1 ∧ (∀ x, x ∈ L ↔ γ.1 *ᵥ x ∈ L) ∧
        ∀ x ∈ L, ∃ y ∈ L, γ.1 *ᵥ x - x = M • y := by
  have h1 := (hat_rational_points_and_approx F E n L hL hsp).1
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have hd : ((emb F).mapMatrix γ.1).det = 1 ↔ γ.1.det = 1 := by
    rw [← RingHom.map_det, ← map_one (emb F), (emb_injective F).eq_iff]
  have hst : ∀ A : Matrix (Fin n) (Fin n) E, (emb F).mapMatrix A ∈ stab (hat F (L : Set (Fin n → E))) ↔
      ∀ x ∈ L, A *ᵥ x ∈ L := fun A => ⟨fun h x hx => by
        rw [← h1, ← emb_mulVec]; exact h _ (Translate.fv_mem_hat hx), emb_mem_stab F⟩
  set A : Matrix (Fin n) (Fin n) E := (M : E)⁻¹ • (γ.1 - 1) with hA
  have eA : γ.1 = 1 + (M : E) • A := by rw [hA, smul_inv_smul₀ hME, add_sub_cancel]
  have eA' : (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • (emb F).mapMatrix A := by
    rw [eA, map_add, map_one, emb_smul, map_natCast]
  have eAx : ∀ x, γ.1 *ᵥ x - x = M • (A *ᵥ x) := fun x => by
    rw [eA, add_mulVec, one_mulVec, add_sub_cancel_left, smul_mulVec, Nat.cast_smul_eq_nsmul]
  have h3 : (∃ B ∈ stab (hat F (L : Set (Fin n → E))), (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • B) ↔
      ∀ x ∈ L, A *ᵥ x ∈ L := by
    rw [← hst]
    refine ⟨?_, fun h => ⟨_, h, eA'⟩⟩
    rintro ⟨B, hB, e⟩
    rw [eA', add_right_inj] at e
    rwa [(isUnit_nat F hM).smul_left_cancel.1 e]
  have h4 : (∀ x ∈ L, ∃ y ∈ L, γ.1 *ᵥ x - x = M • y) ↔ ∀ x ∈ L, A *ᵥ x ∈ L := by
    refine forall₂_congr fun x _ => ⟨?_, fun h => ⟨_, h, eAx x⟩⟩
    rintro ⟨y, hy, e⟩
    rw [eAx, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at e
    rwa [smul_right_injective _ hME e]
  rw [mem_cong, ← map_inv, embGL_val, embGL_val, isU_emb, hd, hst, h3, h4]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun h => ⟨fun h' x => ⟨fun hx => ?_,
    fun hx => ?_⟩, fun h' x hx => ?_⟩
  · rw [← sub_add_cancel (γ.1 *ᵥ x) x, eAx]
    exact add_mem (nsmul_mem (h x hx) M) hx
  · have := h' _ hx
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  · rw [h', mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hx

variable (hrk : Module.finrank F E = 2) (hG : IsHerm (c : E →+* E) G)
  (hiso : ∃ z : Fin n → E, z ≠ 0 ∧ hf (c : E →+* E) G z z = 0)

include hL hsp hrk hG hiso in

theorem exists_inv_mul_mem_cong {M : ℕ} (hM : 0 < M) {s : GL (Fin n) (RA F E)}
    (hs : IsU (sgA c) ((emb F).mapMatrix G) s.1) (hd : s.1.det = 1) :
    ∃ γ : GL (Fin n) E, IsU (c : E →+* E) G γ.1 ∧ (embGL F γ)⁻¹ * s ∈
      cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M := by
  obtain ⟨γ, h1, h2, h3⟩ := strong_approximation F E c n G hrk hG hiso L hL hsp s hs hd M hM
  let δ : GL (Fin n) E := GeneralLinearGroup.mkOfDetNeZero γ (by rw [h2]; exact one_ne_zero)
  have e : ((embGL F δ⁻¹)⁻¹ * s).1 = (emb F).mapMatrix γ * s.1 := by rw [map_inv, inv_inv]; rfl
  have hdet : ((embGL F δ⁻¹)⁻¹ * s).1.det = 1 := by
    rw [e, det_mul, hd, ← RingHom.map_det, h2, map_one, mul_one]
  obtain ⟨B, hB, eB⟩ := exists_of_cong (H := hat F (L : Set (Fin n → E))) (isUnit_nat F hM)
    (A := (emb F).mapMatrix γ * s.1 - 1) fun z hz => by
      obtain ⟨w, hw, e⟩ := h3 z hz
      exact ⟨w, hw, by rw [sub_mulVec, one_mulVec]; exact sub_eq_of_eq_add' e⟩
  have eB' : ((embGL F δ⁻¹)⁻¹ * s).1 = 1 + (M : RA F E) • B := by rw [e, ← eB, add_sub_cancel]
  refine ⟨δ⁻¹, isU_inv (a := δ) h1, by rw [e]; exact isU_mul ((isU_emb c G).2 h1) hs, hdet, ?_, B, hB, eB'⟩
  refine inv_mulVec_mem_hat F E n L _ c hL hsp ?_ (by rw [hdet, map_one, mul_one])
  rw [eB']
  exact add_mem (one_mem (stab _)) (natCast_smul_mem _ hB)

include hL hsp hrk hG hiso in

theorem relIndex_comap {M : ℕ} (hM : 0 < M) {h : GL (Fin n) (RA F E)}
    (hh : IsU (sgA c) ((emb F).mapMatrix G) h.1) (K : Subgroup (GL (Fin n) (RA F E)))
    (hK : K = cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M) :
    ((K.map (MulAut.conj h).toMonoidHom).comap (embGL F)).relIndex (K.comap (embGL F)) =
      (K.map (MulAut.conj h).toMonoidHom).relIndex K ∧
    (K.comap (embGL F)).relIndex ((K.map (MulAut.conj h).toMonoidHom).comap (embGL F)) =
      K.relIndex (K.map (MulAut.conj h).toMonoidHom) := by
  subst hK
  obtain ⟨a, ha0, ha⟩ := exists_bound_stab F hL hsp (h⁻¹).1
  obtain ⟨b, hb0, hb⟩ := exists_bound_stab F hL hsp h.1
  refine GlobalTheory.HL.relIndex_pair_comap_of_dense_image _ _ _ fun s hs => ?_
  have hs' : IsU (sgA c) ((emb F).mapMatrix G) s.1 ∧ s.1.det = 1 := by
    rcases hs with hs | hs
    · rw [mem_map_conj] at hs
      refine ⟨?_, (det_conj h s).symm.trans hs.2.1⟩
      have e : s = h * (h⁻¹ * s * h) * h⁻¹ := by group
      rw [e]
      exact isU_mul (isU_mul hh hs.1) (isU_inv hh)
    · exact ⟨hs.1, hs.2.1⟩
  obtain ⟨γ, -, hγ⟩ := exists_inv_mul_mem_cong c G hL hsp hrk hG hiso
    (Nat.mul_pos (Nat.mul_pos hM ha0) hb0) hs'.1 hs'.2
  exact ⟨γ, cong_le_map_conj hh ha hb hγ, cong_mul_le (cong_mul_le hγ)⟩

end Adelic

section Covolume

open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem covol_of_le (X P : Data E r) (δ : GL (Fin r) E) (hΨ : P.Ψ = X.Ψ) (hG : P.Gm = X.Gm) (hp : P.p0 = X.p0)
    (hδ : ∀ v w, herm X.Gm (δ.1 *ᵥ v) (δ.1 *ᵥ w) = herm X.Gm v w)
    (hle : P.Γ.map (MulAut.conj δ).toMonoidHom ≤ X.Γ)
    (hi : (P.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0) :
    covol P = covol X * ((P.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ) := by
  have h := GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup E r X P hΨ δ _ _ _ _ (fun _ => 1) hG hp hδ hle hi
    (isOrth_x0F X) (isOrth_x0F P) (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec
    (GlobalTheory.MetricWeightTest.exists_fundSet_orth P (isOrth_x0F P)).choose_spec measurable_const
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  rw [setLIntegral_one, setLIntegral_one] at h
  rw [covol, covol, h, ENNReal.toReal_mul, ENNReal.toReal_natCast, congrArg Finset.card hΨ]
  ring

theorem covol_mul_relIndex (X X' : Data E r) (δ : GL (Fin r) E) (hΨ : X'.Ψ = X.Ψ) (hG : X'.Gm = X.Gm)
    (hp : X'.p0 = X.p0) (hδ : ∀ v w, herm X.Gm (δ.1 *ᵥ v) (δ.1 *ᵥ w) = herm X.Gm v w) :
    covol X * ((X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ) =
      covol X' * (X.Γ.relIndex (X'.Γ.map (MulAut.conj δ).toMonoidHom) : ℝ) := by
  set f := (MulAut.conj δ).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj δ).injective
  have h1 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X' X δ hG (by rw [hG]; exact hδ)
  have h2 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X X' δ⁻¹ hG.symm (GlobalTheory.SubgroupUnfold.isIsom_inv hδ)
  have e : X.Γ.map (MulAut.conj δ⁻¹).toMonoidHom = X.Γ.comap f := by
    ext k
    rw [mem_map_conj, inv_inv]; rfl
  rw [e] at h2
  have e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K := fun K => by
    ext k
    rw [mem_map_conj]; simp
  obtain ⟨P, hPΨ, hPG, hPp, hP⟩ := GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup E r X' (X.Γ.comap f ⊓ X'.Γ) inf_le_right
    (by rwa [Subgroup.inf_relIndex_right])
  have e2 : P.Γ.map f = X'.Γ.map f ⊓ X.Γ := by
    rw [hP, Subgroup.map_inf _ _ _ hinj, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj δ).surjective,
      inf_comm]
  have a := covol_of_le X P δ (hPΨ.trans hΨ) (hPG.trans hG) (hPp.trans hp) hδ (e2 ▸ inf_le_right)
    (by rwa [← hf, e2, Subgroup.inf_relIndex_right])
  have b := covol_of_le X' P 1 hPΨ hPG hPp (by simp) (by rw [e1, hP]; exact inf_le_right)
    (by rwa [e1, hP, Subgroup.inf_relIndex_right])
  rw [← hf, e2, Subgroup.inf_relIndex_right] at a
  rw [e1, hP, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap] at b
  rw [← a, b]

end Covolume

theorem covol_eq_of_same_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.Gm = Y.Gm → Y'.ξ0 = Y.ξ0 → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → GlobalTheory.TrueCx.covol Y = GlobalTheory.TrueCx.covol Y' := by
  intro E _ _ _ H l r Y Y' _ _ hΨ hG hξ hp h1 h2 hl hl' hs hs'
  haveI := H.unram
  set F := maximalRealSubfield E
  set c : E ≃ₐ[F] E := IsCMField.complexConj E with hc
  have hM : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos)
    (Nat.dvd_lcm_left _ _))
  have hM0 : 0 < l.M' := by omega
  have hrk : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hH : IsHerm (c : E →+* E) Y.Gm := ⟨IsCMField.complexConj_apply_apply E, by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h), Y.Gm_herm, Y.Gm_det⟩
  have hiso : ∃ z : Fin r → E, z ≠ 0 ∧ hf (c : E →+* E) Y.Gm z z = 0 := GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm E H r Y h1 h2 hs
  have hcomap : ∀ Z : Data E r, Z.Gm = Y.Gm → IsLevGrp l Z → IsSelfDualTr Z →
      (cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Z.Λ : Set (Fin r → E))) l.M').comap (embGL F) = Z.Γ := by
    intro Z hZ hlZ hsZ
    ext γ
    rw [Subgroup.mem_comap, embGL_mem_cong c Y.Gm Z.Λ_fg Z.Λ_span hM0, GlobalTheory.T.mem_fullLevelGroup_iff_congruence_lcm E H l r Z hlZ hsZ, ← hZ]
    exact ⟨fun h => ⟨⟨h.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨h.1.1,
      GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le E r _ Z.Gm Z.Λ γ hM Z.Gm_det Z.Λ_fg Z.Λ_span h.1 h.2, h.1.2, h.2⟩⟩
  have hsd : ∀ Z : Data E r, Z.Gm = Y.Gm → Z.ξ0 = Y.ξ0 → IsSelfDualTr Z → GlobalTheory.SW.SelfD Y Z.Λ := by
    intro Z hZ hZξ hsZ
    refine ⟨Z.Λ_fg, fun x => (hsZ x).trans (forall₂_congr fun y _ => ?_)⟩
    rw [GlobalTheory.ThFr.EF_def, hZ, hZξ]
    rcases Y.κ0_xi with h | h <;> rw [h]
    · rw [mul_div_cancel_left₀ _ two_ne_zero]
    · rw [neg_div, mul_div_cancel_left₀ _ two_ne_zero, neg_neg, neg_mul, map_neg]
      exact ⟨fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩, fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, hk]⟩⟩
  obtain ⟨g, hg, hgU⟩ := GlobalTheory.Ker.OntoLat.exists_adelic_matrix F c (fun _ => rfl) Y (hsd Y rfl rfl hs)
    (hsd Y' hG hξ hs')
  replace hgU : IsU (sgA c) ((emb F).mapMatrix Y.Gm) g.1 := hgU
  have hΓ := hcomap Y rfl hl hs
  have hΓ' := hcomap Y' hG hl' hs'
  rw [← map_conj_cong hgU hg] at hΓ'
  generalize hK : cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Y.Λ : Set (Fin r → E))) l.M' = K at hΓ hΓ'

  obtain ⟨a1, a2⟩ := relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hgU K hK.symm
  rw [hΓ, hΓ'] at a1 a2
  have e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K := fun K => by
    ext k
    rw [mem_map_conj]; simp
  have n1 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y' Y 1 hG (by simp)
  have n2 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y Y' 1 hG.symm (by simp)
  have hcov := covol_mul_relIndex Y Y' 1 hΨ hG hp (by simp)
  rw [e1] at n1 n2 hcov

  obtain ⟨s, hsU, hs1, hsc⟩ := exists_det_one_conj_eq
    (by rw [← RingHom.map_det]; exact Y.Gm_det.isUnit.map _) hgU
  obtain ⟨γ, hγU, hγ⟩ := exists_inv_mul_mem_cong c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hsU hs1
  rw [hK] at hγ
  have e2 : K.map (MulAut.conj (g ^ r)).toMonoidHom = K.map (MulAut.conj (embGL F γ)).toMonoidHom := by
    ext k
    rw [mem_map_conj, mem_map_conj, hsc]
    have : s⁻¹ * k * s = ((embGL F γ)⁻¹ * s)⁻¹ * ((embGL F γ)⁻¹ * k * embGL F γ) * ((embGL F γ)⁻¹ * s) := by
      group
    rw [this, K.mul_mem_cancel_right hγ, K.mul_mem_cancel_left (K.inv_mem hγ)]
  obtain ⟨b1, b2⟩ := relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 (h := embGL F γ)
    ((isU_emb c Y.Gm).2 hγU) K hK.symm
  have e3 : (K.map (MulAut.conj (embGL F γ)).toMonoidHom).comap (embGL F) =
      Y.Γ.map (MulAut.conj γ).toMonoidHom := by
    ext k
    rw [Subgroup.mem_comap, mem_map_conj, mem_map_conj, ← hΓ, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  rw [e3, hΓ] at b1 b2
  have hcov' := mul_left_cancel₀ (GlobalTheory.TrueCx.covol_pos Y).ne' (covol_mul_relIndex Y Y γ rfl rfl rfl hγU)
  have key := GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm _ K g r (by omega) (a1 ▸ n1) (a2 ▸ n2)
    (by rw [e2, ← b1, ← b2]; exact_mod_cast hcov')
  rw [← a1, ← a2] at key
  rw [← key] at hcov
  exact mul_right_cancel₀ (Nat.cast_ne_zero.2 n1) hcov

end GlobalTheory.EqCovol.SameSpace
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.Gm = Y.Gm → Y'.ξ0 = Y.ξ0 → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → GlobalTheory.TrueCx.covol Y = GlobalTheory.TrueCx.covol Y' := by
  atlas_forward_decl GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space
end

section
section
open NumberField

namespace GlobalTheory.EqCovol

theorem covol_eq_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hG hp hq k k'
  obtain ⟨Y, hΨ, hp0, -, -, -, hL, hS, hc⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k
  obtain ⟨Y', hΨ', hp0', -, -, -, hL', hS', hc'⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k'
  obtain ⟨hr, hk, -⟩ := hU
  have hY : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ ▸ (hk k).2 τ
  have hY' : ∀ τ : E →+* ℂ, τ ∈ Y'.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ' ▸ (hk k').2 τ
  have eΨ : Y'.Ψ = Y.Ψ := Finset.ext fun τ => (hY' τ).trans (hY τ).symm
  have ep : Y'.p0 = Y.p0 := by rw [hp0, hp0', (hk k).1, (hk k').1]
  have h1 : 1 ≤ Y.p0 := by rw [hp0, (hk k).1]; exact hq
  have h2 : Y.p0 < r := by rw [hp0, (hk k).1, hr]; omega
  obtain ⟨Z, hZΨ, hZG, hZξ, hZp, hZL, hZS, hZc⟩ := GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace E H l r Y Y' hY eΨ ep h1 h2 hL' hS hS'
  rw [hc, hc', ← hZc]
  exact GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space E H l r Y Z hG hY hZΨ hZG hZξ hZp h1 h2 hL hZL hS hZS

end GlobalTheory.EqCovol
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformisation_components_covolume_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  atlas_forward_decl GlobalTheory.EqCovol.covol_eq_of_isUnf
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CompEqVol

theorem eqVolume_good : Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → EqVolume Y.U := by
  intro hP2 hS hKS hSA D T hT j hp hq hf hj Y e o hY
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨M, hs, hb, hk, hc⟩ := hKS.exists_model_charts hS hr Y.d.Xo₂ Y.d.c₂
  obtain ⟨TF, hTF⟩ := GlobalTheory.CompProport.exists_torFlag_charts hr M hs hb hk hc
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  obtain ⟨-, q, -, hv⟩ := GlobalTheory.CompProport.vZero_eq_covol (GlobalTheory.T.stronger_published_hypotheses_imply hP2) hP2.q7 hSA hY hf TF hTF hσ
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.lev.1.2.1 hg0
  have hcov := GlobalTheory.T.complexUniformisation_components_covolume_eq _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U Y.d.c₂.F.val.toRingHom)) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hY.unf _ hσ)) hg hp hq
  intro Z Z'
  obtain ⟨k, rfl⟩ := q.surjective Z
  obtain ⟨k', rfl⟩ := q.surjective Z'
  rw [hv, hv]
  exact congrArg (fun x => x * _ / _) (hcov k k')

end GlobalTheory.CompEqVol
end
