import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsotropicComplGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate
import Development.AbelianVarietyTheory.Definitions.Divisors.WeilRangeOfAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDNegGram
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConclusionZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open Formalism.UG (cT)

namespace GlobalTheory.SWInt

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

def blockColumnMatrix {R : Type} {k : ℕ} (a b : Matrix (Fin n) (Fin k) R) : Matrix (Fin (n + n)) (Fin k) R :=
  (Matrix.fromRows a b).submatrix finSumFinEquiv.symm id

omit [NumberField E] in

theorem mem_unipN_iff (g : UA σ J₂) : g ∈ unipN σ J₂ ↔ (mat g - 1) * blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 = 0 := by
  have e : ∀ i j, (mat g * blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1) i j =
      mat g i (finSumFinEquiv (.inl j)) + mat g i (finSumFinEquiv (.inr j)) := fun i j => by
    rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    simp [Matrix.one_apply]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, mem_unipOf, mem_siegelOf, keepsDiag_iff]
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    have h3 : ∀ i, mat g (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) +
      mat g (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)) = (1 : Matrix (Fin n) (Fin n) (AE F E)) i j :=
      fun i => congrFun (congrFun h2 i) j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> rw [e] <;>
      simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    · exact h3 i
    · exact (h1 i j).trans (h3 i)
  · intro h
    have h3 : ∀ i j, mat g (finSumFinEquiv i) (finSumFinEquiv (.inl j)) +
      mat g (finSumFinEquiv i) (finSumFinEquiv (.inr j)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 i j :=
      fun i j => by
        rw [← e, h]
        simp only [blockColumnMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    exact ⟨fun i j => (h3 (.inr i) j).trans (h3 (.inl i) j).symm, Matrix.ext fun i j => h3 (.inl i) j⟩

theorem cocompact_unipN (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (hdet : J.det ≠ 0) (h₂ : J₂ = dblGram finSumFinEquiv J) :
    LocallyCompactSpace (unipN σ J₂) ∧
      ∃ C : Set (unipN σ J₂), IsCompact C ∧ ∀ g : unipN σ J₂, ∃ γ : ratN σ J₂, γ • g ∈ C := by
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨δ, hδ, hδs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hc : δ * σ l⁻¹ ≠ 0 := mul_ne_zero hδ ((map_ne_zero σ).2 (inv_ne_zero hl))
  set c := δ * σ l⁻¹ with hcd
  set H : Matrix (Fin n) (Fin n) E := c • J.map σ with hH
  have hHd : H.det ≠ 0 := by
    rw [hH, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ hc) ?_
    rw [show (J.map σ).det = σ J.det from ((σ : E →+* E).map_det J).symm]
    exact (map_ne_zero σ).2 hdet
  have hHh : ∀ i j, σ (H j i) = H i j := fun i j => by
    have h := congrArg σ (hJ i j)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_neg, hσ] at h
    simp only [hH, hcd, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hδs]
    linear_combination (-δ) * h
  have hG : c • J₂.map σ = dblGram finSumFinEquiv H := by
    rw [h₂, dblGram, dblGram, blkMat_map _ _ (map_zero σ), Matrix.map_neg _ (map_neg σ), hH]
    change (c • Matrix.fromBlocks (J.map σ) 0 0 (-J.map σ)).submatrix _ _ = _
    rw [Matrix.fromBlocks_smul, smul_zero, smul_neg, blkMat]
  have hN : IsHermND σ (c • J₂.map σ) := by
    rw [hG]
    refine ⟨fun i j => ?_, ?_⟩
    · obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero,
          Matrix.neg_apply, map_neg, hHh]
    · rw [dblGram, det_blkMat, Matrix.det_neg]
      exact mul_ne_zero hHd (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hHd)
  let C : Matrix (Fin (n + n)) (Fin n) E := blockColumnMatrix 1 1
  let D : Matrix (Fin (n + n)) (Fin n) E := blockColumnMatrix H⁻¹ 0
  have hi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hHd)
  have hi' : H⁻¹ * H = 1 := mul_eq_one_comm.1 hi
  have hCJ : cT (σ : E →+* E) C * (c • J₂.map σ) = (Matrix.fromCols H (-H)).submatrix id finSumFinEquiv.symm := by
    have : cT (σ : E →+* E) C = (Matrix.fromCols 1 1).submatrix id finSumFinEquiv.symm := by
      ext i j
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [C, cT, blockColumnMatrix, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
          id, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
          Matrix.one_apply, apply_ite (σ : E →+* E), map_one, map_zero, eq_comm (a := i)]
    rw [this, hG, dblGram, blkMat, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
    simp
  have xy : cT (σ : E →+* E) C * (c • J₂.map σ) * D = 1 := by
    rw [hCJ]
    simp only [D, blockColumnMatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, hi]
    simp
  have xx : cT (σ : E →+* E) C * (c • J₂.map σ) * C = 0 := by
    rw [hCJ]
    simp only [C, blockColumnMatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows]
    simp
  have hP : 1 - D * (cT (σ : E →+* E) C * (c • J₂.map σ)) =
      C * ((Matrix.fromCols (0 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E)).submatrix id finSumFinEquiv.symm :
        Matrix (Fin n) (Fin (n + n)) E) := by
    rw [hCJ]
    simp only [C, D, blockColumnMatrix]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.submatrix_one_equiv finSumFinEquiv.symm,
      ← Matrix.fromBlocks_one]
    ext i j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;> simp [hi']
  have hC : GlobalTheory.UAut.IsIsoCols σ (c • J₂.map σ) C := by
    refine ⟨Matrix.mulVec_injective_iff.1 fun x y h => funext fun i => ?_, xx⟩
    have := congrFun h (finSumFinEquiv (.inl i))
    simpa only [C, blockColumnMatrix, Matrix.submatrix_mulVec_equiv, Matrix.mulVec, Matrix.submatrix_apply, Equiv.symm_apply_apply, id,
      Matrix.fromRows_apply_inl, Matrix.one_apply, dotProduct, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] using this
  have hCa : GlobalTheory.SiegelSet.adMat F C = blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 := by
    simp only [C, blockColumnMatrix, GlobalTheory.SiegelSet.adMat, ← Matrix.submatrix_map, Matrix.fromRows_map,
      Matrix.map_one _ (map_zero _) (map_one _)]
  set e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ J₂ hc with he
  have hmem : ∀ g : UA σ J₂, g ∈ unipN σ J₂ ↔ e g ∈ GlobalTheory.SiegelSet.unipRad σ (c • J₂.map σ) C := fun g => by
    rw [mem_unipN_iff, GlobalTheory.EisCT.mem_unipRad_iff_dual xy, hP, ← hCa]
    refine ⟨fun h => ⟨h, 0, ?_⟩, fun h => h.1⟩
    rw [GlobalTheory.SiegelSet.adMat, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_zero]
    exact (congrArg (· * _) h).trans (Matrix.zero_mul _)
  have hrat := GlobalTheory.RatCorr.ratU_iff_ratPts F E σ hσ _ J₂ c hc
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hcm hN hC
  obtain ⟨K', hK', hcov'⟩ := GlobalTheory.UAut.cocompact_unipRad hcm hN hC
  have hec : Continuous e := continuous_subtype_val.subtype_mk _
  have hes : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let eH : unipN σ J₂ ≃ₜ GlobalTheory.SiegelSet.unipRad σ (c • J₂.map σ) C :=
    { toFun := fun x => ⟨e x, (hmem x).1 x.2⟩
      invFun := fun y => ⟨e.symm y, (hmem _).2 (by rw [e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      continuous_toFun := (hec.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hes.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨eH.isClosedEmbedding.locallyCompactSpace, eH ⁻¹' K', eH.isCompact_preimage.2 hK', fun g => ?_⟩
  obtain ⟨γ', hγ', hK⟩ := hcov' (eH g)
  refine ⟨⟨eH.symm γ', ?_⟩, ?_⟩
  · show e.symm (γ' : _) ∈ ratU σ J₂
    rw [hrat, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hγ'
  · show eH (eH.symm γ' * g) ∈ K'
    have : eH (eH.symm γ' * g) = γ' * eH g := by
      apply Subtype.ext
      show e (e.symm (γ' : _) * (g : _)) = (γ' : _) * e g
      rw [map_mul, MulEquiv.apply_symm_apply]
    rw [this]
    exact hK

theorem existsUnique_isNormN (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (hdet : J.det ≠ 0) (h₂ : J₂ = dblGram finSumFinEquiv J) :
    ∃! νN : Measure (unipN σ J₂), IsNormN σ νN := by
  obtain ⟨hLC, C, hC, hcov⟩ := cocompact_unipN hcm hl hJ hdet h₂
  obtain ⟨hTG, -, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ J₂
  haveI : BorelSpace (UA σ J₂) := ⟨rfl⟩
  haveI : Countable (ratN σ J₂) := GlobalTheory.UnipMass.countable_ratU' σ J₂ (unipN σ J₂)
  haveI : DiscreteTopology (ratN σ J₂) := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ J₂ (unipN σ J₂)
  obtain ⟨ν, 𝓓, h1, h2, h3⟩ := GlobalTheory.T.cocompact_lattice_unit_covolume _ (ratN σ J₂) C hC hcov
  refine ⟨ν, ⟨h1, 𝓓, h2, h3⟩, ?_⟩
  rintro ν' ⟨h1', 𝓓', h2', h3'⟩
  have e := Measure.isMulLeftInvariant_eq_smul ν' ν
  haveI : MeasurableConstSMul (ratN σ J₂) (unipN σ J₂) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : unipN σ J₂ => (γ : unipN σ J₂) * x).measurable⟩
  haveI : SMulInvariantMeasure (ratN σ J₂) (unipN σ J₂) ν' := ⟨fun γ A _ => measure_preimage_mul ν' (γ : unipN σ J₂) A⟩
  have h4 : IsFundamentalDomain (ratN σ J₂) 𝓓 ν' := h2.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h5 : ν' 𝓓 = 1 := (h4.measure_eq h2').trans h3'
  rw [e, Measure.smul_apply, h3, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h5
  rw [e, h5, one_smul]

end GlobalTheory.SWInt

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit GlobalTheory.SWLink
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWACase.Model

section
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def HypsMet (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n m : ℕ) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧
  ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
  ∃ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 ∧ IsHermND σ (l • JV) ∧ (∀ x, form σ JV x x = 0 → x = 0) ∧
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) ∧ J₂ = dblGram finSumFinEquiv J ∧
  ∃ T : GL (Fin (n + n)) E, IsWittBasis σ J l T ∧
  ∃ (κ : Type) (_ : Fintype κ) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co ∧
  ∃ (_ : MeasurableSpace (κ → AF F)) (_ : BorelSpace (κ → AF F)) (μ : Measure (κ → AF F)), IsTamagawa F κ μ ∧
  ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m ∧
  ∃ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om ∧
  ∃ K : Subgroup (UA σ J₂), IsStdK σ T K ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K ∧
  ∃ Φ ∈ schA F κ, Φ ≠ 0 ∧ FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) ∧
  ∃ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ JV) 𝓕 ν
end

set_option maxHeartbeats 4000000 in
theorem hypsMet_of (D : D7) (A V : HSp D) (han : IsAniso V) :
    HypsMet D.host.F D.host.E D.sp.cm.sig A.rank V.rank := by
  obtain ⟨ψ, χ, θ, μ, 𝓕, ω, H, ν, Φ, hψ, hχ, hres, hθ, hμ, hω, hH, hν, hΦ, hΦ0, -⟩ := GlobalTheory.AnisoStdModel.data D A V
  let n := A.rank
  have hCM := GlobalTheory.AdelicU.isCMExt_host D
  obtain ⟨δ, hδ0, hδ⟩ := skew_xi D
  let J : Matrix (Fin n) (Fin n) D.host.E := δ • 1
  have hJ : ∀ i j, D.sp.cm.sig (J j i) = -J i j := fun i j => by
    by_cases h : i = j
    · subst h; simp [J, hδ]
    · simp [J, h, Ne.symm h]
  have hJ0 : J.det ≠ 0 := by simp [J, hδ0]
  obtain ⟨T, K, hT, hK, -⟩ := GlobalTheory.T.exists_witt_basis_compact_stabiliser D.host.F D.host.E D.sp.cm.sig hCM n 1 J _ one_ne_zero hJ0 rfl
  have hG := gram_witt hJ hT
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.witt_change_basis_unitary_iso D n _ T hG
  obtain ⟨hP, ha⟩ := GlobalTheory.T.siegel_parabolic_chart_levi_block D n _ T κ hκ J hT
  have hK' := GlobalTheory.T.standard_compact_under_witt_chart D n _ T κ hκ K hK
  obtain ⟨ι, hι, hιQ⟩ := GlobalTheory.T.unitary_group_conj_hermitian_automorphisms D V
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let ε := Module.finBasis D.host.F D.host.E
  obtain ⟨co, had, hco⟩ := GlobalTheory.T.darboux_basis_adapted_coordinates D n V J _ T hT hG _ ε
  letI : MeasurableSpace (Fin V.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := borel _
  haveI : BorelSpace (Fin V.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := ⟨rfl⟩
  obtain ⟨μ', hμ', hint⟩ := GlobalTheory.T.tamagawa_measure_matrix_adeles D V.rank n _ ε μ 𝓕 hμ
  obtain ⟨om, hom⟩ := GlobalTheory.T.weil_representation_seesaw_schwartz D n V ψ χ θ hθ μ 𝓕 hμ ω hω _ _ ε ι κ
  obtain ⟨ν', 𝓖, hν', h𝓖, -⟩ := GlobalTheory.T.haar_average_fundamental_domain_descent D V ι hιQ ν hν
  obtain ⟨⟨φ, hφ⟩, e⟩ := GlobalTheory.SchwartzCoord.exists_schA_comp_coord_eq D θ hθ V.rank n _ ε Φ.1 Φ.2
  obtain ⟨hI, -⟩ := height hH hP ha hK'
  have hF := formulas hθ hω hT hG hκ hι hco hint hom
  have hR := GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E hCM.2.2.1 χ V.rank hres
  have h0 : φ ≠ 0 := fun h => hΦ0 (Subtype.ext (by
    have e' : φ ∘ coord ε = Φ.1 := e
    rw [← e', h]; rfl))
  exact ⟨hCM, unramified_host D, ψ, hψ, 1, -V.gram, J, _, one_ne_zero, isHermND_neg_gram V, aniso_neg_gram han,
    by rw [inv_one, one_smul]; exact hJ, rfl, T, hT, _, inferInstance, co, had, inferInstance, inferInstance, μ', hμ', χ, hχ, hR,
    om, hF, K, hK, hI, φ, hφ, h0, kfin hom hK' hφ Φ e hΦ, ν', 𝓖, hν', h𝓖⟩

theorem hypsMet (D : D7) (n m : ℕ) : HypsMet D.host.F D.host.E D.sp.cm.sig n m := by
  obtain ⟨A, V, rfl, rfl, h⟩ := GlobalTheory.AnisoStdModel.ranks D n m
  exact hypsMet_of D A V h


end GlobalTheory.SWACase.Model

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit GlobalTheory.SWLink
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWInt

section
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

def HasWeilModel (ψ : AddChar (AF F) ℂ) (χ : Chr F E) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E)
    (K : Subgroup (UA σ J₂)) (JV : Matrix (Fin m) (Fin m) E) (P : Submodule ℂ (UA σ J₂ → ℂ) → Prop) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co ∧
  ∃ (_ : MeasurableSpace (κ → AF F)) (_ : BorelSpace (κ → AF F)) (μ : Measure (κ → AF F)), IsTamagawa F κ μ ∧
  ∃ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om ∧ P (secSpace om K)

def ComplMet (m t : ℕ) (b : Prop) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧
  ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
  ∃ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin (m + t)) (Fin (m + t)) E)
    (J₂ : Matrix (Fin (m + t + (m + t))) (Fin (m + t + (m + t))) E),
    l ≠ 0 ∧ IsHermND σ (l • JV) ∧ (∀ x, form σ JV x x = 0 → x = 0) ∧
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) ∧ J₂ = dblGram finSumFinEquiv J ∧
  ∃ T : GL (Fin (m + t + (m + t))) E, IsWittBasis σ J l T ∧
  ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m ∧
  ∃ K : Subgroup (UA σ J₂), IsStdK σ T K ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K ∧
    (∃ w : UA σ J₂, IsWeylElt σ T w) ∧ (∃ νN : Measure (GlobalTheory.SWWeil.unipN σ J₂), IsNormN σ νN) ∧
    HasWeilModel σ ψ χ T K JV (fun R => b → R ≠ ⊥) ∧ HasWeilModel σ ψ χ T K (complGram l JV t) fun R => b → R ≠ ⊥

end

theorem exists_frame_hyp (D : D7) (t : ℕ) : ∃ b : Module.Basis (Fin (t + t)) D.host.E (GlobalTheory.OrthSumSp.hypSp D t).V,
    ∀ i j, (GlobalTheory.OrthSumSp.hypSp D t).hT (b i) (b j) = -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 i j := by
  let P : Matrix (Fin (t + t)) (Fin (t + t)) D.host.E := blk 1 (-((2 : D.host.E)⁻¹ • 1)) 1 ((2 : D.host.E)⁻¹ • 1)
  have hP : P * blk ((2 : D.host.E)⁻¹ • 1) ((2 : D.host.E)⁻¹ • 1) (-1) 1 = 1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]
    congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg] <;>
      match_scalars <;> norm_num
  let f := (GlobalTheory.OrthSumSp.hypSp D t).frame
  let b := f.map (Matrix.toLinearEquiv f P (Matrix.isUnit_det_of_right_inverse hP))
  have hb : ∀ j, b j = ∑ i, P i j • f i := fun j => by
    simp only [b, Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hG : ∀ i j, (GlobalTheory.OrthSumSp.hypSp D t).hT (f i) (f j) =
      dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) i j := fun i j => by
    have := gram_hdbl (GlobalTheory.OrthSumSp.posSp D t)
    rw [GlobalTheory.OrthSumSp.posSp_gram D t] at this
    exact congrFun (congrFun this i) j
  refine ⟨b, fun i j => ?_⟩
  have e : (GlobalTheory.OrthSumSp.hypSp D t).hT (b i) (b j) =
      (Pᴴ * dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) * P) i j := by
    simp only [hb, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hG, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e1 : Pᴴ = blk 1 1 (-((2 : D.host.E)⁻¹ • 1)) ((2 : D.host.E)⁻¹ • 1) := by
    simp [P, blk, Matrix.fromBlocks_conjTranspose]
  have e2 : dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) = blk 1 0 0 (-1) := rfl
  have e3 : -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 = blk 0 (-1) (-1) 0 := by
    change (-Matrix.fromBlocks (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0).submatrix _ _ = _
    rw [Matrix.fromBlocks_neg, neg_zero, blk]
  rw [e, ← Matrix.neg_apply, e3, e1, e2, WittModel.blk_mul, WittModel.blk_mul]
  congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_zero, add_zero, zero_add] <;>
    match_scalars <;> norm_num

theorem exists_compl_space (D : D7) (V : HSp D) (t : ℕ) :
    ∃ b : Module.Basis (Fin (t + t)) D.host.E (GlobalTheory.OrthSumSp.hypSp D t).V,
      -(hsum V { GlobalTheory.OrthSumSp.hypSp D t with frame := b }).gram = complGram 1 (-V.gram) t := by
  obtain ⟨b, hb⟩ := exists_frame_hyp D t
  refine ⟨b, ?_⟩
  have e : HSpace.gram { GlobalTheory.OrthSumSp.hypSp D t with frame := b } = -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 :=
    Matrix.ext hb
  rw [gram_hsum, e, complGram, inv_one, one_smul]
  change (-Matrix.fromBlocks V.gram 0 0 (-blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0)).submatrix _ _ = _
  rw [Matrix.fromBlocks_neg, neg_zero, neg_zero, neg_neg, blkMat]

set_option maxHeartbeats 4000000 in

theorem complMet_of (D : D7) (V : HSp D) (han : IsAniso V) (t : ℕ) : ComplMet D.sp.cm.sig V.rank t False := by
  let n := V.rank + t
  obtain ⟨-, ψ, χ, omh, -, -, -, -, hω, -, -, -⟩ :=
    GlobalTheory.SiegelFormula.Model.data_exist GlobalTheory.weilRepresentationUnitaryPair V V
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  obtain ⟨lam, hlam, hψ, -⟩ :=
    GlobalTheory.StdUnn.shift_char_realPar D ψ hω.std θ hθ D.host.xi0 ⟨hxi, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D⟩
  have hl : lam ≠ 0 := fun h => by
    rw [h, map_zero] at hlam
    exact div_ne_zero (neg_ne_zero.2 hxi) hxi hlam.symm
  have hCM := GlobalTheory.AdelicU.isCMExt_host D
  obtain ⟨δ, hδ0, hδ⟩ := skew_xi D
  let J : Matrix (Fin n) (Fin n) D.host.E := δ • 1
  have hJ : ∀ i j, D.sp.cm.sig (J j i) = -J i j := fun i j => by
    by_cases h : i = j
    · subst h; simp [J, hδ]
    · simp [J, h, Ne.symm h]
  have hJ' : ∀ i j, D.sp.cm.sig (((1 : D.host.E)⁻¹ • J) j i) = -((1 : D.host.E)⁻¹ • J) i j := by
    rw [inv_one, one_smul]; exact hJ
  have hJ0 : J.det ≠ 0 := by simp [J, hδ0]
  obtain ⟨T, K, hT, hK, -⟩ := GlobalTheory.T.exists_witt_basis_compact_stabiliser D.host.F D.host.E D.sp.cm.sig hCM n 1 J _ one_ne_zero hJ0 rfl
  have hG := gram_witt hJ hT
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.witt_change_basis_unitary_iso D n _ T hG
  obtain ⟨hP, ha⟩ := GlobalTheory.T.siegel_parabolic_chart_levi_block D n _ T κ hκ J hT
  have hK' := GlobalTheory.T.standard_compact_under_witt_chart D n _ T κ hκ K hK
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D n
  obtain ⟨hI, -⟩ := height hH hP ha hK'
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let ε := Module.finBasis D.host.F D.host.E
  have key : ∀ B : HSp D, ResEta D χ B.rank →
      HasWeilModel D.sp.cm.sig (GlobalTheory.StdUnn.shift ψ lam) χ T K (-B.gram) fun R => False → R ≠ ⊥ := fun B hB => by
    obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank n
    obtain ⟨ω, hW⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D n B ψ hω.std lam hl χ hω.hecT hB θ hθ μ 𝓕 hμ
    obtain ⟨ι, hι, -⟩ := GlobalTheory.T.unitary_group_conj_hermitian_automorphisms D B
    obtain ⟨co, had, hco⟩ := GlobalTheory.T.darboux_basis_adapted_coordinates D n B J _ T hT hG _ ε
    letI : MeasurableSpace (Fin B.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := borel _
    haveI : BorelSpace (Fin B.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := ⟨rfl⟩
    obtain ⟨μ', hμ', hint⟩ := GlobalTheory.T.tamagawa_measure_matrix_adeles D B.rank n _ ε μ 𝓕 hμ
    obtain ⟨om, hom⟩ := GlobalTheory.T.weil_representation_seesaw_schwartz D n B _ χ θ hθ μ 𝓕 hμ ω hW _ _ ε ι κ
    exact ⟨_, inferInstance, co, had, inferInstance, inferInstance, μ', hμ', om, formulas hθ hW hT hG hκ hι hco hint hom,
      False.elim⟩
  obtain ⟨b, hb⟩ := exists_compl_space D V t
  have hres : ResEta D χ (V.rank + (t + t)) := resEta_parity hω.resT (by omega)
  have h2 := key (hsum V { GlobalTheory.OrthSumSp.hypSp D t with frame := b }) hres
  rw [hb] at h2
  obtain ⟨w, -, hw⟩ := exists_isWeylElt (GlobalTheory.SiegelSet.sigma_sigma hCM) one_ne_zero hJ' rfl hT
  exact ⟨hCM, unramified_host D, _, hψ, 1, -V.gram, J, _, one_ne_zero, isHermND_neg_gram V, aniso_neg_gram han, hJ', rfl,
    T, hT, χ, hω.hecT, GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E hCM.2.2.1 χ V.rank hω.resT, K, hK, hI, ⟨w, hw⟩,
    (existsUnique_isNormN hCM one_ne_zero hJ' hJ0 rfl).exists, key V hω.resT, h2⟩


end GlobalTheory.SWInt

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWInt.Model

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

open Classical in

def ind (w g : UA σ J₂) (𝓓 : Set (unipN σ J₂)) (y : UA σ J₂) : ℂ := if ∃ x ∈ 𝓓, y = w * (x : UA σ J₂) * g then 1 else 0

omit [NumberField E] in

theorem ind_apply (w g : UA σ J₂) (𝓓 : Set (unipN σ J₂)) :
    (fun x : unipN σ J₂ => ind w g 𝓓 (w * x * g)) = 𝓓.indicator fun _ => 1 := by
  funext x
  by_cases h : x ∈ 𝓓
  · rw [Set.indicator_of_mem h, ind, if_pos ⟨x, h, rfl⟩]
  · rw [Set.indicator_of_notMem h, ind, if_neg]
    rintro ⟨y, hy, e⟩
    exact h ((Subtype.ext (mul_left_cancel (mul_right_cancel e)) : x = y) ▸ hy)

omit [NumberField E] in

theorem exists_intM_eq_one {νN : Measure (unipN σ J₂)} (h : IsNormN σ νN) (w g : UA σ J₂) :
    ∃ f, IntConv νN w f g ∧ intM νN w f g = 1 := by
  obtain ⟨-, 𝓓, h1, h2⟩ := h
  refine ⟨ind w g 𝓓, ?_, ?_⟩
  · rw [IntConv, ind_apply]
    exact (integrableOn_const (by rw [h2]; exact ENNReal.one_ne_top) : IntegrableOn (fun _ => (1 : ℂ)) 𝓓 νN).integrable_indicator₀
      h1.nullMeasurableSet
  · rw [intM, ind_apply, integral_indicator₀ h1.nullMeasurableSet, setIntegral_const, Measure.real, h2,
      ENNReal.toReal_one, one_smul]

omit [NumberField E] in

theorem coefM_pole {νN : Measure (unipN σ J₂)} {w : UA σ J₂} {f : UA σ J₂ → ℂ} (hf : ∀ g, IntConv νN w f g) :
    HasIntCont νN w (fun s => s⁻¹ • f) ∧ (∀ g, coefM νN w (fun s => s⁻¹ • f) 0 (-1) g = intM νN w f g) ∧
      (∀ g, contM νN w (fun s => s⁻¹ • f) 0 g = 0) ∧ ∀ g, contM νN w (fun s => s⁻¹ • f) (-1) g = -intM νN w f g := by
  have hm : ∀ g s, MeromorphicAt (fun s : ℂ => s⁻¹ * intM νN w f g) s := fun g s =>
    (MeromorphicAt.id s).inv.mul (.const _ _)
  have he : ∀ g, (fun s : ℂ => intM νN w (s⁻¹ • f) g) = fun s => s⁻¹ * intM νN w f g := fun g =>
    funext fun s => intM_smul _ _ _
  have hx : ∀ g, Cont.IsMerExt (fun s : ℂ => s⁻¹ * intM νN w f g) Set.univ fun s => s⁻¹ * intM νN w f g := fun g =>
    Cont.isMerExt_self Cont.isRightDomain_univ fun s _ => hm g s
  refine ⟨⟨⟨0, fun s _ g => (hf g).smul _⟩, fun g => ?_⟩, fun g => ?_, fun g => ?_, fun g => ?_⟩
  · rw [he]; exact ⟨_, hx g⟩
  · rw [coefM, he]
    refine Cont.CoeffAt.laurent_eq (((hx g).isExtAt trivial).coeffAt_of_tendsto (k := 1) ?_)
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have : s ≠ 0 := hs
    simp only [sub_zero, pow_one]
    field_simp
  · rw [contM, he]
    refine Cont.ValueAt.cont_eq ⟨_, (hx g).isExtAt trivial, Polynomial.C (intM νN w f g) * Polynomial.X, by simp, ?_⟩
    refine tendsto_const_nhds.congr fun s => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, sub_zero, mul_comm, sub_self]
  · rw [contM, he]
    refine Cont.ValueAt.cont_eq (Cont.HolValueAt.valueAt ⟨_, (hx g).isExtAt trivial, ?_, by simp⟩)
    exact (analyticAt_id.inv (by simp)).mul analyticAt_const

omit [NumberField E] in

theorem exists_ratN (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (c : ℕ) :
    ∃ u : ratN σ J₂, inBasis σ T ((u : unipN σ J₂) : UA σ J₂) = blk 1 (c • 1) 0 1 := by
  have hG := WittModel.gram_of_isWittBasis hσ hl hJ h
  rw [← h₂] at hG
  have hm : (blk 1 (c • 1) 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) E) * blk 1 (-(c • 1)) 0 1 = 1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]; simp
  let w₀ : GL (Fin (n + n)) E := ⟨_, _, hm, mul_eq_one_comm.1 hm⟩
  have mp : ∀ {S : Type} [CommRing S] (f : E →+* S),
      (blk 1 (c • 1) 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) E).map f = blk 1 (c • 1) 0 1 := fun f => by
    have : (c • (1 : Matrix (Fin n) (Fin n) E)).map f = c • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.one_apply, apply_ite f, map_one, map_zero]
    simp only [blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f), this,
      Matrix.map_zero _ (map_zero f)]
  have hw : w₀.1ᵀ * blk 0 1 (-1) 0 * w₀.1.map σ = blk 0 1 (-1) 0 := by
    have e : w₀.1ᵀ = blk 1 0 (c • 1) 1 := by
      simp only [w₀, blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_one,
        Matrix.transpose_smul, Matrix.transpose_zero]
    have e' : w₀.1.map σ = blk 1 (c • 1) 0 1 := mp (σ : E →+* E)
    rw [e, e', WittModel.blk_mul, WittModel.blk_mul]
    simp
  have hT : T.1ᵀ * J₂ * T.1.map σ = l • blk 0 1 (-1) 0 := by
    rw [← hG, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl, one_smul]
  have i1 : (T⁻¹).1ᵀ * T.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have i2 : T.1.map σ * (T⁻¹).1.map σ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have key : (T * w₀ * T⁻¹).1ᵀ * J₂ * (T * w₀ * T⁻¹).1.map σ = J₂ := by
    calc _ = (T⁻¹).1ᵀ * (w₀.1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * w₀.1.map σ) * (T⁻¹).1.map σ := by
          simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = (T⁻¹).1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * (T⁻¹).1.map σ := by
          rw [hT, Matrix.mul_smul, Matrix.smul_mul, hw]
      _ = ((T⁻¹).1ᵀ * T.1ᵀ) * J₂ * (T.1.map σ * (T⁻¹).1.map σ) := by simp only [Matrix.mul_assoc]
      _ = J₂ := by rw [i1, i2, Matrix.one_mul, Matrix.mul_one]
  have hU : Matrix.GeneralLinearGroup.map (inclR (AF F)) (T * w₀ * T⁻¹) ∈ UG (cA σ) (incM F J₂) := by
    have := congrArg (fun X => incM F X) key
    simp only [incM, Matrix.map_mul, Matrix.transpose_map] at this
    refine Eq.trans ?_ this
    congr 1
  let u : UA σ J₂ := ⟨_, hU⟩
  have hu : inBasis σ T u = blk 1 (c • 1) 0 1 := by
    change incM F (T⁻¹).1 * incM F (T * w₀ * T⁻¹).1 * incM F T.1 = _
    rw [incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul,
      show T⁻¹ * (T * w₀ * T⁻¹) * T = w₀ by group]
    exact mp _
  have hN : u ∈ unipN σ J₂ := by
    obtain ⟨Z, -, hZ⟩ := h
    have hT' : incM F T.1 = blk 1 (incM F Z) 1 (-incM F Z) := by
      simp only [hZ, incM, blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]
    have hc : ∀ a b c d x y : Matrix (Fin n) (Fin n) (AE F E), blk a b c d * blockColumnMatrix x y = blockColumnMatrix (a * x + b * y) (c * x + d * y) :=
      fun a b c d x y => by
        rw [blk, blockColumnMatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows, blockColumnMatrix]
    have e1 : blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 = incM F T.1 * blockColumnMatrix 1 0 := by rw [hT']; erw [hc]; simp
    have e2 : mat u * incM F T.1 = incM F T.1 * blk 1 (c • 1) 0 1 := by
      rw [← hu, inBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]
    rw [mem_unipN_iff, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, e1]
    erw [← Matrix.mul_assoc, e2, Matrix.mul_assoc, hc]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
    rfl
  exact ⟨⟨⟨u, hN⟩, ⟨_, rfl⟩⟩, hu⟩

omit [NumberField E] in

theorem infinite_ratN (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (hn : 1 ≤ n) : Infinite (ratN σ J₂) := by
  choose u hu using exists_ratN hσ hl hJ h₂ h
  refine Infinite.of_injective u fun a b e => ?_
  have h1 := (hu a).symm.trans ((congrArg (fun x : ratN σ J₂ => inBasis σ T ((x : unipN σ J₂) : UA σ J₂)) e).trans (hu b))
  have h2 := congrFun (congrFun h1 (finSumFinEquiv (.inl ⟨0, hn⟩))) (finSumFinEquiv (.inr ⟨0, hn⟩))
  simp only [blk, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply,
    Matrix.one_apply_eq] at h2
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one] at h2
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AE F E) := inferInstanceAs (Nontrivial (AF F ⊗[F] E))
  haveI : CharZero (AE F E) := charZero_of_injective_algebraMap (algebraMap F (AE F E)).injective
  exact_mod_cast h2


omit [NumberField E] in

theorem intM_rank_zero {J₂ : Matrix (Fin (0 + 0)) (Fin (0 + 0)) E} {νN : Measure (unipN σ J₂)} (hν : IsNormN σ νN)
    (w g : UA σ J₂) (f : UA σ J₂ → ℂ) : intM νN w f g = f g := by
  haveI : Subsingleton (UA σ J₂) := ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => i.elim0))⟩
  obtain ⟨-, 𝓓, -, h2⟩ := hν
  have hu : νN Set.univ = 1 := by
    rcases Set.eq_empty_or_nonempty 𝓓 with e | e
    · rw [e, measure_empty] at h2; exact absurd h2 zero_ne_one
    · rw [← h2, Subsingleton.eq_univ_of_nonempty e]
  rw [intM, show (fun x : unipN σ J₂ => f (w * x * g)) = fun _ => f g from funext fun _ => congrArg f (Subsingleton.elim _ _),
    integral_const, Measure.real, hu, ENNReal.toReal_one, one_smul]

omit [NumberField E] in

theorem secSpace_bot_ne_bot {JV : Matrix (Fin m) (Fin m) E} {κ : Type} [Fintype κ]
    (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) : secSpace om ⊥ ≠ ⊥ := by
  obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  refine (Submodule.ne_bot_iff _).2 ⟨_, mem_secSpace.2 ⟨φ, h, (kFin_iff om ⊥ φ).2 ⟨ℂ ∙ φ, inferInstance, fun k hk => ?_⟩, rfl⟩,
    fun e => h0 ?_⟩
  · rw [Subgroup.mem_bot.1 hk, Prod.mk_one_one, map_one]; exact Submodule.mem_span_singleton_self φ
  · have := congrFun e 1
    rwa [Prod.mk_one_one, map_one] at this


end GlobalTheory.SWInt.Model

end
end
