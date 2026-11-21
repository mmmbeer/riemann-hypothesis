import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.DedekindZetaSeries.SummableDedekindZetaTerm

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open NumberField

section Statement

def ClassLogPeriodMean.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 16 = 7 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (∃ x : K, x ^ 2 = -(d : K)) →
      ∀ σ : K →+* ℂ,
        (classNumber K : ℝ)⁻¹ * ∑ A : ClassGroup (𝓞 K), classLogPeriod σ A =
          logPeriodConstant d

end Statement

section Ties

instance fact_sevenQ : Fact (∀ r : ℚ, r ^ 2 ≠ -7 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩

abbrev QuadraticFieldSqrtNegSeven : Type := QuadraticAlgebra ℚ (-7) 0

instance : Algebra.IsQuadraticExtension ℚ QuadraticFieldSqrtNegSeven :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

instance : NumberField QuadraticFieldSqrtNegSeven where





end Ties

end GroundTheory.Heights₂.Theta
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane

def realEisenstein (τ : ℍ) (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

theorem realEisenstein_nonneg (τ : ℍ) (s : ℝ) : 0 ≤ realEisenstein τ s := by
  refine tsum_nonneg fun p => ?_
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _)

end GroundTheory.Heights₂.Theta
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups

namespace EtaPeriodLatticeClass

theorem discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have h := congr_fun
    (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ) τ
  rw [SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  rw [← h, mul_comm (ModularForm.discriminant (γ • τ)), ← mul_assoc, ← zpow_add₀ hd]
  simp

theorem norm_eta_smul_pow_four (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4 = ‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4 := by
  have h := congr_arg norm (discriminant_smul γ τ)
  simp only [ModularForm.discriminant, norm_mul, norm_pow, norm_zpow] at h
  have h6 : (‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4) ^ 6 = (‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul]
    rw [show (4 : ℕ) * 6 = 24 from rfl, show (2 : ℕ) * 6 = 12 from rfl, h]
    norm_cast
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h6

theorem etaPeriod_smul (γ : SL(2, ℤ)) (τ : ℍ) : etaPeriod (γ • τ) = etaPeriod τ := by
  unfold etaPeriod
  rw [norm_eta_smul_pow_four, ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have : ‖denom γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  field_simp

theorem mem_latticeOf {τ z : ℂ} : z ∈ latticeOf τ ↔ ∃ m n : ℤ, z = m + n * τ := by
  unfold latticeOf
  rw [SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩

theorem coord_unique {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * (τ : ℂ) = m' + n' * (τ : ℂ)) : m = m' ∧ n = n' := by
  have him := congr_arg Complex.im h
  have hre := congr_arg Complex.re h
  simp at him hre
  have hn : n = n' := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hn
  refine ⟨?_, rfl⟩
  exact_mod_cast (by linarith : (m : ℝ) = m')

theorem exists_SL_smul_eq {τ τ' : ℍ} {μ : ℂ} (hμ : μ ≠ 0)
    (h1 : ∀ z ∈ latticeOf (τ : ℂ), μ * z ∈ latticeOf (τ' : ℂ))
    (h2 : ∀ w ∈ latticeOf (τ' : ℂ), μ⁻¹ * w ∈ latticeOf (τ : ℂ)) :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  obtain ⟨d, c, hdc⟩ := mem_latticeOf.mp (h2 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨b, a, hba⟩ := mem_latticeOf.mp (h2 τ' (mem_latticeOf.mpr ⟨0, 1, by simp⟩))

  obtain ⟨h, g, hhg⟩ := mem_latticeOf.mp (h1 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨f, e, hfe⟩ := mem_latticeOf.mp (h1 τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩))
  rw [mul_one] at hdc hhg

  have k1 : ((d * h + c * f : ℤ) : ℂ) + ((d * g + c * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination hinv - μ * hdc - (d : ℂ) * hhg - (c : ℂ) * hfe
  have k2 : ((b * h + a * f : ℤ) : ℂ) + ((b * g + a * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination (τ' : ℂ) * hinv - μ * hba - (b : ℂ) * hhg - (a : ℂ) * hfe
  obtain ⟨E4, E3⟩ := coord_unique k1
  obtain ⟨E2, E1⟩ := coord_unique k2
  have hdet1 : (a * d - b * c) * (e * h - f * g) = 1 := by
    linear_combination (c * f + d * h) * E1 + E4 - (c * e + d * g) * E2

  have hw : (c : ℂ) * τ + d ≠ 0 := by
    rw [add_comm, ← hdc]; exact inv_ne_zero hμ
  have hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d) := by
    rw [eq_div_iff hw, add_comm ((c : ℂ) * τ), ← hdc, add_comm ((a : ℂ) * τ), ← hba]
    field_simp

  have hdetpos : 0 < a * d - b * c := by
    have him := congr_arg Complex.im hτ'
    rw [Complex.div_im] at him
    have hN : 0 < Complex.normSq ((c : ℂ) * τ + d) := Complex.normSq_pos.mpr hw
    have key : (τ' : ℂ).im * Complex.normSq ((c : ℂ) * τ + d) = ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [him, sub_mul, div_mul_cancel₀ _ hN.ne', div_mul_cancel₀ _ hN.ne']
      simp
      ring
    have : (0 : ℝ) < ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [← key]; exact mul_pos τ'.im_pos hN
    have := (pos_of_mul_pos_left this τ.im_pos.le)
    exact_mod_cast this
  have hdet : a * d - b * c = 1 :=
    Int.eq_one_of_mul_eq_one_right hdetpos.le hdet1
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨γ, UpperHalfPlane.ext ?_⟩
  rw [coe_specialLinearGroup_apply, hτ']
  simp [γ]

theorem of_EtaPeriodModularInvariant (hinv : EtaPeriodModularInvariant.Statement) :
    EtaPeriodLatticeClass.Statement := by
  rintro Λ τ τ' ⟨c, hc, hΛ⟩ ⟨c', hc', hΛ'⟩
  have h1 : ∀ z ∈ latticeOf (τ : ℂ), c' / c * z ∈ latticeOf (τ' : ℂ) := by
    intro z hz
    rw [← hΛ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [← hΛ']
    exact ⟨x, hx, by field_simp⟩
  have h2 : ∀ w ∈ latticeOf (τ' : ℂ), (c' / c)⁻¹ * w ∈ latticeOf (τ : ℂ) := by
    intro w hw
    rw [← hΛ'] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [← hΛ]
    exact ⟨x, hx, by field_simp⟩
  obtain ⟨γ, hγ⟩ := exists_SL_smul_eq (div_ne_zero hc' hc) h1 h2
  rw [← hγ, hinv]

theorem proof : EtaPeriodLatticeClass.Statement :=
  of_EtaPeriodModularInvariant etaPeriod_smul

end EtaPeriodLatticeClass

example : etaPeriod (ModularGroup.T • UpperHalfPlane.I) = etaPeriod UpperHalfPlane.I :=
  EtaPeriodLatticeClass.etaPeriod_smul _ _

end GroundTheory.Heights₂.Theta
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace projectiveLineClassData

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate

variable {K : Type} [Field K] [NumberField K]

section Embeddings

omit [NumberField K] in

theorem conjugate_ne (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) : conjugate σ ≠ σ := by
  obtain ⟨x, hx⟩ := hσ
  intro h
  apply hx
  have h1 := congrArg (fun φ : K →+* ℂ => φ x) h
  simp only [conjugate_coe_eq] at h1
  exact Complex.conj_eq_iff_im.mp h1

theorem eq_or_eq_conjugate (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (φ : K →+* ℂ) : φ = σ ∨ φ = conjugate σ := by
  classical
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [NumberField.Embeddings.card K ℂ, hK]
  have h2 : ({σ, conjugate σ} : Finset (K →+* ℂ)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (conjugate_ne σ hσ).symm, hcard]
  have : φ ∈ ({σ, conjugate σ} : Finset (K →+* ℂ)) := h2 ▸ Finset.mem_univ φ
  simpa using this

theorem eq_mk (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (w : InfinitePlace K) : w = mk σ := by
  rcases eq_or_eq_conjugate hK σ hσ w.embedding with h | h
  · rw [← mk_embedding w, h]
  · rw [← mk_embedding w, h, mk_conjugate_eq]

theorem place_apply (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (w : InfinitePlace K) (x : K) : w x = ‖σ x‖ := by
  rw [eq_mk hK σ hσ w, apply]

omit [NumberField K] in

theorem isComplex_mk (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) : IsComplex (mk σ) :=
  isComplex_mk_iff.mpr fun h => conjugate_ne σ hσ (ComplexEmbedding.isReal_iff.mp h)

theorem abs_norm_eq (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (x : K) : |((Algebra.norm ℚ x : ℚ) : ℝ)| = ‖σ x‖ ^ 2 := by
  classical
  have h := prod_eq_abs_norm x
  have hall : ∀ w : InfinitePlace K, w = mk σ := eq_mk hK σ hσ
  rw [Finset.prod_eq_single_of_mem (mk σ) (Finset.mem_univ _)
    (fun w _ hw => absurd (hall w) hw)] at h
  have hm : mult (mk σ) = 2 := by
    rw [mult, if_neg (not_isReal_iff_isComplex.mpr (isComplex_mk σ hσ))]
  rw [hm, apply] at h
  rw [h, Rat.cast_abs]

theorem mem_torsion_of (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (u : (𝓞 K)ˣ) : u ∈ Units.torsion K := by
  rw [Units.mem_torsion]
  intro w
  rw [place_apply hK σ hσ]
  have h := abs_norm_eq hK σ hσ (u : K)
  rw [← Rat.cast_abs, Units.norm K u, Rat.cast_one] at h
  have h0 : 0 ≤ ‖σ (u : K)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖σ (u : K)‖ - 1), sq_nonneg (‖σ (u : K)‖ + 1)]

theorem natCard_units (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) :
    Nat.card (𝓞 K)ˣ = Units.torsionOrder K := by
  have htop : Units.torsion K = ⊤ := eq_top_iff.mpr fun u _ => mem_torsion_of hK σ hσ u
  rw [Units.torsionOrder, htop, Subgroup.card_top]

end Embeddings

section Covolume

open EtaPeriodLatticeClass

def embPair (σ : K →+* ℂ) : Fin 2 → (K →ₐ[ℚ] ℂ) :=
  ![σ.toRatAlgHom, (conjugate σ).toRatAlgHom]

theorem embPair_bijective (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) : Function.Bijective (embPair σ) := by
  rw [Fintype.bijective_iff_injective_and_card, AlgHom.card, hK, Fintype.card_fin]
  have hne : σ.toRatAlgHom ≠ (conjugate σ).toRatAlgHom := fun h =>
    conjugate_ne σ hσ (RingHom.ext fun x => by
      have := DFunLike.congr_fun h x
      simpa [RingHom.toRatAlgHom_apply] using this.symm)
  refine ⟨fun i j hij => ?_, rfl⟩
  match i, j with
  | 0, 0 => rfl
  | 0, 1 => exact absurd hij hne
  | 1, 0 => exact absurd hij.symm hne
  | 1, 1 => rfl

def embEquiv (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) :
    Fin 2 ≃ (K →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective _ (embPair_bijective hK σ hσ)

theorem normSq_mul_det (c a b τ : ℂ) (ha : c * a = 1) (hb : c * b = τ) :
    ((‖c‖ ^ 2 : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * τ.im * Complex.I) := by
  have hcb : (starRingEnd ℂ) c * (starRingEnd ℂ) b = (starRingEnd ℂ) τ := by
    rw [← map_mul, hb]
  have hca : (starRingEnd ℂ) c * (starRingEnd ℂ) a = 1 := by
    rw [← map_mul, ha, map_one]
  have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * (starRingEnd ℂ) c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsub : τ - (starRingEnd ℂ) τ = ((2 * τ.im : ℝ) : ℂ) * Complex.I := Complex.sub_conj τ
  rw [hn]
  push_cast at hsub
  linear_combination ((starRingEnd ℂ) c * (starRingEnd ℂ) b) * ha + hcb - (c * b) * hca - hb - hsub

end Covolume

section Covolume2

open EtaPeriodLatticeClass

theorem discr_neg_and_absNorm_mul (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : FractionalIdeal (𝓞 K)⁰ K) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' (I : Set K)) = latticeOf (τ : ℂ)) :
    (discr K : ℝ) < 0 ∧
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2 = 2 * τ.im / Real.sqrt |(discr K : ℝ)| := by
  classical
  have hmem : ∀ x : K, x ∈ I → c * σ x ∈ latticeOf (τ : ℂ) := fun x hx => by
    rw [← himg]; exact ⟨σ x, ⟨x, hx, rfl⟩, rfl⟩
  have hpre : ∀ z ∈ latticeOf (τ : ℂ), ∃ x ∈ I, c * σ x = z := by
    intro z hz
    rw [← himg] at hz
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  obtain ⟨α, hαI, hα⟩ := hpre 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩)
  obtain ⟨β, hβI, hβ⟩ := hpre τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩)
  have hcoord : ∀ x ∈ I, ∃ m n : ℤ, x = m * α + n * β := by
    intro x hx
    obtain ⟨m, n, hmn⟩ := mem_latticeOf.mp (hmem x hx)
    refine ⟨m, n, σ.injective (mul_left_cancel₀ hc ?_)⟩
    rw [hmn, map_add, map_mul, map_mul, map_intCast, map_intCast]
    linear_combination (-(m : ℂ)) * hα - (n : ℂ) * hβ
  have hind : ∀ m n : ℤ, (m : K) * α + n * β = 0 → m = 0 ∧ n = 0 := by
    intro m n h
    have h2 := congrArg (fun x => c * σ x) h
    simp only [map_add, map_mul, map_intCast, map_zero, mul_zero] at h2
    have h3 : (m : ℂ) + n * (τ : ℂ) = ((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ : ℂ) := by
      push_cast
      linear_combination h2 - (m : ℂ) * hα - (n : ℂ) * hβ
    exact coord_unique h3
  let v : Fin 2 → (I : Submodule (𝓞 K) K) := ![⟨α, hαI⟩, ⟨β, hβI⟩]
  have hli : LinearIndependent ℤ v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply hind s t
    have := congrArg (fun y : (I : Submodule (𝓞 K) K) => (y : K)) hst
    simpa [zsmul_eq_mul] using this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨m, n, hxmn⟩ := hcoord x hx
    have h0 : v 0 ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨0, rfl⟩
    have h1 : v 1 ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨1, rfl⟩
    have := Submodule.add_mem _ (Submodule.smul_mem _ m h0) (Submodule.smul_mem _ n h1)
    convert this using 1
    ext
    simp [v, zsmul_eq_mul, hxmn]
  let bJ : Module.Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K) := Module.Basis.mk hli hsp
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hK]
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) :=
    (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq hcard)
  have habs := FractionalIdeal.abs_det_basis_change b I bJ
  set b₀ := b.localizationLocalization ℚ ℤ⁰ K
  set w : Fin 2 → K := (↑) ∘ bJ with hw
  have hw0 : w 0 = α := by simp [hw, bJ, v]
  have hw1 : w 1 = β := by simp [hw, bJ, v]
  have hdisc := Algebra.discr_of_matrix_vecMul (⇑b₀) (b₀.toMatrix w)
  rw [Module.Basis.toMatrix_map_vecMul, ← Module.Basis.det_apply, Algebra.discr_localizationLocalization ℤ ℤ⁰ K b,
    NumberField.discr_eq_discr K b] at hdisc
  have hemb := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ w (embEquiv hK σ hσ)
  rw [Matrix.det_fin_two] at hemb
  simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Algebra.embeddingsMatrix_apply, embEquiv,
    Equiv.ofBijective_apply, embPair, Matrix.cons_val_zero, Matrix.cons_val_one,
    RingHom.toRatAlgHom_apply, hw0, hw1, conjugate_coe_eq] at hemb
  have hX := normSq_mul_det c (σ α) (σ β) τ hα hβ
  rw [UpperHalfPlane.coe_im] at hX
  have hq : Algebra.discr ℚ w = (FractionalIdeal.absNorm I) ^ 2 * (discr K : ℚ) := by
    rw [hdisc, ← sq_abs, habs]
    simp
  have hC : ((‖c‖ ^ 2 : ℝ) : ℂ) ^ 2 *
      ((((FractionalIdeal.absNorm I : ℚ) : ℝ) : ℂ) ^ 2 * (((discr K : ℤ) : ℝ) : ℂ)) =
        ((-(4 * τ.im ^ 2) : ℝ) : ℂ) := by
    have h1 : ((‖c‖ ^ 2 : ℝ) : ℂ) ^ 2 *
        (σ α * (starRingEnd ℂ) (σ β) - (starRingEnd ℂ) (σ α) * σ β) ^ 2 =
          ((-(4 * τ.im ^ 2) : ℝ) : ℂ) := by
      rw [← mul_pow, hX]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [← h1, ← hemb, hq]
    simp only [map_mul, map_pow, eq_ratCast, Rat.cast_intCast]
    push_cast
    ring
  have hR : (‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) =
      -(4 * τ.im ^ 2) := by
    have := Complex.ofReal_injective (by push_cast at hC ⊢; exact hC :
      (((‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) : ℝ) : ℂ) =
        ((-(4 * τ.im ^ 2) : ℝ) : ℂ))
    exact this
  have hy := τ.im_pos
  have hN : 0 ≤ ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg I
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hD : (discr K : ℝ) < 0 := by
    by_contra h
    replace h := not_lt.mp h
    have : 0 ≤ (‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) := by
      positivity
    nlinarith
  refine ⟨hD, ?_⟩
  have hsq : Real.sqrt |(discr K : ℝ)| ^ 2 = -(discr K : ℝ) := by
    rw [Real.sq_sqrt (abs_nonneg _), abs_of_neg hD]
  have hspos : 0 < Real.sqrt |(discr K : ℝ)| := Real.sqrt_pos.mpr (abs_pos.mpr hD.ne)
  have key : Real.sqrt |(discr K : ℝ)| * (((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2) =
      2 * τ.im := by
    have h1 : (Real.sqrt |(discr K : ℝ)| * (((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2)) ^ 2 =
        (2 * τ.im) ^ 2 := by
      rw [mul_pow, hsq]
      linear_combination (-1 : ℝ) * hR
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  rw [eq_div_iff hspos.ne']
  linarith [key]

end Covolume2

end projectiveLineClassData

end GroundTheory.Heights₂.Theta
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace projectiveLineClassData

open NumberField UpperHalfPlane
open scoped nonZeroDivisors

section Series

def eisTerm (τ : ℍ) (s : ℝ) (p : ℤ × ℤ) : ℝ :=
  if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

theorem realEisenstein_eq_tsum (τ : ℍ) (s : ℝ) : realEisenstein τ s = ∑' p, eisTerm τ s p := rfl

theorem eisTerm_nonneg (τ : ℍ) (s : ℝ) (p : ℤ × ℤ) : 0 ≤ eisTerm τ s p := by
  unfold eisTerm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem summable_eisTerm (τ : ℍ) {s : ℝ} (hs : 1 < s) : Summable (eisTerm τ s) := by
  have hk : 2 < 2 * s := by linarith
  have hsum := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
    (τ.im ^ s * EisensteinSeries.r τ ^ (-(2 * s)))
  rw [← (finTwoArrowEquiv ℤ).summable_iff]
  refine Summable.of_nonneg_of_le (fun x => eisTerm_nonneg τ s _) (fun x => ?_) hsum
  have hr := EisensteinSeries.r_pos τ
  simp only [Function.comp_apply, finTwoArrowEquiv_apply, eisTerm]
  split_ifs with hx
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg hr.le _))
      (Real.rpow_nonneg (norm_nonneg _) _)
  · have hb := EisensteinSeries.summand_bound τ (by linarith : (0 : ℝ) ≤ 2 * s) x
    rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _), mul_assoc]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg τ.im_pos.le _)

end Series

section IdealSum

variable (K : Type) [Field K] [NumberField K]

theorem ofReal_dedekindZetaReal {s : ℝ} (hs : 1 < s) :
    ENNReal.ofReal (GroundTheory.Global.dedekindZetaReal K s) =
      ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) := by
  classical
  rw [GroundTheory.Global.dedekindZetaReal, ENNReal.ofReal_tsum_of_nonneg
    (GroundTheory.Global.dedekindZetaTerm_nonneg K s) (ZetaSevenHalvesBounds.summable_dedekindZetaTerm K hs),
    ← ENNReal.tsum_fiberwise (fun I : Ideal (𝓞 K) => ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)))
      Ideal.absNorm]
  refine tsum_congr fun n => ?_
  have hfin : (Ideal.absNorm ⁻¹' {n} : Set (Ideal (𝓞 K))).Finite :=
    Ideal.finite_setOfPred_absNorm_eq n
  have := hfin.fintype
  rw [tsum_congr (fun I : (Ideal.absNorm ⁻¹' {n} : Set (Ideal (𝓞 K))) => by
    rw [show Ideal.absNorm (I : Ideal (𝓞 K)) = n from I.2]), tsum_fintype, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, GroundTheory.Global.dedekindZetaTerm,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← Nat.card_eq_fintype_card]
  rfl

theorem tsum_ideal_eq_sum_class {s : ℝ} (hs : 0 < s) :
    ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) =
      ∑ B : ClassGroup (𝓞 K), ∑' I : (ClassGroup.mk0 ⁻¹' {B} : Set (Ideal (𝓞 K))⁰),
        ENNReal.ofReal ((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
  classical
  have hsupp : Function.support (fun I : Ideal (𝓞 K) => ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)))
      ⊆ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K))) := by
    intro I hI
    rw [SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    apply hI
    simp [Ideal.absNorm_bot, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  change ∑' x : (Ideal (𝓞 K))⁰, ENNReal.ofReal ((Ideal.absNorm (x : Ideal (𝓞 K)) : ℝ) ^ (-s)) = _
  rw [← ENNReal.tsum_fiberwise _ (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K)), tsum_fintype]

end IdealSum

section ClassSum

variable {K : Type} [Field K] [NumberField K]

open FractionalIdeal EtaPeriodLatticeClass

local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem spanSingleton_mul_inv_le_one (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K}
    (hx : x ∈ (↑ᶠ J)) : spanSingleton (𝓞 K)⁰ x * (↑ᶠ J⁻¹) ≤ 1 := by
  rw [spanSingleton_mul_le_iff]
  intro z hz
  have h := mul_mem_mul hx hz
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one] at h

def idealOf (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) : Ideal (𝓞 K) :=
  (le_one_iff_exists_coeIdeal.mp (spanSingleton_mul_inv_le_one J hx)).choose

theorem coe_idealOf (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) :
    ((idealOf J hx : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ x * (↑ᶠ J⁻¹) :=
  (le_one_iff_exists_coeIdeal.mp (spanSingleton_mul_inv_le_one J hx)).choose_spec

theorem idealOf_mem (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) (hx0 : x ≠ 0) :
    idealOf J hx ∈ (Ideal (𝓞 K))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have h2 := coe_idealOf J hx
  rw [h, Ideal.zero_eq_bot, coeIdeal_bot] at h2
  exact mul_ne_zero (spanSingleton_ne_zero_iff.mpr hx0) (Units.ne_zero _) h2.symm

theorem class_idealOf_eq_inv_class (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) (hx0 : x ≠ 0) :
    ClassGroup.mk0 ⟨idealOf J hx, idealOf_mem J hx hx0⟩ = (ClassGroup.mk K J)⁻¹ := by
  rw [← ClassGroup.mk_mk0 K]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, ClassGroup.mk_eq_one_iff, Units.val_mul, FractionalIdeal.coe_mk0, coe_idealOf,
    mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one, coe_spanSingleton]
  exact ⟨⟨x, rfl⟩⟩

abbrev Nz (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type := {x : K // x ∈ (↑ᶠ J) ∧ x ≠ 0}

abbrev InvClassIdeals (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type :=
  ((ClassGroup.mk0 ⁻¹' {(ClassGroup.mk K J)⁻¹} : Set (Ideal (𝓞 K))⁰))

def psi (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) : InvClassIdeals J :=
  ⟨⟨idealOf J x.2.1, idealOf_mem J x.2.1 x.2.2⟩, class_idealOf_eq_inv_class J x.2.1 x.2.2⟩

theorem coe_psi (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) :
    (((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (x : K) * (↑ᶠ J⁻¹) :=
  coe_idealOf J x.2.1

theorem psi_eq_iff (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : Nz J) :
    psi J x = psi J y ↔ spanSingleton (𝓞 K)⁰ (x : K) = spanSingleton (𝓞 K)⁰ (y : K) := by
  constructor
  · intro h
    have h2 := congrArg (fun t : InvClassIdeals J =>
      (((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) h
    simp only [coe_psi] at h2
    exact mul_right_cancel₀ (Units.ne_zero _) h2
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    apply coeIdeal_injective (K := K)
    change (((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      (((psi J y : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [coe_psi, coe_psi, h]

theorem psi_surjective (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (psi J) := by
  rintro ⟨⟨I, hI⟩, hcl⟩
  have hcl' : ClassGroup.mk0 ⟨I, hI⟩ = (ClassGroup.mk K J)⁻¹ := hcl
  have h1 : ClassGroup.mk K (FractionalIdeal.mk0 K ⟨I, hI⟩ * J) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hcl', inv_mul_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  set P := FractionalIdeal.mk0 K ⟨I, hI⟩ * J with hP
  have hPval : (P : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) := by
    rw [hP, Units.val_mul, FractionalIdeal.coe_mk0]
  have hgen := FractionalIdeal.eq_spanSingleton_of_principal (P : FractionalIdeal (𝓞 K)⁰ K)
  set x := Submodule.IsPrincipal.generator ((P : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  have hxP : x ∈ (P : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hgen]; exact mem_spanSingleton_self _ _
  have hxJ : x ∈ (↑ᶠ J) := by
    rw [hPval] at hxP
    have hle : (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) ≤ (↑ᶠ J) := by
      calc (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) ≤ 1 * (↑ᶠ J) := by
            rw [FractionalIdeal.mul_le]
            intro i hi j hj
            exact mul_mem_mul (coeIdeal_le_one hi) hj
        _ = (↑ᶠ J) := one_mul _
    exact hle hxP
  have hx0 : x ≠ 0 := by
    intro h0
    have : (P : FractionalIdeal (𝓞 K)⁰ K) = 0 := by rw [hgen, h0, spanSingleton_zero]
    exact Units.ne_zero P this
  refine ⟨⟨x, hxJ, hx0⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply coeIdeal_injective (K := K)
  change (((psi J ⟨x, hxJ, hx0⟩ : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [coe_psi, ← hgen, hPval, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end ClassSum

section Fibres

variable {K : Type} [Field K] [NumberField K]

open FractionalIdeal

local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

def unitMul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) (u : (𝓞 K)ˣ) : Nz J :=
  ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * x₀, by
    have h := Submodule.smul_mem ((↑ᶠ J) : Submodule (𝓞 K) K) (u : 𝓞 K) (mem_coe.mpr x₀.2.1)
    rw [Algebra.smul_def] at h
    exact mem_coe.mp h,
   mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr u.ne_zero) x₀.2.2⟩

theorem psi_unitMul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) (u : (𝓞 K)ˣ) :
    psi J (unitMul J x₀ u) = psi J x₀ := by
  rw [psi_eq_iff, eq_comm, spanSingleton_eq_spanSingleton]
  exact ⟨u, by rw [Units.smul_def, Algebra.smul_def]; rfl⟩

def fiberEquiv (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) :
    (𝓞 K)ˣ ≃ (psi J ⁻¹' {psi J x₀}) :=
  Equiv.ofBijective (fun u => ⟨unitMul J x₀ u, psi_unitMul J x₀ u⟩) (by
    constructor
    · intro u v h
      have h2 := congrArg (fun y : (psi J ⁻¹' {psi J x₀}) => ((y : Nz J) : K)) h
      simp only [unitMul] at h2
      have h3 := mul_right_cancel₀ x₀.2.2 h2
      exact Units.ext (IsFractionRing.injective (𝓞 K) K h3)
    · rintro ⟨y, hy⟩
      have hy' : psi J y = psi J x₀ := hy
      rw [psi_eq_iff, eq_comm, spanSingleton_eq_spanSingleton] at hy'
      obtain ⟨z, hz⟩ := hy'
      refine ⟨z, Subtype.ext (Subtype.ext ?_)⟩
      rw [← hz, Units.smul_def, Algebra.smul_def]
      rfl)

theorem tsum_psi (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : InvClassIdeals J → ENNReal) :
    ∑' x : Nz J, g (psi J x) = (Units.torsionOrder K : ENNReal) * ∑' t, g t := by
  classical
  have hcard := natCard_units hK σ hσ
  have hfin : Finite (𝓞 K)ˣ :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Units.torsionOrder_ne_zero K)
  have := Fintype.ofFinite (𝓞 K)ˣ
  rw [← ENNReal.tsum_fiberwise (fun x => g (psi J x)) (psi J), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  obtain ⟨x₀, rfl⟩ := psi_surjective J t
  rw [tsum_congr (fun y : (psi J ⁻¹' {psi J x₀}) => by
      rw [show psi J (y : Nz J) = psi J x₀ from y.2]),
    ← (fiberEquiv J x₀).tsum_eq, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, hcard]

end Fibres

section Lattice

variable {K : Type} [Field K] [NumberField K]

open FractionalIdeal EtaPeriodLatticeClass

local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem absNorm_psi (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) :
    (Ideal.absNorm ((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) =
      ‖σ (x : K)‖ ^ 2 / ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) := by
  have h1 := congrArg FractionalIdeal.absNorm (coe_psi J x)
  rw [coeIdeal_absNorm, map_mul, absNorm_span_singleton] at h1
  have hinv : FractionalIdeal.absNorm (↑ᶠ J⁻¹) = (FractionalIdeal.absNorm (↑ᶠ J))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rw [hinv] at h1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs, Rat.cast_inv] at h2
  rw [h2, abs_norm_eq hK σ hσ, div_eq_mul_inv]

theorem rpow_identity {n q y : ℝ} (hn : 0 < n) (hq : 0 < q) (hy : 0 < y) (s : ℝ) :
    (n ^ 2 * q / (2 * y)) ^ (-s) = (2 / q) ^ s * (y ^ s / n ^ (2 * s)) := by
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  have h : (n ^ 2 * q / (2 * y))⁻¹ = (2 / q) * (y / n ^ 2) := by
    rw [inv_div]
    field_simp
  rw [h, Real.mul_rpow (by positivity) (by positivity), Real.div_rpow hy.le (by positivity),
    show (2 : ℝ) * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul hn.le]

abbrev NzPair : Type := {p : ℤ × ℤ // p ≠ 0}

abbrev NzLattice (τ : ℍ) : Type := {z : ℂ // z ∈ latticeOf (τ : ℂ) ∧ z ≠ 0}

def pairToLattice (τ : ℍ) (p : NzPair) : NzLattice τ :=
  ⟨p.1.1 * τ + p.1.2, mem_latticeOf.mpr ⟨p.1.2, p.1.1, by ring⟩, by
    intro h
    apply p.2
    have := coord_unique (τ := τ) (m := p.1.2) (n := p.1.1) (m' := 0) (n' := 0)
      (by push_cast; linear_combination h)
    exact Prod.ext this.2 this.1⟩

theorem pairToLattice_bijective (τ : ℍ) : Function.Bijective (pairToLattice τ) := by
  constructor
  · intro p r h
    have h2 := congrArg (fun z : NzLattice τ => (z : ℂ)) h
    simp only [pairToLattice] at h2
    have := coord_unique (τ := τ) (m := p.1.2) (n := p.1.1) (m' := r.1.2) (n' := r.1.1)
      (by linear_combination h2)
    exact Subtype.ext (Prod.ext this.2 this.1)
  · rintro ⟨z, hz, hz0⟩
    obtain ⟨m, n, rfl⟩ := mem_latticeOf.mp hz
    refine ⟨⟨(n, m), fun h => hz0 ?_⟩, Subtype.ext ?_⟩
    · rw [Prod.mk_eq_zero] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · simp only [pairToLattice]
      ring

def eltToLattice (σ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) (x : Nz J) :
    NzLattice τ :=
  ⟨c * σ x, by rw [← himg]; exact ⟨σ x, ⟨x, x.2.1, rfl⟩, rfl⟩,
    mul_ne_zero hc ((map_ne_zero σ).mpr x.2.2)⟩

theorem eltToLattice_bijective (σ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ)
    (hc : c ≠ 0) (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) :
    Function.Bijective (eltToLattice σ J τ c hc himg) := by
  constructor
  · intro x y h
    have h2 := congrArg (fun z : NzLattice τ => (z : ℂ)) h
    simp only [eltToLattice] at h2
    exact Subtype.ext (σ.injective (mul_left_cancel₀ hc h2))
  · rintro ⟨z, hz, hz0⟩
    rw [← himg] at hz
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    refine ⟨⟨x, hx, fun h => hz0 (by simp [h])⟩, rfl⟩

theorem class_sum (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) {s : ℝ}
    (hs : 1 < s) :
    (Units.torsionOrder K : ENNReal) * ∑' t : InvClassIdeals J,
        ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
      ENNReal.ofReal ((2 / Real.sqrt |(discr K : ℝ)|) ^ s * realEisenstein τ s) := by
  rw [← tsum_psi hK σ hσ J (fun t => ENNReal.ofReal
    ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)))]
  obtain ⟨hD, hcov⟩ := discr_neg_and_absNorm_mul hK σ hσ (↑ᶠ J) τ c hc himg
  set q := Real.sqrt |(discr K : ℝ)| with hqdef
  have hq : 0 < q := Real.sqrt_pos.mpr (abs_pos.mpr hD.ne)
  have hy := τ.im_pos
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set F : NzLattice τ → ENNReal :=
    fun z => ENNReal.ofReal ((2 / q) ^ s * (τ.im ^ s / ‖(z : ℂ)‖ ^ (2 * s))) with hF
  have hterm : ∀ x : Nz J, ENNReal.ofReal
      ((Ideal.absNorm ((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
        F (eltToLattice σ J τ c hc himg x) := by
    intro x
    rw [absNorm_psi hK σ hσ J x, hF]
    congr 1
    have hx0 : σ (x : K) ≠ 0 := (map_ne_zero σ).mpr x.2.2
    have hN : ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) = 2 * τ.im / (q * ‖c‖ ^ 2) := by
      rw [eq_div_iff (by positivity)]
      rw [eq_div_iff hq.ne'] at hcov
      linear_combination hcov
    have h3 : ‖σ (x : K)‖ ^ 2 / ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) =
        ‖c * σ (x : K)‖ ^ 2 * q / (2 * τ.im) := by
      rw [hN, norm_mul]
      field_simp
    rw [h3]
    exact rpow_identity (norm_pos_iff.mpr (mul_ne_zero hc hx0)) hq hy s
  rw [tsum_congr hterm]
  have e1 := (Equiv.ofBijective _ (eltToLattice_bijective σ J τ c hc himg)).tsum_eq F
  simp only [Equiv.ofBijective_apply] at e1
  rw [e1]
  have e2 := (Equiv.ofBijective _ (pairToLattice_bijective τ)).tsum_eq F
  simp only [Equiv.ofBijective_apply] at e2
  rw [← e2]
  have hG : ∀ p : NzPair, F (pairToLattice τ p) =
      ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p.1) := by
    intro p
    simp only [hF, pairToLattice, eisTerm, if_neg p.2]
  rw [tsum_congr hG]
  have hsupp : Function.support (fun p : ℤ × ℤ => ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p)) ⊆
      {p | p ≠ 0} := by
    intro p hp h0
    apply hp
    have h0' : p = 0 := by simpa using h0
    simp [h0', eisTerm]
  have e3 := tsum_subtype_eq_of_support_subset hsupp
  change ∑' p : {p : ℤ × ℤ // p ≠ 0}, _ = _
  rw [show (∑' p : {p : ℤ × ℤ // p ≠ 0}, ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p.1)) =
    ∑' p : ({p | p ≠ 0} : Set (ℤ × ℤ)), ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p) from rfl, e3,
    ← ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg (by positivity) (eisTerm_nonneg τ s p))
      ((summable_eisTerm τ hs).mul_left _), tsum_mul_left, realEisenstein_eq_tsum]

end Lattice

section Main

end Main

end projectiveLineClassData

end GroundTheory.Heights₂.Theta
end
end
