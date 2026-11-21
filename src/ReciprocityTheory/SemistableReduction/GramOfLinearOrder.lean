import Mathlib
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

section
namespace ReciprocityTheory.MultiplicativeHeights

open Finset InnerProductSpace

private theorem exists_eq_gramSchmidt_add_sum_Iio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n : ℕ) (v : Fin n → E) :
    ∃ c : Fin n → Fin n → ℂ,
      ∀ j, v j = gramSchmidt ℂ v j + ∑ i ∈ Iio j, c j i • gramSchmidt ℂ v i :=
  ⟨_, fun j => gramSchmidt_def'' (𝕜 := ℂ) v j⟩

theorem det_gram_eq_prod_gramSchmidt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) :
    (Matrix.gram ℂ v).det = ∏ k, (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then 1 else if i < j then c j i else 0
  have hA : ∀ j, v j = ∑ i, A i j • gramSchmidt ℂ v i := by
    intro j
    have h1 : ∀ i, A i j • gramSchmidt ℂ v i =
        (if i = j then gramSchmidt ℂ v i else 0) +
          (if i < j then c j i • gramSchmidt ℂ v i else 0) := by
      intro i
      by_cases h : i = j
      · subst h; simp [A]
      · by_cases h' : i < j
        · simp [A, h, h']
        · simp [A, h, h']
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, hc j]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp
  have horth : ∀ k l, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v l⟫_ℂ =
      if k = l then (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [if_neg h, gramSchmidt_orthogonal (𝕜 := ℂ) v h]
  have hG : Matrix.gram ℂ v =
      Matrix.conjTranspose A * Matrix.diagonal (fun k => (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ)) * A := by
    ext i j
    show ⟪v i, v j⟫_ℂ = _
    rw [hA i, hA j]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth, mul_ite, mul_zero,
      Finset.mem_univ, if_true, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
      Matrix.conjTranspose_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hAtri : A.BlockTriangular id := by
    intro i j h
    simp only [id] at h
    simp [A, h.ne', not_lt.mpr h.le]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAtri]
    simp [A]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetA, Matrix.det_diagonal]
  simp

theorem prod_le_re_det_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) (δ : Fin n → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (h : ∀ k, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k), δ k ≤ ‖v k - x‖ ^ 2) :
    ∏ k, δ k ≤ (Matrix.gram ℂ v).det.re := by
  classical
  rw [det_gram_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]
  refine Finset.prod_le_prod (fun k _ => hδ k) (fun k _ => ?_)
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  have hmem : ∑ i ∈ Iio k, c k i • gramSchmidt ℂ v i ∈ Submodule.span ℂ (v '' Set.Iio k) := by
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) v k]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  have h1 := h k _ hmem
  rwa [← eq_sub_of_add_eq (hc k).symm] at h1

end ReciprocityTheory.MultiplicativeHeights
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open Finset

theorem exp_torus_mean_le_l2_of_lex {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (hF : F ≠ 0) (s : ι →₀ ℕ)
    (Q : MvPolynomial ι ℂ) (hQ : ∀ t ∈ Q.support, toLex s < toLex t) :
    Real.exp (torusMean F) ≤ polyL2 (F * (MvPolynomial.monomial s 1 - Q)) := by
  classical
  set P := MvPolynomial.monomial s (1 : ℂ) - Q with hPdef
  have hsQ : s ∉ Q.support := fun h => lt_irrefl _ (hQ s h)
  have hQs : Q.coeff s = 0 := MvPolynomial.notMem_support_iff.mp hsQ
  have hPs : P.coeff s = 1 := by
    rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hQs, sub_zero]
  have hP0 : P ≠ 0 := fun h => by rw [h, MvPolynomial.coeff_zero] at hPs; exact zero_ne_one hPs
  have hsupp : s ∈ P.support := by rw [MvPolynomial.mem_support_iff, hPs]; exact one_ne_zero
  have hlex : Real.log ‖P.coeff s‖ ≤ torusMean P := by
    apply hLex ι P s hsupp
    intro t ht hts
    have htQ : t ∈ Q.support := by
      by_contra h
      have h0 : P.coeff t = 0 := by
        rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hts),
          MvPolynomial.notMem_support_iff.mp h, sub_zero]
      exact (MvPolynomial.mem_support_iff.mp ht) h0
    obtain ⟨i, h1, h2⟩ := hQ t htQ
    exact ⟨i, h1, h2⟩
  rw [hPs, norm_one, Real.log_one] at hlex
  have hFP : F * P ≠ 0 := mul_ne_zero hF hP0
  have hmul := (hBasic ι).2.1 F P hF hP0
  have hL := (hL2 ι (F * P)).1 hFP
  have hpos : 0 < polyL2 (F * P) := by
    unfold polyL2
    apply Real.sqrt_pos.mpr
    obtain ⟨t, hne⟩ := MvPolynomial.ne_zero_iff.mp hFP
    have ht : t ∈ (F * P).support := MvPolynomial.mem_support_iff.mpr hne
    calc (0 : ℝ) < ‖(F * P).coeff t‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
      _ ≤ _ := Finset.single_le_sum (f := fun s => ‖(F * P).coeff s‖ ^ 2)
          (fun _ _ => by positivity) ht
  calc Real.exp (torusMean F) ≤ Real.exp (torusMean (F * P)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ polyL2 (F * P) := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hL

def coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) : MvPolynomial ι ℂ →ₗ[ℂ] EuclideanSpace ℂ T where
  toFun P := WithLp.toLp 2 fun t : T => P.coeff t
  map_add' P Q := by ext t; simp
  map_smul' c P := by ext t; simp

theorem coeffVec_apply {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ) (t : T) :
    coeffVec T P t = P.coeff t := rfl

theorem norm_coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : ‖coeffVec T P‖ = polyL2 P := by
  classical
  rw [EuclideanSpace.norm_eq, polyL2]
  congr 1
  simp only [coeffVec_apply]
  rw [Finset.sum_coe_sort T (fun t => ‖P.coeff t‖ ^ 2)]
  exact (Finset.sum_subset hP (fun t _ ht => by
    rw [MvPolynomial.notMem_support_iff.mp ht, norm_zero]; ring)).symm

theorem polyInner_eq_inner {ι : Type*} (T : Finset (ι →₀ ℕ)) (P Q : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : polyInner P Q = inner ℂ (coeffVec T Q) (coeffVec T P) := by
  classical
  rw [PiLp.inner_apply]
  simp only [coeffVec_apply, RCLike.inner_apply, polyInner]
  rw [Finset.sum_coe_sort T (fun t => P.coeff t * (starRingEnd ℂ) (Q.coeff t))]
  exact Finset.sum_subset hP (fun t _ ht => by rw [MvPolynomial.notMem_support_iff.mp ht, zero_mul])

theorem exists_lex_enum {ι : Type*} [LinearOrder ι] (S : Finset (ι →₀ ℕ)) :
    ∃ m : Fin S.card → (ι →₀ ℕ), (∀ k, m k ∈ S) ∧ Function.Injective m ∧
      ∀ j k, j < k → toLex (m k) < toLex (m j) := by
  classical
  let S' : Finset (Lex (ι →₀ ℕ)) := S.map toLex.toEmbedding
  have hc : S'.card = S.card := Finset.card_map _
  let f := S'.orderEmbOfFin hc
  refine ⟨fun k => ofLex (f (Fin.rev k)), ?_, ?_, ?_⟩
  · intro k
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp (S'.orderEmbOfFin_mem hc (Fin.rev k))
    have : ofLex (f (Fin.rev k)) = a := by rw [← he]; rfl
    show ofLex (f (Fin.rev k)) ∈ S
    rw [this]; exact ha
  · intro a b h
    exact Fin.rev_injective (f.injective h)
  · intro j k hjk
    show f (Fin.rev k) < f (Fin.rev j)
    exact f.strictMono (Fin.rev_lt_rev.mpr hjk)

end ReciprocityTheory.MultiplicativeHeights
end

section
namespace ReciprocityTheory.MultiplicativeHeights

open Finset Pointwise

private lemma support_subset_of_mem_span_of_support_subset {ι : Type} (s : Set (ι →₀ ℕ))
    (G : Set (MvPolynomial ι ℂ)) (hG : ∀ g ∈ G, (g.support : Set (ι →₀ ℕ)) ⊆ s)
    {p : MvPolynomial ι ℂ} (hp : p ∈ Submodule.span ℂ G) : (p.support : Set (ι →₀ ℕ)) ⊆ s := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => simp
  | add x y _ _ hx hy =>
    intro t ht
    rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
    exacts [hx h, hy h]
  | smul a x _ hx => exact fun t ht => hx (MvPolynomial.support_smul ht)

theorem gram_of_linearOrder {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)) (hF : F ≠ 0) :
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re := by
  obtain ⟨m, hmS, hminj, hmlex⟩ := exists_lex_enum S
  let T : Finset (ι →₀ ℕ) := S.biUnion fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support
  have hPT : ∀ s ∈ S, (F * MvPolynomial.monomial s (1 : ℂ)).support ⊆ T := fun s hs =>
    Finset.subset_biUnion_of_mem (fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support) hs
  let v : Fin S.card → EuclideanSpace ℂ T := fun k => coeffVec T (F * MvPolynomial.monomial (m k) 1)

  have hbij : Function.Bijective (fun k : Fin S.card => (⟨m k, hmS k⟩ : S)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun a b h => hminj (congrArg Subtype.val h), by simp⟩
  let e : Fin S.card ≃ S := Equiv.ofBijective _ hbij
  have hdet : Matrix.det (Matrix.of fun a b : S =>
        polyInner (F * MvPolynomial.monomial (a : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (b : ι →₀ ℕ) 1)) = (Matrix.gram ℂ v).det := by
    rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose (Matrix.gram ℂ v)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply,
      e, Equiv.ofBijective_apply]
    exact polyInner_eq_inner T _ _ (hPT _ (hmS i))
  have hT : ∀ j, ((F * MvPolynomial.monomial (m j) (1 : ℂ)).support : Set (ι →₀ ℕ)) ⊆ T :=
    fun j => by exact_mod_cast hPT _ (hmS j)

  have hδ : ∀ k : Fin S.card, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k),
      Real.exp (2 * torusMean F) ≤ ‖v k - x‖ ^ 2 := by
    intro k x hx
    have hspan : Submodule.span ℂ (v '' Set.Iio k) =
        (Submodule.span ℂ ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)).map
          ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [hspan] at hx
    obtain ⟨Q, hQ, rfl⟩ := hx
    have hQsupp : ∀ t ∈ Q.support, toLex (m k) < toLex t := by
      have hs := support_subset_of_mem_span_of_support_subset {t | toLex (m k) < toLex t} _ (by
        rintro _ ⟨j, hj, rfl⟩ t ht
        have ht' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
        subst ht'
        exact hmlex j k hj) hQ
      intro t ht
      exact hs ht
    have hmain := exp_torus_mean_le_l2_of_lex hBasic hLex hL2 F hF (m k) Q hQsupp
    have hFQ : ((F * Q).support : Set (ι →₀ ℕ)) ⊆ T := by
      have hmemFQ : F * Q ∈ Submodule.span ℂ
          ((LinearMap.mulLeft ℂ F) '' ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map.mpr ⟨Q, hQ, rfl⟩
      refine support_subset_of_mem_span_of_support_subset _ _ ?_ hmemFQ
      rintro _ ⟨_, ⟨j, _, rfl⟩, rfl⟩
      exact hT j
    have hsupp : (F * (MvPolynomial.monomial (m k) 1 - Q)).support ⊆ T := by
      rw [mul_sub]
      intro t ht
      rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ ht) with h | h
      · exact_mod_cast hT k h
      · exact_mod_cast hFQ h
    have hsub : v k - ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) Q =
        coeffVec T (F * (MvPolynomial.monomial (m k) 1 - Q)) := by
      rw [mul_sub, map_sub] <;> rfl
    rw [hsub, norm_coeffVec T _ hsupp]
    calc Real.exp (2 * torusMean F) = Real.exp (torusMean F) ^ 2 := by
          rw [sq, ← Real.exp_add, two_mul]
      _ ≤ _ := by gcongr
  have hprod := prod_le_re_det_gram S.card v (fun _ => Real.exp (2 * torusMean F))
    (fun _ => (Real.exp_pos _).le) hδ
  rw [hdet]
  refine le_trans (le_of_eq ?_) hprod
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  congr 1
  ring

theorem gram_holds (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) : GramStatement := by
  unfold GramStatement
  intro ι _ _ F S hF
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  convert gram_of_linearOrder hBasic hLex hL2 F S hF

end ReciprocityTheory.MultiplicativeHeights
end
