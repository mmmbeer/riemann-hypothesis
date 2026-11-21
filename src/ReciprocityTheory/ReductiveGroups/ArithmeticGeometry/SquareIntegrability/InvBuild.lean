import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

private lemma Hf_im_IR_lemma {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) {x y : Vsp dim} (hx : x ∈ IR I) (hy : y ∈ IR I) :
    (Hf x y).im = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hI x hx y hy
    | zero => simp [Hf]
    | add y z _ _ h1 h2 =>
      have e : Hf x (y + z) = Hf x y + Hf x z := by
        simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [e, Complex.add_im, h1, h2, add_zero]
    | smul r y _ h =>
      have e : Hf x (r • y) = (r : ℂ) * Hf x y := by
        unfold Hf
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Complex.conj_ofReal]
        ring
      simp [e, h]
  | zero => simp [Hf]
  | add a b _ _ h1 h2 =>
    have e : Hf (a + b) y = Hf a y + Hf b y := by
      simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    rw [e, Complex.add_im, h1, h2, add_zero]
  | smul r a _ h =>
    have e : Hf (r • a) y = (r : ℂ) * Hf a y := by
      unfold Hf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
      ring
    simp [e, h]

lemma norm_projection_sq [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) (u : Vsp dim)
    (h1 : Mc σ 1 u ∈ IR I) (hi : Mc σ Complex.I u ∈ IR I) :
    ‖Mc σ 1 u‖ ^ 2 = 2 * ‖prj σ u‖ ^ 2 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  set S1 : ℝ := ∑ i : Idx dim, if i.1 = σ then ‖u i‖ ^ 2 else 0 with hS1
  set S2 : ℝ := ∑ i : Idx dim, if i.1 = ComplexEmbedding.conjugate σ then ‖u i‖ ^ 2 else 0 with hS2
  have e1 : ‖Mc σ 1 u‖ ^ 2 = S1 + S2 := by
    rw [EuclideanSpace.norm_sq_eq, hS1, hS2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ']
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ]
      · simp [Mc_apply, h1, h2]
  have e2 : ‖prj σ u‖ ^ 2 = S1 := by
    rw [EuclideanSpace.norm_sq_eq, hS1]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i.1 = σ <;> simp [prj_apply, h1]
  have e3 : (Hf (Mc σ 1 u) (Mc σ Complex.I u)).im = S2 - S1 := by
    rw [Hf, Complex.im_sum, hS1, hS2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ', Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
      · simp [Mc_apply, h1, h2]
  have e4 := Hf_im_IR_lemma hI h1 hi
  linarith

lemma orth_prj [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) {t y : Vsp dim} (ht : t ∈ IR I)
    (hy : ∀ c, Mc σ c y ∈ IR I) (horth : ∀ c, inner ℝ t (Mc σ c y) = 0) :
    Hf (prj σ t) (prj σ y) = 0 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  have hre : ∀ a : Vsp dim, inner ℝ t a = (Hf t a).re := by
    intro a
    rw [PiLp.inner_apply, Hf, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.inner, Complex.mul_re]
    ring
  have key : ∀ c : ℂ, Hf t (Mc σ c y) = (starRingEnd ℂ) c * Hf (prj σ t) (prj σ y) +
      c * Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y) := by
    intro c
    rw [Hf, Hf, Hf, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, prj_apply, h1, hσ'] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, prj_apply, h1, h2, hσ] <;> ring
      · simp [Mc_apply, prj_apply, h1, h2]
  have hz : ∀ c : ℂ, Hf t (Mc σ c y) = 0 := fun c =>
    Complex.ext (by rw [← hre]; simpa using horth c) (by simpa using Hf_im_IR_lemma hI ht (hy c))
  have e1 := (key 1).symm.trans (hz 1)
  have e2 := (key Complex.I).symm.trans (hz Complex.I)
  rw [map_one] at e1
  rw [Complex.conj_I] at e2
  linear_combination (1 / 2 : ℂ) * e1 + (Complex.I / 2) * e2 +
    ((Hf (prj σ t) (prj σ y) - Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y)) / 2) *
      Complex.I_sq

abbrev conjO [IsCMField E] (α : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E α

lemma emb_conjO [IsCMField E] (α : 𝓞 E) (τ : E →+* ℂ) :
    τ ((conjO α : 𝓞 E) : E) = (starRingEnd ℂ) (τ (α : E)) := by
  simp [conjO, NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    NumberField.IsCMField.complexEmbedding_complexConj]

lemma act_apply {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v : Vsp dim) (i : Idx dim) :
    act α v i = i.1 (α : E) * v i := rfl

def actL {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun := act α
  map_add' v w := by ext i; simp only [act_apply, PiLp.add_apply]; ring
  map_smul' c v := by ext i; simp only [act_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma act_add_left {dim : (E →+* ℂ) → ℕ} (α β : 𝓞 E) (v : Vsp dim) :
    act (α + β) v = act α v + act β v := by
  ext i
  simp [act, add_mul]

lemma Hf_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (x a : Vsp dim) :
    Hf (act α x) a = Hf x (act (conjO α) a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO]
  ring

lemma inner_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (u a : Vsp dim) :
    inner ℝ (act α u) a = inner ℝ u (act (conjO α) a) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO, Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

lemma act_mem_IR {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {a : Vsp dim} (ha : a ∈ IR I) :
    act α a ∈ IR I := by
  have key : Submodule.span ℝ (I : Set (Vsp dim)) ≤ (IR I).comap ((actL α).restrictScalars ℝ) := by
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span (hs α x hx)
  exact key ha

lemma isU_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {x u : Vsp dim} (h : IsU I x u) :
    IsU I (act α x) (act α u) := by
  exact ⟨act_mem_IR hs α h.1, fun a ha => by
    rw [inner_act, h.2 _ (act_mem_IR hs _ ha), Hf_act]⟩

lemma norm_act_le {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (B : ℝ) (hB : ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ B)
    (v : Vsp dim) : ‖act α v‖ ≤ B * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv
    rw [show act α (0 : Vsp dim) = 0 from (actL α).map_zero]
    simp
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (by ext i; simpa using h i)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i.1)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hB0, ← Real.sqrt_mul (sq_nonneg B)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [act, PiLp.toLp_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB j.1) 2) (sq_nonneg _)

def Xg {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) : AddSubgroup (Vsp dim) where
  carrier := {u | ∃ x ∈ L, IsU I x u}
  add_mem' := by
    rintro u v ⟨x, hx, hu⟩ ⟨y, hy, hv⟩; exact ⟨x + y, L.add_mem hx hy, isU_add hu hv⟩
  zero_mem' := ⟨0, L.zero_mem, isU_zero I⟩
  neg_mem' := by rintro u ⟨x, hx, hu⟩; exact ⟨-x, L.neg_mem hx, isU_neg hu⟩

lemma Xg_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hL : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (α : 𝓞 E) {u : Vsp dim} (hu : u ∈ Xg L I) : act α u ∈ Xg L I := by
  obtain ⟨x, hx, h⟩ := hu
  exact ⟨act α x, hL α x hx, isU_act hs α h⟩

lemma Xg_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)} {u : Vsp dim}
    (hu : u ∈ Xg L I) : u ∈ IR I := by
  obtain ⟨x, -, h⟩ := hu
  exact h.1

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

open NumberField.InfinitePlace Classical in
lemma emb_comb [IsCMField E] (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ τ : E →+* ℂ,
      ∑ i, (r i : ℂ) * τ (RingOfIntegers.basis E i : E) =
        if τ = σ then c else if τ = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c else 0 := by
  classical
  have hne := ne_conj σ
  have hcx : ∀ τ : E →+* ℂ, (mk τ).IsComplex := fun τ => IsTotallyComplex.isComplex _
  let wc : {w : InfinitePlace E // w.IsComplex} := ⟨mk σ, hcx σ⟩
  let c' : ℂ := if (mk σ).embedding = σ then c else (starRingEnd ℂ) c
  let y : mixedEmbedding.mixedSpace E := (0, Pi.single wc c')
  let B := mixedEmbedding.latticeBasis E
  refine ⟨fun i => B.repr y i, fun τ => ?_⟩
  have hsum := B.sum_repr y

  have hcoord : ∑ i, (B.repr y i : ℂ) * (mk τ).embedding (RingOfIntegers.basis E i : E) =
      y.2 ⟨mk τ, hcx τ⟩ := by
    conv_rhs => rw [← hsum]
    rw [Prod.snd_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [B, Prod.smul_snd, Pi.smul_apply, mixedEmbedding.latticeBasis_apply,
      mixedEmbedding.mixedEmbedding_apply_isComplex, integralBasis_apply, Complex.real_smul]
  have hy : y.2 ⟨mk τ, hcx τ⟩ = if mk τ = mk σ then c' else 0 := by
    simp only [y]
    by_cases h : mk τ = mk σ
    · rw [if_pos h]
      have : (⟨mk τ, hcx τ⟩ : {w : InfinitePlace E // w.IsComplex}) = wc := Subtype.ext h
      rw [this, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne]
      intro h'; exact h (congrArg Subtype.val h')
  have hemb := embedding_mk_eq τ

  have hval : ∑ i, (B.repr y i : ℂ) * τ (RingOfIntegers.basis E i : E) =
      if (mk τ).embedding = τ then (if mk τ = mk σ then c' else 0)
      else (starRingEnd ℂ) (if mk τ = mk σ then c' else 0) := by
    rcases hemb with h | h
    · rw [if_pos h, ← hy, ← hcoord, h]
    · by_cases h' : (mk τ).embedding = τ
      · rw [if_pos h', ← hy, ← hcoord, h']
      · rw [if_neg h', ← hy, ← hcoord, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h, map_mul, Complex.conj_ofReal, ComplexEmbedding.conjugate_coe_eq]
        simp
  rw [hval]
  by_cases hτ : τ = σ
  · subst hτ
    simp only [if_true, c']
    split_ifs with h1 <;> simp
  · by_cases hτ' : τ = ComplexEmbedding.conjugate σ
    · subst hτ'
      have hm : mk (ComplexEmbedding.conjugate σ) = mk σ := mk_conjugate_eq σ
      simp only [if_neg hτ, if_true, hm, c']
      rcases embedding_mk_eq σ with h | h
      · have : (mk σ).embedding ≠ ComplexEmbedding.conjugate σ := by rw [h]; exact hne.symm
        simp [h, hm, this, hne, hne.symm]
      · simp [h, hm, hne, hne.symm]
    · have hm : mk τ ≠ mk σ := by
        intro h; rcases mk_eq_iff.mp h with h | h
        · exact hτ h
        · exact hτ' (by rw [← h]; exact (ComplexEmbedding.involutive_conjugate (K := E) τ).symm)
      simp [hτ, hτ', hm]

open Classical in

lemma Mc_comb [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ v : Vsp dim,
      Mc σ c v = ∑ i, r i • act (RingOfIntegers.basis E i) v := by
  classical
  obtain ⟨r, hr⟩ := emb_comb σ c
  refine ⟨r, fun v => ?_⟩
  ext j
  rw [Mc_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have := hr j.1
  simp only [PiLp.smul_apply, act_apply, Complex.real_smul]
  rw [show (∑ i, (r i : ℂ) * (j.1 (RingOfIntegers.basis E i : E) * v j)) =
    (∑ i, (r i : ℂ) * j.1 (RingOfIntegers.basis E i : E)) * v j by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, this]
  split_ifs <;> simp

lemma Mc_mem [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (S : Submodule ℝ (Vsp dim))
    (hS : ∀ (α : 𝓞 E) v, v ∈ S → act α v ∈ S) (c : ℂ) {v : Vsp dim} (hv : v ∈ S) :
    Mc σ c v ∈ S := by
  obtain ⟨r, hr⟩ := Mc_comb (dim := dim) σ c
  rw [hr]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hS _ _ hv)

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

lemma finite_sep {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Set V) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) (R : ℝ) :
    {x | x ∈ S ∧ ‖x‖ ≤ R}.Finite := by
  classical
  have hcpt : IsCompact (Metric.closedBall (0 : V) R) := isCompact_closedBall 0 R
  obtain ⟨t, htfin, hcov⟩ :=
    (Metric.totallyBounded_iff.mp hcpt.totallyBounded) (1 / 2) (by norm_num)
  have hT : ∀ x ∈ {x | x ∈ S ∧ ‖x‖ ≤ R}, ∃ y ∈ t, dist x y < 1 / 2 := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : V) R := by
      rw [mem_closedBall_zero_iff]; exact hx.2
    have := hcov hx'
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this
    exact this
  choose! f hf hfx using hT
  refine Set.Finite.of_finite_image (f := f) (htfin.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  · intro x hx y hy hxy
    by_contra hne
    have hsep := hS x hx.1 y hy.1 hne
    have h1 := hfx x hx
    have h2 := hfx y hy
    rw [hxy] at h1
    have hlt : dist x y < 1 := by
      calc dist x y ≤ dist x (f y) + dist y (f y) := dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    rw [dist_eq_norm] at hlt
    linarith

lemma sep_of_group {V : Type} [NormedAddCommGroup V] (G : AddSubgroup V)
    (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (S : Set V) (hS : S ⊆ G) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖ := by
  intro x hx y hy hne
  exact hG (x - y) (G.sub_mem (hS hx) (hS hy)) (sub_ne_zero.mpr hne)

lemma exists_closest {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (G : AddSubgroup V) (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (p : V) :
    ∃ w ∈ G, ∀ w' ∈ G, ‖p - w‖ ≤ ‖p - w'‖ := by
  classical
  have hsep := sep_of_group G hG (G : Set V) subset_rfl
  have hfin : {x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖}.Finite := finite_sep _ hsep _
  have hne : ({x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖} : Set V).Nonempty :=
    ⟨0, G.zero_mem, by simp⟩
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image _ (fun w => ‖p - w‖) hfin hne
  refine ⟨w, hw.1, fun w' hw' => ?_⟩
  by_cases h : ‖w'‖ ≤ 2 * ‖p‖
  · exact hmin w' ⟨hw', h⟩
  · push Not at h
    have h0 := hmin 0 ⟨G.zero_mem, by simp⟩
    simp only [sub_zero] at h0
    have h3 : ‖w'‖ - ‖p‖ ≤ ‖p - w'‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le w' p
    linarith

lemma cover (hNP : Ext.NearestPlane) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (G : Set V) (ℓ : ℝ) (hG : ∀ g ∈ G, ‖g‖ ≤ ℓ) (D : ℕ)
    (hD : Module.finrank ℝ (Submodule.span ℝ G) ≤ D) {z : V} (hz : z ∈ Submodule.span ℝ G) :
    ∃ g ∈ AddSubgroup.closure G, ‖z - g‖ ^ 2 ≤ D * ℓ ^ 2 / 4 := by
  classical
  obtain ⟨b, hbG, hbspan, hbli⟩ := exists_linearIndependent ℝ G
  have hbfin : b.Finite := LinearIndependent.setFinite hbli
  let _ : Fintype b := hbfin.fintype
  let e := Fintype.equivFin b
  let v : Fin (Fintype.card b) → V := fun i => (e.symm i : V)
  have hv : LinearIndependent ℝ v := hbli.comp _ e.symm.injective
  have hvG : ∀ i, v i ∈ G := fun i => hbG (e.symm i).2
  have hrange : Set.range v = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [v]⟩
  have hn : Fintype.card b ≤ D := by
    have h := finrank_span_set_eq_card (R := ℝ) hbli
    rw [hbspan, Set.toFinset_card] at h
    omega
  have hz' : z ∈ Submodule.span ℝ (Set.range v) := by
    rw [hrange, hbspan]; exact hz
  obtain ⟨c, hc⟩ := hNP V (Fintype.card b) v hv z hz'
  refine ⟨∑ i, (c i : ℝ) • v i, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ (fun i _ => ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hvG i)) _
  · have hsum : ∑ i, ‖v i‖ ^ 2 ≤ (Fintype.card b : ℝ) * ℓ ^ 2 := by
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (Fintype.card b), ℓ ^ 2 :=
            Finset.sum_le_sum (fun i _ => by
              have h1 := hG (v i) (hvG i)
              gcongr)
        _ = (Fintype.card b : ℝ) * ℓ ^ 2 := by simp
    have hnD : (Fintype.card b : ℝ) ≤ D := by exact_mod_cast hn
    have hl : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
    nlinarith

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def actHom {dim : (E →+* ℂ) → ℕ} (y : Vsp dim) : 𝓞 E →+ Vsp dim where
  toFun α := act α y
  map_zero' := by ext i; simp [act_apply]
  map_add' α β := act_add_left α β y

lemma act_omega_expand {dim : (E →+* ℂ) → ℕ} (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) (α : 𝓞 E) (y : Vsp dim) :
    act α y ∈ Submodule.span ℝ (Set.range fun j => act (ω j) y) := by
  classical
  have hsp : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ :=
    by
      first
      | exact hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
      | (haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
         exact hω.span_eq_top_of_card_eq_finrank (Fintype.card_fin _))
  have hα : (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℚ E) → ℚ, ∑ j, c j • (ω j : E) = α := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 hα
    | exact Submodule.mem_span_range_iff_exists_fun.1 hα
  have key : act α y = ∑ j, ((c j : ℝ)) • act (ω j) y := by
    ext i
    simp only [act, ← hc]
    simp [map_sum, Rat.smul_def, map_mul, map_ratCast, Finset.sum_mul, Complex.real_smul, mul_assoc]
  rw [key]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma rank_bound {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim))
    (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (hact : ∀ (α : 𝓞 E) u, u ∈ Xg L I → act α u ∈ Xg L I)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (σ : E →+* ℂ) (b : Set (Vsp dim)) [Fintype b] (hb : b ⊆ prj σ '' (Xg L I))
    (hli : LinearIndependent ℂ (fun s : b => (s : Vsp dim))) :
    Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℝ (IR I) := by
  classical
  have hpre : ∀ s : b, ∃ u, u ∈ Xg L I ∧ prj σ u = (s : Vsp dim) := by
    intro s
    obtain ⟨u, hu, h⟩ := hb s.2
    exact ⟨u, hu, h⟩
  choose u hu hus using hpre
  let v : Fin (Module.finrank ℚ E) × b → Vsp dim := fun p => act (ω p.1) (u p.2)
  have hvX : ∀ p, v p ∈ Xg L I := fun p => hact _ _ (hu p.2)
  have hvIR : ∀ p, v p ∈ IR I := by
    intro p
    have h : ∃ x ∈ L, IsU I x (v p) := hvX p
    obtain ⟨x, _, hx⟩ := h
    exact hx.1
  have hprj : ∀ (α : 𝓞 E) (w : Vsp dim), prj σ (act α w) = σ (α : E) • prj σ w := by
    intro α w
    ext i
    by_cases h : i.1 = σ
    · simp [prj, act_apply, h]
    · simp [prj, h]

  have hZ : ∀ m : Fin (Module.finrank ℚ E) × b → ℤ, ∑ p, m p • v p = 0 → ∀ p, m p = 0 := by
    intro m hm
    have h1 : ∑ s : b, (∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) • (s : Vsp dim) = 0 := by
      have := congrArg (prj σ) hm
      rw [map_sum, map_zero] at this
      rw [← this, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = prj σ (m (j, s) • act (ω j) (u s))
      rw [map_zsmul, hprj, hus, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    rintro ⟨j, s⟩
    have h2 := Fintype.linearIndependent_iff.mp hli
      (fun s => ∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) h1 s
    have h3 : σ (∑ j, ((m (j, s) : E)) * (ω j : E)) = 0 := by
      rw [map_sum]; simpa [map_mul, map_intCast] using h2
    have h4 : ∑ j, ((m (j, s) : ℚ)) • (ω j : E) = 0 := by
      have h5 := (map_eq_zero_iff σ σ.injective).mp h3
      simpa [Rat.smul_def] using h5
    have h6 := Fintype.linearIndependent_iff.mp hω (fun j => (m (j, s) : ℚ)) h4 j
    exact_mod_cast h6

  have hR : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    by_contra hcp
    let y : ℕ → Vsp dim := fun k => -(∑ q, ⌊(k : ℝ) * c q⌋ • v q)
    have hyX : ∀ k, y k ∈ Xg L I := fun k =>
      neg_mem (sum_mem fun q _ => zsmul_mem (hvX q) _)
    have hyeq : ∀ k : ℕ, y k = ∑ q, Int.fract ((k : ℝ) * c q) • v q := by
      intro k
      have h0 : ∑ q, ((k : ℝ) * c q) • v q = 0 := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, hc, smul_zero]
      simp only [y, Int.fract, sub_smul, Finset.sum_sub_distrib, h0, zero_sub]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
    have hyn : ∀ k, ‖y k‖ ≤ ∑ q, ‖v q‖ := by
      intro k
      rw [hyeq]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    have hfin : {x | x ∈ (Xg L I : Set (Vsp dim)) ∧ ‖x‖ ≤ ∑ q, ‖v q‖}.Finite :=
      finite_sep _ (sep_of_group (Xg L I) hsep _ subset_rfl) _
    let g : ℕ → (Fin (Module.finrank ℚ E) × b → ℤ) := fun k q => ⌊(k : ℝ) * c q⌋
    let Φ : (Fin (Module.finrank ℚ E) × b → ℤ) → Vsp dim := fun m => -(∑ q, m q • v q)
    have hΦ : Function.Injective Φ := by
      intro m m' h
      have h' : ∑ q, m q • v q = ∑ q, m' q • v q := neg_inj.mp h
      have h'' : ∑ q, (m q - m' q) • v q = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h', sub_self]
      funext q
      exact sub_eq_zero.mp (hZ _ h'' q)
    have hrg : (Set.range g).Finite := by
      refine Set.Finite.of_finite_image ?_ hΦ.injOn
      refine hfin.subset ?_
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨hyX k, hyn k⟩
    have hrp : (Set.range fun k : ℕ => ⌊(k : ℝ) * c p⌋).Finite :=
      (hrg.image (fun m => m p)).subset (by rintro _ ⟨k, rfl⟩; exact ⟨g k, ⟨k, rfl⟩, rfl⟩)
    obtain ⟨B, hB⟩ := hrp.bddAbove
    obtain ⟨B', hB'⟩ := hrp.bddBelow
    have hcpos : 0 < |c p| := abs_pos.mpr hcp
    obtain ⟨k, hk⟩ := exists_nat_gt ((|(B : ℝ)| + |(B' : ℝ)| + 2) / |c p|)
    have hkc : |(B : ℝ)| + |(B' : ℝ)| + 2 < (k : ℝ) * |c p| := by
      rwa [div_lt_iff₀ hcpos] at hk
    have hup : ⌊(k : ℝ) * c p⌋ ≤ B := hB ⟨k, rfl⟩
    have hlo : B' ≤ ⌊(k : ℝ) * c p⌋ := hB' ⟨k, rfl⟩
    have h1 : (k : ℝ) * c p - 1 < (⌊(k : ℝ) * c p⌋ : ℝ) := Int.sub_one_lt_floor _
    have h2 : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ (k : ℝ) * c p := Int.floor_le _
    have hup' : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ B := by exact_mod_cast hup
    have hlo' : (B' : ℝ) ≤ ⌊(k : ℝ) * c p⌋ := by exact_mod_cast hlo
    have hB0 := abs_nonneg (B : ℝ)
    have hB'0 := abs_nonneg (B' : ℝ)
    rcases lt_or_gt_of_ne hcp with hneg | hpos
    · rw [abs_of_neg hneg, mul_neg] at hkc
      have := neg_abs_le (B' : ℝ)
      linarith
    · rw [abs_of_pos hpos] at hkc
      have := le_abs_self (B : ℝ)
      linarith
  have hw : LinearIndependent ℝ (fun p => (⟨v p, hvIR p⟩ : IR I)) :=
    LinearIndependent.of_comp (IR I).subtype hR
  have := hw.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin] using this

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def Zs {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ {x | ∃ α : 𝓞 E, ∃ y ∈ Xg L I, ‖y‖ ≤ μ ∧ x = act α y}

lemma Zs_mono {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ μ' : ℝ} (h : μ ≤ μ') :
    Zs L I μ ≤ Zs L I μ' := Submodule.span_mono fun _ ⟨α, y, hy, hyμ, hx⟩ => ⟨α, y, hy, hyμ.trans h, hx⟩

lemma Zs_self {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ : ℝ} {y : Vsp dim}
    (hy : y ∈ Xg L I) (hμ : ‖y‖ ≤ μ) : y ∈ Zs L I μ := by
  refine Submodule.subset_span ⟨1, y, hy, hμ, ?_⟩
  ext i
  simp [act]

private lemma act_add_lemma {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (x y : Vsp dim) :
    act β (x + y) = act β x + act β y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_smul_lemma_2 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (r : ℝ) (x : Vsp dim) :
    act β (r • x) = r • act β x := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_zero_lemma_4 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) : act β (0 : Vsp dim) = 0 := by
  ext i
  simp [act]

private lemma act_mul_lemma_5 {dim : (E →+* ℂ) → ℕ} (β α : 𝓞 E) (y : Vsp dim) :
    act β (act α y) = act (β * α) y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_span_lemma_3 {dim : (E →+* ℂ) → ℕ} (S : Set (Vsp dim)) (β : 𝓞 E)
    (hS : ∀ y ∈ S, act β y ∈ Submodule.span ℝ S) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : act β a ∈ Submodule.span ℝ S := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [act_zero_lemma_4]; exact zero_mem _
  | add x y _ _ hx hy => rw [act_add_lemma]; exact add_mem hx hy
  | smul r x _ hx => rw [act_smul_lemma_2]; exact Submodule.smul_mem _ r hx

lemma Zs_act {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) (β : 𝓞 E)
    {x : Vsp dim} (hx : x ∈ Zs L I μ) : act β x ∈ Zs L I μ := by
  refine act_span_lemma_3 _ β ?_ hx
  rintro _ ⟨α, y, hy, hyμ, rfl⟩
  exact Submodule.subset_span ⟨β * α, y, hy, hyμ, act_mul_lemma_5 β α y⟩

lemma Zs_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (μ : ℝ) : Zs L I μ ≤ IR I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨α, y, hy, -, rfl⟩
  obtain ⟨x, -, hu⟩ : ∃ x ∈ L, IsU I x y := hy
  exact act_span_lemma_3 _ α (fun z hz => Submodule.subset_span (hIs α z hz)) hu.1

lemma prj_rsmul {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Vsp dim) :
    prj σ (r • x) = r • prj σ x := by
  simp only [prj]
  exact LinearMap.map_smul_of_tower _ r x

private lemma prj_add_lemma_6 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (x y : Vsp dim) :
    prj σ (x + y) = prj σ x + prj σ y := by
  simp only [prj]
  exact map_add _ x y

private lemma prj_zero_lemma_7 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : prj σ (0 : Vsp dim) = 0 := by
  simp only [prj]
  exact map_zero _

lemma prj_mem_of_span {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (S : Set (Vsp dim)) (hS : ∀ y ∈ S, prj σ y ∈ W) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : prj σ a ∈ W := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [prj_zero_lemma_7]; exact zero_mem _
  | add x y _ _ hx hy => rw [prj_add_lemma_6]; exact add_mem hx hy
  | smul r x _ hx => rw [prj_rsmul]; exact W.smul_of_tower_mem r hx


end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

set_option maxHeartbeats 1000000 in
lemma one_char [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    (L I : Submodule ℤ (Vsp dim))
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (k : ℕ) (χ : ℕ → Vsp dim) (hχX : ∀ j < k, χ j ∈ Xg L I) (hχW : ∀ j < k, prj σ (χ j) ∈ W)
    (hWχ : W ≤ Submodule.span ℂ ((fun i => prj σ (χ i)) '' Set.Iio k))
    (hflag : ∀ j < k, ∃ μ, χ j ∈ Zs L I μ ∧ ∀ y ∈ Xg L I, prj σ y ∉ W → μ ≤ ‖y‖)
    (v : Vsp dim) (hvX : v ∈ Xg L I) (hvW : prj σ v ∉ W)
    (hvmin : ∀ y ∈ Xg L I, prj σ y ∉ W → ‖v‖ ≤ ‖y‖) (T : ℝ) (hT : 0 < T) :
    ∃ t χ' : Vsp dim, (∀ w ∈ W, inner ℂ w (prj σ t) = 0) ∧ ‖prj σ t‖ = T ∧
      ‖t‖ ^ 2 = 2 * T ^ 2 ∧ χ' ∈ Xg L I ∧ χ' ∈ Zs L I ‖v‖ ∧
      ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 ∧
      ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
  classical

  have hMc1 : ∀ (c : ℂ) (x : Vsp dim), Mc σ 1 (Mc σ c x) = Mc σ c x := by
    intro c x
    ext i
    simp only [Mc, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> simp
  have hprj1 : ∀ x : Vsp dim, prj σ (Mc σ 1 x) = prj σ x := by
    intro x; rw [prj_Mc, one_smul]
  have hZact : ∀ (α : 𝓞 E) x, x ∈ Zs L I ‖v‖ → act α x ∈ Zs L I ‖v‖ :=
    fun α x hx => Zs_act L I _ α hx
  have hZMc : ∀ (c : ℂ) {x : Vsp dim}, x ∈ Zs L I ‖v‖ → Mc σ c x ∈ Zs L I ‖v‖ :=
    fun c x hx => Mc_mem σ (Zs L I ‖v‖) hZact c hx
  have hvZ : v ∈ Zs L I ‖v‖ := Zs_self L I hvX le_rfl
  have hχZ : ∀ j < k, χ j ∈ Zs L I ‖v‖ := by
    intro j hj
    obtain ⟨μ, hμ, hμle⟩ := hflag j hj
    exact Zs_mono L I (hμle v hvX hvW) hμ
  have hshort : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → prj σ u ∈ W := by
    intro u hu huv
    by_contra h
    exact absurd (hvmin u hu h) (not_le.mpr huv)

  obtain ⟨U, hU⟩ : ∃ U : Submodule ℝ (Vsp dim), U = Submodule.span ℝ
      {x | ∃ c : ℂ, ∃ y ∈ Zs L I ‖v‖, prj σ y ∈ W ∧ x = Mc σ c y} := ⟨_, rfl⟩
  have hUgen : ∀ (c : ℂ) y, y ∈ Zs L I ‖v‖ → prj σ y ∈ W → Mc σ c y ∈ U := by
    intro c y hy hyW
    rw [hU]; exact Submodule.subset_span ⟨c, y, hy, hyW, rfl⟩
  have hUZ : U ≤ Zs L I ‖v‖ := by
    rw [hU]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨c, y, hy, -, rfl⟩
    exact hZMc c hy
  have hUprj : ∀ x ∈ U, prj σ x ∈ W := by
    intro x hx
    rw [hU] at hx
    refine prj_mem_of_span σ W _ ?_ hx
    rintro y ⟨c, y', -, hy', rfl⟩
    rw [prj_Mc]; exact W.smul_mem c hy'
  have hUMc : ∀ x ∈ U, Mc σ 1 x ∈ U := by
    intro x hx
    rw [hU] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, y', hy', hy'W, rfl⟩ := hy
      rw [hMc1]; exact hUgen c y' hy' hy'W
    | zero => rw [map_zero]; exact U.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact U.add_mem ha hb
    | smul r a _ ha => rw [LinearMap.map_smul_of_tower]; exact U.smul_mem r ha

  haveI : CompleteSpace U := FiniteDimensional.complete ℝ U
  obtain ⟨y₀, hy₀U, z, hzU, hxyz⟩ := U.exists_add_mem_mem_orthogonal (Mc σ 1 v)
  have hz : z = Mc σ 1 v - y₀ := by rw [hxyz]; abel
  have hzZ : z ∈ Zs L I ‖v‖ := by
    rw [hz]; exact Submodule.sub_mem _ (hZMc 1 hvZ) (hUZ hy₀U)
  have hzperp : ∀ u ∈ U, inner ℝ (Mc σ 1 z) u = 0 := by
    intro u hu
    rw [real_inner_Mc, map_one]
    exact Submodule.inner_left_of_mem_orthogonal (hUMc u hu) hzU
  have hprjt₀ : prj σ (Mc σ 1 z) = prj σ v - prj σ y₀ := by
    rw [hprj1, hz, map_sub, hprj1]
  have hp0 : prj σ (Mc σ 1 z) ≠ 0 := by
    intro h0
    apply hvW
    have h' : prj σ v = prj σ y₀ := by rw [← sub_eq_zero, ← hprjt₀, h0]
    rw [h']; exact hUprj y₀ hy₀U
  have hWorth : ∀ w ∈ W, inner ℂ w (prj σ (Mc σ 1 z)) = 0 := by
    have hsub : W ≤ (Submodule.span ℂ {prj σ (Mc σ 1 z)})ᗮ := by
      refine hWχ.trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j < k := hj
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      have hH := orth_prj hiso σ (Zs_IR hIs _ (hZMc 1 hzZ))
        (fun c => Zs_IR hIs _ (hZMc c (hχZ j hj')))
        (fun c => hzperp _ (hUgen c _ (hχZ j hj') (hχW j hj')))
      have key : inner ℂ (prj σ (χ j)) (prj σ (Mc σ 1 z)) =
          Hf (prj σ (Mc σ 1 z)) (prj σ (χ j)) := by
        simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]
      rw [key]; exact hH
    intro w hw
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hsub hw)

  have hpn : 0 < ‖prj σ (Mc σ 1 z)‖ := norm_pos_iff.mpr hp0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = T / ‖prj σ (Mc σ 1 z)‖ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos hT hpn
  obtain ⟨t, ht⟩ : ∃ t : Vsp dim, t = r • Mc σ 1 z := ⟨_, rfl⟩
  have htZ : t ∈ Zs L I ‖v‖ := by rw [ht]; exact Submodule.smul_mem _ r (hZMc 1 hzZ)
  have hprjt : prj σ t = r • prj σ (Mc σ 1 z) := by rw [ht, prj_rsmul]
  have hnT : ‖prj σ t‖ = T := by
    rw [hprjt, norm_smul, Real.norm_of_nonneg hr0.le, hr, div_mul_cancel₀ _ hpn.ne']
  have hWt : ∀ w ∈ W, inner ℂ w (prj σ t) = 0 := by
    intro w hw
    rw [hprjt, ← Complex.coe_smul, inner_smul_right, hWorth w hw, mul_zero]
  have hMt : Mc σ 1 t = t := by rw [ht, LinearMap.map_smul_of_tower, hMc1]
  have htn : ‖t‖ ^ 2 = 2 * T ^ 2 := by
    have h := norm_projection_sq hiso σ t (by rw [hMt]; exact Zs_IR hIs _ htZ)
      (Zs_IR hIs _ (hZMc Complex.I htZ))
    rw [hMt, hnT] at h; exact h
  have htorth : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → inner ℝ t u = 0 := by
    intro u hu huv
    rw [ht, real_inner_smul_left, real_inner_Mc, map_one,
      Submodule.inner_left_of_mem_orthogonal
        (hUgen 1 u (Zs_self L I hu huv.le) (hshort u hu huv)) hzU, mul_zero]

  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : AddSubgroup (Vsp dim), Λ = Xg L I ⊓ (Zs L I ‖v‖).toAddSubgroup :=
    ⟨_, rfl⟩
  have hΛ : ∀ g, g ∈ Λ ↔ g ∈ Xg L I ∧ g ∈ Zs L I ‖v‖ := by
    intro g; rw [hΛdef, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
  obtain ⟨χ', hχ'Λ, hclose⟩ :=
    exists_closest Λ (fun g hg hg0 => hsep g ((hΛ g).1 hg).1 hg0) t

  obtain ⟨S', hS'⟩ : ∃ S' : Set (Vsp dim),
      S' = {x | ∃ j, ∃ y ∈ Xg L I, ‖y‖ ≤ ‖v‖ ∧ x = act (ω j) y} := ⟨_, rfl⟩
  have hS'Λ : ∀ x ∈ S', x ∈ Λ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    exact (hΛ _).2 ⟨Xg_act hLs hIs (ω j) hy, Zs_act L I _ (ω j) (Zs_self L I hy hyv)⟩
  have hS'norm : ∀ x ∈ S', ‖x‖ ≤ B * ‖v‖ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    have hB : 0 ≤ B := (norm_nonneg _).trans (hωB j σ)
    exact (norm_act_le (ω j) B (hωB j) y).trans (mul_le_mul_of_nonneg_left hyv hB)
  have hZS' : Zs L I ‖v‖ ≤ Submodule.span ℝ S' := by
    unfold Zs
    refine Submodule.span_le.mpr ?_
    rintro x ⟨α, y, hy, hyv, rfl⟩
    refine Submodule.span_mono ?_ (act_omega_expand ω hω α y)
    rintro _ ⟨j, rfl⟩
    rw [hS']
    exact ⟨j, y, hy, hyv, rfl⟩
  obtain ⟨b, hbS', hbspan, hbli⟩ := exists_linearIndependent ℝ S'
  have hli : LinearIndependent ℝ (fun x : b => (x : Vsp dim)) := hbli
  haveI : Finite b := hli.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin b
  obtain ⟨vv, hvvdef⟩ : ∃ vv : Fin n → Vsp dim, vv = fun i => ((e.symm i : b) : Vsp dim) :=
    ⟨_, rfl⟩
  have hvv : LinearIndependent ℝ vv := by
    rw [hvvdef]; exact hli.comp e.symm e.symm.injective
  have hvvS' : ∀ i, vv i ∈ S' := fun i => by rw [hvvdef]; exact hbS' (e.symm i).2
  have hrange : Set.range vv = b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; rw [hvvdef]; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by rw [hvvdef]; simp⟩
  have htspan : t ∈ Submodule.span ℝ (Set.range vv) := by
    rw [hrange, hbspan]; exact hZS' htZ
  obtain ⟨c, hc⟩ := hNP (Vsp dim) n vv hvv t htspan
  have hnD : (n : ℝ) ≤ D := by
    have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range vv)) = n := by
      rw [finrank_span_eq_card hvv, Fintype.card_fin]
    have h2 : Submodule.span ℝ (Set.range vv) ≤ IR I := by
      rw [hrange, hbspan]
      exact Submodule.span_le.mpr fun x hx => Zs_IR hIs _ ((hΛ x).1 (hS'Λ x hx)).2
    have h3 : n ≤ D := by rw [← h1]; exact (Submodule.finrank_mono h2).trans hD
    exact_mod_cast h3
  have hgΛ : (∑ i, (c i : ℝ) • vv i) ∈ Λ := by
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (hS'Λ _ (hvvS' i)) _
  have hsum : ∑ i, ‖vv i‖ ^ 2 ≤ n * (B * ‖v‖) ^ 2 := by
    calc ∑ i, ‖vv i‖ ^ 2 ≤ ∑ _i : Fin n, (B * ‖v‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => by gcongr; exact hS'norm _ (hvvS' i)
      _ = n * (B * ‖v‖) ^ 2 := by simp
  have hbound : ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 := by
    have h1 : ‖t - χ'‖ ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ := hclose _ hgΛ
    have h2 : ‖t - χ'‖ ^ 2 ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ ^ 2 := by gcongr
    have h3 : (n : ℝ) * (B * ‖v‖) ^ 2 ≤ D * (B * ‖v‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hnD (sq_nonneg _)
    rw [norm_sub_rev]
    linarith

  have hlast : ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
    intro u hu
    by_cases huv : ‖v‖ ≤ ‖u‖
    · exact Or.inr huv
    left
    push_neg at huv
    have huΛ : u ∈ Λ := (hΛ u).2 ⟨hu, Zs_self L I hu huv.le⟩
    have h1 := hclose (χ' + u) (Λ.add_mem hχ'Λ huΛ)
    have h2 := hclose (χ' - u) (Λ.sub_mem hχ'Λ huΛ)
    have e1 : t - (χ' + u) = (t - χ') - u := by abel
    have e2 : t - (χ' - u) = (t - χ') + u := by abel
    rw [e1] at h1
    rw [e2] at h2
    have s1 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') - u‖ ^ 2 := by gcongr
    have s2 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') + u‖ ^ 2 := by gcongr
    rw [norm_sub_sq_real (t - χ') u] at s1
    rw [norm_add_sq_real (t - χ') u] at s2
    have hi : inner ℝ (t - χ') u = - inner ℝ χ' u := by
      rw [inner_sub_left, htorth u hu huv, zero_sub]
    rw [hi] at s1 s2
    rw [abs_le]; constructor <;> linarith
  exact ⟨t, χ', hWt, hnT, htn, ((hΛ χ').1 hχ'Λ).1, ((hΛ χ').1 hχ'Λ).2, hbound, hlast⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def partSub {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

variable {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

lemma sep_X (hI : IsSplit P I) : ∀ g ∈ Xg X.L I, g ≠ 0 → 1 ≤ ‖g‖ := by
  intro g hg hg0
  obtain ⟨x, hx, hu⟩ := hg
  have h1 := hI.sep x hx g hu hg0
  have h2 : (1:ℝ) ≤ ‖g‖ ^ 2 := P.C2.trans h1
  nlinarith [norm_nonneg g]

lemma exists_short_real_span (hI : IsSplit P I) : ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim,
    (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
    Submodule.span ℝ (Set.range u) = IR I ∧
    ∀ j, ‖u j‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) := by
  obtain ⟨x, u, hxu, hli, hb⟩ := hI.u1
  refine ⟨x, u, hxu, ?_, hb⟩
  have hle : Submodule.span ℝ (Set.range u) ≤ IR I := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hxu j).2.1
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, Fintype.card_fin]

lemma span_inf_partSub_le {σ : E →+* ℂ} (u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim)
    (hu : Submodule.span ℝ (Set.range u) = IR I) (W : Submodule ℂ (Vsp X.dim))
    (hW : ∀ j, prj σ (u j) ∈ W) :
    ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim))) ≤ W := by
  rintro v ⟨hvI, hvσ⟩
  have hvσ' : ∀ j : Idx X.dim, j.1 ≠ σ → v j = 0 := hvσ
  have hfix : prj σ v = v := by
    ext i
    by_cases h : i.1 = σ
    · simp [prj, h]
    · simp [prj, h, hvσ' i h]
  have hspan : Submodule.span ℂ (I : Set (Vsp X.dim)) ≤ Submodule.span ℂ (Set.range u) := by
    rw [Submodule.span_le]
    intro y hy
    have hyR : y ∈ IR I := Submodule.subset_span hy
    rw [← hu] at hyR
    exact Submodule.span_le_restrictScalars ℝ ℂ (Set.range u) hyR
  have hv : v ∈ Submodule.span ℂ (Set.range u) := hspan hvI
  rw [← hfix]
  have hmap : Submodule.map (prj σ) (Submodule.span ℂ (Set.range u)) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hW j
  exact hmap (Submodule.mem_map_of_mem hv)

lemma exists_out {σ : E →+* ℂ} {ρ : ℕ}
    (hρ : Module.finrank ℂ (((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim)))) = ρ)
    (u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim)
    (hu : Submodule.span ℝ (Set.range u) = IR I) (W : Submodule ℂ (Vsp X.dim))
    (hW : Module.finrank ℂ W < ρ) : ∃ j, prj σ (u j) ∉ W := by
  by_contra hcon
  push_neg at hcon
  have hle := span_inf_partSub_le u hu W hcon
  have h2 : Module.finrank ℂ ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ :
      Submodule ℂ (Vsp X.dim))) ≤ Module.finrank ℂ W := Submodule.finrank_mono hle
  rw [hρ] at h2
  omega

lemma rho_le [IsCMField E] (hI : IsSplit P I) (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) {σ : E →+* ℂ} {ρ : ℕ}
    (hρ : Module.finrank ℂ (((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim)))) = ρ) :
    ρ ≤ P.m := by
  classical
  obtain ⟨x, u, hxu, hspan, -⟩ := exists_short_real_span hI
  set S := prj σ '' (Xg X.L I : Set (Vsp X.dim))
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ S
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  have hV1 : ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim))) ≤ Submodule.span ℂ b := by
    rw [hbspan]
    exact span_inf_partSub_le u hspan _ fun j => Submodule.subset_span ⟨u j, ⟨x j, (hxu j).1, (hxu j).2⟩, rfl⟩
  have h1 : ρ ≤ Fintype.card b := by
    have := Submodule.finrank_mono hV1
    rw [hρ] at this
    have h2 := finrank_span_eq_card hbli
    rw [Subtype.range_coe] at h2
    have h3 : Fintype.card {x // x ∈ b} = Fintype.card b := Fintype.card_congr (Equiv.refl _)
    omega
  have h2 := rank_bound X.L I (sep_X hI) (fun α u hu => Xg_act X.stable hI.stable α hu) ω hω σ b hbS hbli
  obtain ⟨ρ', hρ'm, hρ'⟩ := hI.rank
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hf : 2 * PT.f E ≤ Module.finrank ℚ E := by unfold PT.f; omega
  have h3 : Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℚ E * ρ' := by
    rw [hρ'] at h2; nlinarith
  have h4 := Nat.le_of_mul_le_mul_left h3 hn
  omega

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

lemma prj_mem_spanC [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) {y : Vsp dim} (hy : y ∈ IR I) :
    prj σ y ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
  have hMc : ∀ c : ℂ, ∀ y ∈ I, Mc σ c y ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
    intro c y hy
    obtain ⟨r, hr⟩ := Mc_comb (dim := dim) σ c
    rw [hr]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ (r i) (Submodule.subset_span (hIs _ _ hy))
  refine prj_mem_of_span σ _ (I : Set (Vsp dim)) (fun y hy => ?_) hy
  rw [prj_eq_Mc]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hMc 1 y hy) (Submodule.smul_mem _ _ (hMc _ y hy)))

def Wk {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) (k : ℕ) : Submodule ℂ (Vsp dim) :=
  Submodule.span ℂ ((fun i => prj σ (χ i)) '' Set.Iio k)

lemma Wk_mono {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) {a b : ℕ} (h : a ≤ b) :
    Wk σ χ a ≤ Wk σ χ b := Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

lemma prj_mem_Wk {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) {j k : ℕ} (h : j < k) :
    prj σ (χ j) ∈ Wk σ χ k := Submodule.subset_span ⟨j, h, rfl⟩

lemma Wk_update {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) {j k : ℕ} (hj : j ≤ k)
    (c : Vsp dim) : Wk σ (Function.update χ k c) j = Wk σ χ j := by
  unfold Wk
  congr 1
  refine Set.image_congr fun i hi => ?_
  rw [Function.update_of_ne (ne_of_lt (lt_of_lt_of_le hi hj))]

lemma finrank_Wk {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) (k : ℕ) :
    Module.finrank ℂ (Wk σ χ k) ≤ k := by
  classical
  unfold Wk
  have himg : (fun i => prj σ (χ i)) '' Set.Iio k = ↑((Finset.range k).image fun i => prj σ (χ i)) := by
    rw [Finset.coe_image, Finset.coe_range]
  rw [himg]
  exact (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp))

lemma Wk_le [IsCMField E] {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) (χ : ℕ → Vsp dim) (k : ℕ)
    (hχ : ∀ s < k, χ s ∈ Xg L I) :
    Wk σ χ k ≤ (Submodule.span ℂ (I : Set (Vsp dim)) ⊓ partSub σ : Submodule ℂ (Vsp dim)) := by
  rw [Wk, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨prj_mem_spanC hIs σ (Xg_IR (hχ i hi)), prj_inPart σ _⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def Inv {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (σ : E →+* ℂ) (ρ : ℕ) (K0 Bu : ℝ)
    (k : ℕ) (χ w : ℕ → Vsp dim) (R μ : ℕ → ℝ) (ε : ℕ → ℕ → ℂ) : Prop :=
  (∀ s < k, χ s ∈ Xg L I) ∧
  (∀ s < k, w s ∈ Wk σ χ (s + 1)) ∧
  (∀ s < k, ∀ s' < k, inner ℂ (w s) (w s') = if s = s' then (1 : ℂ) else 0) ∧
  (∀ s < k, prj σ (χ s) =
    (R s : ℂ) • (w s + ∑ i ∈ Finset.range s, (starRingEnd ℂ) (ε s i) • w i)) ∧
  (∀ s < k, ∀ i, s ≤ i → ε s i = 0) ∧
  (∀ s < k, ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 ≤ (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2) ∧
  (∀ s < k, 30 * (ρ : ℝ) ^ 2 * K0 * μ s ≤ R s ∧
    ‖χ s‖ ≤ (Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1) * K0 * μ s) ∧
  (∀ s < k, 1 ≤ μ s ∧ ∀ y ∈ Xg L I, |2 * inner ℝ (χ s) y| ≤ ‖y‖ ^ 2 ∨ μ s ≤ ‖y‖) ∧
  (∀ s < k, χ s ∈ Zs L I (μ s) ∧ ∀ y ∈ Xg L I, prj σ y ∉ Wk σ χ s → μ s ≤ ‖y‖) ∧
  (∀ s < k, μ s ^ 2 ≤ Bu)

set_option maxHeartbeats 1000000 in
private lemma inv_step_lemma {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖) (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim)) (y0 : Vsp dim)
    (hy0 : y0 ∈ Xg L I) (hy0W : prj σ y0 ∉ W) :
    ∃ v ∈ Xg L I, prj σ v ∉ W ∧ ‖v‖ ≤ ‖y0‖ ∧ ∀ y ∈ Xg L I, prj σ y ∉ W → ‖v‖ ≤ ‖y‖ := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Set (Vsp dim), S = {y | y ∈ Xg L I ∧ prj σ y ∉ W ∧ ‖y‖ ≤ ‖y0‖} := ⟨_, rfl⟩
  obtain ⟨t, -, ht, hcov⟩ :=
    (isCompact_closedBall (0 : Vsp dim) ‖y0‖).finite_cover_balls (by norm_num : (0 : ℝ) < 1 / 2)
  have hex : ∀ y ∈ S, ∃ x ∈ t, y ∈ Metric.ball x (1 / 2) := by
    intro y hy
    rw [hS] at hy
    have hyb : y ∈ Metric.closedBall (0 : Vsp dim) ‖y0‖ := by
      rw [mem_closedBall_zero_iff]; exact hy.2.2
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hcov hyb)
    exact ⟨x, hx, hyx⟩
  obtain ⟨f, hf⟩ : ∃ f : Vsp dim → Vsp dim, ∀ y ∈ S, f y ∈ t ∧ y ∈ Metric.ball (f y) (1 / 2) := by
    refine ⟨fun y => if h : ∃ x ∈ t, y ∈ Metric.ball x (1 / 2) then h.choose else 0, fun y hy => ?_⟩
    have h := hex y hy
    simp only [dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn f S := by
    intro y hy y' hy' hyy
    have h1 := (hf y hy).2
    have h2 := (hf y' hy').2
    rw [hyy] at h1
    rw [Metric.mem_ball, dist_eq_norm] at h1 h2
    have hd : ‖y - y'‖ < 1 := by
      calc ‖y - y'‖ = ‖(y - f y') - (y' - f y')‖ := by congr 1; abel
        _ ≤ ‖y - f y'‖ + ‖y' - f y'‖ := norm_sub_le _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    by_contra hne
    rw [hS] at hy hy'
    have h3 := hsep (y - y') (sub_mem hy.1 hy'.1) (sub_ne_zero.mpr hne)
    linarith
  have hfin : S.Finite :=
    Set.Finite.of_finite_image (ht.subset (by rintro _ ⟨y, hy, rfl⟩; exact (hf y hy).1)) hinj
  have hne : S.Nonempty := ⟨y0, by rw [hS]; exact ⟨hy0, hy0W, le_rfl⟩⟩
  obtain ⟨v, hv, hvmin⟩ := Set.exists_min_image S (fun y => ‖y‖) hfin hne
  have hv' := hv
  rw [hS] at hv'
  refine ⟨v, hv'.1, hv'.2.1, hv'.2.2, fun y hy hyW => ?_⟩
  by_cases hle : ‖y‖ ≤ ‖y0‖
  · exact hvmin y (by rw [hS]; exact ⟨hy, hyW, hle⟩)
  · exact le_trans hv'.2.2 (le_of_lt (not_le.mp hle))

lemma inv_step [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    {L I : Submodule ℤ (Vsp dim)}
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (ρ : ℕ) (K0 Bu : ℝ) (hK0 : 0 < K0)
    (hK : (D : ℝ) * B ^ 2 / 4 ≤ K0 ^ 2)
    (hex : ∀ W : Submodule ℂ (Vsp dim), Module.finrank ℂ W < ρ →
      ∃ y ∈ Xg L I, prj σ y ∉ W ∧ ‖y‖ ^ 2 ≤ Bu)
    {k : ℕ} (hk : k < ρ) {χ w : ℕ → Vsp dim} {R μ : ℕ → ℝ} {ε : ℕ → ℕ → ℂ}
    (h : Inv L I σ ρ K0 Bu k χ w R μ ε) :
    ∃ (χ' w' : ℕ → Vsp dim) (R' μ' : ℕ → ℝ) (ε' : ℕ → ℕ → ℂ), Inv L I σ ρ K0 Bu (k + 1) χ' w' R' μ' ε' := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hwW : ∀ i < k, w i ∈ Wk σ χ k := fun i hi => Wk_mono σ χ (by omega : i + 1 ≤ k) (h2 i hi)
  obtain ⟨y0, hy0X, hy0W, hy0B⟩ := hex (Wk σ χ k) (lt_of_le_of_lt (finrank_Wk σ χ k) hk)
  obtain ⟨v, hvX, hvW, hvy0, hvmin⟩ := inv_step_lemma hsep σ (Wk σ χ k) y0 hy0X hy0W
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvW (by rw [map_zero]; exact (Wk σ χ k).zero_mem)
  have hμ1 : 1 ≤ ‖v‖ := hsep v hvX hv0
  have hρ : (1 : ℝ) ≤ ρ := by exact_mod_cast (by omega : 1 ≤ ρ)
  have hKμ : 0 < K0 * ‖v‖ := mul_pos hK0 (by linarith)
  have hTpos : 0 < (30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖ := by
    have : 0 < 30 * (ρ : ℝ) ^ 2 + 1 := by positivity
    rw [mul_assoc]; exact mul_pos this hKμ
  obtain ⟨t, χn, hto, htn, htt, hχX, hχZ, hχt, hχu⟩ := one_char hNP L I hLs hIs hiso hsep ω hω B hωB D hD σ
    (Wk σ χ k) k χ (fun j hj => h1 j hj) (fun j hj => prj_mem_Wk σ χ hj) (le_refl _)
    (fun j hj => ⟨μ j, (h9 j hj).1, fun y hy hyW => (h9 j hj).2 y hy
      (fun hm => hyW (Wk_mono σ χ (le_of_lt hj) hm))⟩)
    v hvX hvW hvmin ((30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖) hTpos
  have hK0μ : ‖χn - t‖ ≤ K0 * ‖v‖ := by
    have hsq : ‖χn - t‖ ^ 2 ≤ (K0 * ‖v‖) ^ 2 := by
      calc ‖χn - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 := hχt
        _ = (D * B ^ 2 / 4) * ‖v‖ ^ 2 := by ring
        _ ≤ K0 ^ 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hK (by positivity)
        _ = (K0 * ‖v‖) ^ 2 := by ring
    nlinarith [norm_nonneg (χn - t)]
  obtain ⟨e, he⟩ : ∃ e, e = prj σ (χn - t) := ⟨_, rfl⟩
  have heK : ‖e‖ ≤ K0 * ‖v‖ := by rw [he]; exact le_trans (norm_prj_le σ _) hK0μ
  have hpe : prj σ χn = prj σ t + e := by rw [he, map_sub]; abel
  have hproj : ∀ x : Vsp dim, ∀ j < k,
      inner ℂ (w j) (x - ∑ i ∈ Finset.range k, inner ℂ (w i) x • w i) = 0 := by
    intro x j hj
    rw [inner_sub_right, inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right, h3 j hj j hj, if_pos rfl, mul_one, sub_self]
    · intro i hi hij
      rw [inner_smul_right, h3 j hj i (Finset.mem_range.mp hi), if_neg (Ne.symm hij), mul_zero]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'
  obtain ⟨Wp, hWp⟩ : ∃ Wp, Wp = ∑ i ∈ Finset.range k, inner ℂ (w i) e • w i := ⟨_, rfl⟩
  have hWpW : Wp ∈ Wk σ χ k := by
    rw [hWp]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hwW i (Finset.mem_range.mp hi))
  have heW : ∀ j < k, inner ℂ (w j) (e - Wp) = 0 := fun j hj => by rw [hWp]; exact hproj e j hj
  have hwt : ∀ j < k, inner ℂ (w j) (prj σ t) = 0 := fun j hj => hto (w j) (hwW j hj)
  obtain ⟨q, hq⟩ : ∃ q, q = prj σ χn - Wp := ⟨_, rfl⟩
  have hqt : q = prj σ t + (e - Wp) := by rw [hq, hpe]; abel
  have hqw : ∀ j < k, inner ℂ (w j) q = 0 := fun j hj => by
    rw [hqt, inner_add_right, hwt j hj, heW j hj, add_zero]
  have hperp : inner ℂ (e - Wp) Wp = 0 := by
    nth_rewrite 2 [hWp]
    rw [inner_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [inner_smul_right, inner_eq_zero_symm.mp (heW i (Finset.mem_range.mp hi)), mul_zero]
  have heWp : ‖e - Wp‖ ≤ ‖e‖ := by
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (e - Wp) Wp hperp
    rw [sub_add_cancel] at hpy
    nlinarith [norm_nonneg (e - Wp), norm_nonneg e, norm_nonneg Wp]
  obtain ⟨Rk, hRk⟩ : ∃ Rk : ℝ, Rk = ‖q‖ := ⟨_, rfl⟩
  have hRlow : 30 * (ρ : ℝ) ^ 2 * K0 * ‖v‖ ≤ Rk := by
    have h0 : ‖prj σ t‖ ≤ ‖q‖ + ‖e - Wp‖ := by
      calc ‖prj σ t‖ = ‖q - (e - Wp)‖ := by rw [hqt]; congr 1; abel
        _ ≤ ‖q‖ + ‖e - Wp‖ := norm_sub_le _ _
    rw [htn] at h0
    rw [hRk]
    nlinarith
  have hRpos : 0 < Rk := by
    have : 0 < 30 * (ρ : ℝ) ^ 2 * K0 * ‖v‖ := by
      have h30 : 0 < 30 * (ρ : ℝ) ^ 2 := by positivity
      rw [mul_assoc]; exact mul_pos h30 hKμ
    linarith
  have hRne : (Rk : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  obtain ⟨wk, hwk⟩ : ∃ wk, wk = ((Rk : ℂ)⁻¹) • q := ⟨_, rfl⟩
  have hqR : q = (Rk : ℂ) • wk := by rw [hwk, smul_smul, mul_inv_cancel₀ hRne, one_smul]
  have hwkn : ‖wk‖ = 1 := by
    rw [hwk, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hRpos.le, ← hRk,
      inv_mul_cancel₀ hRpos.ne']
  have hwkw : ∀ j < k, inner ℂ (w j) wk = 0 := fun j hj => by
    rw [hwk, inner_smul_right, hqw j hj, mul_zero]
  obtain ⟨εk, hεk⟩ : ∃ εk : ℕ → ℂ, εk = fun i => if i < k then (starRingEnd ℂ) (inner ℂ (w i) e) / (Rk : ℂ) else 0 :=
    ⟨_, rfl⟩
  have hterm : ∀ i ∈ Finset.range k, (Rk : ℂ) • ((starRingEnd ℂ) (εk i) • w i) = inner ℂ (w i) e • w i := by
    intro i hi
    rw [hεk]
    simp only [if_pos (Finset.mem_range.mp hi)]
    rw [smul_smul, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    field_simp
  have hrep : prj σ χn = (Rk : ℂ) • (wk + ∑ i ∈ Finset.range k, (starRingEnd ℂ) (εk i) • w i) := by
    rw [smul_add, ← hqR, Finset.smul_sum, Finset.sum_congr rfl hterm, ← hWp, hq, sub_add_cancel]
  have hεsum : ∑ i ∈ Finset.range k, ‖εk i‖ ^ 2 ≤ (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2 := by
    have hON : Orthonormal ℂ (fun i : Fin k => w i) := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [h3 i i.2 j j.2]
      simp [Fin.ext_iff]
    have hB := hON.sum_inner_products_le e (s := Finset.univ)
    rw [Fin.sum_univ_eq_sum_range (fun i => ‖inner ℂ (w i) e‖ ^ 2) k] at hB
    have hs : ∑ i ∈ Finset.range k, ‖εk i‖ ^ 2 = (∑ i ∈ Finset.range k, ‖inner ℂ (w i) e‖ ^ 2) / Rk ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hεk]
      simp only [if_pos (Finset.mem_range.mp hi)]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hRpos.le, RCLike.norm_conj, div_pow]
    rw [hs]
    have hle1 : ∑ i ∈ Finset.range k, ‖inner ℂ (w i) e‖ ^ 2 ≤ (K0 * ‖v‖) ^ 2 :=
      le_trans hB (pow_le_pow_left₀ (norm_nonneg e) heK 2)
    have hRd : K0 * ‖v‖ ≤ Rk / (30 * (ρ : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc (∑ i ∈ Finset.range k, ‖inner ℂ (w i) e‖ ^ 2) / Rk ^ 2 ≤ (K0 * ‖v‖) ^ 2 / Rk ^ 2 :=
          div_le_div_of_nonneg_right hle1 (by positivity)
      _ ≤ (Rk / (30 * (ρ : ℝ) ^ 2)) ^ 2 / Rk ^ 2 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hKμ.le hRd 2) (by positivity)
      _ = (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2 := by
          have hρ0 : (ρ : ℝ) ≠ 0 := by linarith
          field_simp
  have hTt : ‖t‖ = Real.sqrt 2 * ((30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖) := by
    rw [← Real.sqrt_sq (norm_nonneg t), htt, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hTpos.le]
  have hχnorm : ‖χn‖ ≤ (Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1) * K0 * ‖v‖ := by
    calc ‖χn‖ = ‖(χn - t) + t‖ := by rw [sub_add_cancel]
      _ ≤ ‖χn - t‖ + ‖t‖ := norm_add_le _ _
      _ ≤ K0 * ‖v‖ + Real.sqrt 2 * ((30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖) := by rw [hTt]; linarith
      _ = (Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1) * K0 * ‖v‖ := by ring
  have hsumw : ∀ s ≤ k, ∀ a : ℕ → ℂ, ∑ i ∈ Finset.range s, a i • Function.update w k wk i =
      ∑ i ∈ Finset.range s, a i • w i := fun s hs a =>
    Finset.sum_congr rfl fun i hi => by
      rw [Function.update_of_ne (show i ≠ k by have := Finset.mem_range.mp hi; omega)]
  refine ⟨Function.update χ k χn, Function.update w k wk, Function.update R k Rk, Function.update μ k ‖v‖,
    Function.update ε k εk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h1 s hs
    · rw [hs, Function.update_self]; exact hχX
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs), Wk_update σ χ (by omega : s + 1 ≤ k)]
      exact h2 s hs
    · rw [hs, Function.update_self, hwk]
      apply Submodule.smul_mem
      rw [hq]
      apply Submodule.sub_mem
      · have hm := prj_mem_Wk σ (Function.update χ k χn) (Nat.lt_succ_self k)
        rwa [Function.update_self] at hm
      · have h' : Wk σ (Function.update χ k χn) k = Wk σ χ k := Wk_update σ χ le_rfl χn
        apply Wk_mono σ _ (Nat.le_succ k)
        rw [h']
        exact hWpW
  · intro s hs s' hs'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs' with hs' | hs'
    · rw [Function.update_of_ne (Nat.ne_of_lt hs), Function.update_of_ne (Nat.ne_of_lt hs')]
      exact h3 s hs s' hs'
    · rw [hs', Function.update_of_ne (Nat.ne_of_lt hs), Function.update_self, hwkw s hs,
        if_neg (Nat.ne_of_lt hs)]
    · rw [hs, Function.update_self, Function.update_of_ne (Nat.ne_of_lt hs'),
        inner_eq_zero_symm.mp (hwkw s' hs'), if_neg (Nat.ne_of_lt hs').symm]
    · rw [hs, hs', Function.update_self, if_pos rfl, inner_self_eq_norm_sq_to_K, hwkn]
      norm_num
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · have hne : s ≠ k := Nat.ne_of_lt hs
      simp only [Function.update_of_ne hne]
      rw [hsumw s hs.le]
      exact h4 s hs
    · rw [hs]
      simp only [Function.update_self]
      rw [hsumw k le_rfl]
      exact hrep
  · intro s hs i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h5 s hs i hi
    · rw [hs, Function.update_self]
      simp only [hεk]
      rw [if_neg (by omega)]
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h6 s hs
    · rw [hs, Function.update_self]; exact hεsum
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · simp only [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h7 s hs
    · rw [hs]
      simp only [Function.update_self]
      exact ⟨hRlow, hχnorm⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · simp only [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h8 s hs
    · rw [hs]
      simp only [Function.update_self]
      exact ⟨hμ1, hχu⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · simp only [Function.update_of_ne (Nat.ne_of_lt hs)]
      rw [Wk_update σ χ (le_of_lt hs)]
      exact h9 s hs
    · rw [hs]
      simp only [Function.update_self]
      rw [Wk_update σ χ le_rfl]
      exact ⟨hχZ, hvmin⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h10 s hs
    · rw [hs, Function.update_self]
      exact le_trans (pow_le_pow_left₀ (norm_nonneg v) hvy0 2) hy0B

lemma inv_build [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    {L I : Submodule ℤ (Vsp dim)}
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (ρ : ℕ) (K0 Bu : ℝ) (hK0 : 0 < K0)
    (hK : (D : ℝ) * B ^ 2 / 4 ≤ K0 ^ 2)
    (hex : ∀ W : Submodule ℂ (Vsp dim), Module.finrank ℂ W < ρ →
      ∃ y ∈ Xg L I, prj σ y ∉ W ∧ ‖y‖ ^ 2 ≤ Bu) :
    ∀ k ≤ ρ, ∃ (χ w : ℕ → Vsp dim) (R μ : ℕ → ℝ) (ε : ℕ → ℕ → ℂ), Inv L I σ ρ K0 Bu k χ w R μ ε := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, ?_⟩
    unfold Inv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro s hs <;> exact absurd hs (Nat.not_lt_zero _)
  | succ k ih =>
    intro hk
    obtain ⟨χ, w, R, μ, ε, h⟩ := ih (Nat.le_of_succ_le hk)
    exact inv_step hNP hLs hIs hiso hsep ω hω B hωB D hD σ ρ K0 Bu hK0 hK hex (Nat.lt_of_succ_le hk) h

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end
