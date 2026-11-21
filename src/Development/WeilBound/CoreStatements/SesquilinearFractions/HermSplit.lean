import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans
import Development.WeilBound.CoreStatements.SesquilinearFractions.PureTypeLatticesOrthogonal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqSmulOfFinrankOne

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.DPer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
variable {Ix : Type} [Fintype Ix] (x : Ix → D.La) (hx : LinearIndependent (𝓞 E) x) (n : ℕ)
  (hn : ∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x))

def toSpan : D.La →ₗ[𝓞 E] Submodule.span (𝓞 E) (Set.range x) where
  toFun y := ⟨n • y, hn y⟩
  map_add' y y' := Subtype.ext (smul_add _ _ _)
  map_smul' c y := Subtype.ext (smul_comm n c y)

def coef : D.La →ₗ[𝓞 E] (Ix →₀ 𝓞 E) := hx.repr ∘ₗ toSpan D x n hn

theorem coef_sum (y : D.La) : ∑ m, coef D x hx n hn y m • x m = n • y := by
  have h := hx.linearCombination_repr (toSpan D x n hn y)
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  exact h

theorem planeCoef_mulVec_smul_x_eq_zero_of_ne (m : Ix) : coef D x hx n hn (x m) = Finsupp.single m (n : 𝓞 E) := by
  have e : toSpan D x n hn (x m) = (n : 𝓞 E) • (⟨x m, Submodule.subset_span ⟨m, rfl⟩⟩ : Submodule.span (𝓞 E) (Set.range x)) := by
    apply Subtype.ext
    simp [toSpan, Nat.cast_smul_eq_nsmul]
  show hx.repr (toSpan D x n hn (x m)) = _
  rw [e, map_smul, LinearIndependent.repr_eq_single hx m _ rfl, Finsupp.smul_single_one]

theorem eq_zero_of_coef (hn0 : 0 < n) (y : D.La) (h : coef D x hx n hn y = 0) : y = 0 := by
  have h0 : n • y = 0 := by
    rw [← coef_sum D x hx n hn y, h]
    simp
  have h1 : (n : 𝓞 E) • y = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h0
  have hn' : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn0.ne'
  obtain ⟨s, hs⟩ := D.proj.out
  have h2 : s y = 0 := by
    have h3 := congrArg s h1
    rw [map_smul, map_zero] at h3
    exact (smul_eq_zero.mp h3).resolve_left hn'
  rw [← hs y, h2, map_zero]

end PositivityTheory.Xgf.DPer

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt_cases (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
  simp at this
  rw [H.sqrt_neg_disc_sq, ← this]

theorem exists_emb (b : Bool) : ∃ τ : E →+* ℂ, τ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
  cases b
  · exact GlobalTheory.CM.LatData.exists_embedding H (by simp [H.sqrt_neg_disc_sq])
  · exact GlobalTheory.CM.LatData.exists_embedding H H.sqrt_neg_disc_sq

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)

def eP (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) : {k // ty k = τ} ≃ Fin p :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).1 h)

def eQ (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) : {k // ty k = τ} ≃ Fin q :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).2 h)

def blk (k : Fin g) : Fin p ⊕ Fin q :=
  if h : ty k (H.rt : E) = H.rt0 then .inl (eP hty (ty k) h ⟨k, rfl⟩) else .inr (eQ hty (ty k) h ⟨k, rfl⟩)

theorem blk_inl (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inl (eP hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

theorem blk_inr (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inr (eQ hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

variable {D : Datum H} (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

def per : D.La →+ (Fin g → ℂ) where
  toFun y k := ty k ((c y (blk hty k) : 𝓞 E) : E) / n
  map_zero' := by funext k; simp
  map_add' y y' := by funext k; simp [add_div]

theorem per_apply (y : D.La) (k : Fin g) : per hty c n y k = ty k ((c y (blk hty k) : 𝓞 E) : E) / n := rfl

theorem per_smul (a : 𝓞 E) (y : D.La) (k : Fin g) : per hty c n (a • y) k = ty k (a : E) * per hty c n y k := by
  simp [per_apply, mul_div_assoc]

theorem per_inl (y : D.La) (a : Fin p) (hc : c y = Finsupp.single (.inl a) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ H.rt0) : per hty c n y k = 0 := by
  rw [per_apply, hc, blk_inr hty (ty k) hk k rfl]
  simp

theorem per_inr (y : D.La) (b : Fin q) (hc : c y = Finsupp.single (.inr b) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ -H.rt0) : per hty c n y k = 0 := by
  have h : ty k (H.rt : E) = H.rt0 := (rt_cases (ty k)).resolve_right hk
  rw [per_apply, hc, blk_inl hty (ty k) h k rfl]
  simp

theorem coef_zero_of_per (hn : 0 < n) (y : D.La) (h : per hty c n y = 0) : c y = 0 := by
  ext m
  cases m with
  | inl a =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) true
    simp only [if_true] at hτ
    let k := ((eP hty τ hτ).symm a).1
    have hk : ty k = τ := ((eP hty τ hτ).symm a).2
    have hb : blk hty k = .inl a := by
      rw [blk_inl hty τ hτ k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1
  | inr b =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) false
    simp only [Bool.false_eq_true, if_false] at hτ
    have hτ' : τ (H.rt : E) ≠ H.rt0 := by rw [hτ]; exact fun h => Host_rt0_ne_neg (H := H) h.symm
    let k := ((eQ hty τ hτ').symm b).1
    have hk : ty k = τ := ((eQ hty τ hτ').symm b).2
    have hb : blk hty k = .inr b := by
      rw [blk_inr hty τ hτ' k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1

end PositivityTheory.Xgf.DPer

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem principal_root_re_zero_im_sq : H.rt0.re = 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [sq] at h1 h2
  by_contra h0
  have : H.rt0.im = 0 := by
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left h0
  rw [this] at h1
  nlinarith [mul_self_nonneg H.rt0.re]

theorem rt0_conj_neg_ne_zero : conj H.rt0 = -H.rt0 := by
  apply Complex.ext <;> simp [principal_root_re_zero_im_sq (H := H)]

theorem conjugate_rt (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0 ↔ σ (H.rt : E) ≠ H.rt0 := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases rt_cases (H := H) σ with h | h
  · rw [h, rt0_conj_neg_ne_zero]
    simp only [ne_eq, not_true_eq_false, iff_false]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm
  · rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    simp only [true_iff]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm

theorem sum_split {M : Type} [AddCommMonoid M] (F : (E →+* ℂ) → M) :
    ∑ σ, F σ = ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F σ +
      ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F (ComplexEmbedding.conjugate σ) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0)]
  congr 1
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact (conjugate_rt σ).2 hσ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact fun h' => ((conjugate_rt σ).1 h') hσ
  · intro σ _; ext x; simp
  · intro σ _; ext x; simp
  · intro σ _; simp

theorem emb_indep (l : (E →+* ℂ) → ℂ) (h : ∀ b : 𝓞 E, ∑ σ, l σ * σ (b : E) = 0) : l = 0 := by
  let F : (E →+* ℂ) → (𝓞 E →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hF : Function.Injective F := by
    intro σ σ' e
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext b
    exact DFunLike.congr_fun e b
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp F hF
  funext σ
  refine Fintype.linearIndependent_iff.1 li l ?_ σ
  funext b
  simpa [F, Finset.sum_apply] using h b

theorem exists_big (a : 𝓞 E) (ha : a ≠ 0) (b : Bool) :
    ∃ σ : E →+* ℂ, σ (H.rt : E) = (if b then H.rt0 else -H.rt0) ∧ 1 ≤ ‖σ (a : E)‖ := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    intro σ
    by_cases hσ : σ (H.rt : E) = (if b then H.rt0 else -H.rt0)
    · exact hcon σ hσ
    · have h2 : ComplexEmbedding.conjugate σ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
        rw [ComplexEmbedding.conjugate_coe_eq]
        rcases rt_cases (H := H) σ with h | h <;> cases b <;>
          simp_all [rt0_conj_neg_ne_zero (H := H)]
      have := hcon _ h2
      rwa [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at this
  obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hlt : ∏ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ₀)]
    have h1 : ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun σ _ => (hall σ).le)
    calc ‖σ₀ (a : E)‖ * ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ ‖σ₀ (a : E)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < 1 := by rw [_root_.mul_one]; exact hall σ₀
  have hge : 1 ≤ ∏ σ : E →+* ℂ, ‖σ (a : E)‖ := by
    have hN : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
    have e1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (a : E)
    rw [← Algebra.coe_norm_int] at e1
    have e2 : ∏ τ : E →ₐ[ℚ] ℂ, τ (a : E) = ∏ σ : E →+* ℂ, σ (a : E) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun τ => rfl)
    rw [e2] at e1
    rw [← norm_prod, ← e1]
    have : ((algebraMap ℚ ℂ) ((Algebra.norm ℤ a : ℤ) : ℚ)) = ((Algebra.norm ℤ a : ℤ) : ℂ) := by simp
    rw [this, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hN
  linarith

end PositivityTheory.Xgf.DPer

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)

theorem blk_isLeft (k : Fin g) : (blk hty k).isLeft = true ↔ ty k (H.rt : E) = H.rt0 := by
  unfold blk
  split_ifs with h <;> simp [h]

theorem blk_inj {k k' : Fin g} (ht : ty k = ty k') (hb : blk hty k = blk hty k') : k = k' := by
  have key : ∀ (τ τ' : E →+* ℂ), τ = τ' → ∀ (h : τ (H.rt : E) = H.rt0) (h' : τ' (H.rt : E) = H.rt0)
      (a : {j : Fin g // ty j = τ}) (b : {j : Fin g // ty j = τ'}),
      eP hty τ h a = eP hty τ' h' b → (a : Fin g) = b := by
    rintro τ τ' rfl h h' a b hab
    exact congrArg Subtype.val ((eP hty τ h).injective hab)
  have key' : ∀ (τ τ' : E →+* ℂ), τ = τ' → ∀ (h : τ (H.rt : E) ≠ H.rt0) (h' : τ' (H.rt : E) ≠ H.rt0)
      (a : {j : Fin g // ty j = τ}) (b : {j : Fin g // ty j = τ'}),
      eQ hty τ h a = eQ hty τ' h' b → (a : Fin g) = b := by
    rintro τ τ' rfl h h' a b hab
    exact congrArg Subtype.val ((eQ hty τ h).injective hab)
  unfold blk at hb
  by_cases h : ty k (H.rt : E) = H.rt0
  · have h' : ty k' (H.rt : E) = H.rt0 := ht ▸ h
    rw [dif_pos h, dif_pos h'] at hb
    exact key _ _ ht h h' ⟨k, rfl⟩ ⟨k', rfl⟩ (Sum.inl.inj hb)
  · have h' : ty k' (H.rt : E) ≠ H.rt0 := ht ▸ h
    rw [dif_neg h, dif_neg h'] at hb
    exact key' _ _ ht h h' ⟨k, rfl⟩ ⟨k', rfl⟩ (Sum.inr.inj hb)

variable {D : Datum H} (x : Fin p ⊕ Fin q → D.La) (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

theorem per_bx (hn0 : 0 < n) (hcx : ∀ m, c (x m) = Finsupp.single m (n : 𝓞 E)) (b : 𝓞 E) (m : Fin p ⊕ Fin q)
    (k : Fin g) : per hty c n (b • x m) k = if blk hty k = m then ty k (b : E) else 0 := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  simp only [per, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul, hcx, Finsupp.smul_single, smul_eq_mul]
  rw [Finsupp.single_apply]
  by_cases h : blk hty k = m
  · rw [if_pos h.symm, if_pos h]
    push_cast
    rw [map_mul, map_natCast]
    field_simp
  · rw [if_neg (Ne.symm h), if_neg h]
    simp

theorem per_span (hn0 : 0 < n) (hcx : ∀ m, c (x m) = Finsupp.single m (n : 𝓞 E)) :
    Submodule.span ℝ (Set.range (per hty c n)) = ⊤ := by
  classical
  have side : ∀ k k' : Fin g, blk hty k = blk hty k' → ComplexEmbedding.conjugate (ty k) ≠ ty k' := by
    intro k k' hkk he
    have h1 := blk_isLeft hty k
    have h2 := blk_isLeft hty k'
    have h3 := conjugate_rt (H := H) (ty k)
    rw [he] at h3
    rw [hkk] at h1
    tauto
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set l : Fin g → ℂ := fun k => ((f (Pi.single k (1 : ℂ)) : ℝ) : ℂ) -
    Complex.I * ((f (Pi.single k Complex.I) : ℝ) : ℂ) with hl
  have hsingle : ∀ (k : Fin g) (z : ℂ), f (Pi.single k z) = (l k * z).re := by
    intro k z
    have hz : (Pi.single k z : Fin g → ℂ) =
        z.re • (Pi.single k (1 : ℂ) : Fin g → ℂ) + z.im • (Pi.single k Complex.I : Fin g → ℂ) := by
      ext j
      rcases eq_or_ne j k with rfl | hj
      · simp [Complex.ext_iff]
      · simp [hj]
    rw [hz, map_add, map_smul, map_smul]
    simp [hl, Complex.mul_re, smul_eq_mul] <;> ring
  have hf : ∀ v : Fin g → ℂ, f v = (∑ k, l k * v k).re := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum, Complex.re_sum]
    exact Finset.sum_congr rfl (fun k _ => hsingle k (v k))
  have hl0 : ∀ k0, l k0 = 0 := by
    intro k0
    set S := Finset.univ.filter (fun k => blk hty k = blk hty k0) with hS
    have hre : ∀ b : 𝓞 E, (∑ k ∈ S, l k * ty k (b : E)).re = 0 := by
      intro b
      have h1 : f (per hty c n (b • x (blk hty k0))) = 0 :=
        hle (Submodule.subset_span ⟨b • x (blk hty k0), rfl⟩)
      rw [hf] at h1
      simp only [per_bx hty x c n hn0 hcx, mul_ite, mul_zero] at h1
      rw [hS, Finset.sum_filter]
      exact h1
    set L : (E →+* ℂ) → ℂ := fun σ => ∑ k ∈ S, ((if ty k = σ then l k else 0) +
      (if ComplexEmbedding.conjugate (ty k) = σ then conj (l k) else 0)) with hL
    have hL0 : L = 0 := by
      apply emb_indep
      intro b
      have hterm : ∀ k, l k * ty k (b : E) + conj (l k) * conj (ty k (b : E)) =
          ((2 * (l k * ty k (b : E)).re : ℝ) : ℂ) := by
        intro k
        rw [← map_mul, Complex.add_conj]
      simp only [hL, Finset.sum_mul, add_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ComplexEmbedding.conjugate_coe_eq]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k _ => hterm k)]
      rw [← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, hre b]
      simp
    have h0 := congrFun hL0 (ty k0)
    simp only [hL, Pi.zero_apply] at h0
    rw [Finset.sum_eq_single k0] at h0
    · simpa [side k0 k0 rfl] using h0
    · intro k hk hne
      have hk' : blk hty k = blk hty k0 := by simpa [hS] using hk
      rw [if_neg (fun h => hne (blk_inj hty h hk')), if_neg (side k k0 hk'), add_zero]
    · intro h
      exact absurd (by simp [hS]) h
  apply hf0
  apply LinearMap.ext
  intro v
  rw [hf v]
  simp [hl0]

private theorem exists_blk_inl_of_rt_eq_rt0 (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (i : Fin p) :
    ∃ k, ty k = σ ∧ blk hty k = Sum.inl i := by
  refine ⟨((eP hty σ h).symm i).1, ((eP hty σ h).symm i).2, ?_⟩
  have key : ∀ (τ : E →+* ℂ), τ = σ → ∀ (h1 : τ (H.rt : E) = H.rt0) (a : {j : Fin g // ty j = τ}),
      (a : Fin g) = ((eP hty σ h).symm i).1 → eP hty τ h1 a = i := by
    rintro τ rfl h1 a ha
    have ha' : a = (eP hty τ h).symm i := Subtype.ext ha
    rw [ha']
    exact (eP hty τ h).apply_symm_apply i
  have hk := ((eP hty σ h).symm i).2
  unfold blk
  rw [dif_pos (by rw [hk]; exact h)]
  exact congrArg Sum.inl (key _ hk _ ⟨_, rfl⟩ rfl)

private theorem exists_blk_inr_of_rt_ne_rt0 (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (j : Fin q) :
    ∃ k, ty k = σ ∧ blk hty k = Sum.inr j := by
  refine ⟨((eQ hty σ h).symm j).1, ((eQ hty σ h).symm j).2, ?_⟩
  have key : ∀ (τ : E →+* ℂ), τ = σ → ∀ (h1 : τ (H.rt : E) ≠ H.rt0) (a : {i : Fin g // ty i = τ}),
      (a : Fin g) = ((eQ hty σ h).symm j).1 → eQ hty τ h1 a = j := by
    rintro τ rfl h1 a ha
    have ha' : a = (eQ hty τ h).symm j := Subtype.ext ha
    rw [ha']
    exact (eQ hty τ h).apply_symm_apply j
  have hk := ((eQ hty σ h).symm j).2
  unfold blk
  rw [dif_neg (by rw [hk]; exact h)]
  exact congrArg Sum.inr (key _ hk _ ⟨_, rfl⟩ rfl)

theorem per_discrete (hn0 : 0 < n) (hc : ∀ y, c y = 0 → y = 0) : DiscreteTopology (per hty c n).range := by
  have hrt0 : H.rt0 ≠ 0 := by
    intro h0
    have h := H.sqrt_neg_disc_sq
    rw [h0] at h
    have hd : (H.d : ℂ) = 0 := by linear_combination h
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have big : ∀ y : D.La, per hty c n y ≠ 0 → 1 / (n : ℝ) ≤ ‖per hty c n y‖ := by
    intro y hy
    have hcy : c y ≠ 0 := fun h => hy (by rw [hc y h, map_zero])
    obtain ⟨m, hm⟩ : ∃ m, c y m ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hcy (Finsupp.ext hcon)
    have hk : ∃ k, blk hty k = m ∧ 1 ≤ ‖ty k (c y m : E)‖ := by
      rcases m with i | j
      · obtain ⟨σ, hσ, hb⟩ := exists_big (H := H) (c y (Sum.inl i)) hm true
        simp only [if_true] at hσ
        obtain ⟨k, hk1, hk2⟩ := exists_blk_inl_of_rt_eq_rt0 hty σ hσ i
        exact ⟨k, hk2, by rw [hk1]; exact hb⟩
      · obtain ⟨σ, hσ, hb⟩ := exists_big (H := H) (c y (Sum.inr j)) hm false
        simp only [Bool.false_eq_true, if_false] at hσ
        have hne : σ (H.rt : E) ≠ H.rt0 := by
          rw [hσ]
          intro h
          apply hrt0
          linear_combination (-1 / 2 : ℂ) * h
        obtain ⟨k, hk1, hk2⟩ := exists_blk_inr_of_rt_ne_rt0 hty σ hne j
        exact ⟨k, hk2, by rw [hk1]; exact hb⟩
    obtain ⟨k, hk1, hk2⟩ := hk
    have hn : (0 : ℝ) < n := by exact_mod_cast hn0
    calc 1 / (n : ℝ) ≤ ‖ty k (c y m : E)‖ / n := by gcongr
      _ = ‖per hty c n y k‖ := by rw [per_apply, hk1, norm_div]; simp
      _ ≤ ‖per hty c n y‖ := norm_le_pi_norm _ k
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨1 / (n : ℝ), by positivity, fun z hz => ?_⟩
  obtain ⟨z, hzmem⟩ := z
  obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hzmem
  by_contra hne
  have hne' : per hty c n y ≠ 0 := fun h => hne (Subtype.ext h)
  have hb := big y hne'
  have hz' : ‖per hty c n y‖ < 1 / (n : ℝ) := by
    simpa [Subtype.dist_eq, dist_zero_right] using hz
  linarith

end PositivityTheory.Xgf.DPer

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)

def Hm : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k k' => if ty k = ty k' then 2 * Complex.I * ty k (G (blk hty k) (blk hty k')) else 0

def Q (σ : E →+* ℂ) (z w : Fin g → ℂ) : ℂ :=
  ∑ k : {k // ty k = σ}, ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k')

theorem herm_split (z w : Fin g → ℂ) : hermForm (Hm hty G) z w = ∑ σ, Q hty G σ z w := by
  have hF : ∀ σ : E →+* ℂ, ∀ k : {k // ty k = σ},
      ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k') =
      z k * (Hm hty G *ᵥ star w) k := by
    intro σ ⟨k, hk⟩
    simp only [mulVec, dotProduct, Pi.star_apply, RCLike.star_def]
    rw [Finset.mul_sum, ← Fintype.sum_subtype_add_sum_subtype (fun k' => ty k' = σ)]
    have h2 : ∑ k' : {k' // ¬ ty k' = σ}, z k * (Hm hty G k k' * conj (w k')) = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨k', hk'⟩ _
      have hne : ¬ ty k = ty k' := by
        rw [hk]
        exact fun h => hk' h.symm
      simp [Hm, hne]
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    rintro ⟨k', hk'⟩ _
    have heq : ty k = ty k' := hk.trans hk'.symm
    simp only [Hm, Matrix.of_apply, heq, if_true]
    rw [hk']
    ring
  unfold hermForm
  rw [dotProduct, ← Fintype.sum_fiberwise ty]
  apply Finset.sum_congr rfl
  intro σ _
  unfold Q
  apply Finset.sum_congr rfl
  intro k _
  exact (hF σ k).symm

theorem Q_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin p, ∑ b : Fin p, z ((eP hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inl a) (.inl b))) * conj (w ((eP hty σ h).symm b)) := by
  have hb : ∀ a : Fin p, blk hty ((eP hty σ h).symm a : Fin g) = Sum.inl a := by
    intro a
    rw [blk_inl hty σ h _ ((eP hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

theorem Q_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin q, ∑ b : Fin q, z ((eQ hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inr a) (.inr b))) * conj (w ((eQ hty σ h).symm b)) := by
  have hb : ∀ a : Fin q, blk hty ((eQ hty σ h).symm a : Fin g) = Sum.inr a := by
    intro a
    rw [blk_inr hty σ h _ ((eQ hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

end PositivityTheory.Xgf.DPer

end
end
