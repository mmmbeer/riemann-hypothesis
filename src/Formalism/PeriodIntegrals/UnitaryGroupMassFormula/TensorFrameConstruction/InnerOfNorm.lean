import Mathlib
import Formalism.PeriodIntegrals.ScPiExists

section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PI.ScPiBuildW.Loc

open PI.ScPiExists

section Basic

variable {n : ℕ} (ε : Fin n → Bool)

lemma hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  first | simp only [hJ, star_add, add_dotProduct] | simp [hJ, add_dotProduct]

lemma hJ_add_right (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  first | simp only [hJ, Matrix.mulVec_add, dotProduct_add] | simp [hJ, Matrix.mulVec_add, dotProduct_add]

lemma hJ_sub_left (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  first | simp only [hJ, star_sub, sub_dotProduct] | simp [hJ, sub_dotProduct]

lemma hJ_sub_right (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  first | simp only [hJ, Matrix.mulVec_sub, dotProduct_sub] | simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

lemma hJ_smul_left (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  first | simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul] | simp [hJ, smul_dotProduct]

lemma hJ_smul_right (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  first | simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] | simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

lemma hJ_zero_left (y : Fin n → ℂ) : hJ ε 0 y = 0 := by
  simp [hJ]

lemma hJ_zero_right (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

lemma hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (u : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * hJ ε x (u i) := by
  classical
  refine Finset.induction_on s (by simp [hJ_zero_right]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_right, hJ_smul_right, ih]

lemma hJ_conj (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

lemma hJ_nondeg_right (y : Fin n → ℂ) (h : ∀ x, hJ ε x y = 0) : y = 0 := by
  funext i
  have h1 := h (Pi.single i (1 : ℂ))
  have hs : star (Pi.single i (1 : ℂ) : Fin n → ℂ) = (Pi.single i 1 : Fin n → ℂ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  have e : hJ ε (Pi.single i 1) y = (if ε i then 1 else -1) * y i := by
    first
      | rw [hJ, hs, single_dotProduct, one_mul, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
      | rw [hJ, hs, Matrix.single_dotProduct, one_mul, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
      | simp [hJ, hs, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  rw [e] at h1
  simp only [Pi.zero_apply]
  split_ifs at h1 <;> simpa using h1


lemma hJ_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  simp only [hJ]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

lemma hJ_span_left {S : Set (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ Submodule.span ℂ S)
    (h : ∀ a ∈ S, hJ ε a y = 0) : hJ ε x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => exact hJ_zero_left ε y
  | add a b _ _ ha hb => rw [hJ_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hJ_smul_left, ha, mul_zero]

lemma hJ_span_right {S : Set (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ Submodule.span ℂ S)
    (h : ∀ a ∈ S, hJ ε y a = 0) : hJ ε y x = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => exact hJ_zero_right ε y
  | add a b _ _ ha hb => rw [hJ_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [hJ_smul_right, ha, mul_zero]

end Basic

structure LocFrame (n r k : ℕ) (ε : Fin n → Bool) where
  e : Fin r → Fin n → ℂ
  f : Fin r → Fin n → ℂ
  z : Fin n → ℂ
  w : Fin k → Fin n → ℂ
  hn : n = 2 * r + k + 1
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z ≠ 0
  ww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0
  ew : ∀ c a, hJ ε (e c) (w a) = 0
  fw : ∀ c a, hJ ε (f c) (w a) = 0
  zw : ∀ a, hJ ε z (w a) = 0

namespace LocFrame

variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)

lemma fe (b a : Fin r) : hJ ε (L.f b) (L.e a) = if a = b then 1 else 0 := by
  rw [hJ_conj, L.ef]
  split_ifs <;> simp

lemma we (c : Fin k) (a : Fin r) : hJ ε (L.w c) (L.e a) = 0 := by
  rw [hJ_conj, L.ew, star_zero]

lemma wf (c : Fin k) (a : Fin r) : hJ ε (L.w c) (L.f a) = 0 := by
  rw [hJ_conj, L.fw, star_zero]

lemma wz (c : Fin k) : hJ ε (L.w c) L.z = 0 := by
  rw [hJ_conj, L.zw, star_zero]

lemma ze (a : Fin r) : hJ ε L.z (L.e a) = 0 := by
  rw [hJ_conj, L.ez, star_zero]

lemma zf (a : Fin r) : hJ ε L.z (L.f a) = 0 := by
  rw [hJ_conj, L.fz, star_zero]

def fam : (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k) → Fin n → ℂ :=
  Sum.elim (Sum.elim L.e L.f) (Sum.elim (fun _ => L.z) L.w)

lemma pair (x : Fin n → ℂ) (g : (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k) → ℂ) :
    hJ ε x (∑ i, g i • L.fam i) =
      (∑ a, g (.inl (.inl a)) * hJ ε x (L.e a)) + (∑ a, g (.inl (.inr a)) * hJ ε x (L.f a)) +
        (g (.inr (.inl ())) * hJ ε x L.z + ∑ c, g (.inr (.inr c)) * hJ ε x (L.w c)) := by
  rw [hJ_sum_right]
  simp only [Fintype.sum_sum_type, fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  all_goals rfl

lemma fam_li : LinearIndependent ℂ L.fam := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ x, (∑ a, g (.inl (.inl a)) * hJ ε x (L.e a)) + (∑ a, g (.inl (.inr a)) * hJ ε x (L.f a)) +
      (g (.inr (.inl ())) * hJ ε x L.z + ∑ c, g (.inr (.inr c)) * hJ ε x (L.w c)) = 0 := fun x => by
    rw [← L.pair x g, hg, hJ_zero_right]
  have hf : ∀ b, g (.inl (.inr b)) = 0 := fun b => by
    have := key (L.e b)
    simpa [L.ee, L.ef, L.ez, L.ew] using this
  have hz : g (.inr (.inl ())) = 0 := by
    have := key L.z
    have h2 : g (.inr (.inl ())) * hJ ε L.z L.z = 0 := by simpa [L.ze, L.zf, L.zw] using this
    exact (mul_eq_zero.mp h2).resolve_right L.zz
  have hw : ∀ c, g (.inr (.inr c)) = 0 := fun c => by
    have := key (L.w c)
    simpa [L.we, L.wf, L.wz, L.ww] using this
  have he : ∀ b, g (.inl (.inl b)) = 0 := fun b => by
    have := key (L.f b)
    simpa [L.fe, hf, hz, hw] using this
  rintro ((a | a) | (⟨⟩ | c))
  · exact he a
  · exact hf a
  · exact hz
  · exact hw c

lemma fam_span : Submodule.span ℂ (Set.range L.fam) = ⊤ := by
  apply L.fam_li.span_eq_top_of_card_eq_finrank
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, Module.finrank_fin_fun]
  rw [L.hn]
  ring

lemma orth_zero (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hf : ∀ a, hJ ε (L.f a) y = 0)
    (hz : hJ ε L.z y = 0) (hw : ∀ c, hJ ε (L.w c) y = 0) : y = 0 := by
  apply hJ_nondeg_right ε y
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range L.fam) := by
    rw [L.fam_span]
    trivial
  apply hJ_span_left ε hx
  rintro _ ⟨((a | a) | (⟨⟩ | c)), rfl⟩
  · exact he a
  · exact hf a
  · exact hz
  · exact hw c

lemma decomp (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    y = ∑ c, hJ ε (L.w c) y • L.w c + ∑ a, hJ ε (L.f a) y • L.e a := by
  suffices h : y - (∑ c, hJ ε (L.w c) y • L.w c + ∑ a, hJ ε (L.f a) y • L.e a) = 0 from
    sub_eq_zero.mp h
  apply L.orth_zero
  · intro b
    rw [hJ_sub_right, he b, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.ew, L.ee]
  · intro b
    rw [hJ_sub_right, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.fw, L.fe]
  · rw [hJ_sub_right, hz, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.zw, L.ze]
  · intro d
    rw [hJ_sub_right, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.ww, L.we]

abbrev X : Submodule ℂ (Fin n → ℂ) := spanLt L.e r

lemma e_mem (a : Fin r) : L.e a ∈ L.X :=
  Submodule.subset_span ⟨a, a.isLt, rfl⟩

lemma spanLt_le (a : ℕ) (ha : a ≤ r) : spanLt L.e a ≤ L.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.isLt)

lemma hJ_X_left {x y : Fin n → ℂ} (hx : x ∈ L.X) (h : ∀ a, hJ ε (L.e a) y = 0) : hJ ε x y = 0 :=
  hJ_span_left ε (S := L.e '' {b | b.1 < r}) hx (by rintro _ ⟨a, _, rfl⟩; exact h a)

lemma hJ_X_right {x y : Fin n → ℂ} (hx : x ∈ L.X) (h : ∀ a, hJ ε y (L.e a) = 0) : hJ ε y x = 0 :=
  hJ_span_right ε (S := L.e '' {b | b.1 < r}) hx (by rintro _ ⟨a, _, rfl⟩; exact h a)

section Grp

variable {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
include hg hS

omit hg in
lemma gX {x : Fin n → ℂ} (hx : x ∈ L.X) : g *ᵥ x ∈ L.X := by
  have key : ∀ a : Fin r, g *ᵥ L.e a ∈ L.X := fun a => by
    have h1 : g *ᵥ L.e a = L.e a + (g - 1) *ᵥ L.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [h1]
    exact L.X.add_mem (L.e_mem a) (L.spanLt_le a.1 a.isLt.le (hS.1 a))
  have hx' : x ∈ Submodule.span ℂ (L.e '' {b | b.1 < r}) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, _, rfl⟩ := hv
    exact key a
  | zero =>
    rw [Matrix.mulVec_zero]
    exact L.X.zero_mem
  | add u v _ _ hu hv =>
    rw [Matrix.mulVec_add]
    exact L.X.add_mem hu hv
  | smul c u _ hu =>
    rw [Matrix.mulVec_smul]
    exact L.X.smul_mem c hu

omit hS in
lemma g_inj {x : Fin n → ℂ} (hx : g *ᵥ x = 0) : x = 0 :=
  hJ_nondeg_right ε x fun x' => by rw [← hJ_unitary ε hg x' x, hx, hJ_zero_right]

lemma g_surj {x : Fin n → ℂ} (hx : x ∈ L.X) : ∃ x' ∈ L.X, g *ᵥ x' = x := by
  let f : L.X →ₗ[ℂ] L.X := (Matrix.mulVecLin g).restrict (fun v hv => L.gX hS hv)
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : g *ᵥ ((u : Fin n → ℂ) - v) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact congrArg Subtype.val huv
    exact Subtype.ext (sub_eq_zero.mp (g_inj hg h1))
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

lemma g_perp {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (a : Fin r) : hJ ε (L.e a) (g *ᵥ y) = 0 := by
  obtain ⟨x', hx', hgx⟩ := L.g_surj hg hS (L.e_mem a)
  rw [← hgx, hJ_unitary ε hg]
  exact L.hJ_X_left hx' hy

lemma local_frame_preserves_orthogonal {y : Fin n → ℂ} (hy : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    hJ ε L.z (g *ᵥ y) = 0 := by
  have h1 : g *ᵥ L.z = L.z + (g - 1) *ᵥ L.z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have h2 : hJ ε (g *ᵥ L.z) (g *ᵥ y) = 0 := by rw [hJ_unitary ε hg, hz]
  rw [h1, hJ_add_left, L.hJ_X_left hS.2 (L.g_perp hg hS hy), add_zero] at h2
  exact h2

end Grp

def M (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => hJ ε (L.w a) (g *ᵥ L.w b)

lemma gw_decomp {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) (b : Fin k) :
    g *ᵥ L.w b = ∑ c, L.M g c b • L.w c + ∑ a, hJ ε (L.f a) (g *ᵥ L.w b) • L.e a :=
  L.decomp _ (L.g_perp hg hS fun a => L.ew a b) (L.local_frame_preserves_orthogonal hg hS (fun a => L.ew a b) (L.zw b))

private lemma mulVec_sum_lemma {ι : Type*} (s : Finset ι) (g : Matrix (Fin n) (Fin n) ℂ) (c : ι → ℂ)
    (u : ι → Fin n → ℂ) : g *ᵥ (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i • (g *ᵥ u i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, Matrix.mulVec_smul, ih]

lemma M_mul {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
    (hg' : Formalism.REAL.inUJ ε g') (hS' : InS L.e L.z g') : L.M (g * g') = L.M g * L.M g' := by
  ext c b
  have hXr : ∀ a, hJ ε (L.w c) (g *ᵥ L.e a) = 0 := fun a =>
    L.hJ_X_right (L.gX hS (L.e_mem a)) (fun a' => L.we c a')
  have e1 : L.M (g * g') c b = hJ ε (L.w c) (g *ᵥ (g' *ᵥ L.w b)) := by
    show hJ ε (L.w c) ((g * g') *ᵥ L.w b) = _
    rw [Matrix.mulVec_mulVec]
  rw [e1, L.gw_decomp hg' hS' b, Matrix.mulVec_add, hJ_add_right, mulVec_sum_lemma, mulVec_sum_lemma,
    hJ_sum_right, hJ_sum_right]
  simp only [hXr, mul_zero, Finset.sum_const_zero, add_zero, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm]
  rfl

private lemma hJ_sum_left_lemma_2 {ι : Type*} (s : Finset ι) (y : Fin n → ℂ) (c : ι → ℂ)
    (u : ι → Fin n → ℂ) : hJ ε (∑ i ∈ s, c i • u i) y = ∑ i ∈ s, star (c i) * hJ ε (u i) y := by
  classical
  refine Finset.induction_on s (by simp [hJ_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_left, hJ_smul_left, ih]

lemma M_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) :
    (L.M g)ᴴ * L.M g = 1 := by
  ext a b
  have h1 : hJ ε (g *ᵥ L.w a) (g *ᵥ L.w b) = if a = b then 1 else 0 := by
    rw [hJ_unitary ε hg, L.ww]
  rw [L.gw_decomp hg hS a, hJ_add_left, hJ_sum_left_lemma_2, hJ_sum_left_lemma_2] at h1
  simp only [L.g_perp hg hS (fun a' => L.ew a' b), mul_zero, Finset.sum_const_zero, add_zero] at h1
  rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.conjTranspose_apply]
  rfl

lemma M_N {g : Matrix (Fin n) (Fin n) ℂ} (hN : InN ε L.e L.z g) : L.M g = 1 := by
  ext c b
  have hx := hN.2 (L.w b) (fun a => L.ew a b)
  have h1 : g *ᵥ L.w b = L.w b + (g - 1) *ᵥ L.w b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  show hJ ε (L.w c) (g *ᵥ L.w b) = (1 : Matrix (Fin k) (Fin k) ℂ) c b
  rw [h1, hJ_add_right, L.ww, L.hJ_X_right hx (fun a => L.we c a), add_zero, Matrix.one_apply]

lemma M_one : L.M 1 = 1 := by
  ext a b
  show hJ ε (L.w a) ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ L.w b) = (1 : Matrix (Fin k) (Fin k) ℂ) a b
  rw [Matrix.one_mulVec, L.ww, Matrix.one_apply]

lemma M_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) :
    L.M g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k) := by
  have hJ1 : PI.UpqRep.Jm (PI.UpqRep.allPos k) = 1 := by
    ext a b
    simp [PI.UpqRep.Jm, PI.UpqRep.allPos, Matrix.diagonal_apply, Matrix.one_apply]
  show (L.M g)ᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) * L.M g = PI.UpqRep.Jm (PI.UpqRep.allPos k)
  rw [hJ1, Matrix.mul_one, L.M_unitary hg hS]

end LocFrame

end PI.ScPiBuildW.Loc
end
end

section
noncomputable section

open Matrix NumberField

namespace PI.ScPiBuildW.Rv

open PI.ScPiExists

lemma phi_star (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (a : I.E) :
    I.φ v (star a) = star (I.φ v a) := by
  exact I.cm.cmUnram.2.1 (I.φ v) a

lemma hJ_rv (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hJm : Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = (I.P v)ᴴ * I.J.map (I.φ v) := by
    rw [← I.P_spec v, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  have hPP : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
  set u : Fin I.n → ℂ := fun i => I.φ v (x i)
  set w : Fin I.n → ℂ := fun i => I.φ v (y i)
  have key : hJ (I.ε v) (rv I v x) (rv I v y) = star u ⬝ᵥ (I.J.map (I.φ v) *ᵥ w) := by
    unfold hJ rv
    rw [Matrix.mulVec_mulVec, hJm, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  rw [key]
  simp only [u, w, Formalism.UG.hform, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
    Pi.star_apply, Finset.mul_sum, starRingEnd_apply, phi_star, mul_assoc]

lemma phi_ite (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {r : ℕ} (a b : Fin r) :
    I.φ v (if a = b then (1 : I.E) else 0) = if a = b then 1 else 0 := by
  split_ifs <;> simp

def locFrame (I : Formalism.MainNotions.S.AutInst) {r k : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (hn : I.n = 2 * r + k + 1) (hF : IsFrame I e f z)
    (hz : Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0) (v : InfinitePlace I.F) (w : Fin k → Fin I.n → ℂ)
    (hw : (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0) :
    Loc.LocFrame I.n r k (I.ε v) where
  e := fun a => rv I v (e a)
  f := fun a => rv I v (f a)
  z := rv I v z
  w := w
  hn := hn
  ee := fun a b => by rw [hJ_rv, hF.1 a b, map_zero]
  ef := fun a b => by rw [hJ_rv, hF.2.2.1 a b, phi_ite]
  ez := fun a => by rw [hJ_rv, (hF.2.2.2 a).1, map_zero]
  fz := fun a => by rw [hJ_rv, (hF.2.2.2 a).2, map_zero]
  zz := by rw [hJ_rv]; exact (map_ne_zero (I.φ v)).2 hz
  ww := hw.1
  ew := fun c a => ((hw.2 a).1 c).1
  fw := fun c a => ((hw.2 a).1 c).2
  zw := fun a => (hw.2 a).2

section Simp

variable (I : Formalism.MainNotions.S.AutInst) {r k : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
  (hn : I.n = 2 * r + k + 1) (hF : IsFrame I e f z)
  (hz : Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0) (v : InfinitePlace I.F) (w : Fin k → Fin I.n → ℂ)
  (hw : (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0)

@[simp] lemma locFrame_e : (locFrame I e f z hn hF hz v w hw).e = fun a => rv I v (e a) := rfl
@[simp] lemma locFrame_f : (locFrame I e f z hn hF hz v w hw).f = fun a => rv I v (f a) := rfl
@[simp] lemma locFrame_z : (locFrame I e f z hn hF hz v w hw).z = rv I v z := rfl
@[simp] lemma locFrame_w : (locFrame I e f z hn hF hz v w hw).w = w := rfl

end Simp

end PI.ScPiBuildW.Rv
end
end

section
noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Module

namespace PI.ScPiBuildW.Tens

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Idx (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)] : Type :=
  ∀ i, Fin (finrank ℂ (Vl i))

abbrev TV (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)] : Type :=
  EuclideanSpace ℂ (Idx Vl)

variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]

def bas (Vl : ι → Type) [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
    [∀ i, FiniteDimensional ℂ (Vl i)] (i : ι) : OrthonormalBasis (Fin (finrank ℂ (Vl i))) ℂ (Vl i) :=
  stdOrthonormalBasis ℂ (Vl i)

def tensU (x : ∀ i, Vl i) : TV Vl :=
  WithLp.toLp 2 (fun p : Idx Vl => ∏ i, ⟪bas Vl i (p i), x i⟫_ℂ)

theorem tensU_apply (x : ∀ i, Vl i) (p : Idx Vl) : tensU x p = ∏ i, ⟪bas Vl i (p i), x i⟫_ℂ := rfl

theorem prod_sum_pi {κ : ι → Type} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    ∏ i, ∑ j, f i j = ∑ p : (∀ i, κ i), ∏ i, f i (p i) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem inner_tensU (x y : ∀ i, Vl i) : ⟪tensU x, tensU y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [tensU_apply, RCLike.inner_apply, map_prod]
  have h : ∀ i, ⟪x i, y i⟫_ℂ = ∑ j, (starRingEnd ℂ) ⟪bas Vl i j, x i⟫_ℂ * ⟪bas Vl i j, y i⟫_ℂ := by
    intro i
    rw [← (bas Vl i).sum_inner_mul_inner (x i) (y i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]
  simp_rw [h, prod_sum_pi, ← Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem tensU_basis (p : Idx Vl) : tensU (fun i => bas Vl i (p i)) = EuclideanSpace.single p 1 := by
  ext q
  rw [tensU_apply, PiLp.single_apply]
  by_cases hqp : q = p
  · subst hqp
    simp only [if_true]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K, (bas Vl i).orthonormal.1 (q i)]
    simp
  · rw [if_neg hqp]
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ p i := by
      by_contra hne
      push Not at hne
      exact hqp (funext hne)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    exact (bas Vl i).orthonormal.2 hi

theorem span_tensU : Submodule.span ℂ (Set.range (tensU (Vl := Vl))) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (EuclideanSpace.basisFun (Idx Vl) ℂ).toBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨p, rfl⟩
  refine ⟨fun i => bas Vl i (p i), ?_⟩
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, tensU_basis]

theorem eq_of_inner_tensU {v v' : TV Vl} (h : ∀ x, ⟪tensU x, v⟫_ℂ = ⟪tensU x, v'⟫_ℂ) : v = v' := by
  have hd : ∀ x, ⟪v - v', tensU x⟫_ℂ = 0 := fun x => by
    rw [← inner_conj_symm, inner_sub_right, h x, sub_self, map_zero]
  have h0 : (innerSL ℂ (v - v')).toLinearMap = 0 :=
    LinearMap.ext_on_range span_tensU (fun x => by simpa using hd x)
  have h2 : ⟪v - v', v - v'⟫_ℂ = 0 := by
    have := LinearMap.congr_fun h0 (v - v')
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, LinearMap.zero_apply] at this
    exact this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h2)

theorem clm_ext {T T' : TV Vl →L[ℂ] TV Vl} (h : ∀ x, T (tensU x) = T' (tensU x)) : T = T' :=
  ContinuousLinearMap.coe_inj.1 (LinearMap.ext_on_range span_tensU h)

def opMat (A : ∀ i, Vl i →L[ℂ] Vl i) : Matrix (Idx Vl) (Idx Vl) ℂ :=
  fun p q => ∏ i, ⟪bas Vl i (p i), A i (bas Vl i (q i))⟫_ℂ

def tensOp (A : ∀ i, Vl i →L[ℂ] Vl i) : TV Vl →L[ℂ] TV Vl :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (opMat A))

theorem tensOp_apply (A : ∀ i, Vl i →L[ℂ] Vl i) (v : TV Vl) (p : Idx Vl) :
    tensOp A v p = ∑ q, opMat A p q * v q := by
  simp only [tensOp, LinearMap.coe_toContinuousLinearMap']
  rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem sum_inner_op {V' : Type} [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (A : V' →L[ℂ] V')
    {m : Type} [Fintype m] (b : OrthonormalBasis m ℂ V') (u x : V') :
    ∑ j, ⟪u, A (b j)⟫_ℂ * ⟪b j, x⟫_ℂ = ⟪u, A x⟫_ℂ := by
  conv_rhs => rw [← b.sum_repr' x]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]

theorem tensOp_tensU (A : ∀ i, Vl i →L[ℂ] Vl i) (x : ∀ i, Vl i) :
    tensOp A (tensU x) = tensU (fun i => A i (x i)) := by
  ext p
  rw [tensOp_apply, tensU_apply]
  simp only [opMat, tensU_apply, ← Finset.prod_mul_distrib]
  rw [← prod_sum_pi (fun i j => ⟪bas Vl i (p i), A i (bas Vl i j)⟫_ℂ * ⟪bas Vl i j, x i⟫_ℂ)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact sum_inner_op (A i) (bas Vl i) _ _

theorem tensOp_one : tensOp (fun i => (1 : Vl i →L[ℂ] Vl i)) = 1 :=
  clm_ext fun x => by rw [tensOp_tensU]; rfl

theorem tensOp_mul (A B : ∀ i, Vl i →L[ℂ] Vl i) :
    tensOp (fun i => A i * B i) = tensOp A * tensOp B :=
  clm_ext fun x => by
    rw [ContinuousLinearMap.mul_apply, tensOp_tensU, tensOp_tensU, tensOp_tensU]
    rfl

theorem inner_tensOp (A : ∀ i, Vl i →L[ℂ] Vl i) (hA : ∀ i (u w : Vl i), ⟪A i u, A i w⟫_ℂ = ⟪u, w⟫_ℂ)
    (u w : TV Vl) : ⟪tensOp A u, tensOp A w⟫_ℂ = ⟪u, w⟫_ℂ := by
  have hQ : (ContinuousLinearMap.adjoint (tensOp A)) * tensOp A = 1 := clm_ext fun y => by
    refine eq_of_inner_tensU fun x => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right, tensOp_tensU,
      tensOp_tensU, ContinuousLinearMap.one_apply, inner_tensU, inner_tensU]
    exact Finset.prod_congr rfl fun i _ => hA i (x i) (y i)
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply, hQ,
    ContinuousLinearMap.one_apply]

theorem continuousOn_tensOp {X : Type*} [TopologicalSpace X] (A : X → ∀ i, Vl i →L[ℂ] Vl i) (S : Set X)
    (hA : ∀ i (y : Vl i), ContinuousOn (fun s => A s i y) S) (v : TV Vl) :
    ContinuousOn (fun s => tensOp (A s) v) S := by
  have hrep : (fun s => tensOp (A s) v) =
      fun s => ∑ p, (tensOp (A s) v p) • EuclideanSpace.basisFun (Idx Vl) ℂ p := by
    funext s
    conv_lhs => rw [← (EuclideanSpace.basisFun (Idx Vl) ℂ).sum_repr' (tensOp (A s) v)]
    simp only [EuclideanSpace.basisFun_inner]
  rw [hrep]
  refine continuousOn_finsetSum _ fun p _ =>
    (show ContinuousOn (fun s => tensOp (A s) v p) S from ?_).smul continuousOn_const
  simp only [tensOp_apply]
  refine continuousOn_finsetSum _ fun q _ =>
    (show ContinuousOn (fun s => opMat (A s) p q) S from ?_).mul continuousOn_const
  simp only [opMat]
  refine continuousOn_finsetProd _ fun i _ => ?_
  exact ContinuousOn.inner continuousOn_const (hA i _)

end PI.ScPiBuildW.Tens
end
end

section
noncomputable section

open NumberField Matrix
open scoped InnerProductSpace

namespace PI.ScPiBuildW.Asm

open PI.ScPiExists Formalism.MainNotions.S

lemma inner_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (u w : H) : ⟪T u, T w⟫_ℂ = ⟪u, w⟫_ℂ :=
  (⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map u w

lemma uMat_one (I : AutInst) (v : InfinitePlace I.F) : uMat ((1 : I.Ginf) v) = 1 := rfl

lemma uMat_mul (I : AutInst) (s t : I.Ginf) (v : InfinitePlace I.F) :
    uMat ((s * t) v) = uMat (s v) * uMat (t v) := rfl

lemma inUJ_uMat (I : AutInst) (s : I.Ginf) (v : InfinitePlace I.F) : Formalism.REAL.inUJ (I.ε v) (uMat (s v)) :=
  (s v).2

lemma cont_uMat (I : AutInst) (v : InfinitePlace I.F) : Continuous fun s : I.Ginf => uMat (s v) :=
  Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))

theorem build : Build := by
  intro hW I r k e f z lam hn hF hz hlam hw
  classical
  choose w hw using hw
  choose H hHN hHI pl hπ using fun v => hW k (lam v) (hlam v)
  let _ := hHN
  let _ := hHI
  have hHF : ∀ v, FiniteDimensional ℂ (H v) := fun v => (hπ v).2.1
  let L : ∀ v, Loc.LocFrame I.n r k (I.ε v) := fun v => Rv.locFrame I e f z hn hF hz v (w v) (hw v)
  let A : I.Ginf → ∀ v, H v →L[ℂ] H v := fun s v => pl v ((L v).M (uMat (s v)))
  have hA1 : A 1 = fun _ => 1 := by
    funext v
    simp only [A]
    rw [uMat_one, Loc.LocFrame.M_one]
    exact (hπ v).2.2.1.1.1
  refine ⟨{
      Vpi := Tens.TV H
      piU := fun s => Tens.tensOp (A s)
      piU_rep := ?_
      Vloc := H
      piLoc := pl
      piLoc_type := hπ
      wfr := w
      wfr_on := fun v => (hw v).1
      wfr_perp := fun v => (hw v).2
      tensU := Tens.tensU
      tensU_inner := Tens.inner_tensU
      tensU_span := Tens.span_tensU
      tensU_equiv := fun s _ x => Tens.tensOp_tensU (A s) x }⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Tens.tensOp (A 1) = 1
    rw [hA1]
    exact Tens.tensOp_one
  · intro s hs t ht
    show Tens.tensOp (A (s * t)) = Tens.tensOp (A s) * Tens.tensOp (A t)
    rw [← Tens.tensOp_mul]
    congr 1
    funext v
    simp only [A]
    rw [uMat_mul, (L v).M_mul (inUJ_uMat I s v) (hs v) (inUJ_uMat I t v) (ht v)]
    exact (hπ v).2.2.1.1.2 _ ((L v).M_inUJ (inUJ_uMat I s v) (hs v)) _
      ((L v).M_inUJ (inUJ_uMat I t v) (ht v))
  · intro s hs x y
    exact Tens.inner_tensOp (A s) (fun v u u' => inner_of_norm _
      (fun y => (hπ v).2.2.1.2.1 _ ((L v).M_inUJ (inUJ_uMat I s v) (hs v)) y) u u') x y
  · intro s hs
    show Tens.tensOp (A s) = 1
    have : A s = fun _ => 1 := by
      funext v
      simp only [A]
      rw [(L v).M_N (hs v)]
      exact (hπ v).2.2.1.1.1
    rw [this]
    exact Tens.tensOp_one
  · intro x
    refine Tens.continuousOn_tensOp A (Sinf I e z) (fun v y => ?_) x
    have hc : Continuous fun s : I.Ginf => (L v).M (uMat (s v)) := by
      apply continuous_pi
      intro a
      apply continuous_pi
      intro b
      simp only [Loc.LocFrame.M, hJ]
      exact continuous_const.dotProduct
        (continuous_const.matrix_mulVec ((cont_uMat I v).matrix_mulVec continuous_const))
    exact ((hπ v).2.2.1.2.2 y).comp hc.continuousOn
      (fun s hs => (L v).M_inUJ (inUJ_uMat I s v) (hs v))

end PI.ScPiBuildW.Asm
end
end
