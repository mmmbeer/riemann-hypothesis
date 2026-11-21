import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetZhatSwapUnit

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T2CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ClaimRL (M : Model F E) (r n : ℕ) : Prop := M.split = none → ClaimR M r n

def ClaimRG (M : Model F E) (r n : ℕ) : Prop := M.split.isSome = true → ClaimR M r n

theorem claimR_of_modes (M : Model F E) (r n : ℕ) (hL : ClaimRL M r n) (hG : ClaimRG M r n) :
    ClaimR M r n := by
  rcases hs : M.split with _ | g
  · exact hL hs
  · exact hG (by rw [hs]; rfl)

theorem X_le_span_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩)

theorem X_le_span_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f' ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inr j.castSucc, rfl⟩)

theorem surj_MMsharp (M : Model F E) (hM : M.OK) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {r : ℕ} (t : Term V M r) (hgen : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    ∀ m : ↥(MMsharp H t), ∃ w : ↥(H.W0 t.f t.f'), (m : V) + w ∈ t.abelian₂ := by
  intro m
  have hU' : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam]
    exact hU
  have hmU : (m : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := spanMM_le_U H t m.2.1
  obtain ⟨x, hx, hpx⟩ := ((local_hermitian_glue F E M hM V H t.abelian₂ hgen.1.1 _ hU').1 (m : V) hmU).2
    (fun y hy hyU => m.2.2 y (hgen.2.2.2 y hy (span_frames_le_MM H t hyU)))
  have hx' : x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) ⊔
      H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f'))) := by
    rw [hU'.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
  have hpa : ((Submodule.linearProjOfIsCompl _ _ hU' x :
      ↥(Submodule.span E (Set.range (Sum.elim t.f t.f')))) : V) = a := by
    rw [← hab, map_add]
    have e1 := Submodule.projectionOnto_apply_left hU' ⟨a, ha⟩
    have e2 := Submodule.projectionOnto_apply_right hU' ⟨b, hb⟩
    simp only [Submodule.linearProjOfIsCompl] at *
    rw [e1, e2, add_zero]
  have hma : (m : V) = a := by rw [← hpx, hpa]
  have hbW : b ∈ H.W0 t.f t.f' := by rw [hermSp_W0_eq_perp_span_range_MMfam]; exact hb
  refine ⟨⟨b, hbW⟩, ?_⟩
  show (m : V) + b ∈ t.abelian₂
  rw [hma, hab]
  exact hx

theorem claimRL_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRL M r n := by
  intro hs V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hMM₁ : MMo H t₁ ≤ t₁.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
  have hMM₂ : MMo H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) ≤ Λ₂ :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
  have hth' : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂ :=
    fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
  have hθ' : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂ := by
    intro m₁ m₂
    rw [hθ m₁ m₂]
    constructor
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
      exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
    · rintro ⟨w, h1, h2⟩
      exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩
  have hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁

  have hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₁
  have hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₂
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  have hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')), ∃ hu' : u' ∈ H.perp (H.X f₂'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW f₂' ⟨u', hu'⟩ := by
    intro v hv hvp
    rw [← U_swap] at hv
    obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
    rw [U_swap] at hv'
    exact ⟨v', hv', hv'p, e⟩
  have hL := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f f₂ (X_le_span_left H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) φ hC1 hC2
  have hL' := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f' f₂' (X_le_span_right H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) φ' hC1' hC2'
  constructor
  · intro hR
    refine ⟨fun _ => ⟨hL.1 hR.1, hL'.1 hR.2.2.1⟩, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)
  · rintro ⟨h1, -⟩
    obtain ⟨a, b⟩ := h1 hs
    refine ⟨hL.2 a, hyp.2.2.2.2.1, hL'.2 b, hyp.2.2.2.2.2, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)

end T2CR

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem hR_add (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm z x]

theorem hR_smul (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem hR_zero (x : V) : H.h x 0 = 0 := by
  have h0 : H.h 0 x = 0 := by
    have h1 := H.h_smul_left 0 0 x
    rwa [zero_smul, zero_mul] at h1
  rw [H.h_herm 0 x, h0, map_zero]

theorem hR_sub (x y z : V) : H.h x (y - z) = H.h x y - H.h x z := by
  rw [sub_eq_add_neg, ← neg_one_smul E z, hR_add, hR_smul, map_neg, map_one]
  ring

theorem q_ne (g : SplitG M.L) : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)

theorem q_mem_O (g : SplitG M.L) : algebraMap F E (g.q : F) ∈ M.L.O := by
  rw [M.L.O_def]
  have h1 : algebraMap F E (g.q : F) = algebraMap 𝒪[F] E g.q := (IsScalarTower.algebraMap_apply 𝒪[F] F E g.q).symm
  rw [h1]
  exact isIntegral_algebraMap

theorem cj_q (g : SplitG M.L) : M.L.cj (algebraMap F E (g.q : F)) = algebraMap F E (g.q : F) :=
  M.L.cj.commutes _

theorem gramMM_unit_of_term (t : Term V M r) (hT : H.IsTerm t) : IsUnit (H.gram (H.MMfam t)).det := by
  have hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T := ⟨hT.2.1.2.1, hT.2.1.2.2.1⟩
  have hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' := ⟨hT.2.2.1.2.1, hT.2.2.1.2.2.1⟩
  have hD : IsUnit (H.Dl t.f t.f' (r + 1)) := hT.2.2.2.1
  have hG : IsUnit (H.Gdet t.f t.f' t.T t.T') := isUnit_Gdet H _ _ _ _ hT.2.2.2.2.1
  obtain ⟨s, hs, hdet⟩ := gram_det H t.f t.f' t.T t.T' hF hF' hD
  have hgu : IsUnit (H.gram (Sum.elim t.f t.f')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim t.f t.f')).det = H.Gdet t.f t.f' t.T t.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam t = Sum.elim t.f t.f' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) (q_ne g))⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam t = Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) = fun j => ∑ i, A i j • Sum.elim t.f t.f' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

theorem exists_dual {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hG : IsUnit (H.gram v).det)
    (d : ι → E) : ∃ u ∈ Submodule.span E (Set.range v), ∀ i, H.h u (v i) = d i := by
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V), H.h (∑ j ∈ s, c j • v j) y = ∑ j ∈ s, c j * H.h (v j) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [H.h_zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, H.h_add_left, H.h_smul_left, ih]
  refine ⟨∑ j, ((H.gram v)⁻¹ *ᵥ d) j • v j, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩), fun i => ?_⟩
  rw [hsum]
  have h1 : (H.gram v *ᵥ ((H.gram v)⁻¹ *ᵥ d)) i = d i := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  rw [← h1]
  simp only [Matrix.mulVec, dotProduct, Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mem_MMsharp_of (t : Term V M r) {u : V} (hu : u ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hd : ∀ i, H.h u (H.MMfam t i) ∈ M.L.O) : u ∈ MMsharp H t := by
  have hcj : ∀ c ∈ M.L.O, M.L.cj c ∈ M.L.O := by
    intro c hc
    rw [M.L.O_def] at hc ⊢
    exact hc.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  refine ⟨hu, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hd i
  | zero =>
    rw [hR_zero]
    exact M.L.O.zero_mem
  | add a b _ _ ha hb =>
    rw [hR_add]
    exact M.L.O.add_mem ha hb
  | smul c x _ hx =>
    rw [Subring.smul_def, hR_smul]
    exact M.L.O.mul_mem (hcj c c.2) hx

theorem MMfam_G (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) :
    H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
  simp only [Formalism.MainNotions.S.Loc.HermSp.MMfam, hs]

theorem f'_eq_G (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (a : Fin (r + 1)) :
    t.f' a = t.f a + algebraMap F E (g.q : F) • H.MMfam t (Sum.inr a) := by
  rw [MMfam_G H g hs t, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ (q_ne g), map_one, one_smul,
    add_sub_cancel]

theorem smul_mem_lat (g : SplitG M.L) (abelian₂ : Submodule M.L.O V) {x : V} (hx : x ∈ abelian₂) :
    algebraMap F E (g.q : F) • x ∈ abelian₂ := by
  have h1 := abelian₂.smul_mem (⟨algebraMap F E (g.q : F), q_mem_O g⟩ : M.L.O) hx
  exact h1

theorem iota_fst_of (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) {x : V} (hx : x ∈ t.abelian₂)
    (hxp : x ∈ H.perp (H.X t.f)) :
    ∃ x' ∈ t.abelian₂, x' ∈ H.perp (H.X t.f') ∧ x - x' ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂ := by
  set c : E := algebraMap F E (g.q : F)
  have hGu := gramMM_unit_of_term H t hg.1
  let d : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim (fun a => H.h x (H.MMfam t (Sum.inr a))) 0
  obtain ⟨u, huS, hud⟩ := exists_dual H (H.MMfam t) hGu d
  have huM : u ∈ MMsharp H t := by
    refine mem_MMsharp_of H t huS fun i => ?_
    rw [hud]
    rcases i with a | a
    · exact (hg.1.1.2.2 x).1 hx _ (hg.2.1 (Sum.inr a))
    · exact M.L.O.zero_mem
  obtain ⟨w, hw⟩ := surj_MMsharp M hM H t hg hU ⟨u, huM⟩
  refine ⟨x - c • ((u : V) + w), t.abelian₂.sub_mem hx (smul_mem_lat g t.abelian₂ hw), ?_, ?_⟩
  · refine mem_perpX_of H fun j => ?_
    have hxf : H.h x (t.f j.castSucc) = 0 := hxp _ (Submodule.subset_span ⟨j, rfl⟩)
    have hyM : H.MMfam t (Sum.inr j.castSucc) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      Submodule.subset_span ⟨_, rfl⟩
    have hfM : t.f j.castSucc ∈ Submodule.span E (Set.range (H.MMfam t)) := by
      rw [MMfam_G H g hs]
      exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩
    have hwf : H.h (w : V) (t.f j.castSucc) = 0 := hermitian_W0_span_zero H t w.2 hfM
    have hwy : H.h (w : V) (H.MMfam t (Sum.inr j.castSucc)) = 0 := hermitian_W0_span_zero H t w.2 hyM
    have hu1 : H.h u (t.f j.castSucc) = H.h x (H.MMfam t (Sum.inr j.castSucc)) := by
      have := hud (Sum.inl j.castSucc)
      simp only [d, Sum.elim_inl] at this
      rw [← this, MMfam_G H g hs, Sum.elim_inl]
    have hu2 : H.h u (H.MMfam t (Sum.inr j.castSucc)) = 0 := hud (Sum.inr j.castSucc)
    rw [f'_eq_G H g hs t, h_sub_left, H.h_smul_left, hR_add, hR_add, hR_smul, hR_smul, H.h_add_left,
      H.h_add_left, hxf, hwf, hwy, hu1, hu2, cj_q]
    ring
  · rw [sub_sub_cancel]
    exact Submodule.subset_span ⟨_, hw, rfl⟩

theorem iota_snd_of (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) {x' : V} (hx : x' ∈ t.abelian₂)
    (hxp : x' ∈ H.perp (H.X t.f')) :
    ∃ x ∈ t.abelian₂, x ∈ H.perp (H.X t.f) ∧ x - x' ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂ := by
  set c : E := algebraMap F E (g.q : F)
  have hGu := gramMM_unit_of_term H t hg.1
  let d : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim (fun a => H.h x' (H.MMfam t (Sum.inr a))) 0
  obtain ⟨u, huS, hud⟩ := exists_dual H (H.MMfam t) hGu d
  have huM : u ∈ MMsharp H t := by
    refine mem_MMsharp_of H t huS fun i => ?_
    rw [hud]
    rcases i with a | a
    · exact (hg.1.1.2.2 x').1 hx _ (hg.2.1 (Sum.inr a))
    · exact M.L.O.zero_mem
  obtain ⟨w, hw⟩ := surj_MMsharp M hM H t hg hU ⟨u, huM⟩
  refine ⟨x' + c • ((u : V) + w), t.abelian₂.add_mem hx (smul_mem_lat g t.abelian₂ hw), ?_, ?_⟩
  · refine mem_perpX_of H fun j => ?_
    have hxf : H.h x' (t.f' j.castSucc) = 0 := hxp _ (Submodule.subset_span ⟨j, rfl⟩)
    have hyM : H.MMfam t (Sum.inr j.castSucc) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      Submodule.subset_span ⟨_, rfl⟩
    have hfM : t.f j.castSucc ∈ Submodule.span E (Set.range (H.MMfam t)) := by
      rw [MMfam_G H g hs]
      exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩
    have hwf : H.h (w : V) (t.f j.castSucc) = 0 := hermitian_W0_span_zero H t w.2 hfM
    have hu1 : H.h u (t.f j.castSucc) = H.h x' (H.MMfam t (Sum.inr j.castSucc)) := by
      have := hud (Sum.inl j.castSucc)
      simp only [d, Sum.elim_inl] at this
      rw [← this, MMfam_G H g hs, Sum.elim_inl]
    have hxf2 : H.h x' (t.f j.castSucc) = - (c * H.h x' (H.MMfam t (Sum.inr j.castSucc))) := by
      have e := f'_eq_G H g hs t j.castSucc
      have : t.f j.castSucc = t.f' j.castSucc - c • H.MMfam t (Sum.inr j.castSucc) := by rw [e]; abel
      rw [this, hR_sub, hR_smul, hxf, cj_q]
      ring
    rw [H.h_add_left, H.h_smul_left, H.h_add_left, hxf2, hwf, hu1]
    ring
  · rw [add_sub_cancel_left]
    exact Submodule.subset_span ⟨_, hw, rfl⟩

theorem Lset_eq_snd (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    H.Lset t.abelian₂ t.f = Prod.snd '' H.iotaGraph g t := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hx'p, hd⟩ := iota_fst_of H hM g hs t hg hU hx x.2
    exact ⟨_, ⟨⟨x', hx'p⟩, x, hx', hx, hd, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨x', x, -, hx, -, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem Lset_eq_fst (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    H.Lset t.abelian₂ t.f' = Prod.fst '' H.iotaGraph g t := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x', hx', rfl⟩
    obtain ⟨x, hx, hxp, hd⟩ := iota_snd_of H hM g hs t hg hU hx' x'.2
    exact ⟨_, ⟨x', ⟨x, hxp⟩, hx', hx, hd, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨x', x, hx', -, -, rfl⟩, rfl⟩
    exact ⟨x', hx', rfl⟩

end RG1

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem dec_of {U W : Submodule E V} (h : IsCompl U W) (x : V) : ∃ a ∈ U, ∃ b ∈ W, a + b = x := by
  have hx : x ∈ U ⊔ W := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  exact Submodule.mem_sup.mp hx

theorem dec_unique {U W : Submodule E V} (h : IsCompl U W) {a a' b b' : V} (ha : a ∈ U) (ha' : a' ∈ U)
    (hb : b ∈ W) (hb' : b' ∈ W) (e : a + b = a' + b') : a = a' ∧ b = b' := by
  have h1 : a - a' ∈ U := U.sub_mem ha ha'
  have heq : a - a' = b' - b := by
    rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
  have h2 : a - a' ∈ W := by
    rw [heq]
    exact W.sub_mem hb' hb
  have h0 : a - a' = 0 := by
    have hbot := h.inf_eq_bot
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot _ ⟨h1, h2⟩
  have haa : a = a' := sub_eq_zero.mp h0
  refine ⟨haa, ?_⟩
  rw [haa] at e
  exact add_left_cancel e

theorem dec_diff {U W : Submodule E V} (h : IsCompl U W) (c : E) {a a' a'' b b' b'' x x' y : V}
    (ha : a ∈ U) (ha' : a' ∈ U) (ha'' : a'' ∈ U) (hb : b ∈ W) (hb' : b' ∈ W) (hb'' : b'' ∈ W)
    (hx : a + b = x) (hx' : a' + b' = x') (hy : a'' + b'' = y) (hd : x - x' = c • y) :
    a - a' = c • a'' ∧ b - b' = c • b'' := by
  have hsum : (a - a') + (b - b') = c • a'' + c • b'' := by
    rw [← smul_add, hy, ← hd, ← hx, ← hx']
    abel
  exact dec_unique h (U.sub_mem ha ha') (U.smul_mem c ha'') (W.sub_mem hb hb') (W.smul_mem c hb'') hsum

theorem part_MMsharp (t : Term V M r) (Λ : Submodule M.L.O V) (hsd : H.IsSelfDual Λ) (hMM : MMo H t ≤ Λ)
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t.f t.f'))) (hb : b ∈ H.W0 t.f t.f')
    (hab : a + b ∈ Λ) : a ∈ MMsharp H t := by

  have hmm_le : ∀ i, H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    intro i
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
          (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  have hspan : Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      exact Submodule.subset_span ⟨i, rfl⟩
    · dsimp only
      rcases i with i | i
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
        have e : t.f' i = t.f i + algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (t.f' i - t.f i)) := by
          rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
          abel
        show t.f' i ∈ _
        rw [e]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  refine ⟨hspan ha, fun m hm => ?_⟩
  have hmΛ : m ∈ Λ := hMM hm
  have hab' := (hsd.2.2 (a + b)).mp hab m hmΛ
  have hmX : m ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    have hle : MMo H t ≤ (H.Xp t.f ⊔ H.Xp t.f').restrictScalars M.L.O := by
      unfold Formalism.L2.SG.LsDatumA.MMo
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmm_le i
    exact hle hm
  have hbm : H.h b m = 0 := (show ∀ x ∈ H.Xp t.f ⊔ H.Xp t.f', H.h b x = 0 from hb) m hmX
  rw [H.h_add_left, hbm, add_zero] at hab'
  exact hab'

theorem perp_left {g : Fin (r + 1) → V} {a b : V} (hb : b ∈ H.perp (H.X g)) (hab : a + b ∈ H.perp (H.X g)) :
    a ∈ H.perp (H.X g) := by
  have h1 := (H.perp (H.X g)).sub_mem hab hb
  simpa using h1

theorem smul_cancel_q (g : SplitG M.L) {v w : V}
    (h : algebraMap F E (g.q : F) • v = algebraMap F E (g.q : F) • w) : v = w := by
  have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hu : IsUnit (algebraMap F E (g.q : F)) := (IsUnit.mk0 _ hq).map _
  exact (hu.smul_left_cancel).mp h

end RG2

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

structure RGHyp (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop where
  hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f')
  hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f')
  hsd₁ : H.IsSelfDual t₁.abelian₂
  hsd₂ : H.IsSelfDual Λ₂
  hMM₁ : MMo H t₁ ≤ t₁.abelian₂
  hMM₂ : MMo H t₂ ≤ Λ₂
  hth : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂
  hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂
  hsurj₁ : ∀ m₁ : ↥(MMsharp H t₁), ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂
  hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW t₂.f ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩
  hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW t₂.f' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩
  hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f),
        φ (H.mkW t₁.f ⟨u, hu⟩) = H.mkW t₂.f ⟨u', hu'⟩
  hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW t₂.f' ⟨u', hu'⟩

theorem RGHyp.trF {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f)) (hx₂ : a + b ∈ H.perp (H.X t₂.f))
    (h : φ (H.mkW t₁.f ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ (H.mkW t₁.f ⟨u₁, hu₁p⟩) = H.mkW t₂.f ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2 u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f) := mem_perp_isotropicSpan_of_mem_framePerp H n.2
  have hsplit : H.mkW t₁.f ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f ⟨u₁, hu₁p⟩ + H.mkW t₁.f ⟨n, hn⟩ := by
    rw [← map_add]
    rfl
  rw [hsplit, map_add, hφ, D.hC1 n, ← map_add] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

theorem RGHyp.trF' {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f'))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f'))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f')) (hx₂ : a + b ∈ H.perp (H.X t₂.f'))
    (h : φ' (H.mkW t₁.f' ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f' ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ' (H.mkW t₁.f' ⟨u₁, hu₁p⟩) = H.mkW t₂.f' ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2' u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f') := mem_perp_isotropicSpan_of_mem_framePerp' H n.2
  have hsplit : H.mkW t₁.f' ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f' ⟨u₁, hu₁p⟩ + H.mkW t₁.f' ⟨n, hn⟩ := by
    rw [← map_add]
    rfl
  rw [hsplit, map_add, hφ, D.hC1' n, ← map_add] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f' := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f' ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inr i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f' := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

theorem RGHyp.θs {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (_D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ') (m₂ : ↥(MMsharp H t₂)) :
    ∃ m₁ : ↥(MMsharp H t₁), θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := by
  obtain ⟨m₁, hm₁⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₂ m₂))
  refine ⟨m₁, ?_⟩
  show θ (Submodule.Quotient.mk m₁) = _
  rw [hm₁, LinearEquiv.apply_symm_apply]

end RG3

end Formalism.L2.SG.LsDatumA
end
end
