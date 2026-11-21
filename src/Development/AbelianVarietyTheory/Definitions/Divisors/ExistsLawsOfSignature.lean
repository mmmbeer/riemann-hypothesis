import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetEqOneOfTrivialOnHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.Model

open NumberField IsDedekindDomain Module Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem det_eq_one_of_half (l : Level H) (Di : Datum H) {r : ℕ} (X : Data E r) (φ : Di.La ≃ₗ[𝓞 E] X.Λ)
    (ef : ∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (γ : GL (Fin r) E) (hU : IsUStab X.Gm X.Λ γ)
    (hh : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Di.La), ∃ b : Di.La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (φ a : Fin r → E) = (φ a : Fin r → E) + (l.M : ℕ) • (φ b : Fin r → E)) :
    (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  let g : (Fin r → E) ≃ₗ[𝓞 E] (Fin r → E) :=
    (Matrix.toLin'OfInv (M := (γ : Matrix (Fin r) (Fin r) E)) (M' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))
      (Units.mul_inv γ) (Units.inv_mul γ)).symm.restrictScalars (𝓞 E)
  have hg : ∀ v, g v = (γ : Matrix (Fin r) (Fin r) E) *ᵥ v := fun v => rfl
  have hmap : X.Λ.map (g : (Fin r → E) →ₗ[𝓞 E] (Fin r → E)) = X.Λ := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hU.2 w).1 hw
    · intro hv
      refine ⟨g.symm v, (hU.2 _).2 ?_, g.apply_symm_apply v⟩
      rw [← hg, g.apply_symm_apply]; exact hv
  let f : Di.La ≃ₗ[𝓞 E] Di.La := φ.trans ((g.ofSubmodules X.Λ X.Λ hmap).trans φ.symm)
  have hf : ∀ a, (φ (f a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := fun a => by
    simp only [f, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l f
    (fun a b => by
      have : ((Di.EF (f a) (f b) : ℤ) : ℚ) = ((Di.EF a b : ℤ) : ℚ) := by rw [ef, ef, hf, hf, hU.1]
      exact_mod_cast this)
    (fun a ha => by
      obtain ⟨b, hb⟩ := hh a ha
      refine ⟨b, φ.injective (Subtype.ext ?_)⟩
      rw [hf, hb, map_add, map_nsmul]; rfl)
  refine GlobalTheory.CongruenceDet.det_eq_one E r l.M X.Gm X.Λ γ X.Gm_det X.Λ_fg X.Λ_span l.three_le hU fun v hv => ?_
  obtain ⟨a, ha⟩ := φ.surjective ⟨v, hv⟩
  obtain ⟨e, he⟩ := hfull a
  have hv' : (φ a : Fin r → E) = v := congrArg Subtype.val ha
  refine ⟨φ e, (φ e).2, ?_⟩
  rw [← hv', ← hf, he, map_add, map_nsmul]; rfl

theorem exists_unf (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E)
    (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hσ : GoodEmb c σ) (hξ : cc ξ₀ = -ξ₀) (hneg : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0)
    (hφ : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) :
    ∃ U : Formalism.L2.PjFree.Unf Xo c σ r, Formalism.L2.PjFree.IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧
      (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) ∧
      ∀ k, ∀ γ ∈ (U.X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  classical
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  refine ⟨GlobalTheory.FrameUnif.unfOf e F M un, GlobalTheory.T.familyUniformisation_isComplexUniformisation hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, hM.chi, hG,
    fun k γ hU hv => (hM.gam k γ).2 ⟨hU, fun a _ => ?_, fun a => ?_⟩, fun k γ hγ => ?_⟩
  · obtain ⟨u, hu, h⟩ := hv _ (M.φ k a).2
    obtain ⟨b, hb⟩ := (M.φ k).surjective ⟨u, hu⟩
    exact ⟨b, by rw [hb]; exact h⟩
  · obtain ⟨u, hu, h⟩ := hv _ (M.φ k a).2
    obtain ⟨b, hb⟩ := (M.φ k).surjective ⟨u, hu⟩
    refine ⟨l.M • b, ?_⟩
    rw [hA, one_smul, map_nsmul, hb]
    exact h
  · obtain ⟨h1, h2, -⟩ := (hM.gam k γ).1 hγ
    exact det_eq_one_of_half l (F.Di k) (M.X k) (M.φ k) (hM.ef k) γ h1 h2

set_option maxHeartbeats 1000000 in

theorem exists_laws (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hF : FnAlgClosed Xo c) (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) :
    ∃ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q), Laws U (Real.sqrt H.d) := by
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hn : ∀ τ : E →+* ℂ, ‖τ (H.rt : E)‖ = Real.sqrt H.d := fun τ => by
    have : ‖τ (H.rt : E)‖ ^ 2 = H.d := by rw [← norm_pow, ← map_pow, hsq]; simp
    rw [← this, Real.sqrt_sq (norm_nonneg _)]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
    have him : z.im ≠ 0 := by
      intro h
      rw [h] at h1
      nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hτ₀ := key (τ₀ (H.rt : E)) (by rw [← map_pow, hsq]; simp)
    apply τ₀.injective
    unfold cc
    rw [IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hτ₀.1]
  have hne : (H.rt : E) ≠ 0 := fun h => by
    rw [h] at hsq
    have : (H.d : E) = 0 := by simpa using hsq
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  obtain ⟨ξ₀, hc0, hne0, him, hx⟩ : ∃ ξ₀ : E, cc ξ₀ = -ξ₀ ∧ ξ₀ ≠ 0 ∧
      (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) ∧ ∀ τ : E →+* ℂ, ‖τ ξ₀‖ = Real.sqrt H.d := by
    rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
    · exact ⟨H.rt, hcc, hne, fun τ hτ => by rw [hτ]; exact h, hn⟩
    · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_, fun τ => by rw [map_neg, norm_neg, hn]⟩
      · unfold cc at hcc ⊢
        rw [map_neg, hcc]
      · rw [map_neg, hτ, Complex.neg_im]; linarith
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hc0 ⊢
    rw [map_neg, hc0]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne0) (Dw.p + Dw.q) rfl
  have hU : ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), GoodEmb c σ →
      Formalism.L2.PjFree.IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧
      (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) ∧
      ∀ k, ∀ γ ∈ (U.X k).Γ, (γ : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) E).det = 1 := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hU⟩ := exists_unf Dw l Xo c σ _ ξ₀ Gm φ hpq hA hσ hc0 him hφ
      exact ⟨U, fun _ => hU⟩
    · exact ⟨{ Comp := PEmpty, X := fun k => k.elim, un := fun k => k.elim }, fun h => absurd h hσ⟩
  choose U hU using hU
  refine ⟨fun σ => (U σ).toPj, hpq, hA, hg, fun σ hσ => (hU σ hσ).1, hF,
    fun σ hσ k τ => ?_, fun σ hσ a n _ k γ _ => (hU σ hσ).2.1 k _ γ, fun σ hσ => (hU σ hσ).2.2.2.2, ?_, h1⟩
  · exact (congrArg (fun z => ‖τ z‖) ((hU σ hσ).2.2.1 k).2).trans (hx τ)
  · intro σ hσ a n hD ha hn P hP
    have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional E H Dw l Xo c _ U hpq hA
      (fun s hs => (hU s hs).1) σ hσ
      (fun k k' => ⟨((hU σ hσ).2.2.1 k).1.trans ((hU σ hσ).2.2.1 k').1.symm,
        ((hU σ hσ).2.2.1 k).2.trans ((hU σ hσ).2.2.1 k').2.symm⟩)
      (hU σ hσ).2.2.2.1 a n hD (fun τ _ h0 => ha τ _ (by omega)) hn (fun k γ _ => (hU σ hσ).2.1 k _ γ)
    exact key ⟨hP.1, hP.2⟩




section Steps

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem hasPts (h : Laws U x) (Z : Comp Xo c) : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z

theorem htValAt_nonempty (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io)
    (hy : y₀.IsAlg) : (htValAt la y₀).Nonempty := by
  obtain ⟨p, hp, ha, k, y, h⟩ := (GlobalTheory.CompHt.exists_isHTFrameCp_and_nonempty E H Dw l Xo c).1 T io y₀ hy
  exact ⟨_, p, hp, ha, k, y, h, rfl⟩


end Steps


end GlobalTheory.FlatCore.Model

end
