import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralFinProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.SettingExistsOfGap

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem weil_inv {μ μS ν : Measure G} [SFinite μS] [SFinite ν]
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) (Ψ : G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z, ∫⁻ s, Ψ (s⁻¹ * z) ∂μS ∂ν = ∫⁻ x, Ψ x ∂μ := by
  rw [hW Ψ hΨ]
  refine lintegral_congr fun z => ?_
  have hm : Measurable (fun s : G => Ψ (s * z)) := hΨ.comp (measurable_id.mul measurable_const)
  conv_rhs => rw [← hinv]
  rw [lintegral_map hm measurable_inv]

variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
  {V V' : Type} [NormedAddCommGroup V] [NormedAddCommGroup V']

@[irreducible] def PhiGG (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (W' : G → V') (γ : G) (a b : G) : ℝ≥0∞ :=
  ‖⟪σ a w, σ γ (σ b w)⟫_ℂ‖ₑ * ‖W a‖ₑ * ‖W' b‖ₑ

theorem measurable_PhiGG {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun p : G × G => PhiGG σ w W W' γ p.1 p.2) := by
  unfold PhiGG
  have h1 : Continuous (fun p : G × G => ⟪σ p.1 w, σ γ (σ p.2 w)⟫_ℂ) :=
    Continuous.inner (𝕜 := ℂ) ((hσ.2.2.2 w).comp continuous_fst)
      ((σ γ).continuous.comp ((hσ.2.2.2 w).comp continuous_snd))
  exact ((h1.enorm.measurable).mul ((hW.comp continuous_fst).enorm.measurable)).mul
    ((hW'.comp continuous_snd).enorm.measurable)

theorem quad_eq_GG {μ μS ν μS' ν' : Measure G} [SFinite μS] [SFinite ν] [SFinite μS'] [SFinite ν'] [SFinite μ]
    {S S' : Set G} {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hWc : Continuous W) (hWc' : Continuous W')
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hWe' : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS' ∂ν')
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (hiS : ∀ a ∈ S, a⁻¹ ∈ S) (hiS' : ∀ a ∈ S', a⁻¹ ∈ S')
    (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) (hWS' : ∀ s ∈ S', ∀ x, ‖W' (s * x)‖ = ‖W' x‖) (γ : G) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS ∂ν' ∂ν =
      ∫⁻ x, ∫⁻ y, PhiGG σ w W W' γ x y ∂μ ∂μ := by
  have hΦ := measurable_PhiGG hσ w hWc hWc' γ

  have hpt : ∀ z z' s s', s ∈ S → s' ∈ S' →
      ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ = PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') := by
    intro z z' s s' hs hs'
    unfold PhiGG
    rw [coef_shift hσ w γ z s z' s']
    have e1 : ‖W (s⁻¹ * z)‖ₑ = ‖W z‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS _ (hiS s hs)]
    have e2 : ‖W' (s'⁻¹ * z')‖ₑ = ‖W' z'‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS' _ (hiS' s' hs')]
    rw [e1, e2]
  have haeS : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have haeS' : ∀ᵐ s ∂μS', s ∈ S' := by rw [ae_iff]; exact h0'
  have hin : ∀ z z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS =
      ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS := by
    intro z z'
    refine lintegral_congr_ae ?_
    filter_upwards [haeS] with s hs
    refine lintegral_congr_ae ?_
    filter_upwards [haeS'] with s' hs'
    exact hpt z z' s s' hs hs'
  simp only [hin]

  have hswap : ∀ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS ∂ν' =
      ∫⁻ s, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂ν' ∂μS := by
    intro z
    have hm : Measurable (Function.uncurry fun z' s : G => ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS') := by
      have hg : Measurable (fun q : (G × G) × G => ((q.1.2⁻¹ * z, q.2⁻¹ * q.1.1) : G × G)) :=
        (((measurable_snd.comp measurable_fst).inv.mul measurable_const)).prodMk
          ((measurable_snd.inv).mul (measurable_fst.comp measurable_fst))
      have h3 : Measurable (fun q : (G × G) × G => PhiGG σ w W W' γ (q.1.2⁻¹ * z) (q.2⁻¹ * q.1.1)) :=
        hΦ.comp hg
      exact h3.lintegral_prod_right'
    exact lintegral_lintegral_swap hm.aemeasurable
  simp only [hswap]

  have hy : ∀ a, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ a (s'⁻¹ * z') ∂μS' ∂ν' = ∫⁻ y, PhiGG σ w W W' γ a y ∂μ := by
    intro a
    exact weil_inv hWe' hinv' (fun y => PhiGG σ w W W' γ a y) (hΦ.comp (measurable_const.prodMk measurable_id))
  simp only [hy]

  have hmy : Measurable (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) := hΦ.lintegral_prod_right'
  exact weil_inv hWe hinv (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) hmy

theorem triple_lintegral_eq {μ μS ν : Measure G} [SFinite μS] [SFinite ν] {S : Set G} {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (h0 : μS Sᶜ = 0) (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν =
      ∫⁻ z, ‖W z‖ₑ * ∫⁻ y, ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ ∂μ ∂ν := by
  refine lintegral_congr fun z => ?_
  set H : G → ℝ≥0∞ := fun y => ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ with hHdef
  have hHm : Measurable H := by
    have h1 : Continuous (fun y => ⟪σ z w, σ y w⟫_ℂ) := Continuous.inner (𝕜 := ℂ) continuous_const (hσ.2.2.2 w)
    exact (h1.enorm.measurable).mul hWc.enorm.measurable
  have hae : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have hin : ∀ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS =
      ‖W z‖ₑ * ∫⁻ s, H (s * z') ∂μS := by
    intro z'
    rw [← lintegral_const_mul (‖W z‖ₑ) (f := fun s => H (s * z')) (hHm.comp (measurable_mul_const z'))]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    simp only [hHdef]
    have e1 : σ s (σ z' w) = σ (s * z') w := (rep_mul_apply hσ s z' w)
    have e2 : ‖W z'‖ₑ = ‖W (s * z')‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS s hs z']
    rw [e1, e2]
    ring
  simp only [hin]
  have hmeas : Measurable (fun z' : G => ∫⁻ s, H (s * z') ∂μS) := by
    have h2 : Measurable (fun p : G × G => H (p.2 * p.1)) := hHm.comp (measurable_snd.mul measurable_fst)
    exact h2.lintegral_prod_right'
  rw [lintegral_const_mul (‖W z‖ₑ) (f := fun z' => ∫⁻ s, H (s * z') ∂μS) hmeas]
  congr 1
  exact (hWe H hHm).symm

end Formalism.L2.S.Pv.ConvG
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

private theorem norm_psiR_eq_one {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ)
    (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by
  unfold psiR
  have hS : (∑ a, (rootCoord ε e f z g a + star (rootCoord ε e f z g a))) =
      ((∑ a, 2 * (rootCoord ε e f z g a).re : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.add_conj]
    push_cast
    ring
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (∑ a, 2 * (rootCoord ε e f z g a).re) / gg) using 2
  rw [hS]
  push_cast
  ring_nf

private theorem norm_psiInf_eq_one (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (g : ℕ) (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (s : I.Ginf) : ‖psiInf I g e f z s‖ = 1 := by
  unfold psiInf
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiR_eq_one _ _ _ _ _ _

theorem norm_Wu_S (u : D.what₂.Word) : ∀ s ∈ X.SinfU u, ∀ x, ‖X.Wu u (s * x)‖ = ‖X.Wu u x‖ := by
  intro s hs x
  rw [(X.Wu_spec u).1 s hs x, norm_smul, norm_psiInf_eq_one, one_mul]
  have h := (X.piU_rep u).2.2.1 s hs (X.Wu u x) (X.Wu u x)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖X.piU u s (X.Wu u x)‖ ^ 2 = ‖X.Wu u x‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

@[irreducible] def phiV (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    ℝ≥0∞ :=
  ‖⟪X.B.σ v (uMat a) (X.B.w v), X.B.σ v (uMat (γ v)) (X.B.σ v (uMat b) (X.B.w v))⟫_ℂ‖ₑ *
    ‖X.Wloc u v a‖ₑ * ‖X.Wloc u' v b‖ₑ

private theorem nnnorm_tensU_eq_prod (u : D.what₂.Word) (a : ∀ v, X.Vloc u v) :
    ‖X.tensU u a‖₊ = ∏ v, ‖a v‖₊ := by
  have h := X.tensU_inner u a a
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖X.tensU u a‖ ^ 2 = (∏ v, ‖a v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  have h3 := (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg (a v))
    two_ne_zero).1 h2
  ext
  push_cast
  exact h3

theorem phiGG_eq (u u' : D.what₂.Word) (γ x y : X.B.I.Ginf) :
    PhiGG X.B.σs (X.B.tens X.B.w) (X.Wu u) (X.Wu u') γ x y = ∏ v, phiV X u u' γ v (x v) (y v) := by
  obtain ⟨hin, hσ, -⟩ := X.B.tens_spec
  unfold PhiGG phiV
  simp only [hσ, hin, X.Wu_tens, enorm_eq_nnnorm, nnnorm_prod, nnnorm_tensU_eq_prod, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]

theorem measurable_phiV (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => phiV X u u' γ v p.1 p.2) := by
  have hc : ∀ h : X.B.H v, Continuous (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g) h) :=
    (Formalism.L2.S.Pv.SchurTens.unitRep_of_URepOn (X.ds v).2.2.1).2.2.2
  have h1 : Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) =>
      ‖⟪X.B.σ v (uMat p.1) (X.B.w v), X.B.σ v (uMat (γ v)) (X.B.σ v (uMat p.2) (X.B.w v))⟫_ℂ‖ₑ) :=
    (((hc _).comp continuous_fst).inner
      ((X.B.σ v (uMat (γ v))).continuous.comp ((hc _).comp continuous_snd))).enorm.measurable
  have h2 : Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => ‖X.Wloc u v p.1‖ₑ) :=
    ((X.Wloc_cont u v).comp continuous_fst).enorm.measurable
  have h3 : Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => ‖X.Wloc u' v p.2‖ₑ) :=
    ((X.Wloc_cont u' v).comp continuous_snd).enorm.measurable
  unfold phiV
  exact (h1.mul h2).mul h3

theorem lint_GG_prod (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    ∫⁻ x, ∫⁻ y, PhiGG X.B.σs (X.B.tens X.B.w) (X.Wu u) (X.Wu u') γ x y
        ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ a, ∫⁻ b, phiV X u u' γ v a b ∂(Formalism.REAL.muG (X.B.I.ε v)) ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hm := measurable_phiV X u u' γ
  have h1 : ∀ x : X.B.I.Ginf, ∫⁻ y, PhiGG X.B.σs (X.B.tens X.B.w) (X.Wu u) (X.Wu u') γ x y
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
        ∏ v, ∫⁻ b, phiV X u u' γ v (x v) b ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
    intro x
    simp_rw [phiGG_eq X u u' γ x]
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v))
      (fun v b => phiV X u u' γ v (x v) b) (fun v => (hm v).comp measurable_prodMk_left)
  simp_rw [h1]
  exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v))
    (fun v a => ∫⁻ b, phiV X u u' γ v a b ∂(Formalism.REAL.muG (X.B.I.ε v))) (fun v => (hm v).lintegral_prod_right')

end Glob

end Formalism.L2.S.Pv.ConvG
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Kv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (a : Formalism.REAL.UJ (X.B.I.ε v)) : ℝ≥0∞ :=
  ‖X.Wloc w v a‖ₑ * ∫⁻ b, ‖⟪X.B.σ v (uMat a) (X.B.w v), X.B.σ v (uMat b) (X.B.w v)⟫_ℂ‖ₑ * ‖X.Wloc w v b‖ₑ
    ∂(Formalism.REAL.muG (X.B.I.ε v))

section Pf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

@[irreducible] def hv (v : InfinitePlace X.B.I.F) (a b : Formalism.REAL.UJ (X.B.I.ε v)) (w : D.what₂.Word) : ℝ≥0∞ :=
  ‖⟪X.B.σ v (uMat a) (X.B.w v), X.B.σ v (uMat b) (X.B.w v)⟫_ℂ‖ₑ * ‖X.Wloc w v b‖ₑ

theorem measurable_hv (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => hv X v p.1 p.2 w) := by
  have hU := (X.ds v).2.2.1
  have hcont : Continuous (fun a : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat a) (X.B.w v)) := by
    refine (hU.2.2 (X.B.w v)).comp_continuous ?_ ?_
    · exact Units.continuous_val.comp continuous_subtype_val
    · intro a; exact a.2
  have hW : Continuous (X.Wloc w v) := X.Wloc_cont w v
  have heq : (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => hv X v p.1 p.2 w) =
      fun p => ‖⟪X.B.σ v (uMat p.1) (X.B.w v), X.B.σ v (uMat p.2) (X.B.w v)⟫_ℂ‖ₑ * ‖X.Wloc w v p.2‖ₑ := by
    funext p
    unfold hv
    rfl
  rw [heq]
  exact ((hcont.comp continuous_fst).inner (hcont.comp continuous_snd)).enorm.measurable.mul
    (hW.comp continuous_snd).enorm.measurable

theorem Kv_eq (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Formalism.REAL.UJ (X.B.I.ε v)) :
    Kv X w v a = ‖X.Wloc w v a‖ₑ * ∫⁻ b, hv X v a b w ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  simp only [Kv, hv]

theorem measurable_Kv (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measurable (Kv X w v) := by
  have h1 : Measurable (fun a => ∫⁻ b, hv X v a b w ∂(Formalism.REAL.muG (X.B.I.ε v))) :=
    (measurable_hv X w v).lintegral_prod_right'
  have h2 : Measurable (fun a => ‖X.Wloc w v a‖ₑ) := (X.Wloc_cont w v).enorm.measurable
  have heq : Kv X w v = fun a => ‖X.Wloc w v a‖ₑ * ∫⁻ b, hv X v a b w ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
    funext (Kv_eq X w v)
  rw [heq]
  exact h2.mul h1

theorem H_eq (w : D.what₂.Word) (z y : X.B.I.Ginf) :
    ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs y (X.B.tens X.B.w)⟫_ℂ‖ₑ * ‖X.Wu w y‖ₑ = ∏ v, hv X v (z v) (y v) w := by
  obtain ⟨hi, hσ, -⟩ := X.B.tens_spec
  rw [hσ, hσ, hi, Formalism.L2.SG.Pf.WuDec.enorm_Wu]
  have hprod : ‖∏ v, ⟪X.B.σ v (uMat (z v)) (X.B.w v), X.B.σ v (uMat (y v)) (X.B.w v)⟫_ℂ‖ₑ =
      ∏ v, ‖⟪X.B.σ v (uMat (z v)) (X.B.w v), X.B.σ v (uMat (y v)) (X.B.w v)⟫_ℂ‖ₑ := by
    simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.coe_finset_prod]
  rw [hprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold hv
  rfl

theorem K_eq (w : D.what₂.Word) (z : X.B.I.Ginf) :
    ‖X.Wu w z‖ₑ * ∫⁻ y, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs y (X.B.tens X.B.w)⟫_ℂ‖ₑ * ‖X.Wu w y‖ₑ
        ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = ∏ v, Kv X w v (z v) := by
  have hmu : Formalism.L2.SG.ProjRows.muInf X.B.I = Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v) := rfl
  have hm : ∀ v, Measurable (fun b => hv X v (z v) b w) := by
    intro v
    have h := measurable_hv X w v
    exact h.comp (measurable_const.prodMk measurable_id)
  simp_rw [H_eq X w z]
  rw [hmu, Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod _ (fun v b => hv X v (z v) b w) hm,
    Formalism.L2.SG.Pf.WuDec.enorm_Wu, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => (Kv_eq X w v (z v)).symm

theorem Kv_inv (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (m : Formalism.REAL.UJ (X.B.I.ε v))
    (hm : m ∈ Formalism.L2.SG.Pf.WuDec.Nloc X w v) (h : Formalism.REAL.UJ (X.B.I.ε v)) (hh : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X w v)
    (x : Formalism.REAL.UJ (X.B.I.ε v)) : Kv X w v (m * h * x) = Kv X w v x := by
  have hg : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X w v :=
    Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc (X := X) (u := w) v
      (Formalism.L2.SG.Pf.WuDec.Nloc_sub (X := X) (u := w) v hm)
      (Formalism.L2.SG.Pf.WuDec.Hloc_sub (X := X) (u := w) v hh)
  set g := m * h with hgdef
  have hn : ∀ y, ‖X.Wloc w v (g * y)‖ₑ = ‖X.Wloc w v y‖ₑ := fun y => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv (X := X) (u := w) v hg y]
  have hinv : ∀ f : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞,
      ∫⁻ b, f (g * b) ∂(Formalism.REAL.muG (X.B.I.ε v)) = ∫⁻ b, f b ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
    intro f
    unfold Formalism.REAL.muG
    exact lintegral_mul_left_eq_self f g
  have hU := (X.ds v).2.2.1
  have hσmul : ∀ a b : Formalism.REAL.UJ (X.B.I.ε v),
      X.B.σ v (uMat (a * b)) = (X.B.σ v (uMat a)).comp (X.B.σ v (uMat b)) :=
    fun a b => hU.1.2 _ a.2 _ b.2
  have hiso : ∀ p q, ⟪X.B.σ v (uMat g) p, X.B.σ v (uMat g) q⟫_ℂ = ⟪p, q⟫_ℂ := by
    intro p q
    let L : X.B.H v →ₗᵢ[ℂ] X.B.H v :=
      ⟨(X.B.σ v (uMat g) : X.B.H v →ₗ[ℂ] X.B.H v), fun y => hU.2.1 _ g.2 y⟩
    exact L.inner_map_map p q
  rw [Kv_eq, Kv_eq, hn x]
  congr 1
  refine ((hinv (fun b => hv X v (g * x) b w)).symm).trans (lintegral_congr fun b => ?_)
  unfold hv
  rw [hn b]
  congr 2
  rw [hσmul g x, hσmul g b, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hiso]

theorem inner_weil (w : D.what₂.Word) (z : X.B.I.Ginf) :
    ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) =
      ‖X.Wu w z‖ₑ * ∫⁻ y, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs y (X.B.tens X.B.w)⟫_ℂ‖ₑ * ‖X.Wu w y‖ₑ
        ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
  obtain ⟨-, hσt, -⟩ := X.B.tens_spec
  set G : X.B.I.Ginf → ℝ≥0∞ := fun y =>
    ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs y (X.B.tens X.B.w)⟫_ℂ‖ₑ * ‖X.Wu w y‖ₑ with hGdef
  have hGm : Measurable G := by
    have hG : G = fun y => ∏ v, hv X v (z v) (y v) w := funext (H_eq X w z)
    rw [hG]
    exact Finset.measurable_prod _ fun v _ =>
      (measurable_hv X w v).comp (measurable_const.prodMk (measurable_pi_apply v))
  have hmul : ∀ s z' : X.B.I.Ginf,
      X.B.σs s (X.B.σs z' (X.B.tens X.B.w)) = X.B.σs (s * z') (X.B.tens X.B.w) := by
    intro s z'
    rw [hσt, hσt, hσt]
    congr 1
    funext v
    have hU := (X.ds v).2.2.1
    rw [show uMat ((s * z') v) = uMat (s v) * uMat (z' v) from rfl, hU.1.2 _ (s v).2 _ (z' v).2]
    rfl
  have hS := Formalism.L2.SG.WuDecayPf.muSOn X w
  have hinner : ∀ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
      ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) = ‖X.Wu w z‖ₑ * ∫⁻ s, G (s * z') ∂(muS X w) := by
    intro z'
    rw [← lintegral_const_mul' _ _ enorm_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hS] with s hs
    have hn : ‖X.Wu w (s * z')‖ₑ = ‖X.Wu w z'‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_Wu_S X w s hs z']
    rw [hmul, hGdef]
    simp only [hn]
    ring
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  congr 1
  have hq := X.nuQ_weil w
  exact (hq G hGm).symm

end Pf

end Formalism.L2.S.Pv.ConvG
end
end

section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocQuadGG_G : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ),
    0 < sc → ∀ (v : InfinitePlace X.B.I.F) (cv : Fin (D.R.rS + 1) → ℂ),
      cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u' → ∀ g : Formalism.REAL.UJ (X.B.I.ε v),
        Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv →
        ∫⁻ x, ∫⁻ y, ‖⟪X.B.σ v (uMat x) (X.B.w v), X.B.σ v (uMat g) (X.B.σ v (uMat y) (X.B.w v))⟫_ℂ‖ₑ *
          ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v y‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def LocQuad1_G : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word)
    (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞),
    Formalism.L2.SG.Pf.WuDec.QuotWit X w μS νl C → ∀ v, ∫⁻ a, Kv X w v a ∂(νl v) < ⊤

def StepConvG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ),
    0 < sc →
    (∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
          X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
        ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤) ∧
    ∀ w : D.what₂.Word,
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

theorem double_integral_finite_diagonal {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ) (hsc : 0 < sc)
    (hL : ∀ (v : InfinitePlace X.B.I.F) (cv : Fin (D.R.rS + 1) → ℂ),
      cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u' → ∀ g : Formalism.REAL.UJ (X.B.I.ε v),
        Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv →
        ∫⁻ x, ∫⁻ y, ‖⟪X.B.σ v (uMat x) (X.B.w v), X.B.σ v (uMat g) (X.B.σ v (uMat y) (X.B.w v))⟫_ℂ‖ₑ *
          ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v y‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤)
    (c : Cinf X) (hc : c ∈ Good X u u') (γ : X.B.I.Ginf) (hγ : HasDiag X u u' sc c γ) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
        X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
      ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤ := by
  obtain ⟨hH, -, -, -, hsf⟩ := Formalism.L2.S.Pv.HaarSubS.stepSubG_holds D X u
  obtain ⟨hH', -, -, -, hsf'⟩ := Formalism.L2.S.Pv.HaarSubS.stepSubG_holds D X u'
  obtain ⟨-, -, -, hiS, hsig, -, h0, -, -, -, hinv⟩ := hH
  obtain ⟨-, -, -, hiS', hsig', -, h0', -, -, -, hinv'⟩ := hH'
  have := hsig
  have := hsig'
  have := hsf
  have := hsf'
  have hrep := (Formalism.L2.S.Pv.SchurTens.stepSchurG_holds D X).1
  rw [quad_eq_GG (μ := Formalism.L2.SG.ProjRows.muInf X.B.I) (μS := muS X u) (μS' := muS X u') hrep
    (X.B.tens X.B.w) (X.Wu_spec u).2.2.1 (X.Wu_spec u').2.2.1 (X.nuQ_weil u) (X.nuQ_weil u') hinv hinv' h0 h0'
    hiS hiS' (norm_Wu_S X u) (norm_Wu_S X u') γ, lint_GG_prod]
  refine ENNReal.prod_lt_top fun v _ => ?_
  unfold phiV
  exact hL v (c v) (hc v) (γ v) (hγ v)

theorem convolution_integral_finite {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word)
    (hC : ∀ (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞),
      Formalism.L2.SG.Pf.WuDec.QuotWit X w μS νl C → ∀ v, ∫⁻ a, Kv X w v a ∂(νl v) < ⊤) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
      ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤ := by
  obtain ⟨μSl, νl, C, hQ⟩ := Formalism.L2.SG.Pf.WuDec.quotAll_of Formalism.L2.SG.Closed.QuotProdK_holds
    Formalism.L2.SG.Pf.WFL.locHNProps_holds Formalism.L2.SG.Closed.NUnimodLoc_holds D X w
  have hQ' := hQ
  obtain ⟨hC0, hCt, -, hprod⟩ := hQ'
  simp only [inner_weil X w, K_eq X w]
  rw [hprod (fun v => Kv X w v) (fun v => measurable_Kv X w v)
    (fun v m hm h hh x => Kv_inv X w v m hm h hh x)]
  exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hCt) (ENNReal.prod_lt_top fun v _ => hC μSl νl C hQ v)

theorem stepConvG_of (hB : LocQuadGG_G) (hC : LocQuad1_G) : StepConvG := by
  intro D hG X u u' sc hsc
  exact ⟨fun c hc γ hγ => double_integral_finite_diagonal X u u' sc hsc (hB D hG X u u' sc hsc) c hc γ hγ,
    fun w => convolution_integral_finite X w (hC D hG X w)⟩

end Formalism.L2.S.Pv.ConvG
end
end
