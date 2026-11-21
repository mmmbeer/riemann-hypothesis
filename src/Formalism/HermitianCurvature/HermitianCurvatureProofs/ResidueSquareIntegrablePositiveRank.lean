import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfOuter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem cf_last_isEmpty (r : ℕ) : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun l => by have := l.1.isLt; have := l.2; simp at *; omega⟩

theorem integrable_cf_last {r : ℕ} (f : Cf r (Fin.last r) → ℂ) : Integrable f := by
  haveI := cf_last_isEmpty r
  have hvol : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (fun l => isEmptyElim l) := by
    rw [volume_pi, Measure.pi_of_empty]
  haveI : IsFiniteMeasure (volume : Measure (Cf r (Fin.last r))) := by rw [hvol]; infer_instance
  have hf : f = fun _ => f (fun l => isEmptyElim l) := by
    funext c'
    congr 1
    funext l
    exact isEmptyElim l
  rw [hf]
  exact integrable_const _

end Formalism.FourierDecayAlt.P5.HerC
end
end

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapI (i : Fin (r + 1)) (c : Fin r → ℂ) (q : Cf r i × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue i c q.1, Matrix.of q.2)

theorem glueMapI_continuous (i : Fin (r + 1)) (c : Fin r → ℂ) : Continuous (glueMapI (k := k) i c) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine continuous_pi fun l => ?_
  by_cases h : i.val ≤ l.val
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun q => q.1 ⟨l, h⟩ := by
      funext q; simp [glue, h]
    rw [e]; exact (continuous_apply _).comp continuous_fst
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun _ => c l := by
      funext q; simp [glue, h]
    rw [e]; exact continuous_const

theorem measurableSet_glueMapI_DomR (i : Fin (r + 1)) (c : Fin r → ℂ) :
    MeasurableSet (glueMapI (k := k) i c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapI_continuous i c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapI_continuous i c)).measurableSet

theorem pair_measurableI (i : Fin (r + 1)) (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r i × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMapI (k := k) i c) (glueMapI (k := k) i c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapI_continuous i c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapI_continuous i c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapI_DomR i c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

theorem pairAt_measI (μ : Measure (Mt k r)) [SFinite μ] (i : Fin (r + 1)) (u v : RadSp k r z z' π π')
    (c : Fin r → ℂ) : StronglyMeasurable (fun c' : Cf r i => pairAt μ u v (glue i c c')) :=
  (pair_measurableI i c u v).stronglyMeasurable.integral_prod_right'

def wtI (i : Fin (r + 1)) (c' : Cf r i) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem wtI_measurable (i : Fin (r + 1)) : Measurable (wtI i) := by
  unfold wtI
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelSquareIntegrable (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u u (glue i c c'))

theorem hsInner_self_ofRealI (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_selfI (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofRealI]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_leI (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_selfI, norm_pairAt_selfI]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_crossI (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1))
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelSquareIntegrable μ i u c) (Iv : LevelSquareIntegrable μ i v c) :
    Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u v (glue i c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    ((wtI_measurable i).aestronglyMeasurable.mul (pairAt_measI μ i u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wtI i c' * pairAt μ u v (glue i c c')‖ ≤
    ‖wtI i c' * pairAt μ u u (glue i c c')‖ + ‖wtI i c' * pairAt μ v v (glue i c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hu hv _) (norm_nonneg _)

end Meas

section Red

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntOuter_of_l2I {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1)) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ lcSub k r z z' π π') (hv : ∀ a, v a ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : ∀ a, LevelSquareIntegrable μ i (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ i (v a) c) :
    Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (u a) (v a) (glue i c c')) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => int_crossI μ hμ i (hu a) (hv a) c (Iu a) (Iv a)

def HermitianSquareIntegrableAt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (i : Fin (P.r + 1)) : Prop :=
  ∀ c ∈ OmX P.r, (∀ u ∈ herKc S P z z' π π' L st l0 D i, LevelSquareIntegrable μ i u c) ∧
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D i) x → ∀ a, LevelSquareIntegrable μ i (act (RRi L st i w) x a) c

def HermitianSquareIntegrableAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ i : Fin (P.r + 1), i.val < P.r → HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D i

theorem outer_form_compact_of_square (h : HermitianSquareIntegrableAll) : FormIntOuterCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy
  by_cases hi : i.val < P.r
  · have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
    have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
      (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
    have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
    have hu : ∀ a, act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' := fun a =>
      (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
    obtain ⟨hK, hR⟩ := h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
    exact formIntOuter_of_l2I μ hD.2.1 i _ y hu (fun a => hle (hy a)) c (hR w hw x hx) (fun a => hK _ (hy a))
  · have e : i = Fin.last P.r := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst e
    exact integrable_cf_last _

end Red

end Formalism.FourierDecayAlt.P5.HerD
end
end

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Shift

def shIdx {r : ℕ} (i : Fin (r + 1)) : {l : Fin (r - i) // (0 : Fin (r - i + 1)).val ≤ l.val} ≃ {l : Fin r // i.val ≤ l.val} where
  toFun l := ⟨⟨l.1.val + i.val, by have := l.1.isLt; have := i.isLt; omega⟩, Nat.le_add_left _ _⟩
  invFun l := ⟨⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩, Nat.zero_le _⟩
  left_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val + i.val - i.val = l.1.val
    omega
  right_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val - i.val + i.val = l.1.val
    have := l.2; omega

def shEq {r : ℕ} (i : Fin (r + 1)) : Cf (r - i) 0 ≃ᵐ Cf r i :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_mp {r : ℕ} (i : Fin (r + 1)) : MeasurePreserving (shEq i) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_apply {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) (l : {l : Fin r // i.val ≤ l.val}) :
    shEq i c' l = c' ((shIdx i).symm l) := by
  unfold shEq
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem shiftCf_glue {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) (c' : Cf (r - i) 0) :
    Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue 0 c'' c') = shEq i c' := by
  funext l
  rw [shEq_apply]
  simp [Formalism.FourierDecayAlt.P.PTie.shiftCf, shIdx]
  rfl

theorem wtI_shEq {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) : wtI i (shEq i c') = wtI 0 c' := by
  unfold wtI
  congr 1
  simp_rw [shEq_apply]
  exact Fintype.prod_equiv (shIdx i).symm _ _ fun l => rfl

end Shift

section Transfer

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem level_square_integrable_of_transport {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (i : Fin (r + 1)) (c : Fin r → ℂ)
    {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ} {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)}
    (μi : Measure (Mt k (r - i))) (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (v : RadSp k r z z' π π') (c'' : Fin (r - i) → ℂ) (h : LevelSquareIntegrable μi 0 (T v) c'') : LevelSquareIntegrable μ i v c := by
  unfold LevelSquareIntegrable at h ⊢
  have e : (fun c' : Cf r i => wtI i c' * pairAt μ v v (glue i c c')) ∘ (shEq i) =
      fun c' => (κ : ℂ)⁻¹ * (wtI 0 c' * pairAt μi (T v) (T v) (glue 0 c'' c')) := by
    funext c'
    simp only [Function.comp_apply]
    rw [hT, shiftCf_glue, wtI_shEq]
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    field_simp
  have h2 := h.const_mul ((κ : ℂ)⁻¹)
  rw [← e] at h2
  exact ((shEq_mp i).integrable_comp_emb (shEq i).measurableEmbedding).mp h2

end Transfer

section Lev

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def HermitianSquareIntegrableLevelZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D 0

theorem act_tr {k r k' r' : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {zi zi' : Fin (2 * r' + k' + 1) → ℂ} {πi : Mx k' r' → (Wp →L[ℂ] Wp)}
    {πi' : Mx k' r' → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k' r' zi zi' πi πi') {M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))}
    {M' : SlopeTestRemainingChoices S (Pr (RadSp k' r' zi zi' πi πi'))} (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M')
    (x : Ix S → RadSp k r z z' π π') (a : Ix S) : T (act M x a) = act M' (fun b => T (x b)) a := by
  unfold act
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := congrArg (fun f => f (x b)) (h a b).1
  simpa using this.symm

end Lev

end Formalism.FourierDecayAlt.P5.HerD
end
end

section
open MeasureTheory Real Module
open scoped FourierTransform

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem moment_integrable {u : V → ℂ} (hu : Continuous u) (m : ℕ) (C : ℝ)
    (hdec : ∀ w, ‖u w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) (n : ℕ) (hn : n ≤ m) :
    Integrable (fun v => ‖v‖ ^ n * ‖u v‖) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hdec 0)
    have hp : 0 < (1 + ‖(0 : V)‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hint : Integrable (fun v : V => C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1))) :=
    (integrable_one_add_norm (by linarith)).const_mul C
  refine hint.mono' ((continuous_norm.pow n).mul (continuous_norm.comp hu)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have h0 : (0 : ℝ) < 1 + ‖v‖ := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ n * ‖u v‖ ≤ (1 + ‖v‖) ^ n * (C * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        gcongr
        · linarith [norm_nonneg v]
        · exact hdec v
    _ = C * ((1 + ‖v‖) ^ (n : ℝ) * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        rw [Real.rpow_natCast]; ring
    _ = C * (1 + ‖v‖) ^ ((n : ℝ) + -((m : ℝ) + finrank ℝ V + 1)) := by
        rw [← Real.rpow_add h0]
    _ ≤ C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1)) := by
        gcongr
        have : (n : ℝ) ≤ m := by exact_mod_cast hn
        linarith

theorem fourier_smooth (D : V → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ w, ‖𝓕 D w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) :
    ∃ D' : V → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  set g : V → ℂ := 𝓕 D with hg
  have hgc : Continuous g :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hD
  set h : V → ℂ := fun x => g (-x) with hh
  have hhc : Continuous h := hgc.comp continuous_neg
  have hhd : ∀ w, ‖h w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by
    intro w
    have := hdec (-w)
    rwa [norm_neg] at this
  have hmom : ∀ n : ℕ, n ≤ m → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    moment_integrable hhc m C hhd
  have hmomN : ∀ n : ℕ, (n : ℕ∞) ≤ (m : ℕ∞) → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    fun n hn => hmom n (by exact_mod_cast hn)
  have hgi : Integrable g := by
    have := moment_integrable hgc m C hdec 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hgc.aestronglyMeasurable).1 this
  have hinv : 𝓕 h = 𝓕⁻ g := (fourierInv_eq_fourier_comp_neg g).symm
  refine ⟨𝓕 h, Real.contDiff_fourier hmomN, fun j hj => ?_, fun t ht => ?_⟩
  · refine ⟨∫ v, (2 * π * ‖innerSL ℝ (E := V)‖) ^ j * (‖v‖ ^ j * ‖h v‖), fun t => ?_⟩
    rw [Real.iteratedFDeriv_fourier hmomN hhc.aestronglyMeasurable (by exact_mod_cast hj)]
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
      ((hmom j hj).const_mul _) (Filter.Eventually.of_forall fun v => ?_)
    have := VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) h v j
    simpa [mul_assoc] using this
  · rw [hinv]
    exact hD.fourierInv_fourier_eq hgi ht

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section
open MeasureTheory Real Complex
open scoped FourierTransform ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

theorem integral_fsv_eq_fourier (D : ℂ → ℂ) (s : ℂ) :
    ∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t = 𝓕 D (-(I * conj s) / (π : ℂ)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1
  unfold Formalism.FourierDecayAlt.P5.fsv
  congr 1
  rw [Complex.inner]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : s * t - conj s * conj t = ((2 * (s * t).im : ℝ) : ℂ) * I := by
    rw [← map_mul, Complex.sub_conj]
  rw [e1]
  congr 1
  push_cast
  have e2 : (-(I * conj s) / (π : ℂ) * conj t).re = -((s * t).im) / π := by
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [e2]
  push_cast
  field_simp

theorem smooth_bounded_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  refine fourier_smooth D m C hD fun w => ?_
  rw [Complex.finrank_real_complex]
  set s : ℂ := -(I * π * conj w) with hs
  have hw : w = -(I * conj s) / (π : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hs]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hns : ‖s‖ = π * ‖w‖ := by
    rw [hs, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have h := hdec s
  rw [integral_fsv_eq_fourier, ← hw] at h
  refine h.trans ?_
  have hC : 0 ≤ C := by
    have h0 := (norm_nonneg _).trans (hdec 0)
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have e : (-((m : ℝ) + ((2 : ℕ) : ℝ) + 1)) = -((m : ℝ) + 3) := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rw [hns]
  nlinarith [Real.pi_gt_three, norm_nonneg w]

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section
open MeasureTheory Module

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem integral_fderiv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : V → W} (hd : Differentiable ℝ F) (hF : Integrable F) (hF' : Integrable (fderiv ℝ F)) (v : V) :
    ∫ x, fderiv ℝ F x v = 0 := by
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := fun _ : V => (1 : ℝ)) (f' := fun _ => 0) (g := F) (g' := fderiv ℝ F) (v := v)
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (by simp) (by simpa using hF'.apply_continuousLinearMap v) (by simpa using hF)
    (fun x _ => hasFDerivAt_const _ _) (fun x _ => hd x |>.hasFDerivAt)
  simpa using h

theorem integrable_of_decay {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {u : V → W} (hu : Continuous u)
    (C : ℝ) (hdec : ∀ x, ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1))) : Integrable u :=
  ((integrable_one_add_norm (by linarith)).const_mul C).mono' hu.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hdec x)

theorem integral_iteratedFDeriv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {D : V → W} {m : ℕ} (hD : ContDiff ℝ m D) (C : ℝ)
    (hdec : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1)))
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  have hint : ∀ i ≤ m, Integrable (iteratedFDeriv ℝ i D) := fun i hi =>
    integrable_of_decay (hD.continuous_iteratedFDeriv (by exact_mod_cast hi)) C (hdec i hi)
  refine ⟨hint j hjm, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i D) :=
    hD.differentiable_iteratedFDeriv (by exact_mod_cast (show i < m by omega))
  have hF' : Integrable (fderiv ℝ (iteratedFDeriv ℝ i D)) := by
    have h := hint (i + 1) hjm
    have hc1 : ContDiff ℝ 1 (iteratedFDeriv ℝ i D) :=
      hD.iteratedFDeriv_right (by exact_mod_cast (show 1 + i ≤ m by omega))
    refine h.norm.mono' (hc1.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_fderiv_iteratedFDeriv]
  ext m'
  rw [ContinuousMultilinearMap.integral_apply (hint (i + 1) hjm)]
  simp only [iteratedFDeriv_succ_apply_left, ContinuousMultilinearMap.zero_apply]
  have h0 := integral_fderiv_eq_zero hdiff (hint i (by omega)) hF' (m' 0)
  rw [← ContinuousMultilinearMap.integral_apply (hF'.apply_continuousLinearMap (m' 0)), h0]
  rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section
open MeasureTheory Module Set
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_iteratedFDeriv_id_le (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j (id : V → V) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | _ | m
  · rw [norm_iteratedFDeriv_zero]
    simp
  · rw [norm_iteratedFDeriv_one, fderiv_id]
    exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
  · rw [iteratedFDeriv_succ_eq_comp_right]
    have e : (fun y : V => fderiv ℝ (id : V → V) y) = fun _ => ContinuousLinearMap.id ℝ V := by
      funext y
      exact fderiv_id
    rw [e, iteratedFDeriv_const_of_ne (by omega : m + 1 ≠ 0)]
    simp
    positivity

theorem norm_iteratedFDeriv_inner_self_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
  have hB := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear
    (f := (id : V → V)) (g := (id : V → V)) (N := ⊤) contDiff_id contDiff_id x (n := n) le_top
  have e : (fun y : V => (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (id y) (id y)) = fun y : V => inner ℝ y y := by
    funext y
    simp
  rw [e] at hB
  have hnB : ‖(innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)‖ ≤ 1 := norm_innerSL_le ℝ
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) * (1 + ‖x‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := norm_iteratedFDeriv_id_le i x
          have h2 := norm_iteratedFDeriv_id_le (n - i) x
          have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          gcongr
      _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]
          ring
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ := Finset.sum_nonneg fun i _ => by positivity
  calc ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ _ := hB
    _ ≤ 1 * (2 ^ n * (1 + ‖x‖) ^ 2) := mul_le_mul hnB hsum hS0 zero_le_one
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := one_mul _

theorem norm_iteratedFDerivWithin_inv_one_le (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) 1‖ ≤ i ! := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    (iteratedDerivWithin_of_isOpen isOpen_Ioi) (show (1 : ℝ) ∈ Ioi 0 by norm_num), iteratedDeriv_eq_iterate]
  have e : (fun t : ℝ => t⁻¹) = Inv.inv := rfl
  rw [e, iter_deriv_inv]
  simp

theorem norm_iteratedFDeriv_u_le (k : ℕ) (x₀ : V) :
    ‖iteratedFDeriv ℝ k (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x₀‖ ≤ (k ! * k ! * 4 ^ k) * (1 + ‖x₀‖ ^ 2)⁻¹ := by
  set q₀ : ℝ := 1 + ‖x₀‖ ^ 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  set f : V → ℝ := fun y => q₀⁻¹ * (1 + inner ℝ y y) with hf
  have hfpos : ∀ y, 0 < f y := fun y => by
    simp only [hf, real_inner_self_eq_norm_sq]; positivity
  have hfc : ContDiff ℝ k f :=
    contDiff_const.mul (contDiff_const.add (contDiff_id.inner ℝ contDiff_id))
  have hfx : f x₀ = 1 := by
    simp only [hf, real_inner_self_eq_norm_sq]
    rw [← hq₀]
    exact inv_mul_cancel₀ hq₀pos.ne'
  have hu : (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) = q₀⁻¹ • ((fun t : ℝ => t⁻¹) ∘ f) := by
    funext y
    simp only [hf, Pi.smul_apply, Function.comp, real_inner_self_eq_norm_sq, smul_eq_mul]
    field_simp
  have hgc : ContDiff ℝ k ((fun t : ℝ => t⁻¹) ∘ f) :=
    hfc.inv fun y => (hfpos y).ne'
  rw [hu, iteratedFDeriv_const_smul_apply (hgc.contDiffAt), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hq₀pos), mul_comm]
  gcongr
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x₀‖ ≤ 4 ^ i := by
    intro i hi _
    have e : f = (fun _ : V => q₀⁻¹) + q₀⁻¹ • (fun y : V => inner ℝ y y) := by
      funext y; simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hin : ContDiff ℝ i (fun y : V => inner ℝ y y) := contDiff_id.inner ℝ contDiff_id
    have hc2 : ContDiffAt ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)) x₀ :=
      ((hin.const_smul q₀⁻¹ : ContDiff ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)))).contDiffAt
    have hc1 : ContDiffAt ℝ i (fun _ : V => q₀⁻¹) x₀ := contDiffAt_const
    rw [e, iteratedFDeriv_add_apply hc1 hc2,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add,
      iteratedFDeriv_const_smul_apply hin.contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq₀pos)]
    have h1 := norm_iteratedFDeriv_inner_self_le i x₀
    have h2 : (1 + ‖x₀‖) ^ 2 ≤ 2 * q₀ := by
      rw [hq₀]; nlinarith [sq_nonneg (‖x₀‖ - 1)]
    have h3 : (2 : ℝ) ^ i * 2 ≤ 4 ^ i := by
      have : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
      rw [this]
      gcongr
      exact le_self_pow₀ (by norm_num) (by omega)
    calc q₀⁻¹ * ‖iteratedFDeriv ℝ i (fun y : V => inner ℝ y y) x₀‖ ≤ q₀⁻¹ * (2 ^ i * (2 * q₀)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 2 ^ i * 2 := by field_simp
      _ ≤ 4 ^ i := h3
  have hC : ∀ i, i ≤ k → ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) (f x₀)‖ ≤ k ! := by
    intro i hi
    rw [hfx]
    exact (norm_iteratedFDerivWithin_inv_one_le i).trans (by exact_mod_cast Nat.factorial_le hi)
  have hmain := norm_iteratedFDeriv_comp_le' (N := (k : ℕ∞)) (t := Ioi (0 : ℝ))
    (by rintro _ ⟨y, rfl⟩; exact hfpos y) (uniqueDiffOn_Ioi 0)
    (ContDiffOn.mono (contDiffOn_inv (𝕜 := ℝ)) (fun t (ht : t ∈ Ioi (0 : ℝ)) => (ne_of_gt ht : t ≠ 0))) hfc le_rfl x₀ hC hD
  calc ‖iteratedFDeriv ℝ k ((fun t : ℝ => t⁻¹) ∘ f) x₀‖ ≤ k ! * k ! * 4 ^ k := hmain
    _ = k ! * k ! * 4 ^ k := rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section
open MeasureTheory Module
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def au (j : ℕ) : ℝ := j ! * j ! * 4 ^ j

theorem au_nonneg (j : ℕ) : 0 ≤ au j := by
  unfold au
  positivity

theorem contDiff_u (n : ℕ∞) : ContDiff ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).inv (fun y => by positivity)

theorem norm_iteratedFDeriv_w_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * au i * au (n - i)) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
  refine (norm_iteratedFDeriv_mul_le (N := (n : ℕ∞)) (contDiff_u n) (contDiff_u n) x le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := norm_iteratedFDeriv_u_le (V := V) i x
  have h2 := norm_iteratedFDeriv_u_le (V := V) (n - i) x
  have hq : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖
      ≤ (n.choose i : ℝ) * (au i * (1 + ‖x‖ ^ 2)⁻¹) * (au (n - i) * (1 + ‖x‖ ^ 2)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (au_nonneg i) hq))
    _ = (n.choose i : ℝ) * au i * au (n - i) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring

theorem inv_sq_le (x : V) : (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ ≤ 4 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have ht0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hA : (0 : ℝ) < (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) := by positivity
  have hB : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
  have hr : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  have h2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖x‖)]
  have h3 : ((1 + ‖x‖) ^ 2) ^ 2 ≤ (2 * (1 + ‖x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [hr, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hB]
  nlinarith [h3]

theorem decay_of_weight {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ ∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hEb 0 (Nat.zero_le _) 0)
  have hDw : D = fun x => ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) • E x := by
    funext x
    rw [hDE x, smul_smul]
    have hq : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    field_simp
    simp
  have hwc : ContDiff ℝ m (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) :=
    (contDiff_u m).mul (contDiff_u m)
  refine ⟨hDw ▸ hwc.smul hE, ?_⟩
  set Kw : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * au l * au (i - l) with hKw
  have hKw0 : ∀ i, 0 ≤ Kw i := fun i =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (au_nonneg _)) (au_nonneg _)
  set Cn : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Kw i * B with hCn
  have hCn0 : ∀ n, 0 ≤ Cn n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hKw0 i)) hB
  refine ⟨4 * ∑ n ∈ Finset.range (m + 1), Cn n, fun j hj x => ?_⟩
  have hq0 : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  have hstep : ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
    rw [hDw]
    refine (norm_iteratedFDeriv_smul_le (N := (j : ℕ∞)) (hwc.of_le (by exact_mod_cast hj))
      (hE.of_le (by exact_mod_cast hj)) x le_rfl).trans ?_
    rw [hCn, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ *
          ‖iteratedFDeriv ℝ (j - i) E x‖
        ≤ (j.choose i : ℝ) * (Kw i * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹)) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_w_le i x) (Nat.cast_nonneg _))
            (hEb (j - i) (by omega) x) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKw0 i) hq0))
      _ = (j.choose i : ℝ) * Kw i * B * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring
  have hsum : Cn j ≤ ∑ n ∈ Finset.range (m + 1), Cn n :=
    Finset.single_le_sum (fun n _ => hCn0 n) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  calc ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := hstep
    _ ≤ (∑ n ∈ Finset.range (m + 1), Cn n) * (4 * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
        mul_le_mul hsum (inv_sq_le x) hq0 (Finset.sum_nonneg fun n _ => hCn0 n)
    _ = 4 * (∑ n ∈ Finset.range (m + 1), Cn n) * (1 + ‖x‖) ^ (-(4 : ℝ)) := by ring

theorem smooth_decay_of_weighted [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (hV : finrank ℝ V ≤ 3)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ (∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  obtain ⟨hD, C, hC⟩ := decay_of_weight hE B hEb hDE
  refine ⟨hD, ⟨C, hC⟩, fun j hj1 hjm => integral_iteratedFDeriv_eq_zero hD C (fun i hi x => ?_) j hj1 hjm⟩
  refine (hC i hi x).trans ?_
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  gcongr
  · linarith [norm_nonneg x]
  · have : (finrank ℝ V : ℝ) ≤ 3 := by exact_mod_cast hV
    linarith

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section
open MeasureTheory Real Complex Module

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

theorem unif_bound {X : Type*} (f : ℕ → X → ℝ) (m : ℕ) (h : ∀ j ≤ m, ∃ B, ∀ t, f j t ≤ B) :
    ∃ B, ∀ j ≤ m, ∀ t, f j t ≤ B := by
  choose! B hB using h
  refine ⟨∑ j ∈ Finset.range (m + 1), |B j|, fun j hj t => ?_⟩
  calc f j t ≤ B j := hB j hj t
    _ ≤ |B j| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (m + 1), |B j| :=
        Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))

theorem smooth_extension_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hE : Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t))
    (hc : ∀ t, t ≠ 0 → ContinuousAt D t)
    (hdD : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3)))
    (hdE : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ t, t ≠ 0 → D' t = D t) ∧ (∫ t, D' t = ∫ t, D t) ∧
      (∃ C', ∀ j ≤ m, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ C' * (1 + ‖t‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D') ∧ ∫ t, iteratedFDeriv ℝ j D' t = 0 := by
  set E : ℂ → ℂ := fun t => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t with hEdef
  obtain ⟨D', hD'c, -, hD'eq⟩ := smooth_bounded_of_fourier_decay D m C hD hdD
  obtain ⟨E', hE'c, hE'b, hE'eq⟩ := smooth_bounded_of_fourier_decay E m C hE hdE
  have hEc : ∀ t, t ≠ 0 → ContinuousAt E t := fun t ht => by
    show ContinuousAt (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) t
    exact (((continuous_const.add (continuous_norm.pow 2)).pow 2).continuousAt).smul (hc t ht)
  have hw : ∀ x, E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x := by
    have hcont1 : Continuous E' := hE'c.continuous
    have hcont2 : Continuous (fun x : ℂ => ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x) :=
      ((continuous_const.add (continuous_norm.pow 2)).pow 2).smul hD'c.continuous
    have h := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcont1 hcont2 (fun x hx => by
      have hx0 : x ≠ 0 := hx
      show E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x
      rw [hE'eq x (hEc x hx0), hD'eq x (hc x hx0)])
    exact fun x => congrFun h x
  obtain ⟨B, hB⟩ := unif_bound (fun j t => ‖iteratedFDeriv ℝ j E' t‖) m hE'b
  obtain ⟨-, hdec, hint⟩ := smooth_decay_of_weighted (V := ℂ) (by rw [Complex.finrank_real_complex]; norm_num) hE'c B hB hw
  have hae : D' =ᵐ[volume] D := by
    have : ∀ᵐ t ∂(volume : Measure ℂ), t ≠ 0 := by
      rw [ae_iff]; simpa using (measure_singleton (0 : ℂ))
    filter_upwards [this] with t ht
    exact hD'eq t (hc t ht)
  exact ⟨D', hD'c, fun t ht => hD'eq t (hc t ht), integral_congr_ae hae, hdec, hint⟩

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

def DecayData (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable D ∧ Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Gen

end Formalism.FourierDecayAlt.P5.HerC
end
end

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.JCx2

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem level_zero_form_integrable (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (x x' : Ix S → B.Mat k r → (Wq →L[ℂ] Wp))
    (Φ Φ' : Ix S → RadSp k r D.z D.z' D.π D.π')
    (hx : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x a)) (hx' : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x' a))
    (hΦ : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ' a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) :
    Integrable (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) c) := by
  obtain ⟨C1, -, hpair⟩ := rb_pairAt D μ hμ
  let f : Ix S → (Fin r → ℂ) × ℂ → ℂ := fun a q =>
    (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D (x' a) (B.gq D q))) (B.hsVec (B.JF D (x a) (B.gq D q)))
  have hint : ∀ a, Integrable (f a) := fun a => rb_int_pair D (x a) (x' a) (hx a) (hx' a)
  have hae : (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) c)
      =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
    filter_upwards [rb_ae_OmX] with c hc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    dsimp only
    rw [rb_weight hc]
    rfl
  refine Integrable.congr ?_ hae.symm
  exact integrable_finset_sum _ fun b _ => ((hint b).integral_prod_left).const_mul _

theorem level_zero_form_integrable_compact (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (x x' : Ix S → B.Mat k r → (Wq →L[ℂ] Wp))
    (Φ Φ' : Ix S → RadSp k r D.z D.z' D.π D.π')
    (hx : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x a)) (hx' : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x' a))
    (hΦ : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ' a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) (c : Fin r → ℂ) :
    Integrable (fun c' : Cf r 0 => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) (glue 0 c c')) := by
  have h := level_zero_form_integrable D μ hμ x x' Φ Φ' hx hx' hΦ hΦ'
  let e : {l : Fin r // (0 : Fin (r + 1)).val ≤ l.val} ≃ Fin r := Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ) e
  have hv : ∀ (c' : Cf r 0) (l : {l : Fin r // (0 : Fin (r + 1)).val ≤ l.val}),
      (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c') (e l) = c' l := fun c' l =>
    Equiv.piCongrLeft_apply_apply _ _ _ _
  have hg : ∀ c' : Cf r 0, glue 0 c c' = MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c' := by
    intro c'
    funext l
    have h1 := hv c' ⟨l, Nat.zero_le _⟩
    simp only [glue]
    exact h1.symm
  have hfun : (fun c' : Cf r 0 => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) (glue 0 c c')) =
      (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) c) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e) := by
    funext c'
    simp only [Function.comp, hg]
    congr 2
    exact Fintype.prod_equiv e (fun l => ‖c' l‖ ^ (-2 : ℤ))
      (fun a => ‖(MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c') a‖ ^ (-2 : ℤ)) (fun l => by rw [hv])
  rw [hfun]
  exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h

end Formalism.FourierDecayAlt.P5.HerC
end
end

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section L2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wt0 (c' : Cf r 0) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem level_zero_weight_measurable : Measurable (wt0 (r := r)) := by
  unfold wt0
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelZeroSquareIntegrable (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u u (glue 0 c c'))

theorem pairAt_meas0 (μ : Measure (Mt k r)) [SFinite μ] (u v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    StronglyMeasurable (fun c' : Cf r 0 => pairAt μ u v (glue 0 c c')) :=
  (pair_measurable c u v).stronglyMeasurable.integral_prod_right'

theorem hsInner_self_ofReal (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_self (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofReal]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_self, norm_pairAt_self]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_cross (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelZeroSquareIntegrable μ u c) (Iv : LevelZeroSquareIntegrable μ v c) :
    Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u v (glue 0 c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    (level_zero_weight_measurable.aestronglyMeasurable.mul (pairAt_meas0 μ u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wt0 c' * pairAt μ u v (glue 0 c c')‖ ≤
    ‖wt0 c' * pairAt μ u u (glue 0 c c')‖ + ‖wt0 c' * pairAt μ v v (glue 0 c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_le μ hμ hu hv _) (norm_nonneg _)

theorem pairAt_zero_zero (μ : Measure (Mt k r)) (c : Fin r → ℂ) :
    pairAt μ (0 : RadSp k r z z' π π') 0 c = 0 := by
  unfold pairAt
  simp [hsInner_zero_left]

theorem pairAt_add_add (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (u + v) (u + v) c = pairAt μ u u c + pairAt μ u v c + pairAt μ v u c + pairAt μ v v c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    show B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
    rw [Formalism.FourierDecayAlt.P.B6.hsInner_add_left, Formalism.FourierDecayAlt.P.B6.hsInner_add_right, Formalism.FourierDecayAlt.P.B6.hsInner_add_right]
    ring
  have e2 : (∫ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ∂μ) =
      ∫ g, ((fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)))) g ∂μ := by
    congr 1; funext g; rw [e g]; rfl
  rw [e2, integral_add' (((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)).add (int_lc μ hμ hv hu c))
      (int_lc μ hμ hv hv c),
    integral_add' ((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)) (int_lc μ hμ hv hu c),
    integral_add' (int_lc μ hμ hu hu c) (int_lc μ hμ hu hv c)]

variable (k r z z' π π') in

def squareIntegrableSmoothSubmoduleGL (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    Submodule ℂ (RadSp k r z z' π π') where
  carrier := {u | u ∈ lcSub k r z z' π π' ∧ ∀ c, LevelZeroSquareIntegrable μ u c}
  zero_mem' := ⟨(lcSub k r z z' π π').zero_mem, fun c => by
    unfold LevelZeroSquareIntegrable
    simp only [pairAt_zero_zero, mul_zero]
    exact integrable_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    refine ⟨(lcSub k r z z' π π').add_mem hu hv, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_add_add μ hμ hu hv, mul_add]
    exact (((Iu c).add (int_cross μ hμ hu hv c (Iu c) (Iv c))).add
      (int_cross μ hμ hv hu c (Iv c) (Iu c))).add (Iv c)
  smul_mem' := by
    rintro a u ⟨hu, Iu⟩
    refine ⟨(lcSub k r z z' π π').smul_mem a hu, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_smul_left, pairAt_smul_right]
    have e : (fun c' : Cf r 0 => wt0 c' * (a * ((starRingEnd ℂ) a * pairAt μ u u (glue 0 c c')))) =
        fun c' => (a * (starRingEnd ℂ) a) * (wt0 c' * pairAt μ u u (glue 0 c c')) := by
      funext c'; ring
    rw [e]
    exact (Iu c).const_mul _

theorem unimodular_multiplier_preserves_L2 (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (hm : ∀ c g, ‖m c g‖ = 1) : ∀ u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ, W u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ := by
  rintro u ⟨hu, Iu⟩
  refine ⟨mul_lc hW u hu, fun c => ?_⟩
  have e : ∀ c0, pairAt μ (W u) (W u) c0 = pairAt μ u u c0 := by
    intro c0
    unfold pairAt
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show B.hsInner ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) = _
    rw [hW u c0 (Matrix.of g), hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hm]
    simp
  unfold LevelZeroSquareIntegrable
  simp_rw [e]
  exact Iu c

theorem norm_fsv (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [this, Real.exp_zero]

end L2

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem radial_transform_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) :
    Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine ⟨jfCptLocAll Wp Wq P z z' π π' D F Φ hP hz hz' hπ hπ' hF hΦ, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => F) (fun _ => F) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hF.1.1) (fun _ => hF.1.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

theorem compact_kernel_le_L2 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') :
    herKc S P z z' π π' L st l0 D 0 ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ => exact fun _ => radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun c _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun c _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
    | waveZ w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun _ _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun _ _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
  exact key 0 Φ hΦ rfl

end Classes

end Formalism.FourierDecayAlt.P5.HerC
end
end

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

end Formalism.FourierDecayAlt.P5.HerD
end
end

section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Pr

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_fst_mul (x y : Pr V) : (x * y).1 = x.1 * y.1 := rfl

theorem pr_fst_algebraMap (a : ℂ) : (algebraMap ℂ (Pr V) a).1 = algebraMap ℂ (Module.End ℂ V) a := rfl

def sendsTo (U : Submodule ℂ V) (v : V) : Submodule ℂ (Pr V) where
  carrier := {x | x.1 v ∈ U}
  zero_mem' := by show (0 : Module.End ℂ V) v ∈ U; simp
  add_mem' := by
    intro x y hx hy
    show (x.1 + y.1) v ∈ U
    rw [LinearMap.add_apply]; exact U.add_mem hx hy
  smul_mem' := by
    intro a x hx
    show (a • x.1) v ∈ U
    rw [LinearMap.smul_apply]; exact U.smul_mem a hx

theorem sendsTo_alg_mul_alg (U : Submodule ℂ V) (v : V) {x : Pr V} (hx : x ∈ sendsTo U v) (a b : ℂ) :
    algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b ∈ sendsTo U v := by
  show (algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b).1 v ∈ U
  rw [pr_fst_mul, pr_fst_mul, pr_fst_algebraMap, pr_fst_algebraMap, Module.End.mul_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  exact U.smul_mem a (U.smul_mem b hx)

end Pr

section Num

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem UUw_mem {𝒜 : StarSubalgebra ℂ A} (s : ℂ) :
    ∀ w : List (Letter ℂ S), (UUw s w : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  intro w
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [UUw]
    refine (entSub 𝒜).mul_mem (Formalism.FourierDecayAlt.P5.HerA.ins_mem _ fun i j => ?_) ih
    show io ((Formalism.YangianSpanCharacter.T.Um (if l.plus then s else star s) : M2 A) i j) ∈ entSub 𝒜
    apply Formalism.FourierDecayAlt.P5.HerA.io_mem
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Um, 𝒜.algebraMap_mem]

theorem star_entSub {𝒜 : StarSubalgebra ℂ A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ entSub 𝒜) : star M ∈ entSub 𝒜 := by
  intro i j
  rw [Matrix.star_apply]
  exact star_mem (hM j i)

theorem mem_bot_alg {x : A} (hx : x ∈ (⊥ : StarSubalgebra ℂ A)) : ∃ a : ℂ, x = algebraMap ℂ A a := by
  rw [StarSubalgebra.mem_bot] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

end Num

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem QQi_castSucc' (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l : Fin P.r) (Y : ℂ) :
    QQi L st l.castSucc Y = (Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have h : ∀ Y' : ℂ, tprod L Y' l.val = tprod L Y' (l.val + 1) * Ts (site L l) Y' := fun Y' => by
    rw [tprod, dif_pos l.isLt]
  unfold QQi
  rw [Fin.val_castSucc, Fin.val_succ, h, h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem diag_comm {A : Type*} [Ring A] {f : A} {M : Matrix (Fin 2) (Fin 2) A} (h : ∀ i j, Commute f (M i j)) :
    Matrix.diagonal (fun _ => f) * M = M * Matrix.diagonal (fun _ => f) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq

theorem commute_inv_of {A : Type*} [Ring A] {f fi x : A} (h1 : f * fi = 1) (h2 : fi * f = 1) (h : Commute f x) :
    Commute fi x := by
  show fi * x = x * fi
  calc fi * x = fi * x * (f * fi) := by rw [h1, mul_one]
    _ = fi * (f * x) * fi := by rw [h.eq]; simp only [mul_assoc]
    _ = x * fi := by rw [← mul_assoc, h2, one_mul]

theorem waveQQ_castSucc (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (hAL : IsActualLevel X L) (l : Fin P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (hC : ∀ Y a b, Commute (mkP Wv Wv') (QQi L st l.succ Y a b)) :
    WaveQQ (QQi L st l.castSucc) (mkP Wv Wv') (mkP Wv' Wv) s := by
  intro Y
  obtain ⟨⟨h1, h2, h3⟩, hc, hci, hp⟩ :=
    Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hAL l s Wv Wv' hW hW'
  have hT : ∀ Y' : ℂ, Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') =
      Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
    intro Y'
    obtain ⟨-, hUiU, hE⟩ := Formalism.YangianSpanCharacter.Final.T_PlaneWave ℂ (Pr (RadSp P.k P.r z z' π π')) (site L l).p (site L l).c
      (site L l).ci (mkP Wv Wv') s Y' hc hci hp
    calc Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv')
        = Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * (Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
          rw [hUiU, Matrix.mul_one]
      _ = (Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          unfold Ts; rw [hE]
  have hDf : (Matrix.diagonal (fun _ : Fin 2 => mkP Wv Wv'))ᴴ = Matrix.diagonal (fun _ => mkP Wv' Wv) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
  have ha := congrArg Matrix.conjTranspose (hT (star Y))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDf] at ha
  have hci' : ∀ a b, Commute (mkP Wv' Wv) (QQi L st l.succ Y a b) := fun a b =>
    commute_inv_of h1 h2 (hC Y a b)
  have hb : Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv') =
      QQi L st l.succ Y := by
    rw [diag_comm hci', Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, h2]
    rw [show (Matrix.diagonal fun _ : Fin 2 => (1 : Pr (RadSp P.k P.r z z' π π'))) = 1 from Matrix.diagonal_one,
      Matrix.mul_one]
  rw [QQi_castSucc']
  calc Matrix.diagonal (fun _ => mkP Wv' Wv) *
        ((Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y) * Matrix.diagonal (fun _ => mkP Wv Wv')
      = (Matrix.diagonal (fun _ => mkP Wv' Wv) * (Ts (site L l) (star Y))ᴴ) * QQi L st l.succ Y *
          (Ts (site L l) Y * Matrix.diagonal (fun _ => mkP Wv Wv')) := by simp only [Matrix.mul_assoc]
    _ = ((Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * ((Ts (site L l) (star Y))ᴴ * Matrix.diagonal (fun _ => mkP Wv' Wv))) *
          QQi L st l.succ Y * (Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
        rw [ha, hT Y]
    _ = (Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * (Ts (site L l) (star Y))ᴴ *
          (Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv')) *
          Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb]; simp only [Matrix.mul_assoc]

end Wave

section WordWave

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem rr_io_wave (QQ : ℂ → M2 A) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (hW : IsWave f fi)
    (hQ : WaveQQ QQ f fi s) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    RRw QQ w * io f = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by
  obtain ⟨hVVi, -, hRR, -⟩ := Formalism.FourierDecayAlt.P.plane_wave_word_identity ℂ A S QQ f fi s w hW hQ hw
  obtain ⟨h1, h2, h3⟩ := hW
  have hsfi : star fi = f := by rw [← h3, star_star]
  have e1 : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Wd11.io_mul, h2, Formalism.FourierDecayAlt.P.Wd11.io_one]
  have hUU : UUiw s w * UUw s w = (1 : SlopeTestRemainingChoices S A) := by
    have hv : io f * UUiw s w * (UUw s w * io fi) = (1 : SlopeTestRemainingChoices S A) := by
      have := hVVi; unfold Vw Viw at this; simpa only [mul_assoc] using this
    calc UUiw s w * UUw s w = (io fi * io f) * (UUiw s w * UUw s w) * (io fi * io f) := by
          rw [e1, one_mul, mul_one]
      _ = io fi * (io f * UUiw s w * (UUw s w * io fi)) * io f := by simp only [mul_assoc]
      _ = 1 := by rw [hv, mul_one, e1]
  have hsVi : star (Viw fi s w) = io f * star (UUw s w) := by
    unfold Viw
    rw [star_mul, Formalism.FourierDecayAlt.P.Wd11.io_star, hsfi]
  have hsVV : star (Viw fi s w) * star (Vw f s w) = 1 := by
    rw [← star_mul, hVVi, star_one]
  have key : RRw QQ w * Vw f s w = star (Viw fi s w) * RRw QQ w := by
    calc RRw QQ w * Vw f s w = (star (Viw fi s w) * star (Vw f s w)) * RRw QQ w * Vw f s w := by
          rw [hsVV, one_mul]
      _ = star (Viw fi s w) * (star (Vw f s w) * RRw QQ w * Vw f s w) := by simp only [mul_assoc]
      _ = star (Viw fi s w) * RRw QQ w := by rw [hRR]
  calc RRw QQ w * io f = RRw QQ w * io f * (UUiw s w * UUw s w) := by rw [hUU, mul_one]
    _ = (RRw QQ w * Vw f s w) * UUw s w := by unfold Vw; simp only [mul_assoc]
    _ = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by rw [key, hsVi]; simp only [mul_assoc]

theorem io_apply_mul (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : ((io x : SlopeTestRemainingChoices S A) * M) a b = x * M a b := by
  simp [io, Matrix.diagonal_mul]

theorem mul_io_apply (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) a b = M a b * x := by
  simp [io, Matrix.mul_diagonal]

end WordWave

end Formalism.FourierDecayAlt.P5.HerD
end
end

section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section JF

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem residue_radial_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F)
    (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) (a b : Ix S) :
    ((RRi L st 0 w) a b).1 Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 := by
  have hlc : Φ ∈ lcSub P.k P.r z z' π π' := jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ
  have hRRlc := RRi_lc X μ L st l0 hD 0 w hw.1.2.1
  refine ⟨(hRRlc a b).1 Φ hlc, fun c => ?_⟩
  subst hz hz' hπ hπ'
  obtain ⟨ε, hε, hG⟩ := hF.1.2
  have hN : JC.NiceCoef D ε F :=
    ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hF.1.1 0 m).choose_spec.1), hF.1.1, hG⟩
  let F' : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => if b' = b then F else fun _ => 0
  have hN' : ∀ b', JC.NiceCoef D ε (F' b') := by
    intro b'
    by_cases h : b' = b
    · simp only [F', if_pos h]; exact hN
    · simp only [F', if_neg h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let x : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => B.JF D (F' b')
  let Φv : Ix S → RadSp P.k P.r D.z D.z' D.π D.π' := fun b' => if b' = b then Φ else 0
  have hx : ∀ b', x b' ∈ FFl P.k P.r D.z D.z' D.π D.π' 0 (OmPlus P.k P.r D.z D.z') := fun b' =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq D (F' b') ε hε (hN' b')
  have hΦv : ∀ b', ∀ y ∈ DomR P.k P.r D.z D.z',
      (Φv b' : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (x b') y.1 y.2 := by
    intro b' y hy
    by_cases h : b' = b
    · simp only [Φv, x, F', if_pos h]; exact hΦ y hy
    · simp only [Φv, x, F', if_neg h]
      simp only [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero, smul_zero]
      rfl
  have key := Formalism.FourierDecayAlt.P.JCx2.rma_main D.z_mem D.z'_mem X L st (M.sgn P l0) hD.2.2.1 hD.2.2.2.1 w x Φv hx hΦv
  have hsingle : act (RRi L st 0 w) Φv a = ((RRi L st 0 w) a b).1 Φ := by
    unfold act
    rw [Finset.sum_eq_single b (fun b' _ hb' => by simp only [Φv, if_neg hb', map_zero])
      (fun h => absurd (Finset.mem_univ b) h)]
    simp only [Φv, if_pos rfl]
  have hR := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure Formalism.FourierDecayAlt.P.JCx2.bcGood_closed
    (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0))
    (fun Y p q => Formalism.FourierDecayAlt.P.JCx2.bcGood_tL (Bs := D) (ε := ε) (M.sgn P l0) Y p q) w
  let G : Mx P.k P.r → (Wq →L[ℂ] Wp) :=
    Formalism.FourierDecayAlt.D.actOp (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w) F' a
  have hGN : JC.NiceCoef D ε G := by
    show JC.NiceCoef D ε (∑ b', Formalism.FourierDecayAlt.D.ap (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w a b') (F' b'))
    exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' Finset.univ _ fun b' _ => (hR a b').1 (F' b') (hN' b')
  have hpic : ∀ y ∈ DomR P.k P.r D.z D.z',
      ((((RRi L st 0 w) a b).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2 := by
    intro y hy
    rw [← hsingle, key a y hy]
    have hGV : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ B.GV P.k P.r := by
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
    have hh : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ JF.Om P.k P.r D.z D.z' :=
      ⟨hGV, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hy.1 hy.2.1 hy.2.2⟩
    simp only [resG]
    congr 1
    exact (Formalism.FourierDecayAlt.P.JCx2.bc_core _ hR F' hN' a hh).symm
  have h := level_zero_form_integrable_compact (S := Empty) D μ hD.2.1 (fun _ => G) (fun _ => G)
    (fun _ => ((RRi L st 0 w) a b).1 Φ) (fun _ => ((RRi L st 0 w) a b).1 Φ)
    (fun _ => hGN.2.1) (fun _ => hGN.2.1) (fun _ => hpic) (fun _ => hpic) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

end JF

section Gd

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

variable (S : Type) [Fintype S] [DecidableEq S] in

def gd0 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) : Submodule ℂ (RadSp P.k P.r z z' π π') where
  carrier := {v | v ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ ∧ ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
    ∀ a b, ((RRi L st 0 w) a b).1 v ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ}
  zero_mem' := ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).zero_mem, fun w _ a b => by
    rw [map_zero]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).zero_mem⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    exact ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).add_mem hu hv, fun w hw a b => by
      rw [map_add]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).add_mem (Iu w hw a b) (Iv w hw a b)⟩
  smul_mem' := by
    rintro c u ⟨hu, Iu⟩
    exact ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).smul_mem c hu, fun w hw a b => by
      rw [map_smul]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).smul_mem c (Iu w hw a b)⟩

variable {S : Type} [Fintype S] [DecidableEq S]

theorem good_domain_plane_wave (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (l : Fin P.r) (hl : l.castSucc = 0) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (h1 : multiplicationOperator Wv (fun c _ => fsv s (c l))) (h2 : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (v : RadSp P.k P.r z z' π π') (hv : v ∈ gd0 S P z z' π π' μ hD.2.1 L st l0) :
    Wv v ∈ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
  obtain ⟨hvl, hvR⟩ := hv
  refine ⟨unimodular_multiplier_preserves_L2 μ hD.2.1 h1 (fun c _ => norm_fsv _ _) v hvl, fun w hw a b => ?_⟩
  have hC := Formalism.FourierDecayAlt.P5.waveCommQQAll Wp Wq P z z' π π' X μ L st l0 hD l s Wv Wv' h1 h2
  have hWQ := waveQQ_castSucc X L st hD.2.2.1 l s Wv Wv' h1 h2 hC
  rw [hl] at hWQ
  obtain ⟨hWave, -⟩ := Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' h1 h2
  have hrr := rr_io_wave (QQi L st 0) (mkP Wv Wv') (mkP Wv' Wv) s w hWave hWQ hw.1.1
  have he := congrFun (congrFun hrr a) b
  rw [mul_io_apply, io_apply_mul] at he
  have hM : ((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b) ∈
      sendsTo (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1) v := by
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨α, hα⟩ := mem_bot_alg (star_entSub (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w) a c)
    obtain ⟨β, hβ⟩ := mem_bot_alg (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w d b)
    rw [hα, hβ]
    exact sendsTo_alg_mul_alg _ v (hvR w hw c d) α β
  have e : ((RRi L st 0 w) a b).1 (Wv v) = Wv ((((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b)).1 v) :=
    congrArg (fun x : Pr (RadSp P.k P.r z z' π π') => x.1 v) he
  rw [e]
  exact unimodular_multiplier_preserves_L2 μ hD.2.1 h1 (fun c _ => norm_fsv _ _) _ hM

theorem compact_kernel_le_good_domain (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (hr : 0 < P.r) :
    herKc S P z z' π π' L st l0 D 0 ≤ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ =>
      exact fun _ => ⟨radial_transform_square_integrable P z z' π π' μ hD.2.1 D hD.1 hz hz' hπ hπ' F hF Φ hΦ,
        fun w hw a b => residue_radial_square_integrable P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' F hF Φ hΦ w hw a b⟩
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w' s Wv Wv' a' b' Φ _ h1 h2 _ ih =>
      intro h
      have hv := ih h
      have hVw : Vw (mkP Wv Wv') s w' a' b' = mkP Wv Wv' * UUiw s w' a' b' := by
        unfold Vw; exact io_apply_mul _ _ _ _
      obtain ⟨κ, hκ⟩ := mem_bot_alg (UUiw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w' a' b')
      have e : (Vw (mkP Wv Wv') s w' a' b').1 Φ = κ • Wv Φ := by
        rw [hVw, hκ, pr_fst_mul, pr_fst_algebraMap, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
        rfl
      rw [e]
      exact (gd0 S P z z' π π' μ hD.2.1 L st l0).smul_mem κ
        (good_domain_plane_wave P z z' π π' X μ L st l0 hD l h s Wv Wv' h1 h2 Φ hv)
    | waveZ w s Wv Wv' a b Φ _ _ _ _ _ =>
      intro h
      exfalso
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
  exact key 0 Φ hΦ rfl

def ResidueSquareIntegrablePositiveRank : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D 0) x → ∀ (a : Ix S) (c : Fin P.r → ℂ), c ∈ OmX P.r →
        LevelSquareIntegrable μ 0 (act (RRi L st 0 w) x a) c

theorem rRL2Lev0Pos : ResidueSquareIntegrablePositiveRank := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' hr w hw x hx a c _
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hle := compact_kernel_le_good_domain (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' hr
  have hm : act (RRi L st 0 w) x a ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 :=
    (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1).sum_mem fun b _ => (hle (hx b)).2 w hw a b
  exact hm.2 c

def HermitianLevelZeroPositiveRank : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D 0

theorem hermitian_level_zero_positive_rank : HermitianLevelZeroPositiveRank := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr c hc
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  refine ⟨fun u hu => ?_, fun w hw x hx a =>
    rRL2Lev0Pos Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr w hw x hx a c hc⟩
  exact (compact_kernel_le_L2 (S := S) P z z' π π' μ hD.2.1 L st l0 D hD.1 hz hz' hπ hπ' hu).2 c

theorem hermitian_all_of_transport (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) : HermitianSquareIntegrableAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
  obtain ⟨Di, Xi, μi, Li, sti, T, hDi, ⟨-, ⟨κ, hκ, hpair⟩, -, hw⟩, hHer⟩ :=
    hT Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i c (fun l _ => hc l)
  have hlow := hermitian_level_zero_positive_rank Wp Wq S (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 Di hDi h1 h2 rfl rfl rfl rfl
    (by show 0 < P.r - (i : ℕ); omega) (fun _ => 1) (fun _ => one_ne_zero)
  refine ⟨fun u hu => ?_, fun w hwo x hx a => ?_⟩
  · exact level_square_integrable_of_transport μ i c μi T κ hκ hpair u _ (hlow.1 (T u) (hHer S u hu))
  · obtain ⟨-, hRR, hWO⟩ := hw S w
    have hA := hRR 0 (by omega)
    have e1 : (⟨0 + i.val, by omega⟩ : Fin (P.r + 1)) = i := Fin.ext (by simp)
    have e0 : (⟨0, by omega⟩ : Fin (P.r - i + 1)) = 0 := rfl
    rw [e1, e0] at hA
    refine level_square_integrable_of_transport μ i c μi T κ hκ hpair _ (fun _ => 1) ?_
    rw [act_tr T hA x a]
    exact hlow.2 w (hWO hwo) _ (fun b => hHer S (x b) (hx b)) a

theorem formIntOuterCpt_of_levT (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) : FormIntOuterCpt :=
  outer_form_compact_of_square (hermitian_all_of_transport hT)

end Gd

end Formalism.FourierDecayAlt.P5.HerD
end
end
