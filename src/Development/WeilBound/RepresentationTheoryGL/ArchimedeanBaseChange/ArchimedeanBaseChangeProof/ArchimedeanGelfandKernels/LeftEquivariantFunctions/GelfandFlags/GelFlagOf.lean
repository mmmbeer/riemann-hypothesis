import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.UnitaryMemGLs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnOfIteratedFDerivZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsWaveTranslateSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoClm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemNilSet

section
noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace KC

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := by
    ext g; rfl
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem mul_val_mem {x : Mat n} (hx : x ∈ GLs n) (y : G n) : x * y.val ∈ GLs n := by
  show (x * y.val).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem val_mem (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

section Congr

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (X : Mat n) : EqOn (Rd X f₁) (Rd X f₂) (GLs n) := by
  intro g hg
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (h.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg))]

theorem eu_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) (a b : Fin n) :
    EqOn (Eu s a b f₁) (Eu s a b f₂) (GLs n) := by
  intro g hg
  have h1 := rd_congr h (Matrix.single a b 1) hg
  have h2 := rd_congr h (Matrix.single a b Complex.I) hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2]

theorem epow_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) :
    ∀ (m : ℕ) (a b : Fin n), EqOn (Epow s m a b f₁) (Epow s m a b f₂) (GLs n)
  | 0, a, b => by
    intro g hg
    simp only [Epow]
    split_ifs
    · exact h hg
    · rfl
  | m + 1, a, b => by
    intro g hg
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr (epow_congr h s m c b) s a c hg

theorem gel_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) (m : ℕ) :
    EqOn (gel s m f₁) (gel s m f₂) (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr h s m a a hg

theorem zop_congr : ∀ (w : List (Bool × ℕ)) {f₁ f₂ : Mat n → V}, EqOn f₁ f₂ (GLs n) →
    EqOn (zOp w f₁) (zOp w f₂) (GLs n)
  | [], _, _, h => h
  | p :: w, _, _, h => by
    intro g hg
    exact gel_congr (zop_congr w h) p.1 p.2 hg

end Congr

section Props

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem gel_ninv (hGC : GelComm) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {F : Mat n → V}
    (hF : ContDiffOn ℝ ∞ F (GLs n)) (hN : NInv W₁ W₂ F) (s : Bool) (m : ℕ) : NInv W₁ W₂ (gel s m F) := by
  intro u hu x hx
  have h1 := ((hGC n V V s m F hF).2 x hx).2.1 u.val (val_mem u)
  rw [← h1.1]
  exact gel_congr (fun y hy => hN u hu y hy) s m hx

theorem zop_props (hGC : GelComm) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} :
    ∀ (w : List (Bool × ℕ)) (F : Mat n → V), ContDiffOn ℝ ∞ F (GLs n) → NInv W₁ W₂ F →
      ContDiffOn ℝ ∞ (zOp w F) (GLs n) ∧ NInv W₁ W₂ (zOp w F)
  | [], F, hF, hN => ⟨hF, hN⟩
  | p :: w, F, hF, hN => by
    obtain ⟨h1, h2⟩ := zop_props hGC w F hF hN
    exact ⟨(hGC n V V p.1 p.2 _ h1).1, gel_ninv hGC h1 h2 p.1 p.2⟩

theorem zop_field (hGC : GelComm) (hGF : GelFlag) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (A : Mat n → (V →L[ℂ] V)) (hA : ContDiffOn ℝ ∞ A (GLs n)) (hQ : QInv W₁ W₂ A) :
    ∀ (w : List (Bool × ℕ)) (F : Mat n → V), ContDiffOn ℝ ∞ F (GLs n) → NInv W₁ W₂ F →
      EqOn (zOp w (fun y => A y (F y))) (fun y => A y (zOp w F y)) (GLs n)
  | [], _, _, _ => fun _ _ => rfl
  | p :: w, F, hF, hN => by
    intro x hx
    have ih := zop_field hGC hGF hW A hA hQ w F hF hN
    obtain ⟨h1, h2⟩ := zop_props hGC w F hF hN
    show gel p.1 p.2 (zOp w (fun y => A y (F y))) x = A x (gel p.1 p.2 (zOp w F) x)
    rw [gel_congr ih p.1 p.2 hx]
    exact hGF n V W₁ W₂ hW A (zOp w F) hA h1 hQ h2 p.1 p.2 x hx

end Props

section Slice

variable {P Q W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem slice_eq {U : P × Q → W} {O : Set Q} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U (Set.univ ×ˢ O)) (p : P) :
    ∀ m : ℕ, ∀ x ∈ O, iteratedFDeriv ℝ m (fun y => U (p, y)) x =
      (iteratedFDeriv ℝ m U (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)
  | 0, x, _ => by
    ext h
    simp [iteratedFDeriv_zero_apply]
  | m + 1, x, hx => by
    have hS : IsOpen (Set.univ ×ˢ O : Set (P × Q)) := isOpen_univ.prod hO
    have hpx : (p, x) ∈ (Set.univ ×ˢ O : Set (P × Q)) := ⟨trivial, hx⟩
    have hev : (iteratedFDeriv ℝ m (fun y => U (p, y))) =ᶠ[nhds x]
        (fun y => (iteratedFDeriv ℝ m U (p, y)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)) :=
      Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => slice_eq hO hU p m y hy
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m U) (p, x) := by
      have h1 := hU.differentiableOn_iteratedFDerivWithin (m := m) (by exact_mod_cast ENat.natCast_lt_top m) hS.uniqueDiffOn
      have h2 : DifferentiableOn ℝ (iteratedFDeriv ℝ m U) (Set.univ ×ˢ O) :=
        h1.congr fun y hy => (iteratedFDerivWithin_of_isOpen m hS hy).symm
      exact h2.differentiableAt (hS.mem_nhds hpx)
    have hj : HasFDerivAt (fun y : Q => (p, y)) (ContinuousLinearMap.inr ℝ P Q) x := hasFDerivAt_prodMk_right p x
    have hC : HasFDerivAt (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q))
        (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)) (iteratedFDeriv ℝ m U (p, x)) :=
      ContinuousLinearMap.hasFDerivAt _
    have hcomp := hC.comp x (hdiff.hasFDerivAt.comp x hj)
    have hfun : (fun y => (iteratedFDeriv ℝ m U (p, y)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)) =
        ⇑(ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)) ∘ iteratedFDeriv ℝ m U ∘ Prod.mk p := by
      funext y; rfl
    ext h
    rw [iteratedFDeriv_succ_apply_left, hev.fderiv_eq, hfun, hcomp.fderiv]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    rw [iteratedFDeriv_succ_apply_left]
    rfl

theorem slice_cont {U : P × Q → W} {O : Set Q} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U (Set.univ ×ˢ O)) (m : ℕ) :
    ContinuousOn (fun q : P × Q => iteratedFDeriv ℝ m (fun y => U (q.1, y)) q.2) (Set.univ ×ˢ O) := by
  have hS : IsOpen (Set.univ ×ˢ O : Set (P × Q)) := isOpen_univ.prod hO
  have h1 : ContinuousOn (iteratedFDeriv ℝ m U) (Set.univ ×ˢ O) :=
    (hU.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top) hS.uniqueDiffOn).congr
      fun y hy => (iteratedFDerivWithin_of_isOpen m hS hy).symm
  have h2 := ((ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)).continuous.comp_continuousOn h1)
  refine h2.congr fun q hq => ?_
  have := slice_eq hO hU q.1 m q.2 hq.2
  simp only [Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  rw [this]

end Slice

end KC

open KC in
theorem kerComm_of (hWN : WaveN) (hWA : WaveA) : KerComm := by
  intro hWE hWS hGC hGF hIS n _ _ μ _ E w g T k hg hk W₁ W₂ hW A hA hQ f hf hfN x hx
  obtain ⟨u, hu, hu0, huN⟩ := hWN hWE hWS hGC n E W₁ W₂ f hf hfN
  have hv := hWA hGF n E W₁ W₂ hW A u hA hQ hu huN
  have h1 := hk.2.2.2 _ hv x hx
  have h2 := hk.2.2.2 _ hu x hx

  have hS : IsOpen (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) := isOpen_univ.prod isOpen_GLs
  have hgc : ContDiff ℝ ∞ fun p : ℝ × Mat n => ((g p.1 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)
  have hU' : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => ((g p.1 : ℝ) : ℂ) • u p.1 p.2) (Set.univ ×ˢ GLs n) :=
    hgc.contDiffOn.smul hu.1
  have hFs : ContDiffOn ℝ ∞ (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') (GLs n) := by
    refine hIS n ℝ MeasureTheory.volume E.V (fun t x' => ((g t : ℝ) : ℂ) • u t x') ?_ ?_ ?_
    · intro t
      exact hU'.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) fun y hy => ⟨trivial, hy⟩
    · intro m
      exact slice_cont isOpen_GLs hU' m
    · intro x₀ _
      refine ⟨Set.univ, Filter.univ_mem, Set.Icc (-T) T, isCompact_Icc, fun t ht y _ => ?_⟩
      have : T < |t| := by
        by_contra hc
        exact ht ⟨by linarith [neg_abs_le t, not_lt.1 hc], le_trans (le_abs_self t) (not_lt.1 hc)⟩
      simp [hg.2.2 t this]
  have hFN : NInv W₁ W₂ (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') := by
    intro v hv' y hy
    simp only
    congr 1
    funext t
    rw [huN t v hv' y hy]
  have hint : ∀ x' ∈ GLs n, Integrable (fun t => ((g t : ℝ) : ℂ) • u t x') := by
    intro x' hx'
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have := hU'.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨trivial, hx'⟩
      exact this
    · refine HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc fun t ht => ?_
      have : T < |t| := by
        by_contra hc
        exact ht ⟨by linarith [neg_abs_le t, not_lt.1 hc], le_trans (le_abs_self t) (not_lt.1 hc)⟩
      simp [hg.2.2 t this]
  have hcong : EqOn (fun x' => ∫ t, ((g t : ℝ) : ℂ) • A x' (u t x'))
      (fun x' => A x' (∫ t, ((g t : ℝ) : ℂ) • u t x')) (GLs n) := by
    intro x' hx'
    simp only
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint x' hx')]
    congr 1
    funext t
    rw [map_smul]
  calc act μ E k (fun y => A y (f y)) x = act μ E k (fun y => A y (u 0 y)) x := by
        simp only [act]
        congr 1
        funext y
        rw [hu0 _ (mul_val_mem hx y)]
    _ = zOp w (fun x' => ∫ t, ((g t : ℝ) : ℂ) • A x' (u t x')) x := h1
    _ = zOp w (fun x' => A x' (∫ t, ((g t : ℝ) : ℂ) • u t x')) x := zop_congr w hcong hx
    _ = A x (zOp w (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') x) :=
        zop_field hGC hGF hW A hA.1 hQ w _ hFs hFN hx
    _ = A x (act μ E k (u 0) x) := by rw [h2]
    _ = A x (act μ E k f x) := by
        congr 1
        simp only [act]
        congr 1
        funext y
        rw [hu0 _ (mul_val_mem hx y)]

end PositivityTheory.RgBcC.VC
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem memGL (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

def S2 (a : Mat n) : ℝ := ∑ i, ∑ j, ‖a i j‖ ^ 2

theorem schatten_two_nonneg (a : Mat n) : 0 ≤ S2 a := by
  unfold S2
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

theorem schatten_two_mul_le (a b : Mat n) : S2 (a * b) ≤ S2 a * S2 b := by
  unfold S2
  have key : ∀ i j, ‖(a * b) i j‖ ^ 2 ≤ (∑ k, ‖a i k‖ ^ 2) * (∑ k, ‖b k j‖ ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    calc ‖∑ k, a i k * b k j‖ ^ 2 ≤ (∑ k, ‖a i k‖ * ‖b k j‖) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          exact (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
      _ ≤ (∑ k, ‖a i k‖ ^ 2) * (∑ k, ‖b k j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ∑ j, ‖(a * b) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖a i k‖ ^ 2) * (∑ k, ‖b k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖a i k‖ ^ 2) * (∑ j, ∑ k, ‖b k j‖ ^ 2) := by rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, ‖a i j‖ ^ 2) * (∑ i, ∑ j, ‖b i j‖ ^ 2) := by rw [Finset.sum_comm (f := fun j k => ‖b k j‖ ^ 2)]

theorem lg_eq (y : Mat n) : lg y = Real.log (1 + S2 y + S2 y⁻¹) := by
  unfold lg S2
  congr 1
  simp only [Finset.sum_add_distrib]
  ring

theorem lg_mul_le (a b : Mat n) : lg (a * b) ≤ lg a + lg b := by
  have h1 := schatten_two_mul_le a b
  have h2 := schatten_two_mul_le b⁻¹ a⁻¹
  have p1 := schatten_two_nonneg a
  have p2 := schatten_two_nonneg a⁻¹
  have p3 := schatten_two_nonneg b
  have p4 := schatten_two_nonneg b⁻¹
  have p5 := schatten_two_nonneg (a * b)
  have p6 := schatten_two_nonneg (b⁻¹ * a⁻¹)
  rw [lg_eq, lg_eq, lg_eq, ← Real.log_mul (by linarith) (by linarith), Matrix.mul_inv_rev]
  apply Real.log_le_log (by linarith)
  nlinarith [mul_nonneg p1 p3, mul_nonneg p1 p4, mul_nonneg p2 p3, mul_nonneg p2 p4]

theorem lg_inv (a : Mat n) (ha : a ∈ GLs n) : lg a⁻¹ = lg a := by
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  rw [lg_eq, lg_eq, Matrix.nonsing_inv_nonsing_inv a hu]
  ring_nf

theorem lg_le_of_mul (u y : Mat n) (hy : y ∈ GLs n) : lg u ≤ lg (u * y) + lg y := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have e : u = u * y * y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc lg u = lg (u * y * y⁻¹) := congrArg lg e
    _ ≤ lg (u * y) + lg y⁻¹ := lg_mul_le _ _
    _ = lg (u * y) + lg y := by rw [lg_inv y hy]

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem lg_contOn : ContinuousOn lg (GLs n) := by
  intro y hy
  have hinv : ContinuousAt (fun x : Mat n => x⁻¹) y := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hy
  have hs : ContinuousAt (fun x : Mat n => 1 + ∑ a, ∑ b, (‖x a b‖ ^ 2 + ‖x⁻¹ a b‖ ^ 2)) y := by
    apply continuousAt_const.add
    apply tendsto_finset_sum
    intro a _
    apply tendsto_finset_sum
    intro b _
    have e1 : ContinuousAt (fun x : Mat n => x a b) y := (continuous_id.matrix_elem a b).continuousAt
    have e2 : ContinuousAt (fun x : Mat n => x⁻¹ a b) y :=
      ((continuous_id.matrix_elem a b).continuousAt).comp (f := fun x : Mat n => x⁻¹) hinv
    exact (e1.norm.pow 2).add (e2.norm.pow 2)
  apply ContinuousAt.continuousWithinAt
  unfold lg
  refine hs.log ?_
  have : 0 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  linarith

end PositivityTheory.RgBcC.VC.KN
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem nil_fix {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {u : G n} (hu : u ∈ nilSet W₁ W₂) :
    ∀ v ∈ W₁, u.val *ᵥ v = v := by
  intro v hv
  have h := hu.2.2 v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h

theorem nil_mem₂ {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {u : G n} (hu : u ∈ nilSet W₁ W₂) :
    ∀ v ∈ W₂, u.val *ᵥ v ∈ W₂ := by
  intro v hv
  have h := W₂.add_mem (hu.1 v) hv
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel] at h

theorem nil_maps {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {u : G n} (hu : u ∈ nilSet W₁ W₂)
    (hu' : u⁻¹ ∈ nilSet W₁ W₂) :
    W₁.map (Matrix.mulVecLin u.val) = W₁ ∧ W₂.map (Matrix.mulVecLin u.val) = W₂ := by
  constructor
  · apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      rw [Matrix.mulVecLin_apply, nil_fix hu v hv]
      exact hv
    · intro v hv
      exact Submodule.mem_map.mpr ⟨v, hv, by rw [Matrix.mulVecLin_apply, nil_fix hu v hv]⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      rw [Matrix.mulVecLin_apply]
      exact nil_mem₂ hW hu v hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨u⁻¹.val *ᵥ v, nil_mem₂ hW hu' v hv, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem mem_nil_of {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {N : Subgroup (G n)} (hN : (N : Set (G n)) = nilSet W₁ W₂)
    (u : N) : (u : G n) ∈ nilSet W₁ W₂ := by
  rw [← hN]
  exact u.2

theorem maps_of {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {N : Subgroup (G n)}
    (hN : (N : Set (G n)) = nilSet W₁ W₂) (u : N) :
    W₁.map (Matrix.mulVecLin (u : G n).val) = W₁ ∧ W₂.map (Matrix.mulVecLin (u : G n).val) = W₂ := by
  refine nil_maps hW (mem_nil_of hN u) ?_
  rw [← Subgroup.coe_inv]
  exact mem_nil_of hN u⁻¹

theorem cptN (hLg : LgCpt) {N : Subgroup (G n)} (hNc : IsClosed (N : Set (G n))) (R : ℝ) :
    IsCompact {u : N | lg (u : G n).val ≤ R} :=
  hNc.isClosedEmbedding_subtypeVal.isCompact_preimage (hLg n R)

theorem mul_memGL (u : G n) (y : Mat n) (hy : y ∈ GLs n) : u.val * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq] at hy ⊢
  rw [Matrix.det_mul]
  exact mul_ne_zero (by simpa [GLs] using memGL u) hy

theorem integrable_N (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] {N : Subgroup (G n)}
    (hNc : IsClosed (N : Set (G n))) (ν : Measure N) [IsFiniteMeasureOnCompacts ν] {X : Type} [NormedAddCommGroup X]
    (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ) (hR : ∀ y ∈ GLs n, R < lg y → h y = 0)
    (y : Mat n) (hy : y ∈ GLs n) : Integrable (fun u : N => h ((u : G n).val * y)) ν := by
  have hcont : Continuous (fun u : N => h ((u : G n).val * y)) :=
    hc.comp_continuous ((Units.continuous_val.comp continuous_subtype_val).mul continuous_const)
      (fun u => mul_memGL _ y hy)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (cptN hLg hNc (R + lg y)) ?_
  intro u hu
  simp only [Set.mem_setOf_eq, not_le] at hu
  apply hR _ (mul_memGL _ y hy)
  have := lg_le_of_mul ((u : G n).val) y hy
  linarith

end PositivityTheory.RgBcC.VC.KN
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contOn_avg (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] {N : Subgroup (G n)}
    (hNc : IsClosed (N : Set (G n))) (ν : Measure N) [IsFiniteMeasureOnCompacts ν] {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ)
    (hR : ∀ y ∈ GLs n, R < lg y → h y = 0) :
    ContinuousOn (fun y => ∫ u : N, h ((u : G n).val * y) ∂ν) (GLs n) := by
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Mat n) := inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  intro y₀ hy₀
  obtain ⟨K, hKn, hKs, hK⟩ := local_compact_nhds (isOpen_GLs.mem_nhds hy₀)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (lg_contOn.mono hKs)
  set S : Set N := {u : N | lg ((u : G n) : Mat n) ≤ R + M} with hSdef
  have hS : IsCompact S := cptN hLg hNc (R + M)
  have hcu : Continuous (fun u : N => ((u : G n) : Mat n)) := by fun_prop
  set T : Set (Mat n) := (fun p : N × Mat n => ((p.1 : G n) : Mat n) * p.2) '' (S ×ˢ K) with hTdef
  have hT : IsCompact T := (hS.prod hK).image (by fun_prop)
  have hTs : T ⊆ GLs n := by
    rintro _ ⟨p, hp, rfl⟩
    exact mul_memGL _ _ (hKs hp.2)
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn (hc.mono hTs)
  have hlc : Continuous (fun u : N => lg ((u : G n) : Mat n)) :=
    lg_contOn.comp_continuous hcu (fun u => memGL _)
  have hSm : MeasurableSet S := (isClosed_le hlc continuous_const).measurableSet
  have hbound : ∀ y ∈ K, ∀ u : N, ‖h (((u : G n) : Mat n) * y)‖ ≤ S.indicator (fun _ => C) u := by
    intro y hy u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      exact hC _ ⟨(u, y), ⟨hu, hy⟩, rfl⟩
    · rw [Set.indicator_of_notMem hu]
      have hu' : ¬ lg ((u : G n) : Mat n) ≤ R + M := hu
      have hyM : lg y ≤ M := hM ⟨y, hy, rfl⟩
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y (hKs hy)
      have h2 : R + M < lg ((u : G n) : Mat n) := lt_of_not_ge hu'
      rw [hR _ (mul_memGL _ _ (hKs hy)) (by linarith), norm_zero]
  apply continuousWithinAt_of_dominated (bound := S.indicator (fun _ => C))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (integrable_N hLg hNc ν h hc R hR y hy).aestronglyMeasurable
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hKn] with y hy
    exact Filter.Eventually.of_forall (hbound y hy)
  · exact (integrable_indicator_iff hSm).2 (integrableOn_const hS.measure_ne_top)
  · refine Filter.Eventually.of_forall (fun u => ?_)
    have hm : Continuous (fun y : Mat n => ((u : G n) : Mat n) * y) := by fun_prop
    exact (hc.comp hm.continuousOn (fun y hy => mul_memGL _ _ hy)) y₀ hy₀

theorem key (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k B : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n)) (Rk : ℝ)
    (hkR : ∀ y ∈ GLs n, Rk < lg y → k y = 0) {N : Subgroup (G n)} (hNc : IsClosed (N : Set (G n)))
    (ν : Measure N) [ν.IsHaarMeasure] [ν.IsInvInvariant] (hBc : ContinuousOn B (GLs n))
    (hBN : ∀ u : N, ∀ y ∈ GLs n, B ((u : G n).val * y) = B y) (φ : Mat n → E.V) (hφc : ContinuousOn φ (GLs n))
    (Rφ : ℝ) (hφR : ∀ y ∈ GLs n, Rφ < lg y → φ y = 0) :
    ∫ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) ∂μ =
      ∫ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) ∂μ := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (G n) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (G n) := ⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun m => hLg n m, by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_ge _⟩⟩
  haveI : SigmaCompactSpace N := ⟨⟨fun m : ℕ => {u : N | lg ((u : G n) : Mat n) ≤ m},
    fun m => cptN hLg hNc m, by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_ge _⟩⟩
  have iφ : ∀ y : G n, Integrable (fun u : N => φ ((u : G n).val * y.val)) ν := fun y =>
    integrable_N hLg hNc ν φ hφc Rφ hφR y.val (memGL y)
  have ik : ∀ y : G n, Integrable (fun u : N => k ((u : G n).val * y.val)) ν := fun y =>
    integrable_N hLg hNc ν k hkc Rk hkR y.val (memGL y)
  set F : G n → N → E.V := fun y u => k y.val (B y.val (φ ((u : G n).val * y.val))) with hF
  set H : G n → N → E.V := fun y u => k ((u : G n).val * y.val) (B y.val (φ y.val)) with hH
  have cu1 : Continuous (fun p : G n × N => p.1.val) := Units.continuous_val.comp continuous_fst
  have cu2 : Continuous (fun p : G n × N => ((p.2 : G n).val * p.1.val)) := by fun_prop
  have hB1 : Continuous (fun p : G n × N => B p.1.val) := hBc.comp_continuous cu1 (fun p => memGL _)
  have iF : Integrable (Function.uncurry F) (μ.prod ν) := by
    have cF : Continuous (Function.uncurry F) :=
      (hkc.comp_continuous cu1 (fun p => memGL _)).clm_apply
        (hB1.clm_apply (hφc.comp_continuous cu2 (fun p => mul_memGL _ _ (memGL _))))
    have KF : IsCompact ({y : G n | lg y.val ≤ Rk} ×ˢ {u : N | lg ((u : G n) : Mat n) ≤ Rk + Rφ}) :=
      (hLg n Rk).prod (cptN hLg hNc (Rk + Rφ))
    refine cF.integrable_of_hasCompactSupport (HasCompactSupport.intro KF ?_)
    rintro ⟨y, u⟩ hp
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_le] at hp
    show k y.val (B y.val (φ ((u : G n).val * y.val))) = 0
    by_cases hy : lg y.val ≤ Rk
    · have hu : Rk + Rφ < lg ((u : G n) : Mat n) := by
        rcases hp with h | h
        · exact absurd hy (not_le.mpr h)
        · exact h
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y.val (memGL y)
      rw [hφR _ (mul_memGL _ _ (memGL y)) (by linarith), map_zero, map_zero]
    · rw [hkR _ (memGL y) (lt_of_not_ge hy), ContinuousLinearMap.zero_apply]
  have iH : Integrable (Function.uncurry H) (μ.prod ν) := by
    have cH : Continuous (Function.uncurry H) :=
      (hkc.comp_continuous cu2 (fun p => mul_memGL _ _ (memGL _))).clm_apply
        (hB1.clm_apply (hφc.comp_continuous cu1 (fun p => memGL _)))
    have KH : IsCompact ({y : G n | lg y.val ≤ Rφ} ×ˢ {u : N | lg ((u : G n) : Mat n) ≤ Rk + Rφ}) :=
      (hLg n Rφ).prod (cptN hLg hNc (Rk + Rφ))
    refine cH.integrable_of_hasCompactSupport (HasCompactSupport.intro KH ?_)
    rintro ⟨y, u⟩ hp
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_le] at hp
    show k ((u : G n).val * y.val) (B y.val (φ y.val)) = 0
    by_cases hy : lg y.val ≤ Rφ
    · have hu : Rk + Rφ < lg ((u : G n) : Mat n) := by
        rcases hp with h | h
        · exact absurd hy (not_le.mpr h)
        · exact h
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y.val (memGL y)
      rw [hkR _ (mul_memGL _ _ (memGL y)) (by linarith), ContinuousLinearMap.zero_apply]
    · rw [hφR _ (memGL y) (lt_of_not_ge hy), map_zero, map_zero]
  have s1 : ∀ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) = ∫ u : N, F y u ∂ν := by
    intro y
    exact (ContinuousLinearMap.integral_comp_comm ((k y.val).comp (B y.val)) (iφ y)).symm
  have s6 : ∀ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) = ∫ u : N, H y u ∂ν :=
    fun y => ContinuousLinearMap.integral_apply (ik y) _
  have s3 : ∀ u : N, ∫ y : G n, F y u ∂μ = ∫ y : G n, H y u⁻¹ ∂μ := by
    intro u
    rw [← integral_mul_left_eq_self (μ := μ) (fun x : G n => H x u⁻¹) (u : G n)]
    congr 1
    ext x
    have e1 : (((u⁻¹ : N) : G n)).val * (((u : G n) * x)).val = x.val := by
      rw [← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel_left]
    have e2 : B (((u : G n) * x)).val = B x.val := by
      rw [Units.val_mul]
      exact hBN u x.val (memGL x)
    simp only [hF, hH]
    rw [e1, e2, Units.val_mul]
  calc ∫ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) ∂μ
      = ∫ y : G n, ∫ u : N, F y u ∂ν ∂μ := integral_congr_ae (Filter.Eventually.of_forall s1)
    _ = ∫ u : N, ∫ y : G n, F y u ∂μ ∂ν := integral_integral_swap iF
    _ = ∫ u : N, ∫ y : G n, H y u⁻¹ ∂μ ∂ν := integral_congr_ae (Filter.Eventually.of_forall s3)
    _ = ∫ u : N, ∫ y : G n, H y u ∂μ ∂ν := integral_inv_eq_self (fun u => ∫ y : G n, H y u ∂μ) ν
    _ = ∫ y : G n, ∫ u : N, H y u ∂ν ∂μ := (integral_integral_swap iH).symm
    _ = ∫ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y => (s6 y).symm))

end PositivityTheory.RgBcC.VC.KN
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC KN
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem integrable_of_continuousOn_of_eq_zero_lg_gt (hLg : LgCpt) {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)]
    (μ : Measure (G n)) [μ.IsHaarMeasure] {X : Type} [NormedAddCommGroup X]
    (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ)
    (hR : ∀ y ∈ GLs n, R < lg y → h y = 0) :
    Integrable (fun y : G n => h ↑y) μ := by
  have hcont : Continuous (fun y : G n => h ↑y) :=
    hc.comp_continuous Units.continuous_val (fun y => KN.memGL y)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (hLg n R) ?_
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  exact hR _ (KN.memGL y) hy

theorem kerNId_of' (hLg : LgCpt) : KerNId := by
  intro hNil hKZ hAvg n i1 i2 μ i3 E k hk hsupp hequi W₁ W₂ hW N hN ν i4 A hA hQ hcomm y hy
  obtain ⟨hNc, hInv⟩ := hNil n W₁ W₂ hW N hN
  haveI := hInv ν
  obtain ⟨Rk, hRk⟩ := hsupp
  have hkc : ContinuousOn k (GLs n) := hk.continuousOn
  have hAc : ContinuousOn A (GLs n) := hA.1.continuousOn
  obtain ⟨K, hK⟩ : ∃ K : Mat n → E.V →L[ℂ] E.V,
      K = fun x => ∫ u : N, k (((u : G n) : Mat n) * x) ∂ν := ⟨_, rfl⟩
  have hKapp : ∀ x, (∫ u : N, k (((u : G n) : Mat n) * x) ∂ν) = K x := fun x => by rw [hK]
  have hKc : ContinuousOn K (GLs n) := by
    rw [hK]
    exact KN.contOn_avg hLg hNc ν k hkc Rk hRk
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hKr : ∀ x ∈ GLs n, ∀ c : unitaryGroup (Fin n) ℂ, K (x * ↑c) = K x * E.ρ c := by
    intro x hx c
    have hint := KN.integrable_N hLg hNc ν k hkc Rk hRk x hx
    rw [← hKapp, ← hKapp]
    have e : ∀ u : N, k (((u : G n) : Mat n) * (x * (c : Mat n))) =
        k (((u : G n) : Mat n) * x) * E.ρ c := by
      intro u
      have := hequi (((u : G n) : Mat n) * x) (KN.mul_memGL _ x hx) 1 c
      simpa [mul_assoc] using this
    simp_rw [e]
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ c)).integral_comp_comm hint
  have hκc : ContinuousOn (fun x => K x * A x - A 1 * K x) (GLs n) :=
    (hKc.mul hAc).sub (continuousOn_const.mul hKc)
  have hρ : ∀ c : unitaryGroup (Fin n) ℂ, E.ρ c * E.ρ c⁻¹ = 1 := fun c => by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hκr : ∀ x ∈ GLs n, ∀ c : unitaryGroup (Fin n) ℂ,
      K (x * ↑c) * A (x * ↑c) - A 1 * K (x * ↑c) = (K x * A x - A 1 * K x) * E.ρ c := by
    intro x hx c
    rw [hKr x hx c, hA.2 x hx c, sub_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (E.ρ c) (E.ρ c⁻¹), hρ, one_mul]
  have hκi : ∀ f ∈ CE E, (∃ R : ℝ, ∀ x ∈ GLs n, R < lg x → f x = 0) →
      ∫ x : G n, (K ↑x * A ↑x - A 1 * K ↑x) (f ↑x) ∂μ = 0 := by
    rintro f hf ⟨Rf, hRf⟩
    have hfc : ContinuousOn f (GLs n) := hf.1.continuousOn
    have hF := hAvg n E W₁ W₂ hW N hN ν f hf ⟨Rf, hRf⟩
    have hBinv : ∀ (u : N), ∀ x ∈ GLs n, A (((u : G n) : Mat n) * x) = A x := fun u x hx =>
      hQ _ (KN.memGL _) (KN.maps_of hW hN u).1 (KN.maps_of hW hN u).2 x hx
    have k1 := KN.key hLg μ E k A hkc Rk hRk hNc ν hAc hBinv f hfc Rf hRf
    have k2 := KN.key hLg μ E k (fun _ => 1) hkc Rk hRk hNc ν continuousOn_const
      (fun _ _ _ => rfl) f hfc Rf hRf
    have hc := hcomm _ hF.1 hF.2 1 h1
    simp only [act, one_mul] at hc
    simp only [ContinuousLinearMap.one_apply] at k2
    simp only [hKapp] at k1 k2
    have I1 : Integrable (fun x : G n => K ↑x (A ↑x (f ↑x))) μ :=
      integrable_of_continuousOn_of_eq_zero_lg_gt hLg μ (fun x => K x (A x (f x)))
        (hKc.clm_apply (hAc.clm_apply hfc)) Rf (fun x hx h => by simp [hRf x hx h])
    have I2 : Integrable (fun x : G n => A 1 (K ↑x (f ↑x))) μ :=
      integrable_of_continuousOn_of_eq_zero_lg_gt hLg μ (fun x => A 1 (K x (f x)))
        ((A 1).continuous.comp_continuousOn (hKc.clm_apply hfc)) Rf
        (fun x hx h => by simp [hRf x hx h])
    have I3 : Integrable (fun x : G n => K ↑x (f ↑x)) μ :=
      integrable_of_continuousOn_of_eq_zero_lg_gt hLg μ (fun x => K x (f x)) (hKc.clm_apply hfc) Rf
        (fun x hx h => by simp [hRf x hx h])
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
    rw [integral_sub I1 I2, (A 1).integral_comp_comm I3, ← k1, ← k2, hc, sub_self]
  have hκ : K y * A y - A 1 * K y = 0 :=
    hKZ n μ E (fun x => K x * A x - A 1 * K x) hκc hκr hκi y hy
  rw [hKapp]
  exact sub_eq_zero.mp hκ

theorem kerNId_of (hLg : LgCpt) (_ : IntSmooth) : KerNId := kerNId_of' hLg

end PositivityTheory.RgBcC.VC
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Topology
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC.NAvgH

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def sq (A : Mat n) : ℝ := ∑ a, ∑ b, ‖A a b‖ ^ 2

theorem sq_nonneg' (A : Mat n) : 0 ≤ sq A := by
  unfold sq; positivity

theorem sq_mul_le (A B : Mat n) : sq (A * B) ≤ sq A * sq B := by
  unfold sq
  have h1 : ∀ a b, ‖(A * B) a b‖ ^ 2 ≤ (∑ c, ‖A a c‖ ^ 2) * ∑ c, ‖B c b‖ ^ 2 := by
    intro a b
    rw [Matrix.mul_apply]
    calc ‖∑ c, A a c * B c b‖ ^ 2 ≤ (∑ c, ‖A a c‖ * ‖B c b‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_mul, le_refl]
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ a, ∑ b, ‖(A * B) a b‖ ^ 2 ≤ ∑ a, ∑ b, (∑ c, ‖A a c‖ ^ 2) * ∑ c, ‖B c b‖ ^ 2 := by
        gcongr with a _ b _
        exact h1 a b
    _ = (∑ a, ∑ c, ‖A a c‖ ^ 2) * ∑ c, ∑ b, ‖B c b‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem lg_eq (y : Mat n) : lg y = Real.log (1 + sq y + sq y⁻¹) := by
  simp only [lg, sq, Finset.sum_add_distrib, add_assoc]

theorem lg_mul_le (A B : Mat n) : lg (A * B) ≤ lg A + lg B := by
  rw [lg_eq, lg_eq, lg_eq, Matrix.mul_inv_rev]
  have hA := sq_nonneg' A; have hA' := sq_nonneg' A⁻¹; have hB := sq_nonneg' B; have hB' := sq_nonneg' B⁻¹
  have hxA : 0 < 1 + sq A + sq A⁻¹ := by linarith
  have hxB : 0 < 1 + sq B + sq B⁻¹ := by linarith
  have hxAB : 0 < 1 + sq (A * B) + sq (B⁻¹ * A⁻¹) := by
    have := sq_nonneg' (A * B); have := sq_nonneg' (B⁻¹ * A⁻¹); linarith
  rw [← Real.log_mul hxA.ne' hxB.ne']
  apply Real.log_le_log hxAB
  have e1 := sq_mul_le A B
  have e2 := sq_mul_le B⁻¹ A⁻¹
  nlinarith [mul_nonneg hA hB, mul_nonneg hA' hB', mul_nonneg hA hB', mul_nonneg hA' hB]

theorem lg_inv (A : Mat n) (hA : A ∈ GLs n) : lg A⁻¹ = lg A := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  rw [lg_eq, lg_eq, Matrix.nonsing_inv_nonsing_inv A hA', add_right_comm]

theorem isOpen_GLs : IsOpen (GLs n) := by
  show IsOpen {g : Mat n | det g ≠ 0}
  exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem continuousAt_lg (x : Mat n) (hx : x ∈ GLs n) : ContinuousAt lg x := by
  have hinv : ContinuousAt (fun y : Mat n => y⁻¹) x := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx
  have hsq : Continuous (sq : Mat n → ℝ) := by
    unfold sq
    refine continuous_finset_sum _ (fun a _ => continuous_finset_sum _ (fun b _ => ?_))
    exact (((continuous_apply b).comp (continuous_apply a)).norm).pow 2
  have hpos : 0 < 1 + sq x + sq x⁻¹ := by linarith [sq_nonneg' x, sq_nonneg' x⁻¹]
  rw [show (lg : Mat n → ℝ) = fun y => Real.log (1 + sq y + sq y⁻¹) from funext lg_eq]
  exact ((continuousAt_const.add hsq.continuousAt).add (hsq.continuousAt.comp hinv)).log hpos.ne'

theorem mem_GLsG (y : G n) : y.val ∈ GLs n := by
  show det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem mem_GLs_mul {A B : Mat n} (hA : A ∈ GLs n) (hB : B ∈ GLs n) : A * B ∈ GLs n := by
  show (A * B).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hA hB

def lmulL : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap
        { toFun := fun x => M * x
          map_add' := fun x y => Matrix.mul_add M x y
          map_smul' := fun c x => Matrix.mul_smul M c x }
      map_add' := fun M M' => by ext x : 1; simp [Matrix.add_mul]
      map_smul' := fun c M => by ext x : 1; simp [Matrix.smul_mul] }

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end PositivityTheory.RgBcC.VC.NAvgH

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC.NAvgH
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nAvg_of (hIS : IntSmooth) (hLg : LgCpt) (hNU : NilUni) : NAvg := by
  intro n _ _ E W₁ W₂ hW N hN ν _ φ hφ hφR
  obtain ⟨R, hR⟩ := hφR
  obtain ⟨hNc, hinv⟩ := hNU n W₁ W₂ hW N hN
  haveI := hinv ν
  haveI : SecondCountableTopology (G n) := secondCountable_G
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨hφs, hφk⟩ := hφ
  have hφc : ContinuousOn φ (GLs n) := hφs.continuousOn
  have hmem : ∀ u : N, ∀ x ∈ GLs n, ((u : G n) : Mat n) * x ∈ GLs n :=
    fun u x hx => mem_GLs_mul (mem_GLsG _) hx
  have hlgu : ∀ u x : Mat n, x ∈ GLs n → lg u ≤ lg (u * x) + lg x := by
    intro u x hx
    have h := lg_mul_le (u * x) x⁻¹
    rwa [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hx), lg_inv x hx] at h
  have cpt : ∀ c : ℝ, IsCompact {u : N | lg ((u : G n) : Mat n) ≤ c} := fun c =>
    hNc.isClosedEmbedding_subtypeVal.isCompact_preimage (hLg n c)
  have hsupp : ∀ x₀ ∈ GLs n, ∃ U ∈ 𝓝 x₀, ∃ K : Set N, IsCompact K ∧
      ∀ u ∉ K, ∀ x ∈ U, φ (((u : G n) : Mat n) * x) = 0 := by
    intro x₀ hx₀
    refine ⟨GLs n ∩ lg ⁻¹' Set.Iio (lg x₀ + 1),
      Filter.inter_mem (isOpen_GLs.mem_nhds hx₀)
        ((continuousAt_lg x₀ hx₀).preimage_mem_nhds (Iio_mem_nhds (by linarith))),
      _, cpt (R + lg x₀ + 1), ?_⟩
    intro u hu x hx
    have hu' : ¬ lg ((u : G n) : Mat n) ≤ R + lg x₀ + 1 := hu
    have h1 := hlgu ((u : G n) : Mat n) x hx.1
    have h2 : lg x < lg x₀ + 1 := hx.2
    exact hR _ (hmem u x hx.1) (by linarith [lt_of_not_ge hu'])
  have hint : ∀ x ∈ GLs n, Integrable (fun u : N => φ (((u : G n) : Mat n) * x)) ν := by
    intro x hx
    obtain ⟨U, hU, K, hK, hKz⟩ := hsupp x hx
    have hc : Continuous (fun u : N => φ (((u : G n) : Mat n) * x)) :=
      hφc.comp_continuous (by fun_prop) (fun u => hmem u x hx)
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK (fun u hu => hKz u hu x (mem_of_mem_nhds hU)))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hmaps : ∀ U : Mat n, U ∈ GLs n → Set.MapsTo (lmulL U) (GLs n) (GLs n) :=
      fun U hU x hx => mem_GLs_mul hU hx
    have hle : ∀ m : ℕ, ((m : ℕ∞ω) ≤ ∞) := fun m => by exact_mod_cast le_top
    have hD : ∀ m : ℕ, ContinuousOn (iteratedFDeriv ℝ m φ) (GLs n) := fun m =>
      (hφs.continuousOn_iteratedFDerivWithin (hle m) isOpen_GLs.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen m isOpen_GLs hx).symm)
    have hform : ∀ (m : ℕ) (U : Mat n), U ∈ GLs n → ∀ x ∈ GLs n,
        iteratedFDeriv ℝ m (φ ∘ ⇑(lmulL U)) x =
          (iteratedFDeriv ℝ m φ (lmulL U x)).compContinuousLinearMap (fun _ => lmulL U) := by
      intro m U hU x hx
      have hopen : IsOpen (⇑(lmulL U) ⁻¹' GLs n) := isOpen_GLs.preimage (lmulL U).continuous
      have hgx : lmulL U x ∈ GLs n := hmaps U hU hx
      have hx' : x ∈ ⇑(lmulL U) ⁻¹' GLs n := hgx
      have h1 := (lmulL U).iteratedFDerivWithin_comp_right hφs isOpen_GLs.uniqueDiffOn
        hopen.uniqueDiffOn hgx (hle m)
      have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := φ ∘ ⇑(lmulL U)) m hopen hx'
      have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := φ) m isOpen_GLs hgx
      rw [← e1, ← e2]
      exact h1
    have hUc : Continuous (fun p : N × Mat n => ((p.1 : G n) : Mat n)) := by fun_prop
    have hUx : Continuous (fun p : N × Mat n => ((p.1 : G n) : Mat n) * p.2) := by fun_prop
    have key := hIS n N ν E.V (fun u => φ ∘ ⇑(lmulL ((u : G n) : Mat n)))
      (fun u => hφs.comp (lmulL ((u : G n) : Mat n)).contDiff.contDiffOn (hmaps _ (mem_GLsG _)))
      (fun m => by
        let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin m => Mat n) (fun _ : Fin m => Mat n) E.V
        have hC : Continuous (fun p : N × Mat n => C (fun _ => lmulL ((p.1 : G n) : Mat n))) :=
          C.cont.comp (continuous_pi fun _ => lmulL.continuous.comp hUc)
        have hDp : ContinuousOn
            (fun p : N × Mat n => iteratedFDeriv ℝ m φ (lmulL ((p.1 : G n) : Mat n) p.2))
            (Set.univ ×ˢ GLs n) :=
          (hD m).comp hUx.continuousOn (fun p hp => hmem p.1 p.2 hp.2)
        refine (hC.continuousOn.clm_apply hDp).congr (fun p hp => ?_)
        exact (hform m _ (mem_GLsG _) p.2 hp.2).trans rfl)
      hsupp
    exact key
  · intro g hg k
    have e : ∀ u : N, φ (((u : G n) : Mat n) * (g * ↑k)) = E.ρ k⁻¹ (φ (((u : G n) : Mat n) * g)) := by
      intro u
      rw [← Matrix.mul_assoc]
      exact hφk _ (hmem u g hg) k
    show ∫ u : N, φ (((u : G n) : Mat n) * (g * ↑k)) ∂ν = E.ρ k⁻¹ (∫ u : N, φ (((u : G n) : Mat n) * g) ∂ν)
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact ContinuousLinearMap.integral_comp_comm _ (hint g hg)
  · intro u₀ hu₀ x hx
    have hu₁ : u₀ ∈ N := by
      rw [← SetLike.mem_coe, hN]
      exact hu₀
    set u₁ : N := ⟨u₀, hu₁⟩ with hu₁def
    have key : ∀ f : N → E.V, ∫ u, f (u * u₁) ∂ν = ∫ u, f u ∂ν := by
      intro f
      rw [← integral_inv_eq_self (fun u => f (u * u₁)) ν]
      have hre : ∀ u : N, f (u⁻¹ * u₁) = (fun v => f v⁻¹) (u₁⁻¹ * u) := fun u => by
        simp [_root_.mul_inv_rev]
      simp_rw [hre]
      rw [integral_mul_left_eq_self (fun v => f v⁻¹) u₁⁻¹, integral_inv_eq_self f ν]
    show ∫ u : N, φ (((u : G n) : Mat n) * ((u₀ : Mat n) * x)) ∂ν = ∫ u : N, φ (((u : G n) : Mat n) * x) ∂ν
    rw [← key (fun u => φ (((u : G n) : Mat n) * x))]
    congr 1
    ext u
    simp [hu₁def, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

end PositivityTheory.RgBcC.VC
end
end

section
noncomputable section

namespace PositivityTheory.RgBcC.VC

theorem trZero : TrZero := by
  intro V _ _ _ B T e i c hc hei heB hTe
  let t : (V →L[ℂ] V) → ℂ := fun A => LinearMap.trace ℂ V (A : V →ₗ[ℂ] V)
  have tadd : ∀ A A' : V →L[ℂ] V, t (A + A') = t A + t A' := fun A A' => by
    simp only [t, ContinuousLinearMap.coe_add, map_add]
  have tneg : ∀ A : V →L[ℂ] V, t (-A) = -t A := fun A => by
    simp only [t, ContinuousLinearMap.coe_neg, map_neg]
  have tsmul : ∀ (a : ℂ) (A : V →L[ℂ] V), t (a • A) = a * t A := fun a A => by
    simp only [t, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul]
  have tcomm : ∀ A A' : V →L[ℂ] V, t (A * A') = t (A' * A) := fun A A' =>
    LinearMap.trace_mul_comm ℂ (A : V →ₗ[ℂ] V) (A' : V →ₗ[ℂ] V)
  set X := B * T with hXdef
  have hX : e * X = -(X * e) := by
    calc e * X = (e * B) * T := (mul_assoc _ _ _).symm
      _ = -(B * e) * T := by rw [heB]
      _ = -(B * (e * T)) := by rw [neg_mul, mul_assoc]
      _ = -(B * (T * e)) := by rw [hTe]
      _ = -(X * e) := by rw [hXdef, mul_assoc]
  have h1 : X * (e * i + i * e) = c • X := by rw [hei, mul_smul_comm, mul_one]
  have key : c * t X = 0 := by
    rw [← tsmul, ← h1, mul_add, tadd, ← mul_assoc, ← mul_assoc, tcomm (X * i) e, ← mul_assoc, hX,
      neg_mul, tneg, add_neg_cancel]
  exact (mul_eq_zero.mp key).resolve_left hc

end PositivityTheory.RgBcC.VC
end
end

section
noncomputable section

open Matrix Module

namespace PositivityTheory.RgBcC.VC.GFA

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

variable {n : ℕ}

theorem mulVec_eq_sum (g : Mat n) (c : Fin n → ℂ) : g *ᵥ c = ∑ j, c j • (fun i => g i j) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem adapted (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) :
    ∃ (g : Mat n) (blk : Fin n → ℕ), IsUnit g ∧ (∀ j, blk j ≤ 2) ∧
      (∀ c, g *ᵥ c ∈ W₁ ↔ ∀ j, blk j ≠ 0 → c j = 0) ∧ (∀ c, g *ᵥ c ∈ W₂ ↔ ∀ j, blk j = 2 → c j = 0) := by
  classical
  obtain ⟨b₁, hb₁, hspan₁, hli₁'⟩ := exists_linearIndependent ℂ (W₁ : Set (Fin n → ℂ))
  have hli₁ : LinearIndepOn ℂ id b₁ := hli₁'
  have hb₁₂ : b₁ ⊆ (W₂ : Set (Fin n → ℂ)) := hb₁.trans hW
  set b₂ := hli₁.extend hb₁₂ with hb₂def
  have hli₂ : LinearIndepOn ℂ id b₂ := hli₁.linearIndepOn_extend hb₁₂
  have hb₂W : b₂ ⊆ (W₂ : Set (Fin n → ℂ)) := hli₁.extend_subset hb₁₂
  have h12 : b₁ ⊆ b₂ := hli₁.subset_extend hb₁₂
  have hW₂s : (W₂ : Set (Fin n → ℂ)) ⊆ Submodule.span ℂ b₂ := hli₁.subset_span_extend hb₁₂
  set B := Module.Basis.extend hli₂ with hBdef
  have h23 : b₂ ⊆ Set.range B := by rw [Module.Basis.range_extend]; exact hli₂.subset_extend _
  have : Finite (hli₂.extend (Set.subset_univ b₂)) := Module.Finite.finite_basis B
  haveI : Fintype (hli₂.extend (Set.subset_univ b₂)) := Fintype.ofFinite _
  have hcard : Fintype.card (hli₂.extend (Set.subset_univ b₂)) = n := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  set B' := B.reindex (Fintype.equivFinOfCardEq hcard) with hB'def
  have hrange : Set.range B' = Set.range B := by
    rw [hB'def, Module.Basis.coe_reindex]
    exact (Fintype.equivFinOfCardEq hcard).symm.surjective.range_comp _
  refine ⟨Matrix.of fun i j => B' j i, fun j => if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2, ?_, ?_, ?_, ?_⟩
  · rw [← linearIndependent_cols_iff_isUnit]
    exact B'.linearIndependent
  · intro j; dsimp only; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₁ : W₁ = Submodule.span ℂ (B' '' {j | B' j ∈ b₁}) := by
      calc W₁ = Submodule.span ℂ (W₁ : Set (Fin n → ℂ)) := (Submodule.span_eq W₁).symm
        _ = Submodule.span ℂ b₁ := hspan₁.symm
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 (h12 hv)
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₁, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₁ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0 at hj
      rw [if_pos h'] at hj
      exact hj rfl
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₁
      by_contra hb
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0
      rw [if_neg hb]; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₂ : W₂ = Submodule.span ℂ (B' '' {j | B' j ∈ b₂}) := by
      calc W₂ = Submodule.span ℂ b₂ :=
            le_antisymm (fun x hx => hW₂s hx) (Submodule.span_le.2 hb₂W)
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 hv
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₂, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₂ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2 at hj
      by_cases h1 : B' j ∈ b₁
      · rw [if_pos h1] at hj; exact absurd hj (by decide)
      · rw [if_neg h1, if_pos h'] at hj; exact absurd hj (by decide)
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₂
      by_contra hb
      have hb1 : B' j ∉ b₁ := fun h1 => hb (h12 h1)
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2
      rw [if_neg hb1, if_neg hb]

end PositivityTheory.RgBcC.VC.GFA
end
end

section
noncomputable section

open Matrix Module
open scoped ContDiff

namespace PositivityTheory.RgBcC.VC.GFB

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def lmul (a b : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y * b
      map_add' := fun y z => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c y => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem mul_mem_GLs {a y b : Mat n} (ha : a ∈ GLs n) (hy : y ∈ GLs n) (hb : b ∈ GLs n) : a * y * b ∈ GLs n := by
  show (a * y * b).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero ha hy) hb


end PositivityTheory.RgBcC.VC.GFB
end
end

section
noncomputable section

open Matrix Module
open scoped ContDiff

namespace PositivityTheory.RgBcC.VC.GFC

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC.GFB
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Blocks

variable (blk : Fin n → ℕ)

def S0 (c : Fin n → ℂ) : Prop := ∀ j, blk j ≠ 0 → c j = 0

variable {blk}

end Blocks

end PositivityTheory.RgBcC.VC.GFC
end
end

section
namespace PositivityTheory.RgBcC.VC

theorem vcOf : PositivityTheory.RgBcC.VCOf := by
  intro hWE hWS hMA hGC hGF hFF hNU hKZ
  have hKC : KerComm := kerComm_of GlobalTheory.CompanionTheory.WaveInv.waveN GlobalTheory.CompanionTheory.WaveField.waveA
  have hKN : KerNId := kerNId_of' GlobalTheory.CompanionTheory.LgBound.lgCpt
  have hNA : NAvg := nAvg_of GlobalTheory.CompanionTheory.ParamInt.intSmooth GlobalTheory.CompanionTheory.LgBound.lgCpt hNU
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ k val τ hMult d W₁ W₂ hW hW1 hd2 hd1 N hN ν _
  letI : NormedAddCommGroup (RgTw.Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (RgTw.Mat n) := Matrix.normedSpace
  obtain ⟨H, hHs, hHh, hHtr, hHk, hHq, hHd⟩ := hFF n W₁ W₂ hW hW1
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := hMult
  have hcl : IsClosed (N : Set (RgTw.G n)) := by
    rw [hN]
    have hc : ∀ v : Fin n → ℂ, Continuous (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) := fun v =>
      (Units.continuous_val.sub continuous_const).matrix_mulVec continuous_const
    have e : nilSet W₁ W₂ = (⋂ v, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' (W₂ : Set (Fin n → ℂ))) ∩
        (⋂ v ∈ W₂, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' (W₁ : Set (Fin n → ℂ))) ∩
        (⋂ v ∈ W₁, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' {0}) := by
      ext u
      simp only [nilSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        SetLike.mem_coe, Set.mem_singleton_iff, and_assoc]
    rw [e]
    refine ((isClosed_iInter fun v => W₂.closed_of_finiteDimensional.preimage (hc v)).inter
      (isClosed_biInter fun v _ => W₁.closed_of_finiteDimensional.preimage (hc v))).inter
      (isClosed_biInter fun v _ => isClosed_singleton.preimage (hc v))
  let A : RgTw.Mat n → E.V →L[ℂ] E.V := fun x => ε (H x)
  have hA : IsField E A := by
    refine ⟨(LinearMap.toContinuousLinearMap ε).contDiff.comp_contDiffOn hHs, ?_⟩
    intro x hx k0
    have hkG : ((k0 : Matrix (Fin n) (Fin n) ℂ) : RgTw.Mat n) ∈ GLs n := by
      have hu := Matrix.det_of_mem_unitary k0.2
      exact right_ne_zero_of_mul_eq_one hu.1
    have h := hCx.frε _ hkG (H x) (hHh x hx)
    rw [hCx.onK] at h
    show ε (H (x * k0)) = E.ρ k0⁻¹ * ε (H x) * E.ρ k0
    rw [hHk x hx k0, mul_assoc (E.ρ k0⁻¹), h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hQ : QInv W₁ W₂ A := by
    intro q hq h1 h2 x hx
    simp only [A, hHq q hq h1 h2 x hx]
  have hdG : (d : RgTw.Mat n) ∈ GLs n := mem_GLs d
  have hAd : A d = -A 1 := by
    simp only [A, hHd _ hdG hd2 hd1, map_neg]
  have hone : ∀ i, MeasureTheory.Integrable (fun u : N => trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n)))) ν ∧
      ∫ u : N, trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) ∂ν = 0 := by
    intro i
    obtain ⟨hb, hker⟩ := hks i
    obtain ⟨hsm, ⟨R, hR⟩, hbi, -⟩ := hker
    have hI : MeasureTheory.Integrable (fun u : N => ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) ν :=
      KN.integrable_N GlobalTheory.CompanionTheory.LgBound.lgCpt hcl ν (ks i) hsm.continuousOn R hR _ hdG
    refine ⟨(trT T).integrable_comp hI, ?_⟩
    rw [ContinuousLinearMap.integral_comp_comm _ hI]
    have hcomm := hKC hWE hWS hGC hGF GlobalTheory.CompanionTheory.ParamInt.intSmooth n μ E (w i) (g i) τ (ks i) hb (hks i).2
      W₁ W₂ hW A hA hQ
    have key := hKN hNU hKZ hNA n μ E (ks i) hsm ⟨R, hR⟩ hbi W₁ W₂ hW N hN ν A hA hQ hcomm _ hdG
    rw [hAd] at key
    have h1G : (1 : RgTw.Mat n) ∈ GLs n := one_mem_GLs
    rw [trT_apply]
    refine trZero E.V _ T (ε (H 1)) (ι (H 1)) ((H 1 * H 1).trace) hHtr
      (hCx.car _ _ (hHh 1 h1G) (hHh 1 h1G)) ?_ (hCx.Tε _)
    have : ∀ B : E.V →L[ℂ] E.V, B * -ε (H 1) = -(B * ε (H 1)) := fun B => by rw [mul_neg]
    rw [this] at key
    exact key.symm
  have hsum : ∀ u : N, phiOf E T k ((u : RgTw.G n) * d) =
      ∑ i, c i * trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) := by
    intro u
    have hm : (((u : RgTw.G n) * d : RgTw.G n) : RgTw.Mat n) ∈ GLs n := mem_GLs _
    rw [phiOf, ← trT_apply, hk _ hm, map_sum]
    simp only [map_smul, smul_eq_mul, Units.val_mul]
  simp only [hsum]
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => (hone i).1.const_mul (c i))]
  simp [MeasureTheory.integral_const_mul, (hone _).2]

end PositivityTheory.RgBcC.VC
end
