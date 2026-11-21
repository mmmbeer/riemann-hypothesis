import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicScalarSection
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocSec
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley

section
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

theorem det_ne_zero_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, Matrix.det_neg] at this
    intro h3
    rw [h3, zero_mul] at this
    simp at this
  exact h2 h1.symm

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2
  (det_ne_zero_of_inG hx))).unit, hx⟩

theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.SiegelWeilFormula

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toC (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ) (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := by
    have hv : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hv, L.map_add, L.map_smul, L.map_smul, hL, RingHom.id_apply, smul_eq_mul]
    simp only [Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  cont := L.cont

theorem cauchy_riemann_derivative_eq (A : M2 n) (Φ : M2 n → ℂ) (x : M2 n) (d1 d2 : ℂ)
    (h1 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z1 A) t)) d1 0)
    (h2 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z2 A) t)) d2 0) : rC A Φ x = d1 + Complex.I * d2 := by
  have key : ∀ E : M2 n, (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • E))) = fun t : ℝ => Φ (x * II.cE E t) := by
    intro E; funext t; simp only [II.cE, Complex.coe_smul]
  change deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z1 A))) 0 +
    Complex.I * deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z2 A))) 0 = _
  rw [key, key, h1.deriv, h2.deriv]

theorem crLem_of (hsec : LocSec) (hfib : Fib) (ha : CauchyRiemannFacts) : CRLem := by
  intro n m e φ Φ Ω hΩ hGΩ hΦ hΦφ hlaw hrC
  classical
  have hF0 : ∀ y : GR n, F0 m 0 e y ≠ 0 := by
    intro y
    rw [ha.1]
    unfold holomorphicScalarSection
    exact mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_inG y.2)) (zpow_ne_zero _ (AbsSt.detU1 n y).1)
  set H : Matrix (Fin n) (Fin n) ℂ → ℂ := fun Z =>
    if h : ∃ y : GR n, zOfE (mR y) = Z then φ h.choose / F0 m 0 e h.choose else 0 with hHdef
  have hH : ∀ y : GR n, φ y = F0 m 0 e y * H (zOfE (mR y)) := by
    intro y
    have hex : ∃ y' : GR n, zOfE (mR y') = zOfE (mR y) := ⟨y, rfl⟩
    simp only [hHdef, dif_pos hex]
    have hz : zOfE (mR hex.choose) = zOfE (mR y) := hex.choose_spec
    have hk := hfib n hex.choose y hz
    have hkK : (hex.choose⁻¹ * y) ∈ AbsSt.KR n := hk
    have e1 : y = hex.choose * (hex.choose⁻¹ * y) := by group
    have h1 : φ y = φ hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact hlaw _ _ hk
    have h2 : F0 m 0 e y = F0 m 0 e hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact ((AbsSt.mult n m 0 e).1 _ _ hkK).1
    rw [h1, h2]
    field_simp [hF0 hex.choose]
  refine ⟨fun Z => H (Matrix.of Z), ?_, fun y => ?_⟩
  swap
  · simp only [↓reduceIte]
    exact hH y
  intro Z0' hZ0
  set Z0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of Z0' with hZ0def
  obtain ⟨s, hs, hsd⟩ := hsec n Z0 hZ0
  obtain ⟨hxG, hxd, hxz⟩ := hs.self_of_nhds
  set x0 := s Z0 with hx0
  set y0 := toGR x0 hxG with hy0
  have hu1 : (u1 x0).det ≠ 0 := (AbsSt.detU1 n y0).1
  obtain ⟨hzd, hFd, hlow, hsig, hW⟩ := ha.2 n x0 hxd hu1
  have hFx0 : holomorphicScalarSection m e x0 ≠ 0 := by
    have := hF0 y0
    rwa [ha.1] at this
  have heq : H =ᶠ[𝓝 Z0] fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹ := by
    filter_upwards [hs] with Z hZ
    obtain ⟨hG, -, hzZ⟩ := hZ
    have h1 := hH (toGR (s Z) hG)
    rw [mR_toGR, hzZ, ← hΦφ (toGR (s Z) hG), mR_toGR] at h1
    have h2 : F0 m 0 e (toGR (s Z) hG) = holomorphicScalarSection m e (s Z) := by rw [ha.1, mR_toGR]
    have h4 : holomorphicScalarSection m e (s Z) ≠ 0 := by rw [← h2]; exact hF0 _
    rw [← div_eq_mul_inv, eq_div_iff h4, mul_comm, ← h2, ← h1]
  have hΦd : DifferentiableAt ℝ Φ x0 :=
    (hΦ.contDiffAt (hΩ.mem_nhds (hGΩ hxG))).differentiableAt (by simp)
  have hsd' : DifferentiableAt ℝ s Z0 := hsd.differentiableAt one_ne_zero
  have hFr : DifferentiableAt ℝ (holomorphicScalarSection m e) x0 := (hFd m e).restrictScalars ℝ
  have hzr : DifferentiableAt ℝ zOfE x0 := hzd.restrictScalars ℝ
  have hR : DifferentiableAt ℝ (fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹) Z0 :=
    (hΦd.comp Z0 hsd').mul ((hFr.comp Z0 hsd').inv hFx0)
  have hHd : DifferentiableAt ℝ H Z0 := hR.congr_of_eventuallyEq heq
  set L := fderiv ℝ H Z0 with hLdef
  have hHd' : DifferentiableAt ℝ H (zOfE x0) := by rw [hxz]; exact hHd

  have key : ∀ Q : Matrix (Fin n) (Fin n) ℂ,
      L (Complex.I • (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) =
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) := by
    intro Q
    set g : M2 n → ℂ := fun x => holomorphicScalarSection m e x * H (zOfE x) with hg
    have hcurve : ∀ E : M2 n, sig E = E → ∀ t : ℝ, Φ (x0 * II.cE E t) = g (x0 * II.cE E t) := by
      intro E hE t
      have hp : InG (x0 * II.cE E t) := inG_mul hxG (inG_cE hE t)
      have := hH (toGR _ hp)
      rw [mR_toGR, ha.1, mR_toGR] at this
      rw [← hΦφ (toGR _ hp), mR_toGR] at this
      exact this
    have hr : rC (lowQ Q) Φ x0 = 0 := hrC y0 Q
    have hder : ∀ E : M2 n, sig E = E → HasDerivAt (fun t : ℝ => Φ (x0 * II.cE E t))
        (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E) * H Z0 + holomorphicScalarSection m e x0 * L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
      intro E hE
      have hc : HasDerivAt (fun t : ℝ => x0 * II.cE E t) (x0 * E) 0 :=
        (II.mulL x0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 E)
      have hc0 : x0 * II.cE E 0 = x0 := by rw [II.cE_zero, Matrix.mul_one]
      have hFc : HasDerivAt (fun t : ℝ => holomorphicScalarSection m e (x0 * II.cE E t)) (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E)) 0 := by
        have h : HasFDerivAt (holomorphicScalarSection m e) ((fderiv ℂ (holomorphicScalarSection m e) x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact (hFd m e).hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hzc : HasDerivAt (fun t : ℝ => zOfE (x0 * II.cE E t)) (fderiv ℂ zOfE x0 (x0 * E)) 0 := by
        have h : HasFDerivAt zOfE ((fderiv ℂ zOfE x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact hzd.hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hHc : HasDerivAt (fun t : ℝ => H (zOfE (x0 * II.cE E t))) (L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
        have h : HasFDerivAt H L (zOfE (x0 * II.cE E 0)) := by
          rw [hc0, hxz]; exact hHd.hasFDerivAt
        exact h.comp_hasDerivAt (0 : ℝ) hzc
      have hprod := hFc.mul hHc
      rw [hc0, hxz] at hprod
      refine hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      exact hcurve E hE t
    rw [cauchy_riemann_derivative_eq (lowQ Q) Φ x0 _ _ (hder _ (conj_real_part_fixed _)) (hder _ (conj_imaginary_part_fixed _))] at hr
    have hsum : ∀ (D : M2 n →L[ℂ] Matrix (Fin n) (Fin n) ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I • D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← D.map_smul, ← D.map_add, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsum' : ∀ (D : M2 n →L[ℂ] ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I * D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← smul_eq_mul Complex.I (D _), ← D.map_smul, ← D.map_add, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsumF : fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z1 (lowQ Q)) + Complex.I * fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z2 (lowQ Q)) =
        0 := (hsum' _).trans ((hlow Q).2 m e)
    have hsumZ := hsum (fderiv ℂ zOfE x0)
    rw [(hlow Q).1] at hsumZ
    have hv1 : fderiv ℂ zOfE x0 (x0 * Z1 (lowQ Q)) = -(Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) :=
      eq_neg_of_add_eq_zero_left hsumZ
    rw [hv1, map_neg] at hr
    have hr2 : holomorphicScalarSection m e x0 * (-L (Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) +
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) = 0 := by
      rw [← hr]
      linear_combination (-(H Z0)) * hsumF
    rcases mul_eq_zero.1 hr2 with h | h
    · exact absurd h hFx0
    · linear_combination -h

  have hsurj : ∀ v : Matrix (Fin n) (Fin n) ℂ, ∃ Q, fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)) = v := by
    intro v
    have hWu : IsUnit (WM x0).det := isUnit_iff_ne_zero.2 (hW hxG)
    have hUu : IsUnit (u1 x0).det := isUnit_iff_ne_zero.2 hu1
    refine ⟨((-(2 * Complex.I)) • ((WM x0)⁻¹ * v * u1 x0))ᴴ, ?_⟩
    rw [Z2, Matrix.mul_smul, map_smul, Matrix.mul_sub, map_sub, (hlow _).1, hsig, Matrix.conjTranspose_conjTranspose,
      zero_sub]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul]
    have : WM x0 * ((WM x0)⁻¹ * v * u1 x0) * (u1 x0)⁻¹ = v := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hUu, Matrix.mul_one]
    rw [this]
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    field_simp
  have hLC : ∀ v, L (Complex.I • v) = Complex.I * L v := by
    intro v
    obtain ⟨Q, hQ⟩ := hsurj v
    have := key Q
    rw [hQ] at this
    exact this
  have hC : HasFDerivAt H (toC L hLC) Z0 :=
    hasFDerivAt_of_restrictScalars ℝ hHd.hasFDerivAt (by ext; rfl)
  have hC' : DifferentiableAt ℂ H Z0 := hC.differentiableAt
  exact (hC'.comp Z0' (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv.differentiableAt).differentiableWithinAt

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section
noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Mn (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cT {ι : Type} [Fintype ι] : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Mᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun r M => by
        ext i j
        simp [conjTranspose_apply, Complex.conj_ofReal] }

theorem contDiffAt_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    {f g : E → Matrix ι ι ℂ} {x : E} {k : WithTop ℕ∞} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    ContDiffAt ℝ k (fun y => f y * g y) x := by
  have hf' : ∀ i j, ContDiffAt ℝ k (fun y => f y i j) x := fun i j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j
  have hg' : ∀ i j, ContDiffAt ℝ k (fun y => g y i j) x := fun i j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hg i) j
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hf' i l).mul (hg' l j)

theorem contDiff_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    {f g : E → Matrix ι ι ℂ} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun y => f y * g y) :=
  contDiff_iff_contDiffAt.2 fun x => contDiffAt_mul' hf.contDiffAt hg.contDiffAt

private theorem hasDerivAt_exp_smul_apply_zero {ι : Type} [Fintype ι] (M0 : Matrix ι ι ℂ) (a b : ι) :
    AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M a b) M0 := by
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) b).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) a)).analyticAt M0

private theorem analyticAt_det_of_analyticAt_entries {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ)
    (F : Matrix ι ι ℂ → Matrix ι ι ℂ) (hF : ∀ a b, AnalyticAt ℂ (fun M => F M a b) M0) :
    AnalyticAt ℂ (fun M => (F M).det) M0 := by
  have e : (fun M => (F M).det) =
      ∑ σ : Equiv.Perm ι, fun M => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ l, F M (σ l) l := by
    ext M
    simp [Matrix.det_apply, Finset.sum_apply, Units.smul_def, zsmul_eq_mul]
  rw [e]
  refine Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul ?_
  have h := Finset.analyticAt_prod (𝕜 := ℂ) Finset.univ (f := fun l M => F M (σ l) l) (c := M0)
    fun l _ => hF _ _
  have e2 : (∏ l : ι, fun M : Matrix ι ι ℂ => F M (σ l) l) = fun M => ∏ l, F M (σ l) l := by
    ext M
    simp [Finset.prod_apply]
  rwa [e2] at h

theorem analyticAt_adj {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) (i j : ι) :
    AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M.adjugate i j) M0 := by
  simp only [Matrix.adjugate_apply]
  refine analyticAt_det_of_analyticAt_entries M0 (fun M => M.updateRow j (Pi.single i 1)) fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne h]
    exact hasDerivAt_exp_smul_apply_zero M0 a b

theorem contDiffAt_inv {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) (h : M0.det ≠ 0)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun M : Matrix ι ι ℂ => M⁻¹) M0 := by
  have hd : AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M.det) M0 :=
    analyticAt_det_of_analyticAt_entries M0 (fun M => M) fun a b => hasDerivAt_exp_smul_apply_zero M0 a b
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have key : ContDiffAt ℝ k (fun M : Matrix ι ι ℂ => (M.det)⁻¹ * M.adjugate i j) M0 :=
    ((hd.inv h).mul (analyticAt_adj M0 i j)).contDiffAt.restrict_scalars ℝ
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun M => ?_)
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

theorem contDiffAt_fromBlocks {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C D : E → Mn n} {x : E} {k : WithTop ℕ∞} (hA : ContDiffAt ℝ k A x) (hB : ContDiffAt ℝ k B x)
    (hC : ContDiffAt ℝ k C x) (hD : ContDiffAt ℝ k D x) :
    ContDiffAt ℝ k (fun y => (fromBlocks (A y) (B y) (C y) (D y) : M2 n)) x := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  rcases i with i | i <;> rcases j with j | j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hA i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hB i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hC i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hD i) j

def reP (V : Mn n) : Mn n := (1 / 2 : ℂ) • (V + Vᴴ)

def imaginary (V : Mn n) : Mn n := (-(Complex.I / 2)) • (V - Vᴴ)

theorem reP_herm (V : Mn n) : (reP V)ᴴ = reP V := by
  ext i j
  simp [reP]
  ring

theorem imaginaryPart_isHermitian (V : Mn n) : (imaginary V)ᴴ = imaginary V := by
  ext i j
  simp [imaginary]
  ring

theorem reP_add_imP (V : Mn n) : reP V + Complex.I • imaginary V = V := by
  ext i j
  simp only [reP, imaginary, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem imaginaryPart_of_isHermitian {V : Mn n} (h : Vᴴ = V) : imaginary V = 0 := by simp [imaginary, h]

theorem reP_of_herm {V : Mn n} (h : Vᴴ = V) : reP V = V := by
  rw [reP, h, ← two_smul ℂ V, smul_smul]
  norm_num

def fM (a0 : Mn n) (V : Mn n) : Mn n := reP V + Complex.I • (a0 * (1 + imaginary V) * (1 + imaginary V) * a0ᴴ)

end PositivityTheory.Rg.Sw.HSt.CRSec
end
end

section
noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reL : Mn n →L[ℝ] Mn n := (1 / 2 : ℂ) • (ContinuousLinearMap.id ℝ (Mn n) + cT)

def imL : Mn n →L[ℝ] Mn n := (-(Complex.I / 2)) • (ContinuousLinearMap.id ℝ (Mn n) - cT)

theorem reL_apply (V : Mn n) : reL V = reP V := rfl

theorem imL_apply (V : Mn n) : imL V = imaginary V := rfl

theorem contDiff_fM (a0 : Mn n) : ContDiff ℝ ⊤ (fM a0) := by
  have h1 : ContDiff ℝ ⊤ (fun V : Mn n => (1 : Mn n) + imaginary V) := contDiff_const.add imL.contDiff
  unfold fM
  refine reL.contDiff.add (ContDiff.const_smul _ ?_)
  exact contDiff_mul' (contDiff_mul' (contDiff_mul' contDiff_const h1) h1) contDiff_const

theorem fM_line (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) (t : ℝ) :
    fM a0 (V0 + t • dV) = (V0 + Complex.I • (a0 * a0ᴴ)) +
      t • (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) +
      (t ^ 2) • (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ)) := by
  have hr : reP (V0 + t • dV) = V0 + t • reP dV := by
    rw [← reL_apply, map_add, map_smul, reL_apply, reL_apply, reP_of_herm h0]
  have hi : imaginary (V0 + t • dV) = t • imaginary dV := by
    rw [← imL_apply, map_add, map_smul, imL_apply, imL_apply, imaginaryPart_of_isHermitian h0, zero_add]
  unfold fM
  rw [hr, hi]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, smul_smul]
  module

theorem fderiv_fM (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) :
    fderiv ℝ (fM a0) V0 dV = reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ) := by
  have hd : DifferentiableAt ℝ (fM a0) V0 := ((contDiff_fM a0).differentiable (by simp)).differentiableAt
  have hl := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const dV).const_add V0
  rw [one_smul] at hl
  have hd' : HasFDerivAt (fM a0) (fderiv ℝ (fM a0) V0) (V0 + (0 : ℝ) • dV) := by
    rw [zero_smul, add_zero]; exact hd.hasFDerivAt
  have hc := hd'.comp_hasDerivAt (0 : ℝ) hl
  have h1 := (hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ))
  have h2 := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).pow 2).smul_const
    (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ))
  have h3 := ((hasDerivAt_const (0 : ℝ) (V0 + Complex.I • (a0 * a0ᴴ))).add h1).add h2
  simp only [one_smul, zero_add] at h3
  have h4 : HasDerivAt (fun t : ℝ => fM a0 (V0 + t • dV)) (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) 0 := by
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp only [fM_line a0 V0 dV h0 t, Pi.add_apply, Pi.pow_apply]
    · norm_num
  exact hc.unique h4

theorem herm_zero_of (H1 H2 : Mn n) (h1 : H1ᴴ = H1) (h2 : H2ᴴ = H2) (h : H1 + Complex.I • H2 = 0) :
    H1 = 0 ∧ H2 = 0 := by
  have hc : H1 - Complex.I • H2 = 0 := by
    have := congrArg conjTranspose h
    rw [conjTranspose_add, conjTranspose_smul, h1, h2, conjTranspose_zero] at this
    rw [sub_eq_add_neg, ← neg_smul]
    simpa using this
  have h2H1 : H1 + H1 = 0 := by
    calc H1 + H1 = (H1 + Complex.I • H2) + (H1 - Complex.I • H2) := by abel
      _ = 0 := by rw [h, hc, add_zero]
  have hH1 : H1 = 0 := by
    have : (2 : ℂ) • H1 = 0 := by rw [two_smul]; exact h2H1
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  refine ⟨hH1, ?_⟩
  rw [hH1, zero_add] at h
  exact (smul_eq_zero.mp h).resolve_left Complex.I_ne_zero

theorem fderiv_fM_inj (a0 V0 : Mn n) (h0 : V0ᴴ = V0) (ha : a0.det ≠ 0) :
    Function.Injective (fderiv ℝ (fM a0) V0) := by
  refine (injective_iff_map_eq_zero (fderiv ℝ (fM a0) V0)).2 fun dV hdV => ?_
  rw [fderiv_fM a0 V0 dV h0] at hdV
  have hH2 : (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)ᴴ = a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul, imaginaryPart_isHermitian,
      Matrix.mul_assoc]
    simp
  obtain ⟨hr, hi⟩ := herm_zero_of _ _ (reP_herm dV) hH2 hdV
  have hu : IsUnit a0.det := isUnit_iff_ne_zero.mpr ha
  have huH : IsUnit a0ᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr ha).star
  have hB : (2 : ℂ) • imaginary dV = 0 := by
    have := congrArg (fun M => a0⁻¹ * M * (a0ᴴ)⁻¹) hi
    simp only [Matrix.mul_zero, Matrix.zero_mul] at this
    rw [← this, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huH, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hB' : imaginary dV = 0 := (smul_eq_zero.mp hB).resolve_left two_ne_zero
  rw [← reP_add_imP dV, hr, hB', smul_zero, add_zero]

end PositivityTheory.Rg.Sw.HSt.CRSec
end
end

section
noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exists_mul_conjTranspose_eq_of_posDef (Y : Mn n) (hY : Y.PosDef) : ∃ a0 : Mn n, a0 * a0ᴴ = Y ∧ a0.det ≠ 0 := by
  have hA : Y.IsHermitian := hY.1
  set U : Mn n := (hA.eigenvectorUnitary : Mn n) with hU
  set d : Mn n := diagonal (fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)) with hd
  have hsp : Y = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hdd : d * dᴴ = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [hd, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
    rfl
  have hprod : (U * d) * (U * d)ᴴ = Y := by
    calc (U * d) * (U * d)ᴴ = U * (d * dᴴ) * Uᴴ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by rw [hdd, Matrix.star_eq_conjTranspose]
      _ = Y := hsp.symm
  refine ⟨U * d, hprod, fun h0 => ?_⟩
  have hY0 : Y.det ≠ 0 := hY.det_pos.ne'
  apply hY0
  rw [← hprod, det_mul, h0, zero_mul]

theorem inG_diag {b : Mn n} (hb : b.det ≠ 0) : InG (fromBlocks b 0 0 (bᴴ)⁻¹ : M2 n) := by
  have hbH : IsUnit bᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr hb).star
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr hb
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, neg_zero]
  rw [Matrix.mul_nonsing_inv _ hbH, Matrix.nonsing_inv_mul _ hbu]

def bO (a0 V : Mn n) : Mn n := a0 * (1 + imaginary V)

def sec (a0 V : Mn n) : M2 n := (fromBlocks 1 (reP V) 0 1 : M2 n) * fromBlocks (bO a0 V) 0 0 ((bO a0 V)ᴴ)⁻¹

theorem sec_props (a0 V : Mn n) (hb : (bO a0 V).det ≠ 0) :
    InG (sec a0 V) ∧ (sec a0 V).det ≠ 0 ∧ zOfE (sec a0 V) = fM a0 V := by
  have hbH : IsUnit (bO a0 V)ᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr hb).star
  refine ⟨inG_mul (inG_upper (reP_herm V)) (inG_diag hb), ?_, ?_⟩
  · unfold sec
    rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul, det_nonsing_inv]
    refine mul_ne_zero hb ?_
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (isUnit_iff_ne_zero.mp hbH)
  · have hs : sec a0 V = fromBlocks (bO a0 V) (reP V * ((bO a0 V)ᴴ)⁻¹) 0 ((bO a0 V)ᴴ)⁻¹ := by
      unfold sec; rw [fromBlocks_multiply]; simp
    unfold zOfE u1
    rw [hs]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero,
      zero_add]
    rw [Matrix.nonsing_inv_nonsing_inv _ hbH, Matrix.add_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbH,
      Matrix.mul_one, Matrix.smul_mul]
    unfold fM bO
    have hB : (1 + imaginary V)ᴴ = 1 + imaginary V := by rw [conjTranspose_add, conjTranspose_one, imaginaryPart_isHermitian]
    rw [conjTranspose_mul, hB, add_comm]
    simp only [Matrix.mul_assoc]

theorem locSec : LocSec := by
  intro n Z0 hY
  obtain ⟨a0, ha0, hdet⟩ := exists_mul_conjTranspose_eq_of_posDef _ hY
  set V0 : Mn n := reP Z0 with hV0def
  have hV0 : V0ᴴ = V0 := reP_herm Z0
  have hfV0 : fM a0 V0 = Z0 := by
    unfold fM
    rw [imaginaryPart_of_isHermitian hV0, reP_of_herm hV0, add_zero, Matrix.mul_one, Matrix.mul_one, ha0]
    exact reP_add_imP Z0
  have hcd : ContDiffAt ℝ ⊤ (fM a0) V0 := (contDiff_fM a0).contDiffAt
  have hd : DifferentiableAt ℝ (fM a0) V0 := ((contDiff_fM a0).differentiable (by simp)).differentiableAt
  let e : Mn n ≃L[ℝ] Mn n :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (fM a0) V0 : Mn n →ₗ[ℝ] Mn n)
      (fderiv_fM_inj a0 V0 hV0 hdet)).toContinuousLinearEquiv
  have he : (e : Mn n →L[ℝ] Mn n) = fderiv ℝ (fM a0) V0 := by ext1 x; rfl
  have hf' : HasFDerivAt (fM a0) (e : Mn n →L[ℝ] Mn n) V0 := by rw [he]; exact hd.hasFDerivAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set g := hcd.localInverse hf' hn with hgdef
  have hg : ContDiffAt ℝ ⊤ g (fM a0 V0) := hcd.to_localInverse hf' hn
  have hgV : g (fM a0 V0) = V0 := hcd.localInverse_apply_image hf' hn
  have hright : ∀ᶠ Z in 𝓝 (fM a0 V0), fM a0 (g Z) = Z := (hcd.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  rw [hfV0] at hg hgV hright
  have hg1 : ContDiffAt ℝ 1 g Z0 := hg.of_le le_top
  have hre : ContDiffAt ℝ 1 (fun Z => reP (g Z)) Z0 := reL.contDiff.contDiffAt.comp Z0 hg1
  have him : ContDiffAt ℝ 1 (fun Z => imaginary (g Z)) Z0 := imL.contDiff.contDiffAt.comp Z0 hg1
  have hbo : ContDiffAt ℝ 1 (fun Z => bO a0 (g Z)) Z0 := contDiffAt_mul' contDiffAt_const (contDiffAt_const.add him)
  have hbZ0 : bO a0 (g Z0) = a0 := by rw [hgV, bO, imaginaryPart_of_isHermitian hV0, add_zero, Matrix.mul_one]
  have hbH0 : ((bO a0 (g Z0))ᴴ).det ≠ 0 := by
    rw [hbZ0, det_conjTranspose]; exact (star_ne_zero).mpr hdet
  have hcT : ContDiffAt ℝ 1 (fun Z => (bO a0 (g Z))ᴴ) Z0 := by
    have h := cT.contDiff.contDiffAt.comp Z0 hbo
    simp only [Function.comp_def] at h
    exact h
  have hinv : ContDiffAt ℝ 1 (fun Z => ((bO a0 (g Z))ᴴ)⁻¹) Z0 :=
    (contDiffAt_inv ((bO a0 (g Z0))ᴴ) hbH0).comp Z0 hcT
  have hcont : ContinuousAt (fun Z => (bO a0 (g Z)).det) Z0 :=
    (continuous_id.matrix_det.continuousAt).comp hbo.continuousAt
  have hev : ∀ᶠ Z in 𝓝 Z0, (bO a0 (g Z)).det ≠ 0 :=
    hcont.eventually_ne (by simp only [hbZ0]; exact hdet)
  refine ⟨fun Z => sec a0 (g Z), ?_, ?_⟩
  · filter_upwards [hright, hev] with Z hZ hb
    obtain ⟨h1, h2, h3⟩ := sec_props a0 (g Z) hb
    exact ⟨h1, h2, h3.trans hZ⟩
  · unfold sec
    exact contDiffAt_mul' (contDiffAt_fromBlocks contDiffAt_const hre contDiffAt_const contDiffAt_const)
      (contDiffAt_fromBlocks hbo contDiffAt_const contDiffAt_const hinv)

end PositivityTheory.Rg.Sw.HSt.CRSec

namespace PositivityTheory.Rg.Sw.HSt

theorem locSec : LocSec := CRSec.locSec

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂ := by
  simp [toBlocks₁₁_mul', Cm, Matrix.mul_smul]

theorem cmS : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 0
    ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simp only [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem cmiH_cmi : (Cmi n)ᴴ * Cmi n = (1 / 2 : ℂ) • (1 : M2 n) := by
  rw [← fromBlocks_one, fromBlocks_smul]
  simp only [Cmi, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.1 cm_mul_cmi

theorem mR_inv_mul (y y' : GR n) : mR (y⁻¹ * y') = (mR y)⁻¹ * mR y' := by
  simp [mR, Matrix.coe_units_inv]

theorem isUnit_mR (y : GR n) : IsUnit (mR y) := (y.1).isUnit

theorem fib : Fib := by
  intro n y y' hz
  have hGk : InG (mR (y⁻¹ * y')) := (y⁻¹ * y').2
  refine ⟨hGk, ?_⟩
  set x := mR y with hxdef
  set x' := mR y' with hx'def
  set k := mR (y⁻¹ * y') with hkdef
  have hkxx : k = x⁻¹ * x' := mR_inv_mul y y'
  have hxu : IsUnit x := isUnit_mR y
  have hxdet : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hxu
  have hu1 : (u1 x).det ≠ 0 := (detU1 n y).1
  have hu1' : (u1 x').det ≠ 0 := (detU1 n y').1
  have hu1u : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 hu1
  have hu1u' : IsUnit (u1 x').det := isUnit_iff_ne_zero.2 hu1'
  set c := (u1 x)⁻¹ * u1 x' with hc

  have h21 : (x' * Cm n).toBlocks₂₁ = (x * Cm n).toBlocks₂₁ * c := by
    rw [mul_cm₂₁, mul_cm₂₁, hc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1u, Matrix.one_mul]
  have h11 : (x' * Cm n).toBlocks₁₁ = (x * Cm n).toBlocks₁₁ * c := by
    rw [mul_cm₁₁, mul_cm₁₁]
    have hz' : (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹ =
        (Complex.I • x'.toBlocks₁₁ + x'.toBlocks₁₂) * (u1 x')⁻¹ := hz
    have := congrArg (· * u1 x') hz'
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1u', Matrix.mul_one] at this
    rw [hc]; exact this.symm

  set D := Cmi n * k * Cm n with hD
  have hDE : D * fromBlocks 1 0 0 0 = fromBlocks c 0 0 0 := by
    have e1 : x' * Cm n * fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 0 =
        x * Cm n * fromBlocks c 0 0 0 := by
      conv_lhs => rw [← fromBlocks_toBlocks (x' * Cm n), fromBlocks_multiply]
      conv_rhs => rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_multiply]
      rw [h11, h21]; simp
    calc D * fromBlocks 1 0 0 0 = Cmi n * x⁻¹ * (x' * Cm n * fromBlocks 1 0 0 0) := by
          rw [hD, hkxx]; simp only [Matrix.mul_assoc]
      _ = Cmi n * x⁻¹ * (x * Cm n * fromBlocks c 0 0 0) := by rw [e1]
      _ = Cmi n * (x⁻¹ * x) * Cm n * fromBlocks c 0 0 0 := by simp only [Matrix.mul_assoc]
      _ = fromBlocks c 0 0 0 := by
          rw [Matrix.nonsing_inv_mul _ hxdet, Matrix.mul_one, cmi_mul_cm, Matrix.one_mul]
  have hD0 : D = fromBlocks c D.toBlocks₁₂ 0 D.toBlocks₂₂ := by
    have := hDE
    conv_lhs at this => rw [← fromBlocks_toBlocks D, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero] at this
    obtain ⟨e11, -, e21, -⟩ := Matrix.fromBlocks_inj.1 this
    conv_lhs => rw [← fromBlocks_toBlocks D]
    rw [e11, e21]

  have hk : kᴴ * JJ n * k = JJ n := hGk
  have hS : Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D = (Cm n)ᴴ * JJ n * Cm n := by
    have hcc : (Cmi n)ᴴ * (Cm n)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, cm_mul_cmi, Matrix.conjTranspose_one]
    calc Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D
        = (Cm n)ᴴ * kᴴ * ((Cmi n)ᴴ * (Cm n)ᴴ) * JJ n * (Cm n * Cmi n) * k * Cm n := by
          rw [hD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * (kᴴ * JJ n * k) * Cm n := by
          rw [hcc, cm_mul_cmi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * JJ n * Cm n := by rw [hk]
  rw [cmS, hD0] at hS
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hS
  obtain ⟨s11, s12, -, s22⟩ := Matrix.fromBlocks_inj.1 hS
  have hI : (-2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hI' : (2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hcc : cᴴ * c = 1 := by
    have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s11
    simpa [smul_smul, inv_mul_cancel₀ hI] using this
  have hcc' : c * cᴴ = 1 := mul_eq_one_comm.1 hcc
  have hB : D.toBlocks₁₂ = 0 := by
    have h1 : cᴴ * D.toBlocks₁₂ = 0 := by
      have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s12
      simpa [smul_smul, inv_mul_cancel₀ hI] using this
    calc D.toBlocks₁₂ = c * cᴴ * D.toBlocks₁₂ := by rw [hcc', Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have hc' : (D.toBlocks₂₂)ᴴ * D.toBlocks₂₂ = 1 := by
    rw [hB] at s22
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, smul_zero] at s22
    have := congrArg (fun M => (2 * Complex.I)⁻¹ • M) s22
    simpa [smul_smul, inv_mul_cancel₀ hI'] using this
  have hDD : Dᴴ * D = 1 := by
    rw [hD0, hB, fromBlocks_conjTranspose, fromBlocks_multiply, hcc, hc', ← fromBlocks_one]
    simp

  have hkD : k = Cm n * D * Cmi n := by
    rw [hD]; simp only [← Matrix.mul_assoc]
    rw [cm_mul_cmi, Matrix.one_mul, Matrix.mul_assoc, cm_mul_cmi, Matrix.mul_one]
  have hcm2 : (Cm n)ᴴ * Cm n = (2 : ℂ) • (1 : M2 n) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [Cm, fromBlocks_conjTranspose, fromBlocks_multiply]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  calc kᴴ * k = (Cmi n)ᴴ * (Dᴴ * ((Cm n)ᴴ * Cm n) * D) * Cmi n := by
        rw [hkD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (2 : ℂ) • ((Cmi n)ᴴ * Cmi n) := by
        rw [hcm2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDD, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one]
    _ = 1 := by rw [cmiH_cmi, smul_smul]; norm_num

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_function_eq_weighted (m : ℕ) (e : ℤ) (y : GR n) : F0 m 0 e y = holomorphicScalarSection m e (mR y) := by
  simp [F0, f0, holomorphicScalarSection]

def Jsw (n : ℕ) : M2 n := fromBlocks 0 1 1 0

def Nm (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂

def Nm' (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂

private theorem Cm_mul_Cmi_eq_one : Cm n * Cmi n = 1 := by
  simp only [Cm, Cmi, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

private theorem Cm_inv_eq_Cmi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi_eq_one

private theorem Cmi_mul_Cm_eq_one : Cmi n * Cm n = 1 := by
  rw [← Cm_inv_eq_Cmi]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse Cm_mul_Cmi_eq_one)

private theorem u1_eq_mul_Cm_toBlocks₂₁ (g : M2 n) : u1 g = (g * Cm n).toBlocks₂₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u1, Cm, Matrix.fromBlocks_multiply]

private theorem u2_eq_mul_Cm_toBlocks₂₂ (g : M2 n) : u2 g = (g * Cm n).toBlocks₂₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u2, Cm, Matrix.fromBlocks_multiply]

private theorem Nm_eq_mul_Cm_toBlocks₁₁ (g : M2 n) : Nm g = (g * Cm n).toBlocks₁₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm, Cm, Matrix.fromBlocks_multiply]

private theorem Nm'_eq_mul_Cm_toBlocks₁₂ (g : M2 n) : Nm' g = (g * Cm n).toBlocks₁₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm', Cm, Matrix.fromBlocks_multiply]

private theorem toBlocks11_mul_fromBlocks (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₁₁ = A.toBlocks₁₁ * P + A.toBlocks₁₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_fromBlocks_toBlocks₂₁ (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₂₁ = A.toBlocks₂₁ * P + A.toBlocks₂₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    x * mX P Q R S * Cm n = x * Cm n * fromBlocks P Q R S := by
  simp only [mX, Cm_inv_eq_Cmi, Matrix.mul_assoc, Cmi_mul_Cm_eq_one, Matrix.mul_one]

theorem zOfE_eq (x : M2 n) : zOfE x = Nm x * (u1 x)⁻¹ := rfl

theorem first_cayley_block_mul_block (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX P Q R S) = u1 x * P + u2 x * R := by
  rw [u1_eq_mul_Cm_toBlocks₂₁, u1_eq_mul_Cm_toBlocks₂₁, u2_eq_mul_Cm_toBlocks₂₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, mul_fromBlocks_toBlocks₂₁]

theorem Nm_mX (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    Nm (x * mX P Q R S) = Nm x * P + Nm' x * R := by
  rw [Nm_eq_mul_Cm_toBlocks₁₁, Nm_eq_mul_Cm_toBlocks₁₁, Nm'_eq_mul_Cm_toBlocks₁₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, toBlocks11_mul_fromBlocks]

theorem da_entry (i j : Fin n ⊕ Fin n) (x : M2 n) : DifferentiableAt ℂ (fun y : M2 n => y i j) x := by
  exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_id (x := x)) i) j

theorem da_matrix {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n}
    (h : ∀ i j, DifferentiableAt ℂ (fun y => f y i j) x) : DifferentiableAt ℂ f x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j
  exact h1

theorem da_apply {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (h : DifferentiableAt ℂ f x) (i j : Fin n) :
    DifferentiableAt ℂ (fun y => f y i j) x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x := h
  exact differentiableAt_pi.1 (differentiableAt_pi.1 h1 i) j

theorem da_mul {f g : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) : DifferentiableAt ℂ (fun y => f y * g y) x := by
  refine da_matrix fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (da_apply hf i k).mul (da_apply hg k j)

theorem differentiableAt_first_cayley_block (x : M2 n) : DifferentiableAt ℂ u1 x := by
  refine da_matrix fun i j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

theorem da_Nm (x : M2 n) : DifferentiableAt ℂ Nm x := by
  refine da_matrix fun i j => ?_
  simp only [Nm, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

private theorem differentiableAt_det_of_differentiableAt_entries {ι : Type} [Fintype ι] [DecidableEq ι] {f : M2 n → Matrix ι ι ℂ}
    {x : M2 n} (hf : ∀ a b, DifferentiableAt ℂ (fun y => f y a b) x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  have hp : ∀ (s : Finset ι) (σ : Equiv.Perm ι),
      DifferentiableAt ℂ (fun y => ∏ i ∈ s, f y (σ i) i) x := by
    intro s σ
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (hf _ _).mul ih
  have e : (fun y => (f y).det) =
      fun y => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e]
  exact DifferentiableAt.fun_sum fun σ _ => (hp _ σ).const_mul _

theorem da_det {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  exact differentiableAt_det_of_differentiableAt_entries (da_apply hf)

theorem da_inv {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) (h : (f x).det ≠ 0) :
    DifferentiableAt ℂ (fun y => (f y)⁻¹) x := by
  have hadj : ∀ i j, DifferentiableAt ℂ (fun y => (f y).adjugate i j) x := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_det_of_differentiableAt_entries fun a b => ?_
    simp only [Matrix.updateRow_apply]
    by_cases hab : a = j
    · simp only [hab, if_true]
      exact differentiableAt_const _
    · simp only [hab, if_false]
      exact da_apply hf a b
  have hd : DifferentiableAt ℂ (fun y => ((f y).det)⁻¹) x := (differentiableAt_det_of_differentiableAt_entries (da_apply hf)).inv h
  refine da_matrix fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.mul (hadj i j)

theorem da_zOfE (x : M2 n) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ zOfE x := by
  have e : zOfE = fun y : M2 n => Nm y * (u1 y)⁻¹ := funext zOfE_eq
  rw [e]
  exact da_mul (da_Nm x) (da_inv (differentiableAt_first_cayley_block x) h)

theorem da_F0E (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ (holomorphicScalarSection m e) x := by
  show DifferentiableAt ℂ (fun y : M2 n => y.det ^ e * (u1 y).det ^ (-(m : ℤ))) x
  exact ((differentiableAt_det_of_differentiableAt_entries (f := fun y => y) fun a b => da_entry a b x).zpow (Or.inl h0)).mul
    ((da_det (differentiableAt_first_cayley_block x)).zpow (Or.inl h))

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Cm n * fromBlocks 0 Q 0 0 * Cmi n := by
  have h1 : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) Q 0 1 : M2 n) = 1 + fromBlocks 0 Q 0 0 := by
    rw [← fromBlocks_one, fromBlocks_add]; simp
  rw [lowQ, mX, h1, cm_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, add_sub_cancel_left]

theorem lowQ_smul (c : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ (c • Q) = c • lowQ Q := by
  rw [lowQ_eq, lowQ_eq, show (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) 0 0 : M2 n) = c • fromBlocks 0 Q 0 0 by
    rw [fromBlocks_smul]; simp]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q 0 1 = 1 + lowQ Q := by
  rw [lowQ]; abel

theorem det_mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : (mX 1 Q 0 1 : M2 n).det = 1 := by
  simp only [mX, Cm_inv_eq_Cmi]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, mul_one]
  rw [← Matrix.det_mul, Cm_mul_Cmi_eq_one, Matrix.det_one]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fderiv_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : M2 n → E} {x : M2 n}
    (hf : DifferentiableAt ℂ f x) (v : M2 n) (hc : ∀ τ : ℂ, f (x + τ • v) = f x) : fderiv ℂ f x v = 0 := by
  have hl : HasDerivAt (fun τ : ℂ => x + τ • v) v 0 :=
    (((hasDerivAt_id' (0:ℂ)).smul_const v).const_add x).congr_deriv (one_smul ℂ v)
  have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) hl (by simp)
  have h2 : HasDerivAt (f ∘ fun τ : ℂ => x + τ • v) 0 0 := by
    have e : (f ∘ fun τ : ℂ => x + τ • v) = fun _ => f x := funext fun τ => hc τ
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem line_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * lowQ Q) = x * mX 1 (τ • Q) 0 1 := by
  rw [mX_low, lowQ_smul, mul_add, mul_one, Matrix.mul_smul]

theorem zOfE_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : zOfE (x * mX 1 Q 0 1) = zOfE x := by
  rw [zOfE_eq, zOfE_eq, first_cayley_block_mul_block, Nm_mX]; simp

theorem holomorphic_section_lowering_invariant (m : ℕ) (e : ℤ) (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : holomorphicScalarSection m e (x * mX 1 Q 0 1) = holomorphicScalarSection m e x := by
  unfold holomorphicScalarSection
  simp only [Matrix.det_mul, det_mX_low, first_cayley_block_mul_block, mul_one, mul_zero, add_zero]

theorem fderiv_zOfE_low (x : M2 n) (h : (u1 x).det ≠ 0) (Q : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_zOfE x h) _ fun τ => by rw [line_low, zOfE_low]

theorem fderiv_F0E_low (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0)
    (Q : Matrix (Fin n) (Fin n) ℂ) : fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_F0E m e x h0 h) _ fun τ => by rw [line_low, holomorphic_section_lowering_invariant]

theorem low_blocks (R : Matrix (Fin n) (Fin n) ℂ) :
    lowQ R = fromBlocks ((-1 / 2 : ℂ) • R) ((Complex.I / 2) • R) ((Complex.I / 2) • R) ((1 / 2 : ℂ) • R) := by
  rw [lowQ_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

def raiseR (S : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 0 S 1 - 1

private theorem Cm_mul_Cmi : Cm n * Cmi n = 1 := by
  unfold Cm Cmi
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem raise_eq (S : Matrix (Fin n) (Fin n) ℂ) : raiseR S = Cm n * fromBlocks 0 0 S 0 * Cmi n := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi
  have hb : (fromBlocks 1 0 S 1 : M2 n) = fromBlocks 0 0 S 0 + 1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp
  unfold raiseR mX
  rw [hinv, hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Cm_mul_Cmi, add_sub_cancel_right]

theorem raise_blocks (S : Matrix (Fin n) (Fin n) ℂ) :
    raiseR S = fromBlocks ((-1 / 2 : ℂ) • S) ((-Complex.I / 2) • S) ((-Complex.I / 2) • S) ((1 / 2 : ℂ) • S) := by
  rw [raise_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem sig_fromBlocks (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    sig (fromBlocks A B C D) = fromBlocks (-Dᴴ) Bᴴ Cᴴ (-Aᴴ) := by
  rw [sig_eq]
  unfold JJ
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem sig_low (R : Matrix (Fin n) (Fin n) ℂ) : sig (lowQ R) = raiseR Rᴴ := by
  rw [low_blocks, raise_blocks, sig_fromBlocks]
  simp only [Matrix.conjTranspose_smul]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply] <;> ring_nf <;> simp [Complex.conj_I] <;> ring_nf

theorem raiseR_smul (c : ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : raiseR (c • S) = c • raiseR S := by
  rw [raise_blocks, raise_blocks, Matrix.fromBlocks_smul]
  congr 1 <;> exact smul_comm _ _ _

theorem line_raise (x : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * raiseR S) = x * mX 1 0 (τ • S) 1 := by
  have : mX 1 0 (τ • S) 1 = 1 + raiseR (τ • S) := by rw [raiseR]; abel
  rw [this, raiseR_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_matrix_mul {A B : ℂ → Matrix (Fin n) (Fin n) ℂ} {A' B' : Matrix (Fin n) (Fin n) ℂ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  have hA' : HasDerivAt (fun τ => (A τ : Fin n → Fin n → ℂ)) (A' : Fin n → Fin n → ℂ) 0 := hA
  have hB' : HasDerivAt (fun τ => (B τ : Fin n → Fin n → ℂ)) (B' : Fin n → Fin n → ℂ) 0 := hB
  have h : HasDerivAt (fun τ => ((A τ * B τ : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ))
      ((A' * B 0 + A 0 * B' : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.mul_apply, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun k _ => ?_
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA' i) k).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB' k) j)
  exact h

theorem fderiv_zOfE_raise (x : M2 n) (h : (u1 x).det ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * raiseR S) = WM x * S * (u1 x)⁻¹ := by
  let v := x * raiseR S
  have hl := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hg := (da_zOfE x h).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  simp only [id_eq, one_smul, Function.comp_def] at hg
  have hu : ∀ τ : ℂ, u1 (x + τ • v) = u1 x + τ • (u2 x * S) := fun τ => by
    rw [line_raise, first_cayley_block_mul_block, Matrix.mul_one, Matrix.mul_smul]
  have hN : ∀ τ : ℂ, Nm (x + τ • v) = Nm x + τ • (Nm' x * S) := fun τ => by
    rw [line_raise, Nm_mX, Matrix.mul_one, Matrix.mul_smul]
  have hc : Continuous fun τ : ℂ => (u1 x + τ • (u2 x * S)).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), (u1 x + τ • (u2 x * S)).det ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using h)
  have hB := ((hasDerivAt_id (0 : ℂ)).smul_const (u2 x * S)).const_add (u1 x)
  simp only [id_eq, one_smul] at hB
  have hL := hasDerivAt_matrix_mul hg hB
  have hR := ((hasDerivAt_id (0 : ℂ)).smul_const (Nm' x * S)).const_add (Nm x)
  simp only [id_eq, one_smul] at hR
  have heq : (fun τ : ℂ => zOfE (x + τ • v) * (u1 x + τ • (u2 x * S))) =ᶠ[𝓝 0]
      fun τ => Nm x + τ • (Nm' x * S) := by
    filter_upwards [hev] with τ hτ
    rw [← hu, zOfE_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (by rwa [hu])), Matrix.mul_one, hN]
  have hfin := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero] at hfin
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have key : fderiv ℂ zOfE x v * u1 x = WM x * S := by
    refine (eq_sub_of_add_eq hfin).trans ?_
    rw [WM, show (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) = Nm' x from rfl, Matrix.sub_mul, Matrix.mul_assoc (zOfE x)]
  calc fderiv ℂ zOfE x v = fderiv ℂ zOfE x v * u1 x * (u1 x)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]
    _ = WM x * S * (u1 x)⁻¹ := congrArg (fun M => M * (u1 x)⁻¹) key

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₁₂_mul' (A B : M2 n) :
    (A * B).toBlocks₁₂ = A.toBlocks₁₁ * B.toBlocks₁₂ + A.toBlocks₁₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Nm x := by
  simp [toBlocks₁₁_mul', Cm, Nm, Matrix.mul_smul]

theorem mul_cm₁₂ (x : M2 n) : (x * Cm n).toBlocks₁₂ = Nm' x := by
  simp [toBlocks₁₂_mul', Cm, Nm', Matrix.mul_smul, Matrix.mul_neg]

theorem det_ne_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    intro h3
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, h3, zero_mul, Matrix.det_neg] at this
    simp at this
  exact h2 h1.symm

theorem det_cm_ne : (Cm n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (cm_mul_cmi (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem wm_det (x : M2 n) (hx : InG x) (h : (u1 x).det ≠ 0) : (WM x).det ≠ 0 := by
  intro hW
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hW
  set w := -(((u1 x)⁻¹ * u2 x) *ᵥ v)
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have hM : (x * Cm n) *ᵥ Sum.elim w v = 0 := by
    rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_mulVec, mul_cm₁₁, mul_cm₁₂, mul_cm₂₁, mul_cm₂₂]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have e1 : Nm x *ᵥ w + Nm' x *ᵥ v = WM x *ᵥ v := by
      simp only [w, WM, Matrix.mulVec_neg, Matrix.mulVec_mulVec, zOfE_eq, Matrix.sub_mulVec, Matrix.mul_assoc]
      rw [show -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂ = Nm' x from rfl]; abel
    have e2 : u1 x *ᵥ w + u2 x *ᵥ v = 0 := by
      simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1,
        Matrix.one_mul, neg_add_cancel]
    rw [e1, e2, hv]
    funext i; cases i <;> simp
  have hdet : (x * Cm n).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero (det_ne_of_inG hx) det_cm_ne
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
  exact hv0 (funext fun i => by simpa using congrFun h0 (Sum.inr i))

theorem cra2 : CauchyRiemannFacts := by
  refine ⟨fun n m e y => orbital_function_eq_weighted m e y, fun n x h0 h => ⟨da_zOfE x h, fun m e => da_F0E m e x h0 h, fun Q =>
    ⟨fderiv_zOfE_low x h Q, fun m e => fderiv_F0E_low m e x h0 h Q⟩, fun R => ?_, fun hx => wm_det x hx h⟩⟩
  rw [sig_low]
  exact fderiv_zOfE_raise x h Rᴴ

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section
namespace PositivityTheory.Rg.Sw.HSt

theorem crLem : CRLem := CR.crLem_of locSec fib CR.cra2

end PositivityTheory.Rg.Sw.HSt
end
