import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoeffRowAct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylCharEqGtChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandPairConvolution.Unimod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JBConjTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationRepUnitaryModel
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryAction

section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem differentiable_entry {r : ℕ} (a b : Fin r) :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).differentiable

theorem differentiable_det {r : ℕ} :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M.det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ => Differentiable.const_mul ?_ _
  have h : ∀ t : Finset (Fin r), Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => ∏ i ∈ t, M (σ i) i := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (differentiable_entry (σ a) a).mul ih
  exact h Finset.univ

theorem differentiable_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ =>
      MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (differentiable_const (MvPolynomial.coeff s (MvPolynomial.C a : MvPolynomial (Fin r × Fin m) ℂ)) :
        Differentiable ℂ fun _ : Matrix (Fin r) (Fin r) ℂ => _)
  | add p q hp hq =>
    intro s
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ,
        MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (p * MvPolynomial.X v)) =
        ∑ b : Fin r, M b v.1 * (if (b, v.2) ∈ s.support then
          MvPolynomial.coeff (s - Finsupp.single (b, v.2) 1) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ p) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M b v.1) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine Differentiable.fun_sum fun b _ => ?_
    refine (differentiable_entry b v.1).mul ?_
    split_ifs
    · exact hp _
    · exact differentiable_const _

theorem detPow_nonsingInvUnit {n : ℕ} {x : Mat n} (h : IsUnit x.det) (c : ℤ) :
    Formalism.BasicNotions.detPow ℂ n (Matrix.nonsingInvUnit x h) c = x.det ^ c := by
  have e : ((Matrix.GeneralLinearGroup.det (Matrix.nonsingInvUnit x h) : ℂˣ) : ℂ) = x.det := rfl
  rw [Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, e]

theorem holRm (n : ℕ) (lam : Fin n → ℤ) : HolRm lam := by
  intro i j g hg
  obtain ⟨S, c, hc⟩ := GlobalTheory.CompanionTheory.WInfCont.exists_finset_factor (Formalism.BasicNotions.nablaSq ℂ n (dw lam)) ((wb lam).coord i)
  have hev : (fun x : Mat n => Rm lam x i j) =ᶠ[𝓝 g] fun x : Mat n =>
      ∑ s : S, c s * (x.det ^ (dw lam).detShift *
        MvPolynomial.coeff s.1 (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) xᵀ (wb lam j).1)) := by
    filter_upwards [isOpen_GLs.mem_nhds hg] with x hx
    have hu := isUnit_det_of_mem hx
    rw [Rm_of_unit lam hu, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hc]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [GlobalTheory.Branching.sqRep_coe, Formalism.BasicNotions.sqAct, MvPolynomial.coeff_smul, smul_eq_mul,
      detPow_nonsingInvUnit hu]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine DifferentiableAt.fun_sum fun s _ => DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.mul ?_ (differentiable_coeff_rowAct _ _ _)
  exact (differentiable_det g).zpow (Or.inl hg)

end GlobalTheory.CompanionTheory.RmHol
end
end

section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)
open Formalism.BasicNotions Formalism.GradedWeylDivisibility

namespace GlobalTheory.CompanionTheory.RmHol.HW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hv (lam : Fin n → ℤ) : nablaSq ℂ n (dw lam) :=
  ⟨extremal ℂ n (dw lam), hwMem ℂ n n le_rfl _ (factNatW n (dw lam)).1⟩

theorem hv_ne (lam : Fin n → ℤ) : hv lam ≠ 0 := fun h =>
  hwNe ℂ n n le_rfl (dw lam).natW (congrArg Subtype.val h)

theorem dw_w {lam : Fin n → ℤ} (h : Antitone lam) (a : Fin n) : (dw lam).w a = lam a := by
  unfold dw
  rw [dif_pos h]

theorem Rm_mulVec (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) (v : nablaSq ℂ n (dw lam)) :
    Rm lam x *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
      ((wb lam).repr (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h) v) : Jd n lam → ℂ) := by
  rw [Rm_of_unit lam h]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

theorem hasDerivAt_mulVec {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (c : Jd n lam → ℂ)
    (i : Jd n lam) :
    HasDerivAt (fun t : ℂ => (Rm lam (1 + t • B) *ᵥ c) i) ((XA lam B *ᵥ c) i) 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_line hD B i j).mul_const _

theorem fix_upper (lam : Fin n → ℤ) {a b : Fin n} (hab : a < b) {t : ℂ}
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) = hv lam := by
  apply Subtype.ext
  refine (factSqHighestWeight ℂ n (dw lam)).2 _ ?_ ?_
  · intro i j hij
    have hij' : j < i := hij
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i j = 0
    have h1 : (1 : Mat n) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij')
    have h2 : Matrix.single a b (1 : ℂ) i j = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 hij'.le)
    rw [Matrix.add_apply, Matrix.smul_apply, h1, h2]
    simp
  · intro i
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i i = 1
    have h2 : Matrix.single a b (1 : ℂ) i i = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, h⟩
      exact hab.ne' h
    rw [Matrix.add_apply, Matrix.smul_apply, h2]
    simp

theorem diag_act {lam : Fin n → ℤ} (hA : Antitone lam) (a : Fin n) {t : ℂ} (ht : 1 + t ≠ 0)
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) =
      ((1 + t) ^ (lam a)) • hv lam := by
  classical
  let u : Fin n → ℂˣ := fun i => if i = a then Units.mk0 (1 + t) ht else 1
  have e : Matrix.nonsingInvUnit _ h = diagGL ℂ n u := by
    apply Units.ext
    ext i j
    show ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)) i j = Matrix.diagonal (fun k => (u k : ℂ)) i j
    by_cases hij : i = j
    · subst hij
      by_cases hia : i = a
      · subst hia; simp [u]
      · have h2 : Matrix.single a a (1 : ℂ) i i = 0 := by
          rw [Matrix.single_apply_of_ne]
          rintro ⟨h, -⟩
          exact hia h.symm
        rw [Matrix.add_apply, Matrix.smul_apply, h2]
        simp [u, hia]
    · have h2 : Matrix.single a a (1 : ℂ) i j = 0 := by
        rw [Matrix.single_apply_of_ne]
        rintro ⟨h, h'⟩
        exact hij (h.symm.trans h')
      rw [Matrix.add_apply, Matrix.smul_apply, h2, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
      simp
  have hp : ((∏ i, (u i) ^ ((dw lam).w i) : ℂˣ) : ℂ) = (1 + t) ^ (lam a) := by
    rw [Finset.prod_eq_single a]
    · simp [u, dw_w hA]
    · intro b _ hb
      simp [u, hb]
    · simp
  rw [e]
  apply Subtype.ext
  have hh := (factSqHighestWeight ℂ n (dw lam)).1 u
  rw [hp] at hh
  exact hh

theorem exists_hw (n : ℕ) (lam : Fin n → ℤ) (hD : HolRm lam) (hA : Antitone lam) :
    ∃ v : Formalism.BasicNotions.nablaSq ℂ n (dw lam), v ≠ 0 ∧
      (∀ a b : Fin n, a < b → Xu lam a b *ᵥ ((wb lam).repr v : Jd n lam → ℂ) = 0) ∧
      ∀ a : Fin n, Xu lam a a *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
        (lam a : ℂ) • ((wb lam).repr v : Jd n lam → ℂ) := by
  refine ⟨hv lam, hv_ne lam, fun a b hab => ?_, fun a => ?_⟩
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a b (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a b (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun _ => ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a b (1 : ℂ))] with t ht
      rw [Rm_mulVec lam ht, fix_upper lam hab ht]
    have h2 := (hasDerivAt_const (0 : ℂ) (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a a (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hne : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ≠ 0 := by
      have hc : ContinuousAt (fun t : ℂ => 1 + t) 0 := by fun_prop
      exact hc.eventually_ne (by simp)
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a a (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun t => (1 + t) ^ (lam a) * ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a a (1 : ℂ)), hne] with t ht ht'
      rw [Rm_mulVec lam ht, diag_act hA a ht' ht]
      simp
    have hz : HasDerivAt (fun t : ℂ => (1 + t) ^ (lam a)) (lam a : ℂ) 0 := by
      have h0 := hasDerivAt_zpow (lam a) ((1 : ℂ) + 0) (Or.inl (by simp))
      have h3 := h0.comp_const_add 1 0
      have e : (lam a : ℂ) * ((1 : ℂ) + 0) ^ (lam a - 1) = lam a := by simp
      rw [e] at h3
      exact h3
    have h2 := (hz.mul_const (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2

end GlobalTheory.CompanionTheory.RmHol.HW
end
end

section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem line_inverse {e : Mat n} {δ t s : ℂ} (he : e * e = δ • e) (hs : s * (1 + t * δ) = t) :
    (1 + t • e) * (1 - s • e) = 1 ∧ (1 - s • e) * (1 + t • e) = 1 := by
  have key : t - s - t * s * δ = 0 := by linear_combination -hs
  have key' : t - s - s * t * δ = 0 := by linear_combination -hs
  constructor
  · calc (1 + t • e) * (1 - s • e) = 1 + (t - s - t * s * δ) • e := by
          simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key, zero_smul, add_zero]
  · calc (1 - s • e) * (1 + t • e) = 1 + (t - s - s * t * δ) • e := by
          simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key', zero_smul, add_zero]

theorem conj_line {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    ∀ᶠ t : ℂ in 𝓝 0, Rm lam (1 + t • e) * XA lam B =
      (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e) := by
  have hc : ContinuousAt (fun t : ℂ => 1 + t * δ) 0 := by fun_prop
  have hδ : ∀ᶠ t : ℂ in 𝓝 0, 1 + t * δ ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [eventually_line_unit e, hδ] with t hu hne
  have hs : t / (1 + t * δ) * (1 + t * δ) = t := div_mul_cancel₀ t hne
  obtain ⟨-, hyx⟩ := line_inverse he hs
  have hB' : (1 + t • e) * B * (1 - (t / (1 + t * δ)) • e) =
      B + t • (e * B) + (-(t / (1 + t * δ))) • (B * e) + (-(t * (t / (1 + t * δ)))) • (e * B * e) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      mul_assoc]
    module
  have hcomm : (1 + t • e) * B = ((1 + t • e) * B * (1 - (t / (1 + t * δ)) • e)) * (1 + t • e) := by
    rw [mul_assoc ((1 + t • e) * B), hyx, mul_one]
  rw [conj_XA hD hu hcomm, hB', XA_add, XA_add, XA_add, XA_smul, XA_smul, XA_smul]

theorem comm_XA {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    XA lam e * XA lam B - XA lam B * XA lam e = XA lam (e * B) - XA lam (B * e) := by
  have hden : HasDerivAt (fun t : ℂ => 1 + t * δ) δ 0 := by
    simpa using ((hasDerivAt_id' (0:ℂ)).mul_const δ).const_add 1
  have hs : HasDerivAt (fun t : ℂ => t / (1 + t * δ)) 1 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).div hden (by simp)
    refine h.congr_deriv ?_
    simp
  have hts : HasDerivAt (fun t : ℂ => t * (t / (1 + t * δ))) 0 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).mul hs
    refine h.congr_deriv ?_
    simp
  have hprod : ∀ (P Q : ℂ → Matrix (Jd n lam) (Jd n lam) ℂ) (P' Q' : Matrix (Jd n lam) (Jd n lam) ℂ),
      (∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0) → (∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0) →
      ∀ i j, HasDerivAt (fun t => (P t * Q t) i j) ((P' * Q 0 + P 0 * Q') i j) 0 := by
    intro P Q P' Q' hP hQ i j
    simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun k _ => (hP i k).mul (hQ k j)
  have hR : ∀ i k, HasDerivAt (fun t : ℂ => Rm lam (1 + t • e) i k) (XA lam e i k) 0 :=
    hasDerivAt_line hD e
  have hC : ∀ k j, HasDerivAt (fun _ : ℂ => XA lam B k j)
      ((0 : Matrix (Jd n lam) (Jd n lam) ℂ) k j) 0 := fun k j => by
    simpa using hasDerivAt_const (0:ℂ) (XA lam B k j)
  have hG : ∀ i k, HasDerivAt (fun t : ℂ => (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) i k) ((XA lam (e * B) - XA lam (B * e)) i k) 0 := by
    intro i k
    have h := ((((hasDerivAt_id' (0:ℂ)).mul_const (XA lam (e * B) i k)).const_add (XA lam B i k)).add
      (hs.neg.mul_const (XA lam (B * e) i k))).add (hts.neg.mul_const (XA lam (e * B * e) i k))
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
    exact h.congr_deriv (by ring)
  ext i j
  have hL := hprod (fun t => Rm lam (1 + t • e)) (fun _ => XA lam B) (XA lam e) 0 hR hC i j
  have hRt := hprod (fun t : ℂ => XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) (fun t => Rm lam (1 + t • e))
      (XA lam (e * B) - XA lam (B * e)) (XA lam e) hG hR i j
  have heq : (fun t : ℂ => (Rm lam (1 + t • e) * XA lam B) i j) =ᶠ[𝓝 0]
      (fun t : ℂ => ((XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e)) i j) := by
    filter_upwards [conj_line hD B he] with t ht
    exact congrArg (fun M => M i j) ht
  have huniq := hL.unique (hRt.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero, Rm_one, mul_zero, mul_one, zero_div, neg_zero, zero_mul] at huniq
  rw [Matrix.sub_apply, huniq, Matrix.add_apply]
  ring

theorem XA_zero (lam : Fin n → ℤ) : XA lam (0 : Mat n) = 0 := by
  simpa using XA_smul lam (0 : ℂ) (0 : Mat n)

theorem xu_glRel : ∀ (n : ℕ) (lam : Fin n → ℤ), HolRm lam → Formalism.HadamardInequality.GlRel (Xu lam) := by
  intro n lam hD a b c d
  have hsq : (Matrix.single a b (1:ℂ) : Mat n) * Matrix.single a b 1 =
      (if b = a then (1:ℂ) else 0) • Matrix.single a b 1 := by
    by_cases h : b = a
    · subst h; rw [if_pos rfl, one_smul, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, zero_smul, Matrix.single_mul_single_of_ne _ _ _ _ h]
  have key := comm_XA hD (Matrix.single c d (1:ℂ)) hsq
  have hEB : XA lam ((Matrix.single a b (1:ℂ) : Mat n) * Matrix.single c d 1) =
      if b = c then XA lam (Matrix.single a d 1) else 0 := by
    by_cases h : b = c
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  have hBE : XA lam ((Matrix.single c d (1:ℂ) : Mat n) * Matrix.single a b 1) =
      if d = a then XA lam (Matrix.single c b 1) else 0 := by
    by_cases h : d = a
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  simp only [Xu]
  rw [key, hEB, hBE]

end GlobalTheory.CompanionTheory.RmHol
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace GlobalTheory.CompanionTheory.CxAvg

section Abstract

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  (μ : Measure K) [μ.IsHaarMeasure] (F : K →* (E →L[ℂ] E))

local notation "adj" => ContinuousLinearMap.adjoint

def gram : E →L[ℂ] E := ∫ k, adj (F k) * F k ∂μ

variable {F}

theorem integrable_gram (hF : Continuous F) : Integrable (fun k => adj (F k) * F k) μ := by
  have hc : Continuous fun k => adj (F k) * F k :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp hF).mul hF
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem inner_gram (hF : Continuous F) (v w : E) :
    ⟪w, gram μ F v⟫_ℂ = ∫ k, ⟪F k w, F k v⟫_ℂ ∂μ := by
  have h := integrable_gram μ hF
  have h1 : gram μ F v = ∫ k, (adj (F k) * F k) v ∂μ := ContinuousLinearMap.integral_apply h v
  have h2 : Integrable (fun k => (adj (F k) * F k) v) μ :=
    (ContinuousLinearMap.apply ℂ E v).integrable_comp h
  rw [h1, ← integral_inner h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem gram_symm (hF : Continuous F) (v w : E) : ⟪gram μ F v, w⟫_ℂ = ⟪v, gram μ F w⟫_ℂ := by
  rw [← inner_conj_symm, inner_gram μ hF, inner_gram μ hF, ← integral_conj]
  simp only [inner_conj_symm]

theorem inner_self_gram (hF : Continuous F) (v : E) :
    ⟪v, gram μ F v⟫_ℂ = ((∫ k, ‖F k v‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [inner_gram μ hF, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [inner_self_eq_norm_sq_to_K]

theorem continuous_norm_apply (hF : Continuous F) (v : E) : Continuous fun k => ‖F k v‖ ^ 2 :=
  ((hF.clm_apply continuous_const).norm).pow 2

theorem gram_isPositive (hF : Continuous F) : (gram μ F).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨?_, fun v => ?_⟩
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun v w => gram_symm μ hF v w
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, gram_symm μ hF, inner_self_gram μ hF]
    simpa using integral_nonneg fun k => by positivity

theorem gram_nonneg (hF : Continuous F) : 0 ≤ gram μ F :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).2 (gram_isPositive μ hF)

theorem gram_commute (hF : Continuous F) (A : E →L[ℂ] E) (hA1 : adj A * A = 1) (hA2 : A * adj A = 1)
    (hc : ∀ k, A * F k = F k * A) : A * gram μ F = gram μ F * A := by
  have h := integrable_gram μ hF
  have e1 : ∀ k, adj A * F k = F k * adj A := fun k => by
    calc adj A * F k = adj A * F k * (A * adj A) := by rw [hA2, mul_one]
      _ = adj A * (A * F k) * adj A := by rw [hc k]; simp only [mul_assoc]
      _ = F k * adj A := by rw [← mul_assoc, hA1, one_mul]
  have e2 : ∀ k, adj (F k) * A = A * adj (F k) := fun k => by
    have := congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)) (e1 k)
    simpa [← ContinuousLinearMap.star_eq_adjoint, star_mul] using this
  calc A * gram μ F = ∫ k, A * (adj (F k) * F k) ∂μ := by
        rw [gram, integral_const_mul_of_integrable h]
    _ = ∫ k, (adj (F k) * F k) * A ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        show A * (adj (F k) * F k) = adj (F k) * F k * A
        rw [← mul_assoc, ← e2 k, mul_assoc, hc k, mul_assoc]
    _ = gram μ F * A := by rw [gram, integral_mul_const_of_integrable h]

theorem sqrt_commute (hF : Continuous F) (A : E →L[ℂ] E) (hA1 : adj A * A = 1) (hA2 : A * adj A = 1)
    (hc : ∀ k, A * F k = F k * A) : A * CFC.sqrt (gram μ F) = CFC.sqrt (gram μ F) * A := by
  have hG := gram_nonneg μ hF
  have hcG := gram_commute μ hF A hA1 hA2 hc
  set s := CFC.sqrt (gram μ F) with hs
  have hss : s * s = gram μ F := CFC.sqrt_mul_sqrt_self _ hG
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg _
  have hb0 : 0 ≤ A * s * adj A := by
    have := star_right_conjugate_nonneg hs0 A
    simpa [ContinuousLinearMap.star_eq_adjoint] using this
  have hbb : (A * s * adj A) * (A * s * adj A) = gram μ F := by
    calc (A * s * adj A) * (A * s * adj A) = A * s * (adj A * A) * s * adj A := by simp only [mul_assoc]
      _ = A * (s * s) * adj A := by rw [hA1]; simp only [mul_assoc, mul_one]
      _ = gram μ F * (A * adj A) := by rw [hss, hcG, mul_assoc]
      _ = gram μ F := by rw [hA2, mul_one]
  have hu : s = A * s * adj A := CFC.sqrt_unique hbb hb0
  calc A * s = A * s * (adj A * A) := by rw [hA1, mul_one]
    _ = (A * s * adj A) * A := by simp only [mul_assoc]
    _ = s * A := by rw [← hu]

end Abstract

section Concrete

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC

variable {n : ℕ}

local notation "KU" n => Matrix.unitaryGroup (Fin n) ℂ

instance secondCountable_unitary : SecondCountableTopology (KU n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _

theorem gamM_one : gamM (1 : Matrix (Md n) (Md n) ℂ) = 1 := by
  have h : (ExteriorAlgebra.map (Matrix.toLin' (1 : Matrix (Md n) (Md n) ℂ))).toLinearMap = LinearMap.id := by
    rw [Matrix.toLin'_one, ExteriorAlgebra.map_id]; rfl
  rw [gamM, h]
  exact LinearMap.toMatrix_id _

theorem gamM_mul (g h : Matrix (Md n) (Md n) ℂ) : gamM (g * h) = gamM g * gamM h := by
  have e : (ExteriorAlgebra.map (Matrix.toLin' (g * h))).toLinearMap =
      (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap ∘ₗ (ExteriorAlgebra.map (Matrix.toLin' h)).toLinearMap := by
    rw [Matrix.toLin'_mul, ← ExteriorAlgebra.map_comp_map]; rfl
  rw [gamM, e]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem continuous_map_dual (w : abelian₂ n) : ∀ φ : Module.Dual ℂ (abelian₂ n),
    Continuous fun g : Matrix (Md n) (Md n) ℂ => φ (ExteriorAlgebra.map (Matrix.toLin' g) w) := by
  induction w using ExteriorAlgebra.induction with
  | algebraMap r => intro φ; simpa using continuous_const
  | ι v =>
    intro φ
    have h1 : Continuous fun u : Md n → ℂ => φ (ExteriorAlgebra.ι ℂ u) :=
      (φ ∘ₗ ExteriorAlgebra.ι ℂ).continuous_of_finiteDimensional
    have h2 : Continuous fun g : Matrix (Md n) (Md n) ℂ => g *ᵥ v :=
      Continuous.matrix_mulVec continuous_id continuous_const
    have e : (fun g : Matrix (Md n) (Md n) ℂ => φ (ExteriorAlgebra.map (Matrix.toLin' g) (ExteriorAlgebra.ι ℂ v))) =
        fun g => φ (ExteriorAlgebra.ι ℂ (g *ᵥ v)) := by
      funext g; simp
    rw [e]
    exact h1.comp h2
  | add a b ha hb =>
    intro φ
    simp only [map_add]
    exact (ha φ).add (hb φ)
  | mul a b ha hb =>
    intro φ
    have key : ∀ x y : abelian₂ n, φ (x * y) =
        ∑ s, ∑ t, ((fb n).coord s x * (fb n).coord t y) * φ (fb n s * fb n t) := by
      intro x y
      calc φ (x * y) = φ ((∑ s, (fb n).repr x s • fb n s) * (∑ t, (fb n).repr y t • fb n t)) := by
            rw [(fb n).sum_repr, (fb n).sum_repr]
        _ = _ := by
            simp only [Finset.sum_mul_sum, map_sum, smul_mul_smul_comm, map_smul, smul_eq_mul,
              Module.Basis.coord_apply]
    have e : ∀ g : Matrix (Md n) (Md n) ℂ, φ (ExteriorAlgebra.map (Matrix.toLin' g) (a * b)) =
        ∑ s, ∑ t, ((fb n).coord s (ExteriorAlgebra.map (Matrix.toLin' g) a) *
          (fb n).coord t (ExteriorAlgebra.map (Matrix.toLin' g) b)) * φ (fb n s * fb n t) :=
      fun g => by rw [map_mul, key]
    simp only [e]
    exact continuous_finset_sum _ fun s _ => continuous_finset_sum _ fun t _ =>
      ((ha _).mul (hb _)).mul continuous_const

theorem continuous_gamM : Continuous (gamM (n := n)) := by
  refine continuous_matrix fun i j => ?_
  have e : (fun g : Matrix (Md n) (Md n) ℂ => gamM g i j) =
      fun g => (fb n).coord i (ExteriorAlgebra.map (Matrix.toLin' g) (fb n j)) := by
    funext g
    simp [gamM, matL, LinearMap.toMatrix_apply]
  rw [e]
  exact continuous_map_dual (fb n j) ((fb n).coord i)

theorem hbM_conjTranspose (m : Md n) : (hbM m)ᴴ = hbM m := GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose _

theorem herm_exp {H : Mat n} (hH : H.IsHermitian) : H = ∑ r : Md n, ((H * hbM r).trace.re : ℝ) • hbM r := by
  have h := GlobalTheory.CompanionTheory.HbBasis.hOf_coords hH
  conv_lhs => rw [← h]
  simp only [hOf, LfSt.coords]
  rw [← Equiv.sum_comp finProdFinEquiv.symm]
  simp [hbM, Complex.coe_smul]

theorem Mt_mul (x y : Mat n) : Mt (x * y) = Mt x * Mt y := by
  ext p q
  rw [Matrix.mul_apply]
  set H := y * hbM q * yᴴ with hHdef
  have hH : H.IsHermitian := by
    simp [Matrix.IsHermitian, hHdef, Matrix.conjTranspose_mul, hbM_conjTranspose, Matrix.mul_assoc]
  have e : x * y * hbM q * (x * y)ᴴ = ∑ r : Md n, ((H * hbM r).trace.re : ℝ) • (x * hbM r * xᴴ) := by
    have h1 : x * y * hbM q * (x * y)ᴴ = x * H * xᴴ := by
      simp [hHdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [h1]
    conv_lhs => rw [herm_exp hH]
    simp [Matrix.mul_sum, Matrix.sum_mul]
  show cf n (x * y * hbM q * (x * y)ᴴ) p = _
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, Pi.smul_apply]
  show _ = cf n (x * hbM r * xᴴ) p * cf n H r
  simp [cf, mul_comm]

theorem Mt_one : Mt (1 : Mat n) = 1 := by
  ext p q
  show cf n (1 * hbM q * (1 : Mat n)ᴴ) p = _
  have h := GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb (finProdFinEquiv.symm q) (finProdFinEquiv.symm p)
  simp only [cf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_one, mul_one, one_mul, hbM]
  rw [h]
  by_cases e : p = q
  · subst e
    rw [if_pos rfl, Matrix.one_apply_eq]
    simp
  · have : ¬ finProdFinEquiv.symm q = finProdFinEquiv.symm p :=
      fun h' => e (finProdFinEquiv.symm.injective h').symm
    rw [if_neg this, Matrix.one_apply_ne e]
    simp

theorem continuous_Mt : Continuous (Mt (n := n)) := by
  refine continuous_matrix fun p q => ?_
  show Continuous fun y : Mat n => cf n (y * hbM q * yᴴ) p
  simp only [cf, LinearMap.coe_mk, AddHom.coe_mk]
  have : Continuous fun y : Mat n => (y * hbM q * yᴴ * hbM p).trace :=
    (((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
      continuous_const).matrix_trace
  exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp this)

theorem Rm_unitary (lam : Fin n → ℤ) (k : KU n) :
    Rm lam k.1 = LinearMap.toMatrix (wb lam) (wb lam)
      (GlobalTheory.Branching.sqRep ℂ n (dw lam) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dif_pos h, e]

theorem Rm_mul (lam : Fin n → ℤ) (k k' : KU n) : Rm lam (k * k').1 = Rm lam k.1 * Rm lam k'.1 := by
  rw [Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : KU n).1 = 1 := by
  rw [Rm_unitary, map_one, map_one]
  exact LinearMap.toMatrix_id _

theorem continuous_unitaryIncl : Continuous (GlobalTheory.Branching.unitaryIncl n) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem continuous_Rm (lam : Fin n → ℤ) : Continuous fun k : KU n => Rm lam k.1 := by
  simp only [Rm_unitary]
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp
    continuous_unitaryIncl

theorem inv_val (k : KU n) : (k.1)⁻¹ = (k⁻¹).1 :=
  Matrix.inv_eq_right_inv (congrArg Subtype.val (mul_inv_cancel k))

theorem conj_val (k : KU n) : k.1ᴴ = (k⁻¹).1 := rfl

theorem Rm_inv (lam : Fin n → ℤ) (k : KU n) : (Rm lam k.1)⁻¹ = Rm lam (k⁻¹).1 :=
  Matrix.inv_eq_right_inv (by rw [← Rm_mul, mul_inv_cancel, Rm_one])

theorem continuous_kron {X a b c d : Type*} [TopologicalSpace X] {A : X → Matrix a b ℂ} {B : X → Matrix c d ℂ}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => A x ⊗ₖ B x :=
  continuous_matrix fun i j => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

theorem frame_rep_unitary (lam : Fin n → ℤ) (k : KU n) :
    fr0 lam k.1 = gamM (Mt (k⁻¹).1)ᵀ ⊗ₖ ((Rm lam (k⁻¹).1)ᵀ ⊗ₖ (Rm lam (k⁻¹).1)ᵀ) := by
  rw [fr0, rhoW, inv_val, conj_val, Rm_inv]

theorem frame_rep_mul (lam : Fin n → ℤ) (k k' : KU n) : fr0 lam (k * k').1 = fr0 lam k.1 * fr0 lam k'.1 := by
  rw [frame_rep_unitary, frame_rep_unitary, frame_rep_unitary, _root_.mul_inv_rev]
  have hM : (Mt (k'⁻¹ * k⁻¹ : KU n).1)ᵀ = (Mt (k⁻¹).1)ᵀ * (Mt (k'⁻¹).1)ᵀ := by
    rw [show (k'⁻¹ * k⁻¹ : KU n).1 = (k'⁻¹).1 * (k⁻¹).1 from rfl, Mt_mul, Matrix.transpose_mul]
  have hR : (Rm lam (k'⁻¹ * k⁻¹ : KU n).1)ᵀ = (Rm lam (k⁻¹).1)ᵀ * (Rm lam (k'⁻¹).1)ᵀ := by
    rw [Rm_mul, Matrix.transpose_mul]
  rw [hM, hR, gamM_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

theorem frame_rep_one (lam : Fin n → ℤ) : fr0 lam (1 : KU n).1 = 1 := by
  rw [frame_rep_unitary, inv_one, Rm_one]
  show gamM (Mt (1 : Mat n))ᵀ ⊗ₖ _ = 1
  rw [Mt_one, Matrix.transpose_one, gamM_one, Matrix.transpose_one, Matrix.one_kronecker_one,
    Matrix.one_kronecker_one]

theorem clm_mul (lam : Fin n → ℤ) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    clm lam (A * B) = clm lam A * clm lam B :=
  map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)) A B

theorem clm_one (lam : Fin n → ℤ) : clm lam 1 = 1 :=
  map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam))

theorem continuous_clm (lam : Fin n → ℤ) : Continuous (clm (n := n) lam) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Ix n lam)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

def fK (lam : Fin n → ℤ) : (KU n) →* (EV n lam →L[ℂ] EV n lam) where
  toFun k := clm lam (fr0 lam k.1)
  map_one' := by rw [frame_rep_one, clm_one]
  map_mul' k k' := by rw [frame_rep_mul, clm_mul]

theorem continuous_fK (lam : Fin n → ℤ) : Continuous (fK (n := n) lam) := by
  have hS : Continuous fun k : KU n => (Rm lam (k⁻¹).1)ᵀ :=
    ((continuous_Rm lam).comp continuous_inv).matrix_transpose
  have hI : Continuous fun k : KU n => (k⁻¹).1 := continuous_subtype_val.comp continuous_inv
  have hT : Continuous fun k : KU n => gamM (Mt (k⁻¹).1)ᵀ :=
    continuous_gamM.comp (continuous_Mt.comp hI).matrix_transpose
  have h : Continuous fun k : KU n => fr0 lam k.1 := by
    simp only [frame_rep_unitary]
    exact continuous_kron hT (continuous_kron hS hS)
  exact (continuous_clm lam).comp h

end Concrete

end GlobalTheory.CompanionTheory.CxAvg
end
end

section
noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate ContDiff Topology

namespace GlobalTheory.CompanionTheory.GelfAct

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem hasDerivAt_exp_entry (X : Mat n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) a b) (X a b) 0 := by
  have h : ∀ t : ℝ, (t : ℂ) • X = t • X := fun t => by ext; simp
  simp only [h]
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

def cf (π : G n →* (U →L[ℂ] U)) (w v : U) : Mat n → ℂ := fun g => ⟪w, piM π g v⟫_ℂ

def lin (π : G n →* (U →L[ℂ] U)) (w : U) (g : Mat n) : kfin π →ₗ[ℂ] ℂ :=
  ((innerSL ℂ w) ∘L (piM π g)).toLinearMap ∘ₗ (kfin π).subtype

end GlobalTheory.CompanionTheory.GelfAct

end
end

section
section
noncomputable section

open Matrix Finset Filter Topology
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmModel

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exists_frame (ν : Fin n → ℤ) :
    ∃ (d : ℕ) (e : (Jd n ν → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d)),
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : Jd n ν → ℂ),
        ⟪e (Rm ν k.1 *ᵥ x), e (Rm ν k.1 *ᵥ y)⟫_ℂ = ⟪e x, e y⟫_ℂ := by
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (Jd n ν → ℂ) :=
    { toFun := fun k => Matrix.mulVecLin (Rm ν k.1)
      map_one' := by
        show Matrix.mulVecLin (Rm ν (1 : Matrix.unitaryGroup (Fin n) ℂ).1) = 1
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_one, Matrix.mulVecLin_one]
        rfl
      map_mul' := fun a b => by
        show Matrix.mulVecLin (Rm ν (a * b).1) = _
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_mul, Matrix.mulVecLin_mul]
        rfl }
  have hρc : ∀ v, Continuous fun k => ρ k v := fun v =>
    (GlobalTheory.CompanionTheory.CxAvg.continuous_Rm ν).matrix_mulVec continuous_const
  obtain ⟨c, hc⟩ := GlobalTheory.exists_invariant_core ρ hρc
  obtain ⟨d, τ, e, hτ, he⟩ := GlobalTheory.ThetaCplV.UnitaryTrick.exists_isURep_of_core ρ
    (fun φ v => (LinearMap.continuous_of_finiteDimensional φ).comp (hρc v)) c hc
  refine ⟨d, e, fun k x y => ?_⟩
  have h1 : ∀ z, e (Rm ν k.1 *ᵥ z) = τ k (e z) := fun z => he k z
  rw [h1, h1]
  exact (LinearIsometry.mk (τ k).toLinearMap (hτ.2.2.1 k)).inner_map_map _ _

theorem hasDerivAt_Rm (ν : Fin n → ℤ) (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) (c : Jd n ν → ℂ) :
    HasDerivAt (fun t : ℝ => Rm ν (γ t).1 *ᵥ c) (XA ν X *ᵥ c) 0 := by
  have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
    refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
    exact GlobalTheory.CompanionTheory.GelfAct.hasDerivAt_exp_entry X a b
  have hentry : ∀ i j, HasDerivAt (fun t : ℝ => Rm ν (NormedSpace.exp ((t : ℂ) • X)) i j) (XA ν X i j) 0 := by
    intro i j
    have h1 := (holRm n ν i j 1 one_mem_GLs).hasFDerivAt.restrictScalars ℝ
    have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
    exact h1.comp_hasDerivAt_of_eq (0 : ℝ) hp h0.symm
  simp only [hγ]
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hentry i j).mul_const _

theorem XA_eq_sum (ν : Fin n → ℤ) (X : Mat n) : XA ν X = ∑ a, ∑ b, X a b • Xu ν a b := by
  have h : XA ν X = XA ν (∑ a, ∑ b, Matrix.single a b (X a b)) := congrArg (XA ν) (Matrix.matrix_eq_sum_single X)
  rw [h, XA_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [XA_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h2 : (Matrix.single a b (X a b) : Mat n) = X a b • Matrix.single a b (1 : ℂ) := by simp
  rw [h2, XA_smul]
  rfl

theorem strict_kill (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) (B : Mat n)
    (hB : ∀ i j, j ≤ i → B i j = 0) : XA ν B *ᵥ c = 0 := by
  rw [XA_eq_sum]
  have h : (∑ a, ∑ b, B a b • Xu ν a b) *ᵥ c = ∑ a, ∑ b, B a b • (Xu ν a b *ᵥ c) := by
    simp only [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [h]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rcases lt_or_ge a b with h | h
  · rw [hc a b h, smul_zero]
  · rw [hB a b h, zero_smul]

theorem fix_of_killed (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) (g : Mat n)
    (h1 : ∀ i j, j < i → g i j = 0) (h2 : ∀ i, g i i = 1) : Rm ν g *ᵥ c = c := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Mat n, N = g - 1 := ⟨_, rfl⟩
  have hNs : ∀ i j, j ≤ i → N i j = 0 := by
    intro i j hji
    rcases hji.eq_or_lt with rfl | h
    · simp [hN, h2]
    · simp [hN, h1 i j h, Matrix.one_apply_ne h.ne']
  let G : ℂ → Mat n := fun t => 1 + t • N
  have hGt : ∀ t, (G t).BlockTriangular id := fun t i j hij => by
    have hij' : j < i := hij
    simp [G, Matrix.one_apply_ne hij'.ne', hNs i j hij'.le]
  have hGd : ∀ t, (G t).det = 1 := by
    intro t
    rw [Matrix.det_of_upperTriangular (hGt t)]
    simp [G, hNs _ _ le_rfl]
  have hGu : ∀ t, IsUnit (G t).det := fun t => by rw [hGd]; exact isUnit_one
  have hGm : ∀ t, G t ∈ GLs n := fun t => mem_GLs_of_isUnit (hGu t)
  have hinv : ∀ t i j, j < i → (G t)⁻¹ i j = 0 := by
    intro t i j hij
    haveI := Matrix.invertibleOfIsUnitDet (G t) (hGu t)
    exact Matrix.blockTriangular_inv_of_blockTriangular (hGt t) hij
  let B : ℂ → Mat n := fun t => (G t)⁻¹ * N
  have hB : ∀ t i j, j ≤ i → B t i j = 0 := by
    intro t i j hji
    simp only [B, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hinv t i k h, zero_mul]
    · rw [hNs k j (hji.trans h), mul_zero]
  have hGB : ∀ t, G t * B t = N := fun t => by
    simp only [B]
    rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hGu t), one_mul]
  have hline : ∀ t, HasDerivAt G N t := fun t => by
    have h := ((hasDerivAt_id t).smul_const N).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have hdi : ∀ i t, HasDerivAt (fun s => (Rm ν (G s) *ᵥ c) i) 0 t := by
    intro i t
    have hij : ∀ j, HasDerivAt (fun s => Rm ν (G s) i j) ((Rm ν (G t) * XA ν (B t)) i j) t := by
      intro j
      have h0 := (holRm n ν i j (G t) (hGm t)).hasFDerivAt.comp_hasDerivAt t (hline t)
      rw [← fderiv_Rm (holRm n ν) (hGm t) (B t) i j, hGB]
      exact h0
    have hs : HasDerivAt (fun s => (Rm ν (G s) *ᵥ c) i) (∑ j, (Rm ν (G t) * XA ν (B t)) i j * c j) t := by
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum fun j _ => (hij j).mul_const _
    have hz : ∑ j, (Rm ν (G t) * XA ν (B t)) i j * c j = 0 := by
      have h3 : (Rm ν (G t) * XA ν (B t)) *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec, strict_kill ν c hc (B t) (hB t), Matrix.mulVec_zero]
      simpa [Matrix.mulVec, dotProduct] using congrFun h3 i
    rwa [hz] at hs
  funext i
  have h3 := is_const_of_deriv_eq_zero (fun t => (hdi i t).differentiableAt) (fun t => (hdi i t).deriv) 1 0
  have e1 : G 1 = g := by simp [G, hN]
  have e0 : G 0 = 1 := by simp [G]
  simp only [e1, e0, GlobalTheory.CompanionTheory.RmHol.Rm_one, Matrix.one_mulVec] at h3
  exact h3

theorem line_of_killed (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) :
    ∃ s : ℂ, c = s • ((wb ν).repr (HW.hv ν) : Jd n ν → ℂ) := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, ((wb ν).repr u : Jd n ν → ℂ) = c :=
    ⟨(wb ν).equivFun.symm c, by
      have h := (wb ν).equivFun.apply_symm_apply c
      rw [Module.Basis.equivFun_apply] at h
      exact h⟩
  have hfix : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      Formalism.BasicNotions.sqAct ℂ n (dw ν) g u.1 = u.1 := by
    intro g h1 h2
    have hdet : IsUnit (g.1).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    have e := HW.Rm_mulVec ν hdet u
    have e1 : Matrix.nonsingInvUnit g.1 hdet = g := Units.ext rfl
    rw [e1, hu, fix_of_killed ν c hc g.1 h1 h2] at e
    have e2 : (wb ν).repr (GlobalTheory.Branching.sqRep ℂ n (dw ν) g u) = (wb ν).repr u :=
      DFunLike.coe_injective (e.symm.trans hu.symm)
    exact congrArg Subtype.val ((wb ν).repr.injective e2)
  obtain ⟨s, hs⟩ := (highest_weight_irreducible n (dw ν)).2.2 u.1 u.2 hfix
  refine ⟨s, ?_⟩
  have h3 : u = s • HW.hv ν := Subtype.ext hs
  rw [← hu, h3, map_smul]
  rfl

section Frame

variable {ν : Fin n → ℤ} {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
  (e : (Jd n ν → ℂ) ≃ₗ[ℂ] L)

def frameL : Matrix (Jd n ν) (Jd n ν) ℂ →ₗ[ℂ] Module.End ℂ L :=
  e.conj.toLinearMap ∘ₗ (Matrix.toLin' : _ ≃ₗ[ℂ] _).toLinearMap

theorem frameL_apply (A : Matrix (Jd n ν) (Jd n ν) ℂ) (x : Jd n ν → ℂ) : frameL e A (e x) = e (A *ᵥ x) := by
  simp [frameL, LinearEquiv.conj_apply]

theorem frameL_one : frameL e 1 = 1 := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e.surjective w
  simp [frameL_apply]

theorem frameL_mul (A B : Matrix (Jd n ν) (Jd n ν) ℂ) : frameL e (A * B) = frameL e A * frameL e B := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e.surjective w
  simp [frameL_apply, Module.End.mul_apply]

theorem frameL_XA (X : Mat n) (w : L) :
    ∑ a, ∑ b, X a b • frameL e (Xu ν a b) w = frameL e (XA ν X) w := by
  rw [XA_eq_sum]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem glRel_frame : Formalism.REAL.GlRel fun a b => frameL e (Xu ν a b) := by
  intro a b c d
  have h := congrArg (frameL e) (xu_glRel n ν (holRm n ν) a b c d)
  rw [map_sub, map_sub, frameL_mul, frameL_mul] at h
  rw [h]
  split_ifs <;> simp

theorem deriv_frame (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) (x : Jd n ν → ℂ) :
    HasDerivAt (fun t : ℝ => e (Rm ν (γ t).1 *ᵥ x)) (e (XA ν X *ᵥ x)) 0 := by
  let E : (Jd n ν → ℂ) →L[ℂ] L := e.toLinearMap.toContinuousLinearMap
  exact (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_Rm ν X γ hγ x)

variable (he : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : Jd n ν → ℂ),
  ⟪e (Rm ν k.1 *ᵥ x), e (Rm ν k.1 *ᵥ y)⟫_ℂ = ⟪e x, e y⟫_ℂ)

include he in

theorem skew_frame (X : Mat n) (hX : Xᴴ = -X) (x y : Jd n ν → ℂ) :
    ⟪e (XA ν X *ᵥ x), e y⟫_ℂ + ⟪e x, e (XA ν X *ᵥ y)⟫_ℂ = 0 := by
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := GlobalTheory.CompanionTheory.RealCount.InjHw.expU X hX
  have hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) := fun _ => rfl
  have h0 : (γ 0).1 = 1 := by simp [hγ]
  have d3 := (deriv_frame e X γ hγ x).inner ℂ (deriv_frame e X γ hγ y)
  have hc : (fun t : ℝ => ⟪e (Rm ν (γ t).1 *ᵥ x), e (Rm ν (γ t).1 *ᵥ y)⟫_ℂ) = fun _ => ⟪e x, e y⟫_ℂ :=
    funext fun t => he _ x y
  rw [hc] at d3
  have h := d3.unique (hasDerivAt_const _ _)
  rw [h0, GlobalTheory.CompanionTheory.RmHol.Rm_one, Matrix.one_mulVec, Matrix.one_mulVec] at h
  rw [add_comm]
  exact h

include he in
theorem herm_frame (a b : Fin n) (x y : Jd n ν → ℂ) :
    ⟪e (Xu ν a b *ᵥ x), e y⟫_ℂ = ⟪e x, e (Xu ν b a *ᵥ y)⟫_ℂ := by
  have s1 : (Matrix.single a b (1 : ℂ) + (-1 : ℂ) • Matrix.single b a (1 : ℂ) : Mat n)ᴴ =
      -(Matrix.single a b (1 : ℂ) + (-1 : ℂ) • Matrix.single b a (1 : ℂ)) := by
    rw [conjTranspose_add, conjTranspose_smul, InjHw.single_conjT, InjHw.single_conjT]
    simp [add_comm]
  have s2 : (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ)) : Mat n)ᴴ =
      -(Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ))) := by
    rw [conjTranspose_smul, conjTranspose_add, InjHw.single_conjT, InjHw.single_conjT]
    simp [add_comm]
  have h1 := skew_frame e he _ s1 x y
  have h2 := skew_frame e he _ s2 x y
  unfold Xu
  simp only [XA_add, XA_smul, Matrix.add_mulVec, Matrix.smul_mulVec, map_add, map_smul,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at h1 h2
  simp only [map_neg, map_one, Complex.conj_I] at h1 h2
  generalize ⟪e (XA ν (Matrix.single a b 1) *ᵥ x), e y⟫_ℂ = p at h1 h2 ⊢
  generalize ⟪e (XA ν (Matrix.single b a 1) *ᵥ x), e y⟫_ℂ = q at h1 h2
  generalize ⟪e x, e (XA ν (Matrix.single a b 1) *ᵥ y)⟫_ℂ = r at h1 h2
  generalize ⟪e x, e (XA ν (Matrix.single b a 1) *ᵥ y)⟫_ℂ = s at h1 h2 ⊢
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + (1 / 2 : ℂ) * (p + q - r - s) * Complex.I_sq

include he in

theorem frame_model (hν : Antitone ν) :
    ∃ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L)) (K : Fin n → Fin n → Module.End ℂ L) (v : L),
      Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
        (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  obtain ⟨v0, hv0, hup, hwt⟩ := HW.exists_hw n ν (holRm n ν) hν
  generalize hc : ((wb ν).repr v0 : Jd n ν → ℂ) = c0 at hup hwt
  have hc0 : c0 ≠ 0 := fun h => hv0 ((wb ν).repr.map_eq_zero_iff.1 (DFunLike.coe_injective (hc.trans h)))
  let σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L) :=
    { toFun := fun k => frameL e (Rm ν k.1)
      map_one' := by
        show frameL e (Rm ν (1 : Matrix.unitaryGroup (Fin n) ℂ).1) = 1
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_one, frameL_one]
      map_mul' := fun a b => by
        show frameL e (Rm ν (a * b).1) = _
        rw [GlobalTheory.CompanionTheory.CxAvg.Rm_mul, frameL_mul] }
  have hσ : ∀ k x, σ k (e x) = e (Rm ν k.1 *ᵥ x) := fun k x => frameL_apply e _ x
  refine ⟨σ, fun a b => frameL e (Xu ν a b), e c0, glRel_frame e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    show ⟪frameL e (Xu ν a b) (e x), e y⟫_ℂ = ⟪e x, frameL e (Xu ν b a) (e y)⟫_ℂ
    rw [frameL_apply, frameL_apply]
    exact herm_frame e he a b x y
  · refine ⟨fun k x y => ?_, fun w => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ => Submodule.mem_top,
      fun _ _ _ _ => Submodule.mem_top, fun X γ hγ w' _ => ?_⟩⟩
    · obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [hσ, hσ]
      exact he k x y
    · obtain ⟨x, rfl⟩ := e.surjective w'
      have h := deriv_frame e X γ hγ x
      have e1 : (∑ a, ∑ b, X a b • frameL e (Xu ν a b) (e x)) = e (XA ν X *ᵥ x) := by
        rw [frameL_XA, frameL_apply]
      show HasDerivAt (fun t : ℝ => σ (γ t) (e x)) (∑ a, ∑ b, X a b • frameL e (Xu ν a b) (e x)) 0
      rw [e1]
      simpa only [hσ] using h
  · exact e.map_ne_zero_iff.2 hc0
  · refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · show frameL e (Xu ν a a) (e c0) = ((wtR ν a : ℝ) : ℂ) • e c0
      rw [frameL_apply, hwt a, map_smul]
      simp [wtR]
    · show frameL e (Xu ν a b) (e c0) = 0
      rw [frameL_apply, hup a b hab, map_zero]
  · intro w hw
    obtain ⟨x, rfl⟩ := e.surjective w
    have hx : ∀ a b, a < b → Xu ν a b *ᵥ x = 0 := fun a b hab =>
      e.map_eq_zero_iff.1 (by rw [← frameL_apply]; exact hw a b hab)
    obtain ⟨s, hs⟩ := line_of_killed ν x hx
    obtain ⟨s0, hs0⟩ := line_of_killed ν c0 hup
    have hs00 : s0 ≠ 0 := by
      rintro rfl
      exact hc0 (by simpa using hs0)
    refine ⟨s / s0, ?_⟩
    have hxc : x = (s / s0) • c0 := by
      rw [hs]
      conv_rhs => rw [hs0]
      rw [smul_smul, div_mul_cancel₀ _ hs00]
    rw [hxc, map_smul]
  · intro k z hk hz
    have hu : IsUnit (k.1).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
    have h0 : ∀ a, z a ≠ 0 := by
      rw [hk, Matrix.det_diagonal] at hu
      exact fun a => (Finset.prod_ne_zero_iff.1 hu.ne_zero) a (Finset.mem_univ a)
    show LinearMap.trace ℂ L (frameL e (Rm ν k.1)) = _
    have h1 : frameL e (Rm ν k.1) = e.conj (Matrix.toLin' (Rm ν k.1)) := rfl
    rw [h1, LinearMap.trace_conj', Matrix.trace_toLin'_eq, hk]
    exact GlobalTheory.CompanionTheory.RmCharacter.rmChar n ν hν z h0 hz

end Frame

theorem rmModel : ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν → ∃ (L : Type) (_ : NormedAddCommGroup L)
    (_ : InnerProductSpace ℂ L) (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L))
    (K : Fin n → Fin n → Module.End ℂ L) (v : L), Formalism.REAL.GlRel K ∧
      (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
      (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
        LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  intro n ν hν
  obtain ⟨d, e, he⟩ := exists_frame ν
  exact ⟨EuclideanSpace ℂ (Fin d), inferInstance, inferInstance, inferInstance, frame_model e he hν⟩

end GlobalTheory.CompanionTheory.RmModel
end
end

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_hermitian_derivation : ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν → ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L)) (K : Fin n → Fin n → Module.End ℂ L) (v : L), Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧ (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧ ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RmModel.rmModel
end

section
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Isotypic

variable {n : ℕ}

theorem exists_map_out (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (d : H) (hd : Formalism.REAL.KHighest (fun _ => true) G μ d) :
    ∃ T : L →ₗ[ℂ] H, T v = d ∧ ∀ a b w, T (K a b w) = G a b (T w) := by
  have hsp : ∀ x ∈ Submodule.span ℂ {v}, Formalism.REAL.KHighest (fun _ => true) K μ x := by
    intro x hx
    have hvm : v ∈ hwOf K μ := hv
    have : x ∈ hwOf K μ := (Submodule.span_singleton_le_iff_mem v (hwOf K μ)).2 hvm hx
    exact this
  let f : (Submodule.span ℂ {v}) →ₗ[ℂ] H :=
    ((innerₛₗ ℂ v).comp (Submodule.subtype _)).smulRight ((⟪v, v⟫_ℂ)⁻¹ • d)
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) G μ (f x) := by
    intro x
    have hdm : d ∈ hwOf G μ := hd
    have : f x ∈ hwOf G μ := by
      simp only [f, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hdm)
    exact this
  obtain ⟨T, hT, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition L H K G μ hK hG hKs hGs (Submodule.span ℂ {v}) hsp f hf
  refine ⟨T, ?_, hi⟩
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have := hT ⟨v, Submodule.mem_span_singleton_self v⟩
  simp only at this
  rw [this]
  simp only [f, LinearMap.smulRight_apply, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply]
  rw [smul_smul, mul_inv_cancel₀ hvv, one_smul]

theorem exists_map_in (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (D : Submodule ℂ H) (hD : ∀ x ∈ D, Formalism.REAL.KHighest (fun _ => true) G μ x) (φ : D →ₗ[ℂ] ℂ) :
    ∃ P : H →ₗ[ℂ] L, (∀ d : D, P d = φ d • v) ∧ ∀ a b w, P (G a b w) = K a b (P w) := by
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) K μ (φ.smulRight v x) := by
    intro x
    have hvm : v ∈ hwOf K μ := hv
    have : φ.smulRight v x ∈ hwOf K μ := by
      simp only [LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ hvm
    exact this
  obtain ⟨P, hP, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition H L G K μ hG hK hGs hKs D hD (φ.smulRight v) hf
  exact ⟨P, fun d => by rw [hP d, LinearMap.smulRight_apply], hi⟩

theorem eq_smul_id_of_apply (L : Type) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (K : Fin n → Fin n → Module.End ℂ L) (hK : Formalism.REAL.GlRel K)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) (v : L)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (R : L →ₗ[ℂ] L) (hR : ∀ a b w, R (K a b w) = K a b (R w)) (r : ℂ) (hr : R v = r • v) :
    R = r • LinearMap.id := by
  have h0 := GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest L L K K hK hKs (R - r • LinearMap.id)
    (fun a b w => by simp [hR, map_smul]) (fun μ w hw => by
      obtain ⟨c, rfl⟩ := huniq w (fun a b hab => hw.2 a b hab rfl)
      simp [hr, smul_comm c r])
  exact sub_eq_zero.1 h0

theorem map_highest_eq_zero {H L : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup L] [Module ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ μ' : Fin n → ℝ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ' v)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (P : H →ₗ[ℂ] L) (hP : ∀ a b w, P (G a b w) = K a b (P w))
    (hne : μ ≠ μ') (w : H) (hw : Formalism.REAL.KHighest (fun _ => true) G μ w) : P w = 0 := by
  obtain ⟨c, hc⟩ := huniq (P w) (fun a b hab => by rw [← hP, hw.2 a b hab rfl, map_zero])
  by_contra hne0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne0 (by simpa using hc)
  apply hne
  funext a
  have h1 : K a a (P w) = (μ a : ℂ) • P w := by rw [← hP, hw.1 a, map_smul]
  rw [hc, map_smul, hv.1 a, smul_comm] at h1
  have h2 : ((μ' a : ℂ) - (μ a : ℂ)) • (c • v) = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : (μ' a : ℂ) - (μ a : ℂ) = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (smul_ne_zero hc0 hv0)
  have h4 : (μ' a : ℂ) = (μ a : ℂ) := sub_eq_zero.1 h3
  exact (Complex.ofReal_injective h4).symm

theorem map_mem_hwOf {H : Type} [AddCommGroup H] [Module ℂ H]
    (G : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (S : H →ₗ[ℂ] H)
    (hS : ∀ a b w, S (G a b w) = G a b (S w)) (x : H) (hx : x ∈ hwOf G μ) : S x ∈ hwOf G μ :=
  ⟨fun a => by rw [← hS, hx.1 a, map_smul],
    fun a b hab he => by rw [← hS, hx.2 a b hab he, map_zero]⟩

theorem exists_isotypic_projection {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H))
    (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ) :
    Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) →
    (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) →
    Antitone ν →
    ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  intro hG hGs hder hν
  obtain ⟨L, _, _, _, σ, K, v, hK, hKs, hσ, hv0, hv, huniq, htr⟩ := GlobalTheory.T.exists_highest_weight_hermitian_derivation ν hν
  have hD : ∀ x ∈ hwOf G (wtR ν), Formalism.REAL.KHighest (fun _ => true) G (wtR ν) x := fun x hx => hx
  let b := Module.finBasis ℂ (hwOf G (wtR ν))
  have ex1 : ∀ j, ∃ T : L →ₗ[ℂ] H, T v = (b j : H) ∧ ∀ a c w, T (K a c w) = G a c (T w) := fun j =>
    exists_map_out H L G K (wtR ν) hG hK hGs hKs v hv0 hv (b j : H) (b j).2
  choose T hTv hTi using ex1
  have ex2 : ∀ j, ∃ P : H →ₗ[ℂ] L, (∀ d : hwOf G (wtR ν), P d = b.coord j d • v) ∧
      ∀ a c w, P (G a c w) = K a c (P w) := fun j =>
    exists_map_in H L G K (wtR ν) hG hK hGs hKs v hv _ hD (b.coord j)
  choose P hPd hPi using ex2
  have hPk : ∀ j k w, P j (ρ k w) = σ k (P j w) := fun j =>
    GlobalTheory.T.derivative_unitary_action H L ρ G hder σ K hσ hKs (P j) (hPi j)
  have hp : ∀ w, (∑ j, T j ∘ₗ P j) w = ∑ j, T j (P j w) := fun w => by
    simp [LinearMap.sum_apply]
  refine ⟨∑ j, T j ∘ₗ P j, ?_, ?_, ?_, ?_⟩
  · intro a c w
    rw [hp, hp, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hPi, hTi]
  · intro d hd
    rw [hp]
    have h1 : ∀ j, T j (P j d) = b.coord j ⟨d, hd⟩ • (b j : H) := fun j => by
      have := hPd j ⟨d, hd⟩
      simp only at this
      rw [this, map_smul, hTv]
    simp only [h1]
    have h2 : ∑ j, b.coord j ⟨d, hd⟩ • b j = ⟨d, hd⟩ := b.sum_repr _
    calc ∑ j, b.coord j ⟨d, hd⟩ • (b j : H)
        = ((∑ j, b.coord j ⟨d, hd⟩ • b j : hwOf G (wtR ν)) : H) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
      _ = d := by rw [h2]
  · intro μ w hne hw
    rw [hp]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_highest_eq_zero G K μ (wtR ν) v hv0 hv huniq (P j) (hPi j) hne w hw, map_zero]
  · intro S hS k z hk hz
    have hSD : ∀ x ∈ hwOf G (wtR ν), S x ∈ hwOf G (wtR ν) := map_mem_hwOf G (wtR ν) S hS
    have hj : ∀ j, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j)) =
        b.coord j ⟨S (b j), hSD _ (b j).2⟩ * weylChar ν z := by
      intro j
      have hR : P j ∘ₗ S ∘ₗ T j = b.coord j ⟨S (b j), hSD _ (b j).2⟩ • LinearMap.id := by
        refine eq_smul_id_of_apply L K hK hKs v huniq _ (fun a c w => ?_) _ ?_
        · simp only [LinearMap.comp_apply]
          rw [hTi, hS, hPi]
        · simp only [LinearMap.comp_apply]
          rw [hTv]
          exact hPd j ⟨S (b j), hSD _ (b j).2⟩
      have e1 : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) = ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) ∘ₗ P j := rfl
      have e2 : P j ∘ₗ ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) = σ k ∘ₗ (P j ∘ₗ S ∘ₗ T j) := by
        ext w
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        exact hPk j k _
      rw [e1, LinearMap.trace_comp_comm', e2, hR, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
        htr k z hk hz, smul_eq_mul]
    have hsum : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (∑ j, T j ∘ₗ P j) =
        ∑ j, (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) := by
      ext w
      simp [LinearMap.sum_apply, map_sum]
    rw [hsum, map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul]
    congr 1
    unfold trOn
    rw [dif_pos hSD, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl

end GlobalTheory.CompanionTheory.RealCountG.Isotypic
end
end

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_integral_of_unitary : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → Antitone ν → ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧ (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧ ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RealCountG.Isotypic.exists_isotypic_projection
end
