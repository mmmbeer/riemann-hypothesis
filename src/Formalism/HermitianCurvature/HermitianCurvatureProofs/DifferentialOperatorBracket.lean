import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantGeneric
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliTwoByTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QRadialDecompositionOfPieces
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres

section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieBracketMultiplication

section Geometry

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem uw_mul {g h : Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) : g * h ∈ UWset k r z := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hh1, hh2, hh3⟩ := hh
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e1 : gᴴ * Hpk k r * g = Hpk k r := hg1
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hh1
    show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · rw [← Matrix.mulVec_mulVec, (hh2 a).1, (hg2 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a).2, (hg2 a).2]
  · rw [← Matrix.mulVec_mulVec, hh3, hg3]

theorem uw_pow {g : Mx k r} (hg : g ∈ UWset k r z) (n : ℕ) : g ^ n ∈ UWset k r z := by
  induction n with
  | zero =>
    rw [pow_zero]
    refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
    · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
      simp
    all_goals simp
  | succ n ih =>
    rw [pow_succ]
    exact uw_mul ih hg

theorem uw_inv {h : Mx k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have := FrameEntries.glev_inv (Qx8.uw_glev (Fin.last r) hh)
  refine ⟨this.1, fun a => this.2 a (by simp), ?_⟩
  calc h⁻¹ *ᵥ z = h⁻¹ *ᵥ (h *ᵥ z) := by rw [hh.2.2]
    _ = z := by rw [Matrix.mulVec_mulVec, LeftDerivativeCurves.uh_inv_mul hh.1, Matrix.one_mulVec]

theorem lie_zero : InLieW k r z (0 : Mx k r) := by
  unfold InLieW inLieLev
  refine ⟨?_, by simp⟩
  simp

theorem lie_add {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X + Y) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  obtain ⟨⟨h3, h3'⟩, h4⟩ := hY
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_add, add_mul, mul_add]
    calc Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y)
        = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  · rw [Matrix.add_mulVec, (h1' a ha).1, (h3' a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (h1' a ha).2, (h3' a ha).2, add_zero]
  · rw [Matrix.add_mulVec, h2, h4, add_zero]

theorem lie_smul {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) : InLieW k r z ((s : ℂ) • X) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  have hs : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · first
    | rw [Matrix.smul_mulVec, (h1' a ha).1, smul_zero]
    | simp [(h1' a ha).1]
  · first
    | rw [Matrix.smul_mulVec, (h1' a ha).2, smul_zero]
    | simp [(h1' a ha).2]
  · first
    | rw [Matrix.smul_mulVec, h2, smul_zero]
    | simp [h2]

theorem lie_bracket {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) :
    InLieW k r z (X * Y - Y * X) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  obtain ⟨⟨h3, h3'⟩, h4⟩ := hY
  have eX : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left h1
  have eY : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left h3
  have t1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * Y * X := by
    rw [mul_assoc, eX, mul_neg, ← mul_assoc, eY, neg_mul, neg_neg]
  have t2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * X * Y := by
    rw [mul_assoc, eY, mul_neg, ← mul_assoc, eX, neg_mul, neg_neg]
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, sub_mul, t1, t2,
      mul_sub, ← mul_assoc, ← mul_assoc]
    abel
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (h1' a ha).1, (h3' a ha).1,
      Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (h1' a ha).2, (h3' a ha).2,
      Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, h4,
      Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]

theorem lie_conj {X h : Mx k r} (hX : InLieW k r z X) (hh : h ∈ UWset k r z) : InLieW k r z (h * X * h⁻¹) := by
  have hi := uw_inv hh
  have h1 := LeftDerivativeCurves.lie_conj (Qx8.uw_glev (Fin.last r) hi) hX.1
  rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)] at h1
  refine ⟨h1, ?_⟩
  rw [← Matrix.mulVec_mulVec, hi.2.2, ← Matrix.mulVec_mulVec, hX.2, Matrix.mulVec_zero]

theorem exp_inv (X : Mx k r) (s : ℝ) :
    (NormedSpace.exp ((s : ℂ) • X))⁻¹ = NormedSpace.exp (((-s : ℝ) : ℂ) • X) := by
  have e : (((-s : ℝ) : ℂ) • X) = -((s : ℂ) • X) := by
    push_cast
    rw [neg_smul]
  rw [e, Matrix.exp_neg]

end Geometry

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem pi_pow (hπ : IsCRepOn (UWset k r z) π) {g : Mx k r} (hg : g ∈ UWset k r z) (n : ℕ) :
    π (g ^ n) = (π g) ^ n := by
  induction n with
  | zero => simpa using hπ.1
  | succ n ih =>
    rw [pow_succ, hπ.2 _ (uw_pow hg n) _ hg, ih, pow_succ]
    try rfl

theorem dOp_smul (hπ : Qr.IsRepW k r z π) {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) :
    dOp π ((s : ℂ) • X) = s • dOp π X := by
  unfold dOp
  have h := deriv_comp_mul_left s (fun u : ℝ => π (NormedSpace.exp ((u : ℂ) • X))) 0
  rw [mul_zero] at h
  rw [← h]
  congr 1
  funext t
  congr 2
  push_cast
  rw [smul_smul, mul_comm (t : ℂ) (s : ℂ)]

end Rep

end LieBracketMultiplication

theorem differential_operator_adjoint : Formalism.FourierDecayAlt.Qr.DOpAd := by
  intro W _ _ _ k r z π hπ X hX h hh
  have hi := LieBracketMultiplication.uw_inv hh
  refine ⟨hi, LieBracketMultiplication.lie_conj hX hh, ?_⟩
  have hd := dOp_hasDeriv hπ.1 hπ.2 hX
  let L : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) :=
    (ContinuousLinearMap.compL ℂ W W W (π h)).comp ((ContinuousLinearMap.compL ℂ W W W).flip (π h⁻¹))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have h3 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (h * X * h⁻¹)))) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [Qx8.exp_conj_uh hh.1, Matrix.mul_assoc, hπ.1.2 _ hh _ (LieBracketMultiplication.uw_mul (exp_uw hX t) hi),
      hπ.1.2 _ (exp_uw hX t) _ hi]
    rfl
  unfold dOp
  rw [h3]
  exact h2.deriv

namespace LieBracketMultiplication

section Add

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem pi_exp_add (hT : Qr.Trotter) (hM : Qr.TrotterMx) (hP : Qr.PiExp) (hπ : Qr.IsRepW k r z π) {X Y : Mx k r}
    (hX : InLieW k r z X) (hY : InLieW k r z Y) (t : ℝ) :
    π (NormedSpace.exp ((t : ℂ) • (X + Y))) = NormedSpace.exp (t • (dOp π X + dOp π Y)) := by
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hX' := lie_smul hX t
  have hY' := lie_smul hY t
  have h1 := hM _ ((t : ℂ) • X) ((t : ℂ) • Y)
  rw [← smul_add] at h1
  have hmem : ∀ n : ℕ, (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • ((t : ℂ) • X)) *
      NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • ((t : ℂ) • Y))) ^ n ∈ UWset k r z :=
    fun n => uw_pow (uw_mul (exp_uw hX' _) (exp_uw hY' _)) n
  have hlim := exp_uw (lie_add hX hY) t
  have h2 := (hπ.2 _ hlim).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall hmem⟩)
  have h3 := hT (W →L[ℂ] W) (t • dOp π X) (t • dOp π Y)
  rw [← smul_add] at h3
  refine tendsto_nhds_unique h2 (h3.congr fun n => ?_)
  simp only [Function.comp]
  rw [pi_pow hπ.1 (uw_mul (exp_uw hX' _) (exp_uw hY' _)) n, hπ.1.2 _ (exp_uw hX' _) _ (exp_uw hY' _),
    hP W k r z π hπ _ hX', hP W k r z π hπ _ hY', dOp_smul hπ hX, dOp_smul hπ hY]
  rfl

end Add

end LieBracketMultiplication

theorem qr_dOpLin_of (hT : Formalism.FourierDecayAlt.Qr.Trotter) (hM : Formalism.FourierDecayAlt.Qr.TrotterMx) (hP : Formalism.FourierDecayAlt.Qr.PiExp) :
    Formalism.FourierDecayAlt.Qr.DOpLin := by
  intro W _ _ _ k r z π hπ X Y hX hY
  refine ⟨?_, fun s => LieBracketMultiplication.dOp_smul hπ hX s⟩
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (dOp π X + dOp π Y) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (X + Y)))) =
      fun t : ℝ => NormedSpace.exp (t • (dOp π X + dOp π Y)) :=
    funext (LieBracketMultiplication.pi_exp_add hT hM hP hπ hX hY)
  show deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (X + Y)))) 0 = _
  rw [e]
  exact h.deriv

namespace LieBracketMultiplication

section Bracket

variable {k r : ℕ}

theorem real_smul (s : ℝ) (X : Mx k r) : s • X = (s : ℂ) • X := by
  first
  | exact (Complex.coe_smul s X).symm
  | simp [Complex.coe_smul]

def lieSub (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Mx k r) where
  carrier := {X | InLieW k r z X}
  add_mem' := fun hX hY => lie_add hX hY
  zero_mem' := lie_zero
  smul_mem' := fun s X hX => by
    show InLieW k r z (s • X)
    rw [real_smul]
    exact lie_smul hX s

def mulB (k r : ℕ) : Mx k r →L[ℝ] Mx k r →L[ℝ] Mx k r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Mx k r →ₗ[ℝ] Mx k r) ≃ₗ[ℝ] (Mx k r →L[ℝ] Mx k r)).toLinearMap ∘ₗ
      LinearMap.mul ℝ (Mx k r))

theorem conj_hasDeriv (X Y : Mx k r) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X)))
      (X * Y - Y * X) 0 := by
  have hu := LeftDerivativeCurves.lcurve_hasDeriv X Y
  have hv := hasDerivAt_mul_exp_smul_zero (1 : Mx k r) (-X)
  have h : HasDerivAt
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • (-X))))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * Y * ((1 : Mx k r) * -X) +
        X * Y * ((1 : Mx k r) * NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)))) 0 :=
    (mulB k r).hasDerivAt_of_bilinear (fun _ => hu) (fun _ => hv)
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one,
    Matrix.mul_neg] at h
  rw [neg_add_eq_sub] at h
  exact h

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem op_hasDeriv (A B : W →L[ℂ] W) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * B * NormedSpace.exp (s • (-A))) (A * B - B * A) 0 := by
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have ha := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  have hb := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ)
  have h := (ha.mul_const B).mul hb
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg] at h
  rw [← sub_eq_add_neg] at h
  exact h

end Bracket

end LieBracketMultiplication

theorem qr_dOpBracket_of (hP : Formalism.FourierDecayAlt.Qr.PiExp) (hL : Formalism.FourierDecayAlt.Qr.DOpLin) (hAd : Formalism.FourierDecayAlt.Qr.DOpAd) :
    Formalism.FourierDecayAlt.Qr.DOpBracket := by
  intro W _ _ _ k r z π hπ X Y hX hY
  have hbr := LieBracketMultiplication.lie_bracket hX hY
  refine ⟨hbr, ?_⟩
  let Λ₀ : LieBracketMultiplication.lieSub k r z →ₗ[ℝ] (W →L[ℂ] W) :=
    { toFun := fun U => dOp π U.1
      map_add' := fun U V => (hL W k r z π hπ U.1 V.1 U.2 V.2).1
      map_smul' := fun s U => by
        show dOp π (s • U.1) = s • dOp π U.1
        rw [LieBracketMultiplication.real_smul]
        exact (hL W k r z π hπ U.1 U.1 U.2 U.2).2 s }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  have hΛ' : ∀ U : Mx k r, InLieW k r z U → Λ U = dOp π U := fun U hU =>
    LinearMap.congr_fun hΛ (⟨U, hU⟩ : LieBracketMultiplication.lieSub k r z)
  have h1 := (LinearMap.toContinuousLinearMap Λ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (LieBracketMultiplication.conj_hasDeriv X Y)
  have h2 := LieBracketMultiplication.op_hasDeriv (dOp π X) (dOp π Y)
  have e : (LinearMap.toContinuousLinearMap Λ) ∘
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) =
      fun s : ℝ => NormedSpace.exp (s • dOp π X) * dOp π Y * NormedSpace.exp (s • (-dOp π X)) := by
    funext s
    have e1 : (s : ℂ) • (-X) = ((-s : ℝ) : ℂ) • X := by
      rw [Complex.ofReal_neg, neg_smul, smul_neg]
    have e2 : s • (-dOp π X) = (-s) • dOp π X := by rw [neg_smul, smul_neg]
    have h3 := hAd W k r z π hπ Y hY _ (exp_uw hX s)
    show Λ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) = _
    rw [e1, ← LieBracketMultiplication.exp_inv, hΛ' _ h3.2.1, h3.2.2, LieBracketMultiplication.exp_inv, hP W k r z π hπ X hX, hP W k r z π hπ X hX, e2,
      mul_assoc]
    rfl
  rw [e] at h1
  have h4 := h1.unique h2
  rw [← hΛ' _ hbr]
  exact h4

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieListProducts

theorem alg_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (a b : ℂ) (A₁ A₂ : M) :
    (a • A₁ - b • A₂) + Complex.I • (a • A₂ + b • A₁) = (a + b * Complex.I) • (A₁ + Complex.I • A₂) := by
  have h : Complex.I • Complex.I • A₂ = -A₂ := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [smul_add, add_smul, mul_smul, h]
  module

theorem alg_bracket {R : Type*} [Ring R] [Algebra ℂ R] (A₁ A₂ B₁ B₂ : R) :
    (A₁ + Complex.I • A₂) * (B₁ + Complex.I • B₂) - (B₁ + Complex.I • B₂) * (A₁ + Complex.I • A₂) =
      ((A₁ * B₁ - B₁ * A₁) - (A₂ * B₂ - B₂ * A₂)) + Complex.I • ((A₁ * B₂ - B₂ * A₁) + (A₂ * B₁ - B₁ * A₂)) := by
  have h : ∀ x : R, Complex.I • Complex.I • x = -x := fun x => by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, h]
  module

section Lie

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem lie_zero : InLieW k r z 0 := by
  refine ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩

theorem lie_add {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X + Y) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    have h1 := hX.1.1
    have h2 := hY.1.1
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).1, (hY.1.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).2, (hY.1.2 a ha).2, add_zero]
  · rw [Matrix.add_mulVec, hX.2, hY.2, add_zero]

theorem lie_smul {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) : InLieW k r z ((s : ℂ) • X) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
    rw [this, ← smul_add, hX.1.1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).2, smul_zero]
  · rw [Matrix.smul_mulVec, hX.2, smul_zero]

theorem lie_sub {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X - Y) := by
  have := lie_add hX (lie_smul hY (-1))
  simpa [sub_eq_add_neg] using this

theorem conj_lie {X : Mx k r} (hX : InLieW k r z X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have h : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1.1
  rw [Qx8.hpk_inv, Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.one_mul]

theorem hpart1_lie {X : Mx k r} (hX : InLieW k r z X) : hpart1 (Hpk k r) X = X := by
  unfold hpart1
  rw [conj_lie hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_lie {X : Mx k r} (hX : InLieW k r z X) : hpart2 (Hpk k r) X = 0 := by
  unfold hpart2
  rw [conj_lie hX, add_neg_cancel, smul_zero]

theorem hpart1_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart1 (Hpk k r) (X₁ + Complex.I • X₂) = X₁ := by
  rw [CapelliCoordinates.hpart1_add, CapelliCoordinates.hpart1_smul, hpart1_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hpart2_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart2 (Hpk k r) (X₁ + Complex.I • X₂) = X₂ := by
  rw [CapelliCoordinates.hpart2_add, CapelliCoordinates.hpart2_smul, hpart2_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hsum (Z : Mx k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp [Complex.I_ne_zero]
  rw [e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem gl_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    InGlW k r z (X₁ + Complex.I • X₂) := by
  unfold InGlW
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]
  exact ⟨h1, h2⟩

theorem ec_comb {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (π : Mx k r → (W →L[ℂ] W))
    {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    ecOp π (X₁ + Complex.I • X₂) = dOp π X₁ + Complex.I • dOp π X₂ := by
  unfold ecOp
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]

end Lie

end LieListProducts

open LieListProducts in
theorem qr_ecLie_of : Qr.DOpLin → Qr.DOpBracket → Qr.EcLie := by
  intro hLin hBr W _ _ _ k r z π hπ Z Z' hZ hZ'
  obtain ⟨hX₁, hX₂⟩ := hZ
  obtain ⟨hY₁, hY₂⟩ := hZ'
  have eZ := hsum Z
  have eZ' := hsum Z'
  set X₁ := hpart1 (Hpk k r) Z
  set X₂ := hpart2 (Hpk k r) Z
  set Y₁ := hpart1 (Hpk k r) Z'
  set Y₂ := hpart2 (Hpk k r) Z'
  have dadd : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X + Y) = dOp π X + dOp π Y :=
    fun X Y hX hY => (hLin W k r z π hπ X Y hX hY).1
  have dsm : ∀ X (s : ℝ), InLieW k r z X → dOp π ((s : ℂ) • X) = (s : ℂ) • dOp π X := fun X s hX => by
    rw [(hLin W k r z π hπ X X hX hX).2 s, Complex.coe_smul]
  have dsub : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X - Y) = dOp π X - dOp π Y := fun X Y hX hY => by
    have e : X - Y = X + (((-1 : ℝ) : ℂ)) • Y := by simp [sub_eq_add_neg]
    rw [e, dadd _ _ hX (lie_smul hY _), dsm _ _ hY]
    simp [sub_eq_add_neg]
  have ecZ : ecOp π Z = dOp π X₁ + Complex.I • dOp π X₂ := rfl
  have ecZ' : ecOp π Z' = dOp π Y₁ + Complex.I • dOp π Y₂ := rfl
  refine ⟨?_, fun c => ?_, ?_⟩
  · have e : Z + Z' = (X₁ + Y₁) + Complex.I • (X₂ + Y₂) := by
      rw [← eZ, ← eZ', smul_add]; abel
    rw [e]
    refine ⟨gl_comb (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), ?_⟩
    rw [ec_comb π (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), dadd _ _ hX₁ hY₁, dadd _ _ hX₂ hY₂, ecZ, ecZ', smul_add]
    abel
  · have e : c • Z = ((c.re : ℂ) • X₁ - (c.im : ℂ) • X₂) + Complex.I • ((c.re : ℂ) • X₂ + (c.im : ℂ) • X₁) := by
      rw [alg_smul, Complex.re_add_im, eZ]
    have l1 := lie_sub (lie_smul hX₁ c.re) (lie_smul hX₂ c.im)
    have l2 := lie_add (lie_smul hX₂ c.re) (lie_smul hX₁ c.im)
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ (lie_smul hX₁ c.re) (lie_smul hX₂ c.im),
      dadd _ _ (lie_smul hX₂ c.re) (lie_smul hX₁ c.im), dsm X₁ c.re hX₁, dsm X₂ c.im hX₂, dsm X₂ c.re hX₂, dsm X₁ c.im hX₁, alg_smul, Complex.re_add_im, ecZ]
  · have b11 := hBr W k r z π hπ X₁ Y₁ hX₁ hY₁
    have b22 := hBr W k r z π hπ X₂ Y₂ hX₂ hY₂
    have b12 := hBr W k r z π hπ X₁ Y₂ hX₁ hY₂
    have b21 := hBr W k r z π hπ X₂ Y₁ hX₂ hY₁
    have e : Z * Z' - Z' * Z = ((X₁ * Y₁ - Y₁ * X₁) - (X₂ * Y₂ - Y₂ * X₂)) +
        Complex.I • ((X₁ * Y₂ - Y₂ * X₁) + (X₂ * Y₁ - Y₁ * X₂)) := by
      rw [← alg_bracket, eZ, eZ']
    have l1 := lie_sub b11.1 b22.1
    have l2 := lie_add b12.1 b21.1
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ b11.1 b22.1, dadd _ _ b12.1 b21.1, b11.2, b22.2, b12.2, b21.2, ecZ, ecZ']
    exact (alg_bracket (dOp π X₁) (dOp π X₂) (dOp π Y₁) (dOp π Y₂)).symm

namespace LieListProducts

theorem unitB_mul {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ)
    (ho : ∀ a b, herm H (Bs a) (Bs b) = if a = b then 1 else 0) (a b c d : Fin m) :
    unitB H Bs a b * unitB H Bs c d = if b = c then unitB H Bs a d else 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, Qx8.unitB_mulVec H Bs c d, Matrix.mulVec_smul, Qx8.unitB_mulVec, ho]
  by_cases h : b = c
  · rw [if_pos h, if_pos h.symm, one_smul, Qx8.unitB_mulVec]
  · rw [if_neg h, if_neg (Ne.symm h), zero_smul, smul_zero, Matrix.zero_mulVec]

theorem list_prod_apply {W : Type*} [AddCommGroup W] [Module ℂ W] (L : List (Module.End ℂ W)) (v : W) :
    (L.map fun T : Module.End ℂ W => fun y : W => T y).foldr (fun T h => T h) v = L.prod v := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    rw [ih]
    rfl

end LieListProducts

open LieListProducts in
theorem qr_frameGl_of : Qr.EcLie → Qr.FrameGl := by
  intro hE W _ _ _ k r m z π Bs hπ hB
  have hgl : ∀ a b, InGlW k r z (unitB (Hpk k r) Bs a b) := fun a b => frame_lie hB a b
  have h0 : InGlW k r z 0 ∧ ecOp π (0 : Mx k r) = 0 := by
    have h := (hE W k r z π hπ 0 0 ?_ ?_).2.1 0
    · simpa using h
    all_goals
      unfold InGlW
      rw [hpart1_lie (z := z) lie_zero, hpart2_lie (z := z) lie_zero]
      exact ⟨lie_zero, lie_zero⟩
  have hsub : ∀ Z Z', InGlW k r z Z → InGlW k r z Z' → ecOp π (Z - Z') = ecOp π Z - ecOp π Z' := by
    intro Z Z' hZ hZ'
    have h1 := (hE W k r z π hπ Z' Z' hZ' hZ').2.1 (-1)
    have h2 := (hE W k r z π hπ Z ((-1 : ℂ) • Z') hZ h1.1).1.2
    rw [h1.2] at h2
    simpa [sub_eq_add_neg] using h2
  have hite : ∀ (p : Prop) [Decidable p] (Z : Mx k r), InGlW k r z Z →
      InGlW k r z (if p then Z else 0) ∧ ecOp π (if p then Z else 0) = if p then ecOp π Z else 0 := by
    intro p _ Z hZ
    by_cases h : p
    · simpa [h] using hZ
    · simpa [h] using h0
  refine ⟨fun a b c d => ?_, fun w v => ?_⟩
  · have h := (hE W k r z π hπ _ _ (hgl a b) (hgl c d)).2.2.2
    rw [unitB_mul _ _ hB.2.1, unitB_mul _ _ hB.2.1, hsub _ _ (hite _ _ (hgl a d)).1 (hite _ _ (hgl c b)).1,
      (hite _ _ (hgl a d)).2, (hite _ _ (hgl c b)).2] at h
    unfold EB
    ext x
    have hx := congrArg (fun T : W →L[ℂ] W => T x) h
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] at hx ⊢ <;> exact hx.symm
  · unfold capRep qmF qdet qminor
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Module.End.mul_apply, ← list_prod_apply, List.map_ofFn]
    have e : ((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) = (((Equiv.Perm.sign σ : ℤ) : ℂ)) • (1 : Module.End ℂ W) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [e, LinearMap.smul_apply, Module.End.one_apply]
    congr 3
    funext j y
    simp only [Function.comp, Tm, id, LinearMap.add_apply]
    rw [ecRep_eq hπ.1 hπ.2 (hgl _ _).1 (hgl _ _).2]
    congr 1
    by_cases h : σ j = j
    · simp [h, Algebra.algebraMap_eq_smul_one]
    · simp [h]

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.FrameExtension

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frame_weaken {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) : IsFrameOf k r [z] Bs := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a v hv => h3 a v (by rw [List.mem_singleton] at hv; subst hv; simp)⟩

private theorem hpk_apply_comm (k r : ℕ) (t u : Fin (2 * r + k + 1)) : Hpk k r u t = Hpk k r t u := by
  have := t.isLt
  have := u.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

private theorem star_hpk_apply (k r : ℕ) (t u : Fin (2 * r + k + 1)) : star (Hpk k r t u) = Hpk k r t u := by
  simp only [Hpk]
  split_ifs <;> simp

private theorem herm_hpk_eq_star_herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, star_hpk_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hpk_apply_comm]
  ring

theorem frame_snoc {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    IsFrameOf k r [z] (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · induction a using Fin.lastCases with
    | last => simpa using he
    | cast i => simpa using h1 i
  · induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa using hee
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last j).ne', herm_hpk_eq_star_herm_swap, h3 j e (by simp), star_zero]
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne, h3 i e (by simp)]
      | cast j =>
        simp only [Fin.snoc_castSucc]
        rw [h2 i j]
        simp [Fin.castSucc_inj]
  · rw [List.mem_singleton] at hv
    subst hv
    induction a using Fin.lastCases with
    | last => simpa using hez
    | cast i => simpa using h3 i v (by simp)

theorem subA_EB {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r m : ℕ} (π : Mx k r → (W →L[ℂ] W))
    (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (e : Fin (2 * r + k + 1) → ℂ) :
    subA (EB π (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e)) = EB π Bs := by
  funext a b
  simp [subA, EB, unitB, Fin.snoc_castSucc]

theorem prod_Icc_fin (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 (n + 1), f i = ∏ j : Fin (n + 1), f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n + 1)]
    simp

end Formalism.FourierDecayAlt.P.FrameExtension

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qr_branchingK_of : Qr.BranchingAlg → Qr.FrameGl → Qr.LieStab → Qr.StabLie → Qr.FrameChange →
    Qr.FrameExists2 → Qr.BranchingK := by
  intro hBA hFG hLS hSL hFC hFE Wp _ _ _ n r z e π u β L hz hT hty hL hu he hez hee
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨Bs₀, hB₀⟩ := hFE n r z e hz hT he hez hee
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := hFG Wp (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (hLS Wp (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := hBA Wp n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  refine ⟨fun M => CapSp (EB π Bs₀) (shf β M.1), hint, fun M => ⟨(hS M).1, fun S' hle hst => ?_⟩, ?_⟩
  · exact (hS M).2 S' hle (hSL Wp (n + 1) r n z e π Bs₀ hR hB₀ S' hst)
  · intro Bs hBs M w v hv
    rw [(hFG Wp (n + 1) r n z π Bs hR (FrameExtension.frame_weaken hBs)).2 w v,
      hFC Wp n r z e π Bs Bs₀ hz hT he hez hee hR hBs hB₀ w]
    exact Qr.mem_CapSp.1 hv w

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem isInternal_comp {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup W] [Module ℂ W]
    (Φ : ι → κ) (hΦ : Function.Bijective Φ) (S : κ → Submodule ℂ W) (h : DirectSum.IsInternal S) :
    DirectSum.IsInternal (fun i => S (Φ i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  exact ⟨h.1.comp hΦ.1, by rw [hΦ.2.iSup_comp S]; exact h.2⟩

theorem prod_Icc_one (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n)]
    simp

abbrev par (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) : M.Par := ⟨n + 1, r, T, T', u, u⟩

theorem rho_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (ρ : M.Ty (par n r T T' u)) (j : Fin n) :
    M.rho (par n r T T' u) ρ ((j : ℕ) + 1) = u ((j : ℕ) + 2) + 1 / 2 + (((ρ j : Fin _) : ℕ) : ℝ) := by
  have hj := j.isLt
  simp only [M.rho, M.Par.lo, par, max_self]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem wid_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (L : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc) (j : Fin n) :
    (((par n r T T' u).wid ((j : ℕ) + 1) : ℕ) : ℤ) = L j.castSucc - L j.succ - 1 := by
  have h1 := hL j.castSucc
  have h2 := hL j.succ
  simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
  have hd : (par n r T T' u).hi ((j : ℕ) + 1) - (par n r T T' u).lo ((j : ℕ) + 1) =
      ((L j.castSucc - L j.succ - 1 : ℤ) : ℝ) := by
    simp only [M.Par.hi, M.Par.lo, par, min_self, max_self]
    push_cast
    linarith
  have hnn : 0 ≤ L j.castSucc - L j.succ - 1 := by linarith [hg j]
  simp only [M.Par.wid]
  rw [hd, ← Int.floor_toNat, Int.floor_intCast, Int.toNat_of_nonneg hnn]

theorem main (hK : BranchingK) (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (hOK : (par n r T T' u).OK)
    (z e : Fin (2 * r + (n + 1) + 1) → ℂ) (π : Mx (n + 1) r → (Wp →L[ℂ] Wp)) (hz : inWb (n + 1) r z)
    (hT : 0 < Tz (n + 1) r z) (hπ : IsType (n + 1) r z π u) (he : inWb (n + 1) r e)
    (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1) :
    ∃ S : M.Ty (par n r T T' u) → Submodule ℂ Wp, DirectSum.IsInternal S ∧
      (∀ ρ, S ρ ≠ ⊥ ∧ ∀ S' : Submodule ℂ Wp, S' ≤ S ρ →
        (∀ h ∈ UWset (n + 1) r z, h *ᵥ e = e → ∀ v ∈ S', π h v ∈ S') → S' = ⊥ ∨ S' = S ρ) ∧
      ∀ Bs : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [z, e] Bs →
        ∀ (ρ : M.Ty (par n r T T' u)) (w : ℂ), ∀ v ∈ S ρ,
        capRep (n + 1) r π Bs w v = M.xC (par n r T T' u) ρ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2) • v := by
  have hint : ∀ j : Fin (n + 1), ∃ N : ℤ, u ((j : ℕ) + 1) - u 1 = (N : ℝ) := fun j =>
    hOK.int_u ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1
        omega)
  choose L hL using hint
  have hgap : ∀ j : Fin n, u ((j : ℕ) + 2) + 1 ≤ u ((j : ℕ) + 1) := fun j => by
    have h := hOK.gap ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1 - 1
        omega)
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at h
    linarith
  have hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc := fun j => by
    have h1 := hL j.castSucc
    have h2 := hL j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have : (L j.succ : ℝ) + 1 ≤ (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by have := hg j; omega
  have hw := wid_eq n r T T' u L hL hg
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL j)
    rw [hβ, ← h]
    ring
  obtain ⟨S₀, hint₀, hirr, heig⟩ := hK Wp n r z e π u β L hz hT hπ hanti hrel he hez hee
  let Φ : M.Ty (par n r T T' u) → {M : Fin n → ℤ // Box L M} := fun ρ =>
    ⟨fun j => L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ), fun j => by
      have h1 := (ρ j).2
      have h2 := hw j
      constructor
      · show L j.succ < L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ)
        omega
      · show L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ) ≤ L j.castSucc
        omega⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro ρ ρ' h
      funext j
      have h1 := congrFun (congrArg Subtype.val h) j
      simp only [Φ] at h1
      apply Fin.ext
      omega
    · intro M
      refine ⟨fun j => ⟨(M.1 j - L j.succ - 1).toNat, ?_⟩, ?_⟩
      · have h1 := M.2 j
        have h2 := hw j
        omega
      · apply Subtype.ext
        funext j
        have h1 := M.2 j
        simp only [Φ]
        omega
  refine ⟨fun ρ => S₀ (Φ ρ), isInternal_comp Φ hΦ S₀ hint₀, fun ρ => hirr (Φ ρ), ?_⟩
  intro Bs hBs ρ w v hv
  rw [heig Bs hBs (Φ ρ) w v hv]
  congr 1
  unfold M.xC cpol
  rw [show (par n r T T' u).k - 1 = n from rfl, prod_Icc_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rho_eq]
  have h : (u ((j : ℕ) + 2) : ℂ) - (u 1 : ℂ) = (L j.succ : ℂ) := by
    have := hL j.succ
    simp only [Fin.val_succ] at this
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  simp only [shf, Φ, hβ]
  push_cast
  rw [← h]
  ring

end Formalism.FourierDecayAlt.P.ProductIntervalFrames

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem qr_branching_of : Qr.BranchingK → Formalism.FourierDecayAlt.Q.Branching := by
  intro hK Wp _ _ _ P hOK hu'
  obtain ⟨k, r, T, T', u, u'⟩ := P
  dsimp only at hu'
  subst hu'
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hOK.k_pos; dsimp only at this; omega⟩
  intro z e π hz hT hπ he hez hee
  exact ProductIntervalFrames.main hK Wp n r T T' _ hOK z e π hz hT hπ he hez hee

end Formalism.FourierDecayAlt.P
end
end

section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem radialDecompositionSpectral_of_branching : Branching → RadialDecompositionSpectral := fun hB =>
  q_radial_decomposition_of_pieces second_contraction_adapted contractions_covariant capelli_two_by_two
    right_type_action hB qnTPres

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem differential_operator_linear : Qr.DOpLin := qr_dOpLin_of trotter_product_formula trotter_product_matrices representation_exp

theorem differential_operator_bracket : Qr.DOpBracket := qr_dOpBracket_of representation_exp differential_operator_linear differential_operator_adjoint

theorem elementary_lie_elements : Qr.EcLie := qr_ecLie_of differential_operator_linear differential_operator_bracket

theorem frame_general_linear : Qr.FrameGl := qr_frameGl_of elementary_lie_elements

theorem lie_stabilizer : Qr.LieStab := qr_lieStab_of exp_generates representation_exp elementary_lie_elements

theorem qr_frameChange_proof : Qr.FrameChange := qr_frameChange_of elementary_lie_elements frame_general_linear

theorem branching_compact : Qr.BranchingK :=
  qr_branchingK_of branching_algebraic frame_general_linear lie_stabilizer stabilizer_lie_algebra qr_frameChange_proof
    exists_frame_two

theorem branching_proof : Branching := qr_branching_of branching_compact

theorem spectral_two_by_two : RadialDecompositionSpectral := radialDecompositionSpectral_of_branching branching_proof

end Formalism.FourierDecayAlt.P
end
