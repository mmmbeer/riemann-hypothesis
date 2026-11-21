import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDefs

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

section ps

variable {TT : ℝ}

lemma gg_eval (ζ : ℂ) : gg TT ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ]
    (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.mul_conj]
  push_cast
  ring

lemma ps_const (c : ℂ) : PS TT (fun _ => c) := ⟨0, MvPolynomial.C c, fun ζ _ => by simp⟩

lemma ps_id : PS TT (fun ζ => ζ) := ⟨0, MvPolynomial.X 0, fun ζ _ => by simp⟩

lemma ps_conj : PS TT (fun ζ => conj ζ) := ⟨0, MvPolynomial.X 1, fun ζ _ => by simp⟩

lemma ps_sig : PS TT (fun ζ => sig TT ζ) := ⟨0, MvPolynomial.X 2, fun ζ _ => by simp⟩

lemma ps_add {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ n * p + (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)) ^ m * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_pow, ← gg_eval, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma ps_mul {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨n, q, hq⟩ := hg
  refine ⟨m + n, p * q, fun ζ hζ => ?_⟩
  rw [MvPolynomial.eval_mul, ← hp ζ hζ, ← hq ζ hζ]
  ring

lemma sig_sq {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ * sig TT ζ = gg TT ζ := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.gg Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]

lemma sig_ne {ζ : ℂ} (hζ : TT < Complex.normSq ζ) : sig TT ζ ≠ 0 := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.sig
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by linarith))

lemma ps_sigInv : PS TT (fun ζ => (sig TT ζ)⁻¹) := by
  refine ⟨1, MvPolynomial.X 2, fun ζ hζ => ?_⟩
  rw [pow_one, ← sig_sq hζ, mul_assoc, mul_inv_cancel₀ (sig_ne hζ), mul_one]
  simp

end ps

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

set_option linter.unusedSimpArgs false

variable {k : ℕ}

def Su (k : ℕ) (i j : Fin (k + 1)) : Mb k := Matrix.single i j 1

lemma Su_mul (i j j' m : Fin (k + 1)) : Su k i j * Su k j' m = if j = j' then Su k i m else 0 := by
  unfold Su
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]

def nuG (k : ℕ) (v s w : ℂ) : Mb k :=
  1 + (v - 1) • Su k 0 0 + s • (Su k 0 (Fin.last k) + Su k (Fin.last k) 0) + (w - 1) • Su k (Fin.last k) (Fin.last k)

lemma nu_eq (w s : ℂ) : nu k w s = nuG k (star w) s w := by
  unfold nu nuG Su
  simp only [Matrix.single_eq_single_vecMulVec_single, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
  module

lemma dnu_eq (a b c : ℂ) : dnu k a b c =
    a • Su k 0 0 + b • (Su k 0 (Fin.last k) + Su k (Fin.last k) 0) + c • Su k (Fin.last k) (Fin.last k) := rfl

lemma nuG_mul (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (hw : w * v - s * s = 1) :
    nuG k v s w * nuG k w (-s) v = 1 := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  linear_combination (norm := module) hw • (Su k 0 0 + Su k (Fin.last k) (Fin.last k))

lemma conj_corner_matrix_unit (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) :
    nuG k w (-s) v * Su k 0 0 * nuG k v s w = (w * v) • Su k 0 0 + (w * s) • Su k 0 (Fin.last k) -
      (s * v) • Su k (Fin.last k) 0 - (s * s) • Su k (Fin.last k) (Fin.last k) := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  module

lemma conj0m (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (m : Fin (k + 1)) (hm0 : m ≠ 0) (hml : m ≠ Fin.last k) :
    nuG k w (-s) v * Su k 0 m * nuG k v s w = w • Su k 0 m - s • Su k (Fin.last k) m := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, hm0, hml,
    hm0.symm, hml.symm, if_true, if_false, smul_zero, add_zero, zero_add]
  module

lemma conjm0 (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (m : Fin (k + 1)) (hm0 : m ≠ 0) (hml : m ≠ Fin.last k) :
    nuG k w (-s) v * Su k m 0 * nuG k v s w = v • Su k m 0 + s • Su k m (Fin.last k) := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, hm0, hml,
    hm0.symm, hml.symm, if_true, if_false, smul_zero, add_zero, zero_add]
  module

lemma nuI_dnu (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w a b c : ℂ) :
    nuG k w (-s) v * dnu k a b c = (w * a - s * b) • Su k 0 0 + (w * b - s * c) • Su k 0 (Fin.last k) +
      (-s * a + v * b) • Su k (Fin.last k) 0 + (-s * b + v * c) • Su k (Fin.last k) (Fin.last k) := by
  simp only [nuG, dnu_eq, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  module

lemma unit0l (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c p : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hp : 2 * s * p = -c * v) :
    Su k 0 (Fin.last k) = (-(v / (2 * s))) • Su k 0 0 + nuG k w (-s) v * ((v / (2 * s)) • Su k 0 0) * nuG k v s w +
      (-(s / c)) • (nuG k w (-s) v * dnu k 0 p (-c)) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  have hp' : p = -c * v / (2 * s) := by field_simp; linear_combination hp
  subst hw' hp'
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_corner_matrix_unit h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

lemma unitl0 (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c q : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hq : 2 * s * q = -c * w) :
    Su k (Fin.last k) 0 = (w / (2 * s)) • Su k 0 0 + nuG k w (-s) v * ((-(w / (2 * s))) • Su k 0 0) * nuG k v s w +
      (-(s / c)) • (nuG k w (-s) v * dnu k (-c) q 0) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  subst hw'
  have hq' : q = -c * ((1 + s * s) / v) / (2 * s) := by field_simp; field_simp at hq; linear_combination hq
  subst hq'
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_corner_matrix_unit h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

lemma unitll (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c p q : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hp : 2 * s * p = -c * v) (hq : 2 * s * q = -c * w) :
    Su k (Fin.last k) (Fin.last k) = nuG k w (-s) v * Su k 0 0 * nuG k v s w +
      (-(w / c)) • (nuG k w (-s) v * dnu k 0 p (-c)) + (v / c) • (nuG k w (-s) v * dnu k (-c) q 0) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  subst hw'
  have hp' : p = -c * v / (2 * s) := by field_simp; linear_combination hp
  have hq' : q = -c * ((1 + s * s) / v) / (2 * s) := by field_simp; field_simp at hq; linear_combination hq
  subst hp' hq'
  rw [conj_corner_matrix_unit h0, nuI_dnu h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k r : ℕ}

lemma single_apply_mul (a b i j : Fin (k + 1)) :
    (Matrix.single a b (1 : ℂ)) i j = (Pi.single a 1 : Fin (k + 1) → ℂ) i * (Pi.single b 1 : Fin (k + 1) → ℂ) j := by
  rw [Matrix.single_apply, Pi.single_apply, Pi.single_apply]
  by_cases hi : i = a
  · by_cases hj : j = b
    · subst hi
      subst hj
      simp
    · simp [hj, Ne.symm hj]
  · simp [hi, Ne.symm hi]

lemma nu_lin (w s : ℂ) :
    nu k w s = (1 - Matrix.single 0 0 1 - Matrix.single (Fin.last k) (Fin.last k) 1) + star w • Matrix.single 0 0 1 +
      s • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
      w • Matrix.single (Fin.last k) (Fin.last k) 1 := by
  ext i j
  rw [nu_apply]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, single_apply_mul]
  ring

def aa (r : ℕ) (G G' X : Mb k) : Q.Mx k r := e0 k r (G * X * G')

lemma aa_add (G G' X Y : Mb k) : aa r G G' (X + Y) = aa r G G' X + aa r G G' Y := by
  simp only [aa, e0, Matrix.mul_add, Matrix.add_mul]

lemma aa_smul (G G' X : Mb k) (c : ℂ) : aa r G G' (c • X) = c • aa r G G' X := by
  simp only [aa, e0, Matrix.mul_smul, Matrix.smul_mul]

lemma mu0_eq_corner_entry_expansion (z z' : Fin (2 * r + k + 1) → ℂ) (w : ℂ) :
    mu0 k r z z' w =
      (aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
          (1 - Matrix.single 0 0 1 - Matrix.single (Fin.last k) (Fin.last k) 1) + (1 - Em k r * (Em k r)ᵀ)) +
        star (wZ (Tz k r z) (Tz k r z') w) •
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) (Matrix.single 0 0 1) +
        sZ (Tz k r z) (Tz k r z') w •
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
        wZ (Tz k r z) (Tz k r z') w •
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single (Fin.last k) (Fin.last k) 1) := by
  have h : mu0 k r z z' w = embWb k r (gA k (wbPart k r z) (Tz k r z) *
      nu k (wZ (Tz k r z) (Tz k r z') w) (sZ (Tz k r z) (Tz k r z') w) * gB k (wbPart k r z') (Tz k r z')) := rfl
  rw [h, emb_eq, nu_lin]
  have h2 : ∀ X : Mb k, Em k r * (gA k (wbPart k r z) (Tz k r z) * X * gB k (wbPart k r z') (Tz k r z')) * (Em k r)ᵀ =
      aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) X := fun X => rfl
  rw [h2, aa_add, aa_add, aa_add, aa_smul, aa_smul, aa_smul]
  abel

lemma dZ_lin (f1 f2 f3 : ℂ → ℂ) (a0 a1 a2 a3 ζ : ℂ) (h1 : DifferentiableAt ℝ f1 ζ) (h2 : DifferentiableAt ℝ f2 ζ)
    (h3 : DifferentiableAt ℝ f3 ζ) :
    NF.dZ (fun w => a0 + f1 w * a1 + f2 w * a2 + f3 w * a3) ζ =
        NF.dZ f1 ζ * a1 + NF.dZ f2 ζ * a2 + NF.dZ f3 ζ * a3 ∧
      NF.dZb (fun w => a0 + f1 w * a1 + f2 w * a2 + f3 w * a3) ζ =
        NF.dZb f1 ζ * a1 + NF.dZb f2 ζ * a2 + NF.dZb f3 ζ * a3 := by
  have h : HasFDerivAt (fun w => a0 + f1 w * a1 + f2 w * a2 + f3 w * a3)
      (0 + a1 • fderiv ℝ f1 ζ + a2 • fderiv ℝ f2 ζ + a3 • fderiv ℝ f3 ζ) ζ :=
    (((hasFDerivAt_const a0 ζ).add (h1.hasFDerivAt.mul_const a1)).add (h2.hasFDerivAt.mul_const a2)).add
      (h3.hasFDerivAt.mul_const a3)
  unfold NF.dZ NF.dZb
  rw [h.fderiv]
  simp only [add_apply, zero_apply, smul_apply, smul_eq_mul]
  constructor <;> ring

lemma wZ_has (T T' : ℝ) (ζ : ℂ) :
    HasFDerivAt (wZ T T') ((-(kap T T')⁻¹) • (ContinuousLinearMap.id ℝ ℂ)) ζ :=
  (hasFDerivAt_id ζ).const_mul (-(kap T T')⁻¹)

lemma wZ_d (T T' : ℝ) (ζ : ℂ) : NF.dZ (wZ T T') ζ = -(kap T T')⁻¹ ∧ NF.dZb (wZ T T') ζ = 0 := by
  unfold NF.dZ NF.dZb
  rw [(wZ_has T T' ζ).fderiv]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  constructor
  · linear_combination ((1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I
  · linear_combination (-(1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I

lemma kap_star (T T' : ℝ) : star (kap T T') = kap T T' := Complex.conj_ofReal _

lemma wZs_has (T T' : ℝ) (ζ : ℂ) :
    HasFDerivAt (fun w => star (wZ T T' w))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((-(kap T T')⁻¹) • (ContinuousLinearMap.id ℝ ℂ))) ζ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp ζ (wZ_has T T' ζ)

lemma wZs_d (T T' : ℝ) (ζ : ℂ) :
    NF.dZ (fun w => star (wZ T T' w)) ζ = 0 ∧ NF.dZb (fun w => star (wZ T T' w)) ζ = -(kap T T')⁻¹ := by
  unfold NF.dZ NF.dZb
  rw [(wZs_has T T' ζ).fderiv]
  have hk : conj (kap T T') = kap T T' := kap_star T T'
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, map_neg, map_inv₀, hk, map_one, Complex.conj_I]
  constructor
  · linear_combination (-(1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I
  · linear_combination ((1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I

lemma normSq_has (ζ : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.normSq w)
      ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) + (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM)) ζ := by
  have h := (Complex.reCLM.hasFDerivAt (x := ζ)).mul (Complex.reCLM.hasFDerivAt (x := ζ))
  have h' := (Complex.imCLM.hasFDerivAt (x := ζ)).mul (Complex.imCLM.hasFDerivAt (x := ζ))
  have h2 := h.add h'
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp [Complex.normSq_apply]

lemma sr_facts (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    0 < Complex.normSq ζ / (T * T') - 1 ∧
      Real.sqrt (Complex.normSq ζ / (T * T') - 1) * (Real.sqrt T * Real.sqrt T') = Real.sqrt (Complex.normSq ζ - T * T') ∧
      0 < Real.sqrt (Complex.normSq ζ - T * T') ∧ 0 < Real.sqrt T * Real.sqrt T' ∧
      (Real.sqrt T * Real.sqrt T') * (Real.sqrt T * Real.sqrt T') = T * T' := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hne : T * T' ≠ 0 := hTT.ne'
  have hs : Real.sqrt T * Real.sqrt T' = Real.sqrt (T * T') := (Real.sqrt_mul hT.le T').symm
  have h1 : 0 < Complex.normSq ζ / (T * T') - 1 := sub_pos.mpr ((one_lt_div hTT).mpr hζ)
  refine ⟨h1, ?_, Real.sqrt_pos.mpr (sub_pos.mpr hζ),
    mul_pos (Real.sqrt_pos.mpr hT) (Real.sqrt_pos.mpr hT'), ?_⟩
  · rw [hs, ← Real.sqrt_mul h1.le]
    congr 1
    rw [sub_mul, div_mul_cancel₀ _ hne, one_mul]
  · rw [hs, Real.mul_self_sqrt hTT.le]

lemma sZ_has (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    HasFDerivAt (sZ T T')
      ((Complex.ofRealCLM).comp ((1 / (2 * Real.sqrt (Complex.normSq ζ / (T * T') - 1))) •
        ((T * T')⁻¹ • ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) + (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM))))) ζ := by
  have h0 := (sr_facts T T' hT hT' ζ hζ).1
  have h1 : HasFDerivAt (fun w : ℂ => Complex.normSq w / (T * T') - 1)
      ((T * T')⁻¹ • ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) + (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM))) ζ := by
    have := ((normSq_has ζ).const_mul (T * T')⁻¹).sub_const 1
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    show Complex.normSq w / (T * T') - 1 = (T * T')⁻¹ * Complex.normSq w - 1
    rw [div_eq_inv_mul]
  exact (Complex.ofRealCLM.hasFDerivAt).comp ζ (h1.sqrt h0.ne')

lemma sZ_d (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    NF.dZ (sZ T T') ζ = (2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹ ∧
      NF.dZb (sZ T T') ζ = (2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := sr_facts T T' hT hT' ζ hζ
  unfold NF.dZ NF.dZb
  rw [(sZ_has T T' hT hT' ζ hζ).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, add_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.ofRealCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add]
  unfold kap sig
  rw [← h1]
  set sr := Real.sqrt (Complex.normSq ζ / (T * T') - 1) with hsr
  set κ := Real.sqrt T * Real.sqrt T' with hκ
  have hs0 : (sr : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 h0).ne'
  have hk0 : (κ : ℂ) ≠ 0 := by exact_mod_cast h3.ne'
  have hc : conj ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  rw [← h4, hc]
  constructor
  · push_cast
    field_simp
    ring
  · conv_rhs => rw [hz]
    push_cast
    field_simp
    ring

theorem dmu_both (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (ζ : ℂ)
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    (Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k 0 ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * conj ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            (-(kap (Tz k r z) (Tz k r z'))⁻¹) * gB k (wbPart k r z') (Tz k r z')) ∧
      (Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k (-(kap (Tz k r z) (Tz k r z'))⁻¹) ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            0 * gB k (wbPart k r z') (Tz k r z')) := by
  have hR : ∀ a b c : ℂ, e0 k r (gA k (wbPart k r z) (Tz k r z) * dnu k a b c * gB k (wbPart k r z') (Tz k r z')) =
      a • aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) (Matrix.single 0 0 1) +
        b • aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
        c • aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single (Fin.last k) (Fin.last k) 1) := by
    intro a b c
    show aa r _ _ (dnu k a b c) = _
    unfold dnu
    rw [aa_add, aa_add, aa_smul, aa_smul, aa_smul]
  have hL : ∀ i j, (fun w => mu0 k r z z' w i j) = fun w =>
      (aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
          (1 - Matrix.single 0 0 1 - Matrix.single (Fin.last k) (Fin.last k) 1) + (1 - Em k r * (Em k r)ᵀ) : Q.Mx k r) i j +
        star (wZ (Tz k r z) (Tz k r z') w) *
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) (Matrix.single 0 0 1) i j +
        sZ (Tz k r z) (Tz k r z') w *
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) i j +
        wZ (Tz k r z) (Tz k r z') w *
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single (Fin.last k) (Fin.last k) 1) i j := by
    intro i j
    funext w
    rw [mu0_eq_corner_entry_expansion]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hd := fun a0 a1 a2 a3 => dZ_lin (fun w => star (wZ (Tz k r z) (Tz k r z') w)) (sZ (Tz k r z) (Tz k r z'))
    (wZ (Tz k r z) (Tz k r z')) a0 a1 a2 a3 ζ (wZs_has _ _ ζ).differentiableAt
    (sZ_has _ _ hT hT' ζ hζ).differentiableAt (wZ_has _ _ ζ).differentiableAt
  constructor
  · ext i j
    rw [Matrix.of_apply, hL, (hd _ _ _ _).1, hR, (wZs_d _ _ ζ).1, (sZ_d _ _ hT hT' ζ hζ).1, (wZ_d _ _ ζ).1]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · ext i j
    rw [Matrix.of_apply, hL, (hd _ _ _ _).2, hR, (wZs_d _ _ ζ).2, (sZ_d _ _ hT hT' ζ hζ).2, (wZ_d _ _ ζ).2]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem dmu_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (ζ : ℂ)
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    (Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k 0 ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * conj ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            (-(kap (Tz k r z) (Tz k r z'))⁻¹) * gB k (wbPart k r z') (Tz k r z')) :=
  (dmu_both k r z z' hT hT' ζ hζ).1

theorem dmub_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (ζ : ℂ)
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    (Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k (-(kap (Tz k r z) (Tz k r z'))⁻¹) ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            0 * gB k (wbPart k r z') (Tz k r z')) :=
  (dmu_both k r z z' hT hT' ζ hζ).2

theorem sZ_eq (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    sZ T T' ζ = (kap T T')⁻¹ * sig (T * T') ζ := by
  obtain ⟨_, h1, _, h3, _⟩ := sr_facts T T' hT hT' ζ hζ
  unfold sZ kap sig
  rw [← h1]
  have key : ∀ sr κ : ℝ, 0 < κ → ((sr : ℝ) : ℂ) = ((κ : ℝ) : ℂ)⁻¹ * ((sr * κ : ℝ) : ℂ) := by
    intro sr κ h
    have h0 : (κ : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast
    field_simp
  exact key _ _ h3

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k : ℕ}

section ann

variable {T T' : ℝ}

lemma kap_ne (hT : 0 < T) (hT' : 0 < T') : kap T T' ≠ 0 := by
  unfold kap
  exact_mod_cast (mul_pos (Real.sqrt_pos.2 hT) (Real.sqrt_pos.2 hT')).ne'

lemma kap_sq (hT : 0 < T) (hT' : 0 < T') : kap T T' * kap T T' = ((T * T' : ℝ) : ℂ) := by
  unfold kap
  rw [← Complex.ofReal_mul, mul_mul_mul_comm, Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]

lemma wZ_eq (ζ : ℂ) : wZ T T' ζ = -(kap T T')⁻¹ * ζ := rfl

lemma wZ_star (ζ : ℂ) : star (wZ T T' ζ) = -(kap T T')⁻¹ * conj ζ := by
  rw [wZ_eq, star_mul', star_neg, star_inv₀, kap_star]
  rfl

lemma zeta_ne (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) : ζ ≠ 0 := by
  intro h
  rw [h, map_zero] at hζ
  exact absurd hζ (not_lt.2 (mul_pos hT hT').le)

lemma ws_rel (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    wZ T T' ζ * star (wZ T T' ζ) - sZ T T' ζ * sZ T T' ζ = 1 := by
  have hk := kap_ne hT hT'
  have h1 := sig_sq hζ
  have h2 := kap_sq hT hT'
  have h3 : gg (T * T') ζ = ζ * conj ζ - ((T * T' : ℝ) : ℂ) := by
    rw [Complex.mul_conj]; unfold gg; push_cast; ring
  rw [wZ_star, wZ_eq, sZ_eq T T' hT hT' ζ hζ]
  have h4 : ζ * conj ζ - sig (T * T') ζ * sig (T * T') ζ = kap T T' * kap T T' := by rw [h1, h3, h2]; ring
  field_simp
  linear_combination h4

lemma nuI_eq (ζ : ℂ) : nuI k T T' ζ = nuG k (wZ T T' ζ) (-sZ T T' ζ) (star (wZ T T' ζ)) := by
  unfold nuI
  rw [nu_eq, star_star]

lemma nuI_mul (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ}
    (hζ : T * T' < Complex.normSq ζ) : nuI k T T' ζ * nu k (wZ T T' ζ) (sZ T T' ζ) = 1 := by
  rw [nuI_eq, nu_eq]
  have h := nuG_mul h0 (wZ T T' ζ) (-sZ T T' ζ) (star (wZ T T' ζ)) (by linear_combination ws_rel hT hT' hζ)
  rwa [neg_neg] at h

end ann

def PSL (k : ℕ) (TT : ℝ) (C : ℂ → Mb k) : Prop := (∀ i j, PS TT (fun ζ => C ζ i j)) ∧ ∀ ζ, InL k (C ζ)

lemma psl_smul {TT : ℝ} {f : ℂ → ℂ} (hf : PS TT f) {A : Mb k} (hA : InL k A) : PSL k TT (fun ζ => f ζ • A) := by
  refine ⟨fun i j => ?_, fun ζ i => ⟨?_, ?_⟩⟩
  · exact ps_mul hf (ps_const (A i j))
  · show f ζ * A i (Fin.last k) = 0
    rw [(hA i).1, mul_zero]
  · show f ζ * A (Fin.last k) i = 0
    rw [(hA i).2, mul_zero]

lemma psl_add {TT : ℝ} {C D : ℂ → Mb k} (hC : PSL k TT C) (hD : PSL k TT D) : PSL k TT (fun ζ => C ζ + D ζ) := by
  refine ⟨fun i j => ps_add (hC.1 i j) (hD.1 i j), fun ζ i => ⟨?_, ?_⟩⟩
  · show C ζ i (Fin.last k) + D ζ i (Fin.last k) = 0
    rw [(hC.2 ζ i).1, (hD.2 ζ i).1, add_zero]
  · show C ζ (Fin.last k) i + D ζ (Fin.last k) i = 0
    rw [(hC.2 ζ i).2, (hD.2 ζ i).2, add_zero]

lemma psl_csmul {TT : ℝ} (c : ℂ) {C : ℂ → Mb k} (hC : PSL k TT C) : PSL k TT (fun ζ => c • C ζ) := by
  refine ⟨fun i j => ps_mul (ps_const c) (hC.1 i j), fun ζ i => ⟨?_, ?_⟩⟩
  · show c * C ζ i (Fin.last k) = 0
    rw [(hC.2 ζ i).1, mul_zero]
  · show c * C ζ (Fin.last k) i = 0
    rw [(hC.2 ζ i).2, mul_zero]

def Dec (k : ℕ) (T T' : ℝ) (M : Mb k) : Prop :=
  ∃ (C₁ C₂ : ℂ → Mb k) (β₁ β₂ : ℂ → ℂ), PSL k (T * T') C₁ ∧ PSL k (T * T') C₂ ∧ PS (T * T') β₁ ∧ PS (T * T') β₂ ∧
    ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
      M = C₁ ζ + nuI k T T' ζ * C₂ ζ * nu k (wZ T T' ζ) (sZ T T' ζ) + β₁ ζ • H1 k T T' ζ + β₂ ζ • H2 k T T' ζ

variable {T T' : ℝ}

lemma dec_mk (M : Mb k) (f₁ f₂ β₁ β₂ : ℂ → ℂ) (A₁ A₂ : Mb k) (hA₁ : InL k A₁) (hA₂ : InL k A₂) (h1 : PS (T * T') f₁)
    (h2 : PS (T * T') f₂) (h3 : PS (T * T') β₁) (h4 : PS (T * T') β₂)
    (h : ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
      M = f₁ ζ • A₁ + nuI k T T' ζ * (f₂ ζ • A₂) * nu k (wZ T T' ζ) (sZ T T' ζ) + β₁ ζ • H1 k T T' ζ +
        β₂ ζ • H2 k T T' ζ) : Dec k T T' M :=
  ⟨_, _, β₁, β₂, psl_smul h1 hA₁, psl_smul h2 hA₂, h3, h4, h⟩

lemma dec_add {M N : Mb k} (hM : Dec k T T' M) (hN : Dec k T T' N) : Dec k T T' (M + N) := by
  obtain ⟨C₁, C₂, β₁, β₂, a1, a2, a3, a4, a5⟩ := hM
  obtain ⟨D₁, D₂, γ₁, γ₂, b1, b2, b3, b4, b5⟩ := hN
  refine ⟨_, _, _, _, psl_add a1 b1, psl_add a2 b2, ps_add a3 b3, ps_add a4 b4, fun ζ hζ => ?_⟩
  conv_lhs => rw [a5 ζ hζ, b5 ζ hζ]
  rw [Matrix.mul_add, Matrix.add_mul, add_smul, add_smul]
  abel

lemma dec_smul (c : ℂ) {M : Mb k} (hM : Dec k T T' M) : Dec k T T' (c • M) := by
  obtain ⟨C₁, C₂, β₁, β₂, a1, a2, a3, a4, a5⟩ := hM
  refine ⟨_, _, _, _, psl_csmul c a1, psl_csmul c a2, ps_mul (ps_const c) a3, ps_mul (ps_const c) a4, fun ζ hζ => ?_⟩
  conv_lhs => rw [a5 ζ hζ]
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_add, smul_add, smul_smul, smul_smul]

lemma inL_Su {a b : Fin (k + 1)} (ha : a ≠ Fin.last k) (hb : b ≠ Fin.last k) : InL k (Su k a b) := by
  intro i
  unfold Su
  constructor
  · rw [Matrix.single_apply, if_neg (fun h => hb h.2)]
  · rw [Matrix.single_apply, if_neg (fun h => ha h.1)]

lemma inL_zero : InL k (0 : Mb k) := fun _ => ⟨rfl, rfl⟩

lemma ps_zero {TT : ℝ} : PS TT (fun _ => (0 : ℂ)) := ps_const 0

lemma dec_LL {a b : Fin (k + 1)} (ha : a ≠ Fin.last k) (hb : b ≠ Fin.last k) : Dec k T T' (Su k a b) :=
  dec_mk _ (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (Su k a b) 0 (inL_Su ha hb) inL_zero (ps_const 1) ps_zero
    ps_zero ps_zero (fun ζ _ => by simp)

lemma dec_lm (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') (m : Fin (k + 1)) (hm0 : m ≠ 0)
    (hml : m ≠ Fin.last k) : Dec k T T' (Su k (Fin.last k) m) := by
  refine dec_mk _ (fun ζ => (-1 : ℂ) * (ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (-kap T T') * (sig (T * T') ζ)⁻¹) (fun _ => 0)
    (fun _ => 0) (Su k 0 m) (Su k 0 m) (inL_Su h0 hml) (inL_Su h0 hml) (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv))
    (ps_mul (ps_const _) ps_sigInv) ps_zero ps_zero (fun ζ hζ => ?_)
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  rw [Matrix.mul_smul, Matrix.smul_mul, nuI_eq, nu_eq, conj0m h0 _ _ _ m hm0 hml, sZ_eq T T' hT hT' ζ hζ, wZ_eq]
  match_scalars <;> field_simp <;> ring

lemma dec_ml (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') (m : Fin (k + 1)) (hm0 : m ≠ 0)
    (hml : m ≠ Fin.last k) : Dec k T T' (Su k m (Fin.last k)) := by
  refine dec_mk _ (fun ζ => conj ζ * (sig (T * T') ζ)⁻¹) (fun ζ => kap T T' * (sig (T * T') ζ)⁻¹) (fun _ => 0)
    (fun _ => 0) (Su k m 0) (Su k m 0) (inL_Su hml h0) (inL_Su hml h0) (ps_mul ps_conj ps_sigInv)
    (ps_mul (ps_const _) ps_sigInv) ps_zero ps_zero (fun ζ hζ => ?_)
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  rw [Matrix.mul_smul, Matrix.smul_mul, nuI_eq, nu_eq, conjm0 h0 _ _ _ m hm0 hml, sZ_eq T T' hT hT' ζ hζ, wZ_star]
  match_scalars <;> field_simp <;> ring

section plane

variable (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T')
include h0 hT hT'

lemma plane_facts {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    sZ T T' ζ ≠ 0 ∧ (kap T T')⁻¹ ≠ 0 ∧ star (wZ T T' ζ) ≠ 0 ∧
      2 * sZ T T' ζ * ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) = -(kap T T')⁻¹ * star (wZ T T' ζ) ∧
      2 * sZ T T' ζ * ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) = -(kap T T')⁻¹ * wZ T T' ζ := by
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have hz := zeta_ne hT hT' hζ
  have hzc : conj ζ ≠ 0 := by simpa using hz
  refine ⟨?_, inv_ne_zero hk, ?_, ?_, ?_⟩
  · rw [sZ_eq T T' hT hT' ζ hζ]; exact mul_ne_zero (inv_ne_zero hk) hs
  · rw [wZ_star]; exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hk)) hzc
  · rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  · rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp

lemma dec_0l : Dec k T T' (Su k 0 (Fin.last k)) := by
  refine dec_mk _ (fun ζ => (2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (-2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹))
    (fun ζ => (-1 : ℂ) * sig (T * T') ζ) (fun _ => 0) (Su k 0 0) (Su k 0 0) (inL_Su h0 h0) (inL_Su h0 h0)
    (ps_mul (ps_const _) (ps_mul ps_conj ps_sigInv)) (ps_mul (ps_const _) (ps_mul ps_conj ps_sigInv))
    (ps_mul (ps_const _) ps_sig) ps_zero (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have key := unit0l h0 _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f4
  have e1 : -(star (wZ T T' ζ) / (2 * sZ T T' ζ)) = (2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  have e2 : star (wZ T T' ζ) / (2 * sZ T T' ζ) = (-2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  have e3 : -(sZ T T' ζ / (kap T T')⁻¹) = (-1 : ℂ) * sig (T * T') ζ := by
    rw [sZ_eq T T' hT hT' ζ hζ]; field_simp
  rw [e1, e2, e3, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, add_zero]
  exact key

lemma decomposition_lower_corner_unit : Dec k T T' (Su k (Fin.last k) 0) := by
  refine dec_mk _ (fun ζ => (-2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹))
    (fun _ => 0) (fun ζ => (-1 : ℂ) * sig (T * T') ζ) (Su k 0 0) (Su k 0 0) (inL_Su h0 h0) (inL_Su h0 h0)
    (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv)) (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv))
    ps_zero (ps_mul (ps_const _) ps_sig) (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have key := unitl0 h0 _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f5
  have e1 : wZ T T' ζ / (2 * sZ T T' ζ) = (-2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp
  have e2 : -(wZ T T' ζ / (2 * sZ T T' ζ)) = (2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp
  have e3 : -(sZ T T' ζ / (kap T T')⁻¹) = (-1 : ℂ) * sig (T * T') ζ := by
    rw [sZ_eq T T' hT hT' ζ hζ]; field_simp
  rw [e2, e1, e3, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, add_zero]
  exact key

lemma dec_ll : Dec k T T' (Su k (Fin.last k) (Fin.last k)) := by
  refine dec_mk _ (fun _ => 0) (fun _ => 1) (fun ζ => ζ) (fun ζ => (-1 : ℂ) * conj ζ) (Su k 0 0) (Su k 0 0)
    (inL_Su h0 h0) (inL_Su h0 h0) ps_zero (ps_const 1) ps_id (ps_mul (ps_const _) ps_conj) (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have key := unitll h0 _ _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f4 f5
  have e1 : -(wZ T T' ζ / (kap T T')⁻¹) = ζ := by rw [wZ_eq]; field_simp
  have e2 : star (wZ T T' ζ) / (kap T T')⁻¹ = (-1 : ℂ) * conj ζ := by rw [wZ_star]; field_simp
  rw [e1, e2, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, zero_add, one_smul]
  exact key

lemma dec_unit (a b : Fin (k + 1)) : Dec k T T' (Su k a b) := by
  by_cases ha : a = Fin.last k
  · subst ha
    by_cases hb : b = Fin.last k
    · subst hb; exact dec_ll h0 hT hT'
    · by_cases hb0 : b = 0
      · subst hb0; exact decomposition_lower_corner_unit h0 hT hT'
      · exact dec_lm h0 hT hT' b hb0 hb
  · by_cases hb : b = Fin.last k
    · subst hb
      by_cases ha0 : a = 0
      · subst ha0; exact dec_0l h0 hT hT'
      · exact dec_ml h0 hT hT' a ha0 ha
    · exact dec_LL ha hb

lemma dec_all (M : Mb k) : Dec k T T' M := by
  have hz : Dec k T T' (0 : Mb k) := by
    have := dec_smul (T := T) (T' := T') 0 (dec_LL (k := k) h0 h0)
    rwa [zero_smul] at this
  rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_induction _ _ (fun _ _ => dec_add) hz fun i _ => ?_
  refine Finset.sum_induction _ _ (fun _ _ => dec_add) hz fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Su k i j := by
    unfold Su; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact dec_smul _ (dec_unit h0 hT hT' i j)

end plane

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k r : ℕ}

lemma Hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)

lemma Hb_sq (k : ℕ) : Hb k * Hb k = 1 := by
  unfold Formalism.QuantumDeterminants.Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

private lemma Em_conjTranspose_eq_transpose : (Em k r)ᴴ = (Em k r)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]
  split_ifs <;> simp

private lemma Em_transpose_conjTranspose_eq_Em : ((Em k r)ᵀ)ᴴ = Em k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]
  split_ifs <;> simp

lemma embed_conj_transpose (X : Mb k) : (e0 k r X)ᴴ = e0 k r Xᴴ := by
  unfold Dc.e0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjTranspose_eq_transpose, Em_transpose_conjTranspose_eq_Em]
  simp only [Matrix.mul_assoc]

private lemma Hpk_apply_wI_right_eq_ite (i : Fin (2 * r + k + 1)) (m : Fin (k + 1)) :
    Hpk k r i (wI k r m) = if i = wI k r m then Hb k m m else 0 := by
  have hm := m.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply_eq, wI, Fin.ext_iff, Fin.val_mk, Fin.val_last]
  split_ifs <;> first | rfl | omega | (exfalso; omega)

private lemma Hpk_wI_apply_left_eq_ite (j : Fin (2 * r + k + 1)) (m : Fin (k + 1)) :
    Hpk k r (wI k r m) j = if j = wI k r m then Hb k m m else 0 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  rw [← hH, Matrix.conjTranspose_apply, Hpk_apply_wI_right_eq_ite]
  by_cases h : j = wI k r m
  · simp only [h, if_true, Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [h]

private lemma Hpk_mul_Em_eq_Em_mul_Hb : Hpk k r * Em k r = Em k r * Hb k := by
  ext i m
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single (wI k r m) (fun j _ hj => by simp [Em, hj]) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single m (fun j _ hj => by simp [Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply, hj])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Em, Hpk_apply_wI_right_eq_ite]
  split_ifs <;> simp_all

lemma Hpk_mulVec_e0 (X : Mb k) : Hpk k r * e0 k r X = e0 k r (Hb k * X) := by
  unfold Dc.e0
  simp only [← Matrix.mul_assoc, Hpk_mul_Em_eq_Em_mul_Hb]

private lemma Em_transpose_mul_Hpk_eq_Hb_mul_transpose : (Em k r)ᵀ * Hpk k r = Hb k * (Em k r)ᵀ := by
  ext m i
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single (wI k r m) (fun j _ hj => by simp [Em, hj]) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single m (fun j _ hj => by simp [Formalism.QuantumDeterminants.Hb, Matrix.diagonal_apply, Ne.symm hj])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Matrix.transpose_apply, Em, Hpk_wI_apply_left_eq_ite]
  split_ifs <;> simp_all

lemma embed_mul_hermitian_form (X : Mb k) : e0 k r X * Hpk k r = e0 k r (X * Hb k) := by
  unfold Dc.e0
  simp only [Matrix.mul_assoc, Em_transpose_mul_Hpk_eq_Hb_mul_transpose]

lemma embed_add (X Y : Mb k) : e0 k r (X + Y) = e0 k r X + e0 k r Y := by
  unfold Dc.e0
  simp only [Matrix.mul_add, Matrix.add_mul]

lemma embed_sub (X Y : Mb k) : e0 k r (X - Y) = e0 k r X - e0 k r Y := by
  unfold Dc.e0
  simp only [Matrix.mul_sub, Matrix.sub_mul]

lemma embed_smul (c : ℂ) (X : Mb k) : e0 k r (c • X) = c • e0 k r X := by
  unfold Dc.e0
  simp only [Matrix.mul_smul, Matrix.smul_mul]

lemma embed_zero : e0 k r (0 : Mb k) = 0 := by
  unfold Dc.e0
  simp only [Matrix.mul_zero, Matrix.zero_mul]

lemma hermitian_real_part_embed (X : Mb k) :
    hpart1 (Hpk k r) (e0 k r X) = e0 k r ((1 / 2 : ℂ) • (X - Hb k * Xᴴ * Hb k)) := by
  unfold Formalism.QuantumDeterminants.hpart1
  rw [Hpk_inv, embed_conj_transpose, Hpk_mulVec_e0, embed_mul_hermitian_form, embed_smul, embed_sub]

lemma hermitian_imag_part_embed (X : Mb k) :
    hpart2 (Hpk k r) (e0 k r X) = e0 k r ((1 / (2 * Complex.I) : ℂ) • (X + Hb k * Xᴴ * Hb k)) := by
  unfold Formalism.QuantumDeterminants.hpart2
  rw [Hpk_inv, embed_conj_transpose, Hpk_mulVec_e0, embed_mul_hermitian_form, embed_smul, embed_add]

lemma embed_mul_vec (Y : Mb k) (v : Fin (2 * r + k + 1) → ℂ) :
    e0 k r Y *ᵥ v = Em k r *ᵥ (Y *ᵥ ((Em k r)ᵀ *ᵥ v)) := by
  unfold Dc.e0
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma EmT_mulVec (v : Fin (2 * r + k + 1) → ℂ) : (Em k r)ᵀ *ᵥ v = wbPart k r v := by
  ext j
  simp [Matrix.mulVec, dotProduct, Em, wbPart]

lemma wbPart_e (a : Fin r) : wbPart k r (bvec (eI k r a)) = 0 := by
  funext j
  have ha := a.isLt
  simp only [wbPart, bvec, Pi.zero_apply]
  rw [Pi.single_eq_of_ne]
  intro h
  simp only [wI, eI, Fin.ext_iff, Fin.val_mk] at h
  omega

lemma wbPart_es (a : Fin r) : wbPart k r (bvec (esI k r a)) = 0 := by
  funext j
  have ha := a.isLt
  have hj := j.isLt
  simp only [wbPart, bvec, Pi.zero_apply]
  rw [Pi.single_eq_of_ne]
  intro h
  simp only [wI, esI, Fin.ext_iff, Fin.val_mk] at h
  omega

lemma embed_mem_unitary_lie_algebra (z : Fin (2 * r + k + 1) → ℂ) (Y : Mb k) (hY : Yᴴ * Hb k + Hb k * Y = 0)
    (hz : Y *ᵥ wbPart k r z = 0) : P.QrD.InLieW k r z (e0 k r Y) := by
  unfold Formalism.FourierDecayAlt.P.QrD.InLieW Formalism.FourierDecayAlt.Q.inLieLev
  refine ⟨⟨?_, fun a _ => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [embed_conj_transpose, embed_mul_hermitian_form, Hpk_mulVec_e0, ← embed_add, hY, embed_zero]
  · rw [embed_mul_vec, EmT_mulVec, wbPart_e, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · rw [embed_mul_vec, EmT_mulVec, wbPart_es, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · rw [embed_mul_vec, EmT_mulVec, hz, Matrix.mulVec_zero]

lemma skew1 (X : Mb k) :
    ((1 / 2 : ℂ) • (X - Hb k * Xᴴ * Hb k))ᴴ * Hb k + Hb k * ((1 / 2 : ℂ) • (X - Hb k * Xᴴ * Hb k)) = 0 := by
  have h1 : Hb k * Hb k = 1 := Hb_sq k
  have h1' : ∀ Y : Mb k, Hb k * (Hb k * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2 : (Hb k)ᴴ = Hb k := Formalism.FourierDecayAlt.P.SettingConstruction.Hb_herm k
  have h3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have key : (X - Hb k * Xᴴ * Hb k)ᴴ * Hb k + Hb k * (X - Hb k * Xᴴ * Hb k) = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h1, h1', Matrix.mul_one]
    abel
  rw [Matrix.conjTranspose_smul, h3, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, key, smul_zero]

lemma skew2 (X : Mb k) :
    ((1 / (2 * Complex.I) : ℂ) • (X + Hb k * Xᴴ * Hb k))ᴴ * Hb k +
      Hb k * ((1 / (2 * Complex.I) : ℂ) • (X + Hb k * Xᴴ * Hb k)) = 0 := by
  have h1 : Hb k * Hb k = 1 := Hb_sq k
  have h1' : ∀ Y : Mb k, Hb k * (Hb k * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2 : (Hb k)ᴴ = Hb k := Formalism.FourierDecayAlt.P.SettingConstruction.Hb_herm k
  have h3 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    show (starRingEnd ℂ) (1 / (2 * Complex.I)) = _
    rw [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have key : (X + Hb k * Xᴴ * Hb k)ᴴ * Hb k = Hb k * (X + Hb k * Xᴴ * Hb k) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h1, h1', Matrix.mul_one]
    abel
  rw [Matrix.conjTranspose_smul, h3, Matrix.smul_mul, Matrix.mul_smul, key, neg_smul, neg_add_cancel]

lemma gwc_of (z : Fin (2 * r + k + 1) → ℂ) (X : Mb k) (h1 : X *ᵥ wbPart k r z = 0)
    (h2 : (Hb k * Xᴴ * Hb k) *ᵥ wbPart k r z = 0) : GWc k r z (e0 k r X) := by
  have hs : ∀ (c : ℂ) (A : Mb k) (w : Fin (k + 1) → ℂ), (c • A) *ᵥ w = c • (A *ᵥ w) := fun c A w => by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.GWc
  rw [hermitian_real_part_embed, hermitian_imag_part_embed]
  refine ⟨embed_mem_unitary_lie_algebra z _ (skew1 X) ?_, embed_mem_unitary_lie_algebra z _ (skew2 X) ?_⟩
  · rw [hs, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
  · rw [hs, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]

lemma inL_col {C : Mb k} (hC : InL k C) : C *ᵥ Pi.single (Fin.last k) 1 = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, (hC i).1]

lemma inL_colH {C : Mb k} (hC : InL k C) : Cᴴ *ᵥ Pi.single (Fin.last k) 1 = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.conjTranspose_apply, (hC i).2]

lemma Hb_last (k : ℕ) : Hb k *ᵥ Pi.single (Fin.last k) 1 = -Pi.single (Fin.last k) 1 := by
  funext i
  unfold Formalism.QuantumDeterminants.Hb
  rw [Matrix.mulVec_diagonal]
  by_cases h : i = Fin.last k
  · subst h; simp
  · simp [h]

lemma unit_inv {g : Mb k} (hg : gᴴ * Hb k * g = Hb k) : g⁻¹ = Hb k * gᴴ * Hb k := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Hb_sq]

lemma unit_invH {g : Mb k} (hg : gᴴ * Hb k * g = Hb k) : (g⁻¹)ᴴ = Hb k * g * Hb k := by
  have h2 : (Hb k)ᴴ = Hb k := Formalism.FourierDecayAlt.P.SettingConstruction.Hb_herm k
  rw [unit_inv hg]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2, Matrix.mul_assoc]

lemma unit_inv_mul {g : Mb k} (hg : gᴴ * Hb k * g = Hb k) : g⁻¹ * g = 1 := by
  rw [unit_inv hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Hb_sq]

lemma kill_right {g C : Mb k} (hg : gᴴ * Hb k * g = Hb k) (hC : InL k C) {v : Fin (k + 1) → ℂ} {c : ℂ}
    (hv : g *ᵥ v = c • Pi.single (Fin.last k) 1) :
    (g⁻¹ * C * g) *ᵥ v = 0 ∧ (Hb k * (g⁻¹ * C * g)ᴴ * Hb k) *ᵥ v = 0 := by
  have hbb : ∀ w, Hb k *ᵥ (Hb k *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Hb_sq, Matrix.one_mulVec]
  constructor
  · simp only [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, inL_col hC, smul_zero, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, unit_invH hg]
    simp only [← Matrix.mulVec_mulVec, hbb, hv, Matrix.mulVec_smul, Matrix.mulVec_neg, Hb_last, inL_colH hC, neg_zero,
      smul_zero, Matrix.mulVec_zero]

lemma kill_left {g C : Mb k} (hg : gᴴ * Hb k * g = Hb k) (hC : InL k C) {v : Fin (k + 1) → ℂ} {c : ℂ}
    (hv : g *ᵥ (c • Pi.single (Fin.last k) 1) = v) :
    (g * C * g⁻¹) *ᵥ v = 0 ∧ (Hb k * (g * C * g⁻¹)ᴴ * Hb k) *ᵥ v = 0 := by
  subst hv
  have hgg : ∀ w, g⁻¹ *ᵥ (g *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, unit_inv_mul hg, Matrix.one_mulVec]
  have hgg2 : ∀ w, gᴴ *ᵥ (Hb k *ᵥ (g *ᵥ w)) = Hb k *ᵥ w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]
  constructor
  · simp only [← Matrix.mulVec_mulVec, hgg, Matrix.mulVec_smul, inL_col hC, smul_zero, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, unit_invH hg]
    simp only [← Matrix.mulVec_mulVec, hgg2, Matrix.mulVec_smul, Matrix.mulVec_neg, Hb_last, inL_colH hC, neg_zero,
      smul_zero, Matrix.mulVec_zero]

theorem gwc_right (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hT' : 0 < Tz k r z') (C : Mb k)
    (hC : InL k C) :
    GWc k r z' (e0 k r ((gB k (wbPart k r z') (Tz k r z'))⁻¹ * C * gB k (wbPart k r z') (Tz k r z'))) := by
  obtain ⟨hg, hv⟩ := Formalism.FourierDecayAlt.P.TheSec.gB_spec (k := k) hT' (Formalism.FourierDecayAlt.P.SettingConstruction.herm_self (k := k) (r := r) z' hz')
  obtain ⟨h1, h2⟩ := kill_right hg hC hv
  exact gwc_of z' _ h1 h2

theorem gwc_left (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) (C : Mb k)
    (hC : InL k C) :
    GWc k r z (e0 k r (gA k (wbPart k r z) (Tz k r z) * C * (gA k (wbPart k r z) (Tz k r z))⁻¹)) := by
  obtain ⟨hg, hv⟩ := Formalism.FourierDecayAlt.P.TheSec.gA_spec (k := k) hT (Formalism.FourierDecayAlt.P.SettingConstruction.herm_self (k := k) (r := r) z hz)
  obtain ⟨h1, h2⟩ := kill_left hg hC hv
  exact gwc_of z _ h1 h2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k r : ℕ}

lemma block_embedding_mul_embed (g X : Mb k) : embWb k r g * e0 k r X = e0 k r (g * X) := by
  rw [emb_eq]
  unfold e0
  rw [Matrix.add_mul]
  have h1 : Em k r * g * (Em k r)ᵀ * (Em k r * X * (Em k r)ᵀ) = Em k r * (g * X) * (Em k r)ᵀ := by
    calc Em k r * g * (Em k r)ᵀ * (Em k r * X * (Em k r)ᵀ) = Em k r * g * ((Em k r)ᵀ * Em k r) * X * (Em k r)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Em k r * (g * X) * (Em k r)ᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have h2 : (1 - Em k r * (Em k r)ᵀ) * (Em k r * X * (Em k r)ᵀ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, Matrix.zero_mul]
  rw [h1, h2, add_zero]

lemma embed_mul_block_embedding (g X : Mb k) : e0 k r X * embWb k r g = e0 k r (X * g) := by
  rw [emb_eq]
  unfold e0
  rw [Matrix.mul_add]
  have h1 : Em k r * X * (Em k r)ᵀ * (Em k r * g * (Em k r)ᵀ) = Em k r * (X * g) * (Em k r)ᵀ := by
    calc Em k r * X * (Em k r)ᵀ * (Em k r * g * (Em k r)ᵀ) = Em k r * X * ((Em k r)ᵀ * Em k r) * g * (Em k r)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Em k r * (X * g) * (Em k r)ᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have h2 : Em k r * X * (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
    rw [Matrix.mul_assoc, EmT_Q, Matrix.mul_zero]
  rw [h1, h2, add_zero]

lemma single_wI (a b : Fin (k + 1)) : Matrix.single (wI k r a) (wI k r b) (1 : ℂ) = e0 k r (Su k a b) := by
  have hE : ∀ c : Fin (k + 1), Em k r *ᵥ Pi.single c 1 = Pi.single (wI k r c) 1 := by
    intro c
    funext i
    rw [Matrix.mulVec_single_one]
    show Em k r i c = _
    rw [Em, Pi.single_apply]
  unfold e0 Su
  rw [Matrix.single_eq_single_vecMulVec_single, Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hE, hE]

def LS (k : ℕ) (p : Fin (k + 1) × Fin (k + 1)) : Mb k :=
  if p.1 = Fin.last k ∨ p.2 = Fin.last k then 0 else Su k p.1 p.2

lemma inL_LS (p : Fin (k + 1) × Fin (k + 1)) : InL k (LS k p) := by
  unfold LS
  split_ifs with h
  · exact inL_zero
  · exact inL_Su (not_or.1 h).1 (not_or.1 h).2

lemma sum_LS {n : ℕ} (e : Fin (k + 1) × Fin (k + 1) ≃ Fin n) (C : Mb k) (hC : InL k C) :
    ∑ t : Fin n, C (e.symm t).1 (e.symm t).2 • LS k (e.symm t) = C := by
  rw [e.symm.sum_comp (fun p => C p.1 p.2 • LS k p), Fintype.sum_prod_type]
  conv_rhs => rw [Matrix.matrix_eq_sum_single C]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold LS
  split_ifs with h
  · have : C i j = 0 := by
      rcases h with h | h
      · have h' : i = Fin.last k := h
        rw [h']; exact (hC j).2
      · have h' : j = Fin.last k := h
        rw [h']; exact (hC i).1
    rw [this, zero_smul, Matrix.single_zero]
  · unfold Su
    rw [Matrix.smul_single, smul_eq_mul, mul_one]

lemma embed_conj_finset_sum {n : ℕ} (g h : Mb k) (c : Fin n → ℂ) (X : Fin n → Mb k) :
    ∑ t, c t • e0 k r (g * X t * h) = e0 k r (g * (∑ t, c t • X t) * h) := by
  unfold e0
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma ringSpec_normalisedCharacter_eq (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) :
    mu0 k r z z' ζ = embWb k r (gA k (wbPart k r z) (Tz k r z) * nu k (wZ (Tz k r z) (Tz k r z') ζ) (sZ (Tz k r z) (Tz k r z') ζ) *
      gB k (wbPart k r z') (Tz k r z')) := rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2 Dc

noncomputable section

theorem radial_decomposition_holds : Decomp := by
  intro k r z z' hk hz hz' hT hT' a b
  have h0 : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  obtain ⟨hA, -⟩ := gA_spec k hT (herm_self k r z hz)
  obtain ⟨hB, -⟩ := gB_spec k hT' (herm_self k r z' hz')
  set T := Tz k r z with hTd
  set T' := Tz k r z' with hTd'
  set ga := gA k (wbPart k r z) T with hga
  set gb := gB k (wbPart k r z') T' with hgb
  have iA : ga⁻¹ * ga = 1 := unit_inv_mul hA
  have iB : gb⁻¹ * gb = 1 := unit_inv_mul hB
  obtain ⟨C₁, C₂, β₁, β₂, c1, c2, c3, c4, c5⟩ := dec_all (T := T) (T' := T') h0 hT hT' (gb * Su k a b * gb⁻¹)
  let e := Fintype.equivFin (Fin (k + 1) × Fin (k + 1))
  refine ⟨_, _, fun t => e0 k r (gb⁻¹ * LS k (e.symm t) * gb), fun t ζ => C₁ ζ (e.symm t).1 (e.symm t).2,
    fun t => e0 k r (ga * LS k (e.symm t) * ga⁻¹), fun t ζ => C₂ ζ (e.symm t).1 (e.symm t).2, β₁, β₂,
    fun t => gwc_right k r z' hz' hT' _ (inL_LS _), fun t => gwc_left k r z hz hT _ (inL_LS _),
    fun t => c1.1 _ _, fun t => c2.1 _ _, c3, c4, fun ζ hζ => ?_⟩
  have hν := nuI_mul (k := k) h0 hT hT' hζ
  set ν := nu k (wZ T T' ζ) (sZ T T' ζ) with hνd
  set νi := nuI k T T' ζ with hνi
  have hmu : mu0 k r z z' ζ = embWb k r (ga * ν * gb) := ringSpec_normalisedCharacter_eq z z' ζ
  have hinv : (mu0 k r z z' ζ)⁻¹ = embWb k r (gb⁻¹ * νi * ga⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hmu, ← emb_mul]
    have : gb⁻¹ * νi * ga⁻¹ * (ga * ν * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * ν)) * gb := by simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul, hν, Matrix.mul_one, iB, emb_one]
  have s1 : ∑ t, C₁ ζ (e.symm t).1 (e.symm t).2 • e0 k r (gb⁻¹ * LS k (e.symm t) * gb) = e0 k r (gb⁻¹ * C₁ ζ * gb) := by
    rw [embed_conj_finset_sum, sum_LS e _ (c1.2 ζ)]
  have s2 : ∑ t, C₂ ζ (e.symm t).1 (e.symm t).2 • e0 k r (ga * LS k (e.symm t) * ga⁻¹) = e0 k r (ga * C₂ ζ * ga⁻¹) := by
    rw [embed_conj_finset_sum, sum_LS e _ (c2.2 ζ)]
  have s3 : (mu0 k r z z' ζ)⁻¹ * e0 k r (ga * C₂ ζ * ga⁻¹) * mu0 k r z z' ζ = e0 k r (gb⁻¹ * (νi * C₂ ζ * ν) * gb) := by
    rw [hinv, hmu, block_embedding_mul_embed, embed_mul_block_embedding]
    congr 1
    have : gb⁻¹ * νi * ga⁻¹ * (ga * C₂ ζ * ga⁻¹) * (ga * ν * gb) =
        gb⁻¹ * (νi * ((ga⁻¹ * ga) * C₂ ζ * (ga⁻¹ * ga)) * ν) * gb := by simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul, Matrix.mul_one]
  have s4 : etaZ k r z z' ζ = e0 k r (gb⁻¹ * H1 k T T' ζ * gb) := by
    unfold etaZ
    rw [dmu_eq k r z z' hT hT' ζ hζ, hinv, block_embedding_mul_embed]
    congr 1
    unfold H1
    have : ∀ D : Mb k, gb⁻¹ * νi * ga⁻¹ * (ga * D * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * D)) * gb := by
      intro D; simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul]
  have s5 : etaZb k r z z' ζ = e0 k r (gb⁻¹ * H2 k T T' ζ * gb) := by
    unfold etaZb
    rw [dmub_eq k r z z' hT hT' ζ hζ, hinv, block_embedding_mul_embed]
    congr 1
    unfold H2
    have : ∀ D : Mb k, gb⁻¹ * νi * ga⁻¹ * (ga * D * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * D)) * gb := by
      intro D; simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul]
  have s6 : Su k a b = gb⁻¹ * (gb * Su k a b * gb⁻¹) * gb := by
    have : gb⁻¹ * (gb * Su k a b * gb⁻¹) * gb = (gb⁻¹ * gb) * Su k a b * (gb⁻¹ * gb) := by simp only [Matrix.mul_assoc]
    rw [this, iB, Matrix.one_mul, Matrix.mul_one]
  rw [s1, s2, s3, s4, s5, single_wI, s6, c5 ζ hζ, ← embed_smul, ← embed_smul, ← embed_add, ← embed_add, ← embed_add]
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end
