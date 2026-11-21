import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact

section
namespace CompanionTheory.D.Upq

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem continuousOn_matrix_inv :
    ContinuousOn (fun A : Matrix n n 𝕜 => A⁻¹) {A | IsUnit A} := by
  rintro _ ⟨u, rfl⟩
  have h := NormedRing.inverse_continuousAt u
  have he : (fun A : Matrix n n 𝕜 => A⁻¹) = Ring.inverse := funext nonsing_inv_eq_ringInverse
  rw [he]
  exact h.continuousWithinAt

theorem posDef_conjTranspose_mul_self_GL (g : GL n 𝕜) : ((g : Matrix n n 𝕜)ᴴ * g).PosDef :=
  PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)

noncomputable def polarPos (g : GL n 𝕜) : Matrix n n 𝕜 := CFC.sqrt ((g : Matrix n n 𝕜)ᴴ * g)

theorem polarPos_posDef (g : GL n 𝕜) : (polarPos g).PosDef := by
  have h := posDef_conjTranspose_mul_self_GL g
  rw [← isStrictlyPositive_iff_posDef] at h ⊢
  exact IsStrictlyPositive.sqrt _ h

theorem polarPos_mul_self (g : GL n 𝕜) : polarPos g * polarPos g = (g : Matrix n n 𝕜)ᴴ * g :=
  CFC.sqrt_mul_sqrt_self _ ((posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarUnitary (g : GL n 𝕜) : Matrix n n 𝕜 := (g : Matrix n n 𝕜) * (polarPos g)⁻¹

theorem isUnit_det_of_posDef {p : Matrix n n 𝕜} (hp : p.PosDef) : IsUnit p.det :=
  (isUnit_iff_isUnit_det p).1 hp.isUnit

theorem polarUnitary_mem (g : GL n 𝕜) : polarUnitary g ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hP : (polarPos g)ᴴ = polarPos g := (polarPos_posDef g).isHermitian
  have hd := isUnit_det_of_posDef (polarPos_posDef g)
  rw [star_eq_conjTranspose, polarUnitary, conjTranspose_mul, conjTranspose_nonsing_inv, hP]
  calc (polarPos g)⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * (polarPos g)⁻¹)
      = (polarPos g)⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * (polarPos g)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarPos g)⁻¹ * (polarPos g * polarPos g) * (polarPos g)⁻¹ := by rw [polarPos_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hd]

theorem polarUnitary_mul_polarPos (g : GL n 𝕜) : polarUnitary g * polarPos g = g := by
  rw [polarUnitary, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef (polarPos_posDef g)), Matrix.mul_one]

theorem polar_unique {g : GL n 𝕜} {k p : Matrix n n 𝕜} (hk : k ∈ unitaryGroup n 𝕜)
    (hp : p.PosDef) (h : k * p = g) : polarPos g = p ∧ polarUnitary g = k := by
  have hkk : kᴴ * k = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hk
  have hP : pᴴ = p := hp.isHermitian
  have hpp : p * p = (g : Matrix n n 𝕜)ᴴ * g := by
    rw [← h, conjTranspose_mul, hP]
    calc p * p = p * (kᴴ * k) * p := by rw [hkk, Matrix.mul_one]
      _ = p * kᴴ * (k * p) := by simp only [Matrix.mul_assoc]
  have h1 : polarPos g = p := CFC.sqrt_unique hpp hp.posSemidef.nonneg
  refine ⟨h1, ?_⟩
  rw [polarUnitary, h1, ← h, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hp), Matrix.mul_one]

noncomputable def polarMul (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) : GL n 𝕜 :=
    ⟨kp.1 * kp.2, kp.2.1⁻¹ * star (kp.1 : Matrix n n 𝕜), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (kp.2 : Matrix n n 𝕜),
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef kp.2.2), Matrix.one_mul]
      exact mem_unitaryGroup_iff.1 kp.1.2, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star (kp.1 : Matrix n n 𝕜)),
        mem_unitaryGroup_iff'.1 kp.1.2, Matrix.one_mul,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef kp.2.2)]⟩

noncomputable def polarEquiv : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ GL n 𝕜 where
  toFun := polarMul
  invFun g := (⟨polarUnitary g, polarUnitary_mem g⟩, ⟨polarPos g, polarPos_posDef g⟩)
  left_inv kp := by
    obtain ⟨⟨k, hk⟩, ⟨p, hp⟩⟩ := kp
    have := polar_unique (g := polarMul (⟨k, hk⟩, ⟨p, hp⟩)) hk hp rfl
    exact Prod.ext (Subtype.ext this.2) (Subtype.ext this.1)
  right_inv g := Units.ext (polarUnitary_mul_polarPos g)

@[simp] theorem coe_polarEquiv_apply (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) :
    ((polarEquiv kp : GL n 𝕜) : Matrix n n 𝕜) = kp.1 * kp.2 := rfl

theorem continuous_polarPos
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    Continuous (polarPos : GL n 𝕜 → Matrix n n 𝕜) :=
  hsqrt.comp_continuous
    ((Units.continuous_val.matrix_conjTranspose).mul Units.continuous_val)
    (fun g => (posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarHomeomorph
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ₜ GL n 𝕜 where
  toEquiv := polarEquiv
  continuous_toFun := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuousOn_matrix_inv.comp_continuous (continuous_subtype_val.comp continuous_snd)
        (fun kp => kp.2.2.isUnit)).mul
        (continuous_star.comp (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    have hP := continuous_polarPos (n := n) (𝕜 := 𝕜) hsqrt
    refine Continuous.prodMk ?_ (hP.subtype_mk _)
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.mul
      (continuousOn_matrix_inv.comp_continuous hP (fun g => (polarPos_posDef g).isUnit))

section ExpHermitianComplex

theorem posDef_exp_of_isHermitian_complex {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)

noncomputable def expHermitianHomeomorphComplex :
    {X : Matrix n n ℂ // X.IsHermitian} ≃ₜ {p : Matrix n n ℂ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_complex X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℂ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _

end ExpHermitianComplex

section ExpHermitianReal

theorem posDef_exp_of_isHermitian_real {X : Matrix n n ℝ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)

noncomputable def expHermitianHomeomorphReal :
    {X : Matrix n n ℝ // X.IsHermitian} ≃ₜ {p : Matrix n n ℝ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_real X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℝ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _

end ExpHermitianReal

end CompanionTheory.D.Upq
end

section
namespace CompanionTheory.D.Upq

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

set_option linter.unusedSectionVars false

variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}

theorem mul_J_mul_conjTranspose (hJJ : J * J = 1) {g : Matrix m m ℂ} (hg : gᴴ * J * g = J) :
    g * J * gᴴ = J := by
  have h1 : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have h2 : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 h1
  calc g * J * gᴴ = g * (J * gᴴ * J) * J := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h2, Matrix.one_mul]

theorem sqrt_mem_UJ (hJJ : J * J = 1) (hJh : Jᴴ = J) {P : Matrix m m ℂ} (hP : P.PosDef)
    (hPJ : Pᴴ * J * P = J) : (CFC.sqrt P)ᴴ * J * CFC.sqrt P = J := by
  set S := CFC.sqrt P with hSdef
  have hSpd : S.PosDef := by
    rw [← isStrictlyPositive_iff_posDef] at hP ⊢
    exact IsStrictlyPositive.sqrt _ hP
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hPh : Pᴴ = P := hP.isHermitian
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg
  have hPJ' : P * J * P = J := by rwa [hPh] at hPJ
  have hJPJ : J * P * J = P⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc J * P * J * P = J * (P * J * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJ', hJJ]
  have h1 : CFC.sqrt (J * P * J) = J * S * J := by
    refine CFC.sqrt_unique ?_ ?_
    · calc J * S * J * (J * S * J) = J * S * (J * J) * S * J := by simp only [Matrix.mul_assoc]
        _ = J * P * J := by rw [hJJ, Matrix.mul_one, Matrix.mul_assoc J S S, hSS]
    · have := hSpd.posSemidef.conjTranspose_mul_mul_same J
      rw [hJh] at this
      exact this.nonneg
  have h2 : CFC.sqrt P⁻¹ = S⁻¹ := by
    refine CFC.sqrt_unique ?_ hSpd.inv.posSemidef.nonneg
    rw [← Matrix.mul_inv_rev, hSS]
  have h3 : J * S * J = S⁻¹ := by rw [← h1, hJPJ, h2]
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  rw [hSh]
  calc S * J * S = S * (J * S * J) * J := by
        simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h3, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul]

theorem mul_mem_UJ {a b : Matrix m m ℂ} (ha : aᴴ * J * a = J) (hb : bᴴ * J * b = J) :
    (a * b)ᴴ * J * (a * b) = J := by
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * J * (a * b) = bᴴ * (aᴴ * J * a) * b := by simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]

theorem inv_mem_UJ {a : Matrix m m ℂ} (hu : IsUnit a.det) (ha : aᴴ * J * a = J) :
    a⁻¹ᴴ * J * a⁻¹ = J := by
  calc a⁻¹ᴴ * J * a⁻¹ = a⁻¹ᴴ * (aᴴ * J * a) * a⁻¹ := by rw [ha]
    _ = (a * a⁻¹)ᴴ * J * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = J := by rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem polar_mem_UJ (hJJ : J * J = 1) (hJh : Jᴴ = J) (g : GL m ℂ)
    (hg : (g : Matrix m m ℂ)ᴴ * J * g = J) :
    (polarPos g)ᴴ * J * polarPos g = J ∧ (polarUnitary g)ᴴ * J * polarUnitary g = J := by
  have hp : (polarPos g)ᴴ * J * polarPos g = J := by
    refine sqrt_mem_UJ hJJ hJh (posDef_conjTranspose_mul_self_GL g) ?_
    have hg' := mul_J_mul_conjTranspose hJJ hg
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc (g : Matrix m m ℂ)ᴴ * g * J * ((g : Matrix m m ℂ)ᴴ * g)
        = (g : Matrix m m ℂ)ᴴ * ((g : Matrix m m ℂ) * J * (g : Matrix m m ℂ)ᴴ) * g := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hg', hg]
  exact ⟨hp, mul_mem_UJ hg (inv_mem_UJ (isUnit_det_of_posDef (polarPos_posDef g)) hp)⟩

theorem unitary_group_polar_decomposition : PI.QuotSetU.UnitaryGroupMassFormula.PolarUH := by
  intro k r g hg
  have hHh := PI.QuotSetU.UnitaryGroupMassFormula.hpk_conjTranspose k r
  have hHH := PI.QuotSetU.UnitaryGroupMassFormula.hpk_mul_self k r
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (PI.QuotSetU.UnitaryGroupMassFormula.uh_det hg)
  set G : GL (Fin (2 * r + k + 1)) ℂ := hU.unit with hGdef
  have hGg : (G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = g := hU.unit_spec
  have hgG : (G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ *
      PI.QuotSetU.Hpk k r * G = PI.QuotSetU.Hpk k r := by rw [hGg]; exact hg
  obtain ⟨hp, hu⟩ := polar_mem_UJ hHH hHh G hgG
  refine ⟨polarUnitary G, polarPos G, hu, ?_, hp, (polarPos_posDef G).isHermitian, ?_⟩
  · have := mem_unitaryGroup_iff'.1 (polarUnitary_mem G)
    rwa [star_eq_conjTranspose] at this
  · rw [polarUnitary_mul_polarPos, hGg]

theorem unitary_group_modular_function_trivial : PI.QuotSetU.UnitaryGroupMassFormula.TrivG :=
  PI.QuotSetU.UnitaryGroupMassFormula.trivG_of unitary_group_polar_decomposition PI.QuotSetU.UnitaryGroupMassFormula.maximal_compact_isCompact

end CompanionTheory.D.Upq
end
