import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronTate

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing IsDiscreteValuationRing Polynomial

noncomputable section

section Node

variable {F : Type*} [Field F] (V : WeierstrassCurve F)

theorem exists_node (hΔ : V.Δ = 0) (hc : V.c₄ ≠ 0) :
    ∃ x y : F, V.toAffine.Equation x y ∧
      V.a₁ * y - (3 * x ^ 2 + 2 * V.a₂ * x + V.a₄) = 0 ∧ 2 * y + V.a₁ * x + V.a₃ = 0 := by
  by_cases h2 : (2 : F) = 0
  · have ha : V.a₁ ≠ 0 := by
      intro h0
      apply hc
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h0]
      linear_combination (8 * V.a₂ ^ 2 - 24 * V.a₄) * h2
    set x₀ := V.a₃ / V.a₁ with hx₀
    set y₀ := (x₀ ^ 2 + V.a₄) / V.a₁ with hy₀
    refine ⟨x₀, y₀, ?_, ?_, ?_⟩
    · rw [Affine.equation_iff']
      have key : V.a₁ ^ 6 * (y₀ ^ 2 + V.a₁ * x₀ * y₀ + V.a₃ * y₀ -
          (x₀ ^ 3 + V.a₂ * x₀ ^ 2 + V.a₄ * x₀ + V.a₆)) = V.Δ + 2 * (6 * V.a₁ ^ 4 * V.a₂ * V.a₆ -
          4 * V.a₁ ^ 3 * V.a₂ * V.a₃ * V.a₄ - 18 * V.a₁ ^ 3 * V.a₃ * V.a₆ +
          4 * V.a₁ ^ 2 * V.a₂ ^ 2 * V.a₃ ^ 2 + 24 * V.a₁ ^ 2 * V.a₂ ^ 2 * V.a₆ -
          4 * V.a₁ ^ 2 * V.a₂ * V.a₄ ^ 2 + 16 * V.a₁ ^ 2 * V.a₃ ^ 2 * V.a₄ -
          36 * V.a₁ ^ 2 * V.a₄ * V.a₆ - 8 * V.a₁ * V.a₂ ^ 2 * V.a₃ * V.a₄ -
          18 * V.a₁ * V.a₂ * V.a₃ ^ 3 - 72 * V.a₁ * V.a₂ * V.a₃ * V.a₆ +
          48 * V.a₁ * V.a₃ * V.a₄ ^ 2 + 8 * V.a₂ ^ 3 * V.a₃ ^ 2 + 32 * V.a₂ ^ 3 * V.a₆ -
          8 * V.a₂ ^ 2 * V.a₄ ^ 2 - 36 * V.a₂ * V.a₃ ^ 2 * V.a₄ - 144 * V.a₂ * V.a₄ * V.a₆ +
          14 * V.a₃ ^ 4 + 108 * V.a₃ ^ 2 * V.a₆ + 32 * V.a₄ ^ 3 + 216 * V.a₆ ^ 2) := by
        rw [hy₀, hx₀]
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        field_simp
        ring
      rw [hΔ, h2, zero_mul, add_zero] at key
      exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero 6 ha)
    · rw [hy₀]; field_simp; linear_combination (-(x₀ ^ 2) - V.a₂ * x₀) * h2
    · rw [hx₀]; field_simp; linear_combination (y₀ + V.a₃) * h2
  · set x₀ := (18 * V.b₆ - V.b₂ * V.b₄) / V.c₄ with hx₀
    have hD : V.b₂ ^ 2 * (V.b₂ * V.b₆ - V.b₄ ^ 2) + 32 * V.b₄ ^ 3 + 108 * V.b₆ ^ 2 -
        36 * V.b₂ * V.b₄ * V.b₆ = 0 := by
      have := V.b_relation
      rw [WeierstrassCurve.Δ] at hΔ
      linear_combination -4 * hΔ - V.b₂ ^ 2 * this
    have hc4 : V.c₄ = V.b₂ ^ 2 - 24 * V.b₄ := rfl
    have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    have hf : 4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆ = 0 := by
      have key : V.c₄ ^ 3 * (4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆) =
          (V.b₂ ^ 3 - 36 * V.b₂ * V.b₄ + 216 * V.b₆) * (V.b₂ ^ 2 * (V.b₂ * V.b₆ - V.b₄ ^ 2) +
            32 * V.b₄ ^ 3 + 108 * V.b₆ ^ 2 - 36 * V.b₂ * V.b₄ * V.b₆) := by
        rw [hx₀]; field_simp; rw [hc4]; ring
      rw [hD, mul_zero] at key
      exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero 3 hc)
    have hf' : 12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄ = 0 := by
      have key : V.c₄ ^ 2 * (12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄) =
          36 * (V.b₂ ^ 2 * (V.b₂ * V.b₆ - V.b₄ ^ 2) + 32 * V.b₄ ^ 3 + 108 * V.b₆ ^ 2 -
            36 * V.b₂ * V.b₄ * V.b₆) := by
        rw [hx₀]; field_simp; rw [hc4]; ring
      rw [hD, mul_zero] at key
      exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero 2 hc)
    refine ⟨x₀, -(V.a₁ * x₀ + V.a₃) / 2, ?_, ?_, ?_⟩
    · rw [Affine.equation_iff']
      have : (-(V.a₁ * x₀ + V.a₃) / 2) ^ 2 + V.a₁ * x₀ * (-(V.a₁ * x₀ + V.a₃) / 2) +
          V.a₃ * (-(V.a₁ * x₀ + V.a₃) / 2) - (x₀ ^ 3 + V.a₂ * x₀ ^ 2 + V.a₄ * x₀ + V.a₆) =
          -(4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆) / 4 := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
        field_simp; ring
      rw [this, hf]; simp
    · have : V.a₁ * (-(V.a₁ * x₀ + V.a₃) / 2) - (3 * x₀ ^ 2 + 2 * V.a₂ * x₀ + V.a₄) =
          -(12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄) / 4 := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
        field_simp; ring
      rw [this, hf']; simp
    · field_simp; ring

end Node

section Form

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [DecidableEq (ResidueField 𝒪)] {π : 𝒪}
  (hπ : Irreducible π) (W : WeierstrassCurve 𝒪)
include hπ

theorem tate_step2 (V : WeierstrassCurve 𝒪) (h2 : V.a₂ = 0) (he : IsUnit V.a₁) (h3 : π ∣ V.a₃)
    (h4 : π ∣ V.a₄) (h6 : π ∣ V.a₆) :
    ∃ r s t : 𝒪, ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₂ = 0 ∧
      ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₃ = 0 ∧
      ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₄ = 0 ∧
      IsUnit ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₁ ∧
      π ∣ ((⟨1, r, s, t⟩ : VariableChange 𝒪) • V).a₆ := by
  have hγ : IsUnit (12 * V.a₃ - V.a₁ ^ 3) := by
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply (isUnit_iff_not_dvd hπ).1 (he.pow 3)
    have := dvd_sub (dvd_mul_of_dvd_right h3 12) h
    convert this using 1; ring
  obtain ⟨t, dt, ht⟩ := exists_root_cubic hπ (α := 0) (β := 12) hγ
    (δ := 3 * V.a₃ ^ 2 + V.a₁ ^ 2 * V.a₄)
    (dvd_add (dvd_mul_of_dvd_right (dvd_pow h3 two_ne_zero) 3) (dvd_mul_of_dvd_right h4 _))
  obtain ⟨r, hr⟩ : ∃ r, V.a₁ * r = -(V.a₃ + 2 * t) := ⟨-(V.a₃ + 2 * t) * ↑he.unit⁻¹, by
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]⟩
  have dr : π ∣ r := by
    have h1 : π ∣ V.a₁ * r := by rw [hr]; exact dvd_neg.2 (dvd_add h3 (dvd_mul_of_dvd_right dt 2))
    exact (he.dvd_mul_left).1 h1
  obtain ⟨s, ds, hs⟩ := exists_root_cubic hπ (α := 0) (β := 1) he (δ := -(3 * r))
    (dvd_neg.2 (dvd_mul_of_dvd_right dr 3))
  refine ⟨r, s, t, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [variableChange_a₂, inv_one, Units.val_one, one_pow, one_mul, h2]
    linear_combination -hs
  · simp only [variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hr
  · simp only [variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul, h2]
    have hk : V.a₁ ^ 2 * (V.a₄ - t * V.a₁ + 3 * r ^ 2 - s * (V.a₁ * r + V.a₃ + 2 * t)) = 0 := by
      linear_combination ht + (3 * (V.a₁ * r - V.a₃ - 2 * t) - V.a₁ ^ 2 * s) * hr
    have hk' := (mul_eq_zero.1 hk).resolve_left (pow_ne_zero 2 he.ne_zero)
    linear_combination hk'
  · simp only [variableChange_a₁, inv_one, Units.val_one, one_mul]
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply (isUnit_iff_not_dvd hπ).1 he
    have := dvd_sub h (dvd_mul_of_dvd_right ds 2)
    rwa [add_sub_cancel_right] at this
  · simp only [variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul, h2]
    exact dvd_sub (dvd_sub (dvd_sub (dvd_add (dvd_add (dvd_add h6 (dvd_mul_of_dvd_left dr _))
      (dvd_mul_of_dvd_left (dvd_pow dr two_ne_zero) _)) (dvd_pow dr three_ne_zero))
      (dvd_mul_of_dvd_left dt _)) (dvd_pow dt two_ne_zero)) (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left dr _) _)

theorem tate_step1 (W : WeierstrassCurve 𝒪) (hc : ¬π ∣ W.c₄) (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄)
    (h6 : π ∣ W.a₆) {s₀ : 𝒪} (hs₀ : π ∣ s₀ ^ 2 + W.a₁ * s₀ - W.a₂) :
    ∃ s₁ : 𝒪, ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₂ = 0 ∧
      IsUnit ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₁ ∧
      π ∣ ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₃ ∧
      π ∣ ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₄ ∧
      π ∣ ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • W).a₆ := by
  have hb4 : π ∣ W.b₄ := by
    rw [WeierstrassCurve.b₄]; exact dvd_add (dvd_mul_of_dvd_right h4 2) (dvd_mul_of_dvd_right h3 _)
  have hb2 : ¬π ∣ W.b₂ := fun h => hc (by
    rw [WeierstrassCurve.c₄]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right hb4 24))
  have hγ₁ : IsUnit (2 * s₀ + W.a₁) := by
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply hb2
    have : W.b₂ = (2 * s₀ + W.a₁) ^ 2 - 4 * (s₀ ^ 2 + W.a₁ * s₀ - W.a₂) := by
      rw [WeierstrassCurve.b₂]; ring
    rw [this]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right hs₀ 4)
  obtain ⟨Z, -, hZ⟩ := exists_root_cubic hπ (α := 0) (β := 1) hγ₁ hs₀
  have hs₁ : (s₀ + Z) ^ 2 + W.a₁ * (s₀ + Z) - W.a₂ = 0 := by linear_combination hZ
  refine ⟨s₀ + Z, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [variableChange_a₂, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -hs₁
  · simp only [variableChange_a₁, inv_one, Units.val_one, one_mul]
    rw [isUnit_iff_not_dvd hπ]
    intro h
    apply hb2
    have : W.b₂ = (W.a₁ + 2 * (s₀ + Z)) ^ 2 - 4 * ((s₀ + Z) ^ 2 + W.a₁ * (s₀ + Z) - W.a₂) := by
      rw [WeierstrassCurve.b₂]; ring
    rw [this, hs₁, mul_zero, sub_zero]
    exact dvd_pow h two_ne_zero
  · simp only [variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero,
      mul_zero]
    exact h3
  · simp only [variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero,
      mul_zero, sub_zero, zero_pow two_ne_zero]
    exact dvd_sub h4 (dvd_mul_of_dvd_right h3 _)
  · simp only [variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero,
      mul_zero, sub_zero, zero_pow two_ne_zero, zero_pow three_ne_zero]
    exact h6

end Form

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic]

local notation "ι" => algebraMap 𝒪 K
local notation "v" => addVal 𝒪

theorem split_equiv [IsMinimal 𝒪 (W.map (algebraMap 𝒪 K))]
    (hs : (W.map (algebraMap 𝒪 K)).HasSplitMultiplicativeReduction 𝒪) :
    Nonempty ((curveK K W).Point ⧸ E0 K W ≃+ ZMod (v W.Δ).toNat) := by
  obtain ⟨π, hπ⟩ := exists_irreducible 𝒪
  have hm := hs.toHasMultiplicativeReduction
  have hc := not_dvd_c₄_of_hasMultiplicativeReduction K W hπ hm
  have hΔ := dvd_Δ_of_hasMultiplicativeReduction K W hπ hm
  have hres : ∀ {a : 𝒪}, π ∣ a ↔ residue 𝒪 a = 0 := dvd_iff_residue_eq_zero hπ
  obtain ⟨xb, yb, heb, hAb, hBb⟩ := exists_node (W.map (residue 𝒪))
    (by rw [map_Δ]; exact hres.1 hΔ) (by rw [map_c₄]; exact fun h => hc (hres.2 h))
  obtain ⟨x₀, rfl⟩ := IsLocalRing.residue_surjective xb
  obtain ⟨y₀, rfl⟩ := IsLocalRing.residue_surjective yb
  rw [Affine.equation_iff'] at heb
  set C₀ : VariableChange 𝒪 := ⟨1, x₀, 0, y₀⟩ with hC₀
  have h3 : π ∣ (C₀ • W).a₃ := by
    rw [hres]
    simp only [hC₀, variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul, map_add, map_mul,
      map_ofNat]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at hBb
    linear_combination hBb
  have h4 : π ∣ (C₀ • W).a₄ := by
    rw [hres]
    simp only [hC₀, variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul, map_add, map_mul,
      map_sub, map_pow, map_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄] at hAb
    linear_combination -hAb
  have h6 : π ∣ (C₀ • W).a₆ := by
    rw [hres]
    simp only [hC₀, variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul, map_add, map_mul,
      map_sub, map_pow]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heb
    linear_combination -heb
  have hc₀ : ¬π ∣ (C₀ • W).c₄ := by
    rw [variableChange_c₄]; simpa [hC₀] using hc

  have hsp := hs.splitMultiplicativeReduction
  rw [integralModel_map, splitPoly_origin W hπ h3 h4 h6] at hsp
  have hc4r : residue 𝒪 W.c₄ ≠ 0 := fun h => hc (hres.2 h)
  have hdeg : (C (residue 𝒪 W.c₄) * (X ^ 2 + C (residue 𝒪 (C₀ • W).a₁) * X -
      C (residue 𝒪 (C₀ • W).a₂))).degree ≠ 0 := by
    rw [degree_C_mul hc4r, show (X ^ 2 + C (residue 𝒪 (C₀ • W).a₁) * X -
      C (residue 𝒪 (C₀ • W).a₂) : Polynomial (ResidueField 𝒪)) = C 1 * X ^ 2 +
      C (residue 𝒪 (C₀ • W).a₁) * X + C (-residue 𝒪 (C₀ • W).a₂) by simp [sub_eq_add_neg],
      degree_quadratic one_ne_zero]
    decide
  obtain ⟨sb, hsb⟩ := hsp.exists_eval_eq_zero hdeg
  obtain ⟨s₀, rfl⟩ := IsLocalRing.residue_surjective sb
  have hs₀ : π ∣ s₀ ^ 2 + (C₀ • W).a₁ * s₀ - (C₀ • W).a₂ := by
    rw [hres]
    simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_X] at hsb
    have := (mul_eq_zero.1 hsb).resolve_left hc4r
    simp only [map_sub, map_add, map_mul, map_pow]
    exact this
  obtain ⟨s₁, t2, te, t3, t4, t6⟩ := tate_step1 hπ (C₀ • W) hc₀ h3 h4 h6 hs₀
  obtain ⟨r, s, t, g2, g3, g4, ge, g6⟩ := tate_step2 hπ _ t2 te t3 t4 t6
  set W₂ := (⟨1, r, s, t⟩ : VariableChange 𝒪) • ((⟨1, 0, s₁, 0⟩ : VariableChange 𝒪) • (C₀ • W))
  have eT := tateQuotientEquiv K hπ g2 g3 g4 ge g6
  have hΔ₂ : W₂.Δ = W.Δ := by simp only [W₂, hC₀, vc_Δ_one]
  have hq0 : W₂.a₆ ≠ 0 := a₆_ne_zero K g2 g3 g4
  have hv : v W₂.a₆ = v W.Δ := by
    rw [← hΔ₂]
    have : W₂.Δ = W₂.a₆ * -(W₂.a₁ ^ 6 + 432 * W₂.a₆) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈, g2, g3, g4]
      ring
    have hu : IsUnit (-(W₂.a₁ ^ 6 + 432 * W₂.a₆)) := by
      rw [IsUnit.neg_iff, isUnit_iff_not_dvd hπ]
      intro h
      apply (isUnit_iff_not_dvd hπ).1 (ge.pow 6)
      have := dvd_sub h (dvd_mul_of_dvd_right g6 432)
      rwa [add_sub_cancel_right] at this
    rw [this, addVal_mul, v_unit hu, add_zero]
  exact ⟨(quotientE0VariableChangeEquiv K W C₀).trans ((quotientE0VariableChangeEquiv K (C₀ • W) ⟨1, 0, s₁, 0⟩).trans
    ((quotientE0VariableChangeEquiv K _ ⟨1, r, s, t⟩).trans
      (eT.trans (ZMod.ringEquivCongr (by rw [hv])).toAddEquiv)))⟩


end Main

end

end GroundTheory.Arith.Abelian
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

section Generic

variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}

theorem map_add_of_triple {G : Type*} [AddCommGroup G] (Φ : V.toAffine.Point → G) (h0 : Φ 0 = 0)
    (hneg : ∀ P, Φ (-P) = -Φ P)
    (htri : ∀ {x₁ y₁ x₂ y₂ x₃ y₃ : F} (h₁ : V.toAffine.Nonsingular x₁ y₁)
      (h₂ : V.toAffine.Nonsingular x₂ y₂) (h₃ : V.toAffine.Nonsingular x₃ y₃),
      Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0 →
        Φ (.some _ _ h₁) + Φ (.some _ _ h₂) + Φ (.some _ _ h₃) = 0)
    (P Q : V.toAffine.Point) : Φ (P + Q) = Φ P + Φ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change Φ (0 + Q) = Φ 0 + Φ Q; rw [zero_add, h0, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change Φ (_ + 0) = _ + Φ 0; rw [add_zero, h0, add_zero]
  set S := Point.some _ _ h₁ + Point.some _ _ h₂ with hS
  rcases hSc : S with _ | ⟨x₃, y₃, h₃⟩
  · have hQ : Point.some _ _ h₂ = -Point.some _ _ h₁ := by
      have : S = 0 := hSc
      rw [hS] at this
      exact eq_neg_of_add_eq_zero_right this
    change Φ 0 = _
    rw [h0, hQ, hneg, add_neg_cancel]
  · have hn := (nonsingular_neg (W' := V.toAffine) x₃ y₃).2 h₃
    have ht := htri h₁ h₂ hn (by
      have e : (Point.some _ _ hn : V.toAffine.Point) = -Point.some _ _ h₃ := by
        rw [Point.neg_some]
      rw [e, ← hSc, hS]; abel)
    have e : (Point.some _ _ hn : V.toAffine.Point) = -Point.some _ _ h₃ := by
      rw [Point.neg_some]
    rw [e, hneg, add_neg_eq_zero] at ht
    exact ht.symm

end Generic

section Origin

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0)
include h3 h4 h6

theorem origin_eq {x y : F} (h : V.toAffine.Equation x y) :
    y ^ 2 + V.a₁ * x * y - V.a₂ * x ^ 2 = x ^ 3 := by
  rw [equation_iff, h3, h4, h6] at h
  linear_combination h

theorem origin_x_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  subst hx
  have he := origin_eq V h3 h4 h6 h.1
  have hy : y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linear_combination he)
  subst hy
  have := (nonsingular_zero (W := V.toAffine)).1 h
  rcases this.2 with h' | h'
  · exact h' h3
  · exact h' h4

theorem origin_nonsingular {x y : F} (h : V.toAffine.Equation x y) (hx : x ≠ 0) :
    V.toAffine.Nonsingular x y := by
  rw [nonsingular_iff']
  refine ⟨h, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hA, hB⟩ := hc
  have he := origin_eq V h3 h4 h6 h
  rw [h4] at hA
  rw [h3] at hB
  apply hx
  apply pow_eq_zero_iff (n := 3) (by norm_num) |>.1
  linear_combination (-x) * hA + (-y) * hB + 2 * he

end Origin

section Cusp

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) (α : F) (h1 : V.a₁ = -2 * α) (h2 : V.a₂ = -α ^ 2)

def cuspMap : V.toAffine.Point → F
  | 0 => 0
  | .some x y _ => x / (y - α * x)

include h3 h4 h6 h1 h2

theorem cusp_eq {x y : F} (h : V.toAffine.Equation x y) : (y - α * x) ^ 2 = x ^ 3 := by
  have := origin_eq V h3 h4 h6 h
  rw [h1, h2] at this
  linear_combination this

theorem cusp_den_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : y - α * x ≠ 0 := by
  intro h0
  apply origin_x_ne_zero V h3 h4 h6 h
  have := cusp_eq V h3 h4 h6 α h1 h2 h.1
  rw [h0] at this
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 (by linear_combination -this)

theorem cuspMap_neg (P : V.toAffine.Point) : cuspMap V α (-P) = -cuspMap V α P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [cuspMap]; rfl
  · rw [Point.neg_some]
    simp only [cuspMap, negY, h1, h3]
    rw [show -y - -2 * α * x - 0 - α * x = -(y - α * x) by ring, div_neg]

theorem cuspMap_triple {x₁ y₁ x₂ y₂ x₃ y₃ : F} (g₁ : V.toAffine.Nonsingular x₁ y₁)
    (g₂ : V.toAffine.Nonsingular x₂ y₂) (g₃ : V.toAffine.Nonsingular x₃ y₃)
    (hs : Point.some _ _ g₁ + Point.some _ _ g₂ + Point.some _ _ g₃ = 0) :
    cuspMap V α (.some _ _ g₁) + cuspMap V α (.some _ _ g₂) + cuspMap V α (.some _ _ g₃) = 0 := by
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_line_of_add_eq_zero g₁ g₂ g₃ hs
  have d1 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₁
  have d2 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₂
  have d3 := cusp_den_ne_zero V h3 h4 h6 α h1 h2 g₃
  simp only [cuspMap]
  rw [div_add_div _ _ d1 d2, div_add_div _ _ (mul_ne_zero d1 d2) d3, div_eq_zero_iff]
  left
  rw [h1, h2] at v1
  rw [h1, h3, h4] at v2
  rw [h3, h6] at v3
  rw [l1, l2, l3]
  linear_combination 3 * (ℓ - α) ^ 2 * v3 + 2 * (ℓ - α) * ν * v2 + ν ^ 2 * v1

def cuspHom : V.toAffine.Point →+ F :=
  AddMonoidHom.mk' (cuspMap V α) (map_add_of_triple (cuspMap V α) rfl
    (cuspMap_neg V h3 h4 h6 α h1 h2) (cuspMap_triple V h3 h4 h6 α h1 h2))

end Cusp

section Node

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) {L : Type*} [Field L] [Algebra F L] (α β : L)
  (hs : algebraMap F L V.a₁ = -(α + β)) (hp : algebraMap F L V.a₂ = -(α * β))

local notation "ι" => algebraMap F L

include h3 h4 h6 hs hp

theorem node_eq {x y : F} (h : V.toAffine.Equation x y) :
    (ι y - α * ι x) * (ι y - β * ι x) = ι x ^ 3 := by
  have := congrArg ι (origin_eq V h3 h4 h6 h)
  simp only [map_sub, map_add, map_mul, map_pow] at this
  rw [hs, hp] at this
  linear_combination this

theorem node_num_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : ι y - α * ι x ≠ 0 := by
  intro h0
  have := node_eq V h3 h4 h6 α β hs hp h.1
  rw [h0, zero_mul, eq_comm] at this
  exact origin_x_ne_zero V h3 h4 h6 h ((map_eq_zero _).1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this))

theorem node_den_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y) : ι y - β * ι x ≠ 0 := by
  intro h0
  have := node_eq V h3 h4 h6 α β hs hp h.1
  rw [h0, mul_zero, eq_comm] at this
  exact origin_x_ne_zero V h3 h4 h6 h ((map_eq_zero _).1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this))

def nodeVal : V.toAffine.Point → Lˣ
  | 0 => 1
  | .some x y h => Units.mk0 ((ι y - α * ι x) / (ι y - β * ι x))
      (div_ne_zero (node_num_ne_zero V h3 h4 h6 α β hs hp h) (node_den_ne_zero V h3 h4 h6 α β hs hp h))

theorem nodeVal_neg (P : V.toAffine.Point) :
    Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (-P)) =
      -Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [← ofMul_inv]
    congr 1
    rw [Point.neg_some]
    ext
    have hn := node_num_ne_zero V h3 h4 h6 α β hs hp h
    simp only [nodeVal, Units.val_mk0, Units.val_inv_eq_inv_val, negY, h3, map_sub, map_neg,
      map_mul, sub_zero, hs]
    rw [inv_div, div_eq_div_iff (by intro h0; apply hn; linear_combination -h0) hn]
    ring

theorem nodeVal_triple {x₁ y₁ x₂ y₂ x₃ y₃ : F} (g₁ : V.toAffine.Nonsingular x₁ y₁)
    (g₂ : V.toAffine.Nonsingular x₂ y₂) (g₃ : V.toAffine.Nonsingular x₃ y₃)
    (hsum : Point.some _ _ g₁ + Point.some _ _ g₂ + Point.some _ _ g₃ = 0) :
    Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ g₁)) +
      Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ g₂)) +
      Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ g₃)) = 0 := by
  rw [← ofMul_mul, ← ofMul_mul, ← ofMul_one]
  congr 1
  obtain ⟨ℓ, ν, l1, l2, l3, v1, v2, v3⟩ := exists_line_of_add_eq_zero g₁ g₂ g₃ hsum
  rw [h3, h4] at v2
  rw [h3, h6] at v3
  have w1 := congrArg ι v1
  have w2 := congrArg ι v2
  have w3 := congrArg ι v3
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_ofNat, hs, hp] at w1 w2 w3
  have k1 := congrArg ι l1
  have k2 := congrArg ι l2
  have k3 := congrArg ι l3
  simp only [map_add, map_mul] at k1 k2 k3
  have hN : (ι y₁ - α * ι x₁) * (ι y₂ - α * ι x₂) * (ι y₃ - α * ι x₃) = ι ν ^ 3 := by
    rw [k1, k2, k3]
    linear_combination (ι ℓ - α) ^ 3 * w3 + (ι ℓ - α) ^ 2 * ι ν * w2 + (ι ℓ - α) * ι ν ^ 2 * w1
  have hD : (ι y₁ - β * ι x₁) * (ι y₂ - β * ι x₂) * (ι y₃ - β * ι x₃) = ι ν ^ 3 := by
    rw [k1, k2, k3]
    linear_combination (ι ℓ - β) ^ 3 * w3 + (ι ℓ - β) ^ 2 * ι ν * w2 + (ι ℓ - β) * ι ν ^ 2 * w1
  have hD0 : (ι y₁ - β * ι x₁) * (ι y₂ - β * ι x₂) * (ι y₃ - β * ι x₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (node_den_ne_zero V h3 h4 h6 α β hs hp g₁)
      (node_den_ne_zero V h3 h4 h6 α β hs hp g₂)) (node_den_ne_zero V h3 h4 h6 α β hs hp g₃)
  ext
  simp only [nodeVal, Units.val_mul, Units.val_mk0, Units.val_one]
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq hD0, hN, hD]

def nodeHom : V.toAffine.Point →+ Additive Lˣ :=
  AddMonoidHom.mk' (fun P => Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp P))
    (map_add_of_triple (V := V) (fun P => Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp P)) rfl
      (nodeVal_neg V h3 h4 h6 α β hs hp) (nodeVal_triple V h3 h4 h6 α β hs hp))

theorem nodeHom_injective (hαβ : α ≠ β) : Function.Injective (nodeHom V h3 h4 h6 α β hs hp) := by
  rw [injective_iff_map_eq_zero]
  rintro (_ | ⟨x, y, h⟩) hP
  · rfl
  · exfalso
    change Additive.ofMul (nodeVal V h3 h4 h6 α β hs hp (.some _ _ h)) = Additive.ofMul 1 at hP
    have hv := congrArg Units.val (Additive.ofMul.injective hP)
    simp only [nodeVal, Units.val_mk0, Units.val_one] at hv
    rw [div_eq_one_iff_eq (node_den_ne_zero V h3 h4 h6 α β hs hp h)] at hv
    have hx : (α - β) * ι x = 0 := by linear_combination -hv
    rcases mul_eq_zero.1 hx with h0 | h0
    · exact hαβ (sub_eq_zero.1 h0)
    · exact origin_x_ne_zero V h3 h4 h6 h ((map_eq_zero _).1 h0)

end Node

section NodeSplit

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) (α β : F) (hs : algebraMap F F V.a₁ = -(α + β))
  (hp : algebraMap F F V.a₂ = -(α * β))
include h3 h4 h6 hs hp

theorem node_point_of_value {u : F} (hαβ : α ≠ β) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ x y : F, V.toAffine.Nonsingular x y ∧ (y - α * x) / (y - β * x) = u := by
  have hs' : V.a₁ = -(α + β) := hs
  have hp' : V.a₂ = -(α * β) := hp
  have h1u : (1 : F) - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu1)
  have hab : α - β ≠ 0 := sub_ne_zero.2 hαβ
  set t := (α - u * β) / (1 - u)
  have hta : t - α = u * (α - β) / (1 - u) := by simp only [t]; field_simp; ring
  have htb : t - β = (α - β) / (1 - u) := by simp only [t]; field_simp; ring
  have hx : (t - α) * (t - β) ≠ 0 := by
    rw [hta, htb]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hu0 hab) h1u) (div_ne_zero hab h1u)
  have he : V.toAffine.Equation ((t - α) * (t - β)) (t * ((t - α) * (t - β))) := by
    rw [equation_iff, h3, h4, h6, hs', hp']
    ring
  refine ⟨_, _, origin_nonsingular V h3 h4 h6 he hx, ?_⟩
  rw [show t * ((t - α) * (t - β)) - α * ((t - α) * (t - β)) = (t - α) * ((t - α) * (t - β)) by ring,
    show t * ((t - α) * (t - β)) - β * ((t - α) * (t - β)) = (t - β) * ((t - α) * (t - β)) by ring,
    mul_div_mul_right _ _ hx, hta, htb]
  field_simp

end NodeSplit

section Torus

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) (h3 : V.a₃ = 0)
  (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) {L : Type*} [Field L] [Algebra F L] (α β : L)
  (hs : algebraMap F L V.a₁ = -(α + β)) (hp : algebraMap F L V.a₂ = -(α * β)) (σ : L ≃ₐ[F] L)

def normOne : Subgroup Lˣ where
  carrier := {u | (u : L) * σ u = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at *
    linear_combination (b : L) * σ b * ha + hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at *
    rw [← mul_inv, ha, inv_one]

local notation "ι" => algebraMap F L

include h3 h4 h6 hs hp

theorem nodeVal_mem (hσ : σ α = β) (P : V.toAffine.Point) :
    nodeVal V h3 h4 h6 α β hs hp P ∈ normOne σ := by
  have hσβ : σ β = α := by
    have h1 : σ (α + β) = α + β := by
      rw [← neg_neg (α + β), ← hs, map_neg, AlgEquiv.commutes]
    rw [map_add, hσ] at h1
    linear_combination h1
  rcases P with _ | ⟨x, y, h⟩
  · simp [nodeVal, normOne]
  · simp only [normOne, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
      nodeVal, Units.val_mk0, map_div₀, map_sub, map_mul, AlgEquiv.commutes, hσ, hσβ]
    rw [div_mul_div_comm, mul_comm (ι y - β * ι x), div_self (mul_ne_zero
      (node_num_ne_zero V h3 h4 h6 α β hs hp h) (node_den_ne_zero V h3 h4 h6 α β hs hp h))]

def nodeTorusHom (hσ : σ α = β) : V.toAffine.Point →+ Additive (normOne σ) :=
  AddMonoidHom.mk' (fun P => Additive.ofMul ⟨nodeVal V h3 h4 h6 α β hs hp P,
    nodeVal_mem V h3 h4 h6 α β hs hp σ hσ P⟩) (fun P Q => by
      have := (nodeHom V h3 h4 h6 α β hs hp).map_add P Q
      change Additive.ofMul _ = Additive.ofMul _ + Additive.ofMul _ at this
      rw [← ofMul_mul] at this ⊢
      congr 1
      exact Subtype.ext (Additive.ofMul.injective this))

end Torus

end

end GroundTheory.Arith.Abelian
end
