import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ProductLValuesPolynomialBound

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory

theorem deg_epsI_empty {N : ℕ} : epsI (∅ : Finset (Fin N)) = 0 := by
  funext x; simp [epsI]

theorem deg_epsI_insert {N : ℕ} (I : Finset (Fin N)) (a : Fin N) (ha : a ∉ I) :
    epsI (insert a I) = epsI I + Pi.single a 1 := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [epsI, ha]
  · simp [epsI, hx]

theorem deg_hc_int {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (x : Fin N) :
    ∃ m : ℤ, (μ + epsI I) x - ((N : ℝ) - 1) / 2 = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 x
  by_cases hx : x ∈ I
  · refine ⟨m + 1, ?_⟩
    simp only [Pi.add_apply, epsI, if_pos hx]
    push_cast
    linarith
  · refine ⟨m, ?_⟩
    simp only [Pi.add_apply, epsI, if_neg hx]
    linarith

theorem deg_hc_diff {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (a b : Fin N) : ∃ m : ℤ, μ a - μ b = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 a
  obtain ⟨m', hm'⟩ := h.2 b
  refine ⟨m - m', ?_⟩
  push_cast
  linarith

theorem deg_hc_drop {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (a : Fin N)
    (hmax : ∀ x ∈ I, x < a) (h' : IsHCParam (μ + epsI (insert a I))) : IsHCParam (μ + epsI I) := by
  refine ⟨fun i j hij => ?_, deg_hc_int h I⟩
  have h1 := h.1 hij
  have h2 := h'.1 hij
  have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
  simp only [Pi.add_apply, epsI, Finset.mem_insert] at h2 ⊢
  by_cases hja : j = a
  · subst hja
    rw [if_neg ha]
    split_ifs <;> linarith
  · by_cases hia : i = a
    · subst hia
      have hj : j ∉ I := fun hh => lt_asymm hij (hmax j hh)
      rw [if_neg ha, if_neg hj]
      linarith
    · simpa [hja, hia] using h2

theorem deg_ind_up {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (Pr : Finset (Fin N) → Prop) (h0 : Pr ∅)
    (hs : ∀ I a, a ∉ I → IsHCParam (μ + epsI I) → IsHCParam (μ + epsI I + Pi.single a 1) → Pr I → Pr (insert a I)) :
    ∀ I, IsHCParam (μ + epsI I) → Pr I := by
  intro I
  induction I using Finset.induction_on_max with
  | empty => intro _; exact h0
  | insert a I hmax ih =>
    intro h'
    have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
    have h1 := deg_hc_drop hμ I a hmax h'
    refine hs I a ha h1 ?_ (ih h1)
    rw [add_assoc, ← deg_epsI_insert I a ha]
    exact h'

theorem deg_fdeg_pos {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) : 0 < fdegHC μ := by
  unfold fdegHC
  apply div_pos
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      abs_pos.2 (sub_ne_zero.2 (h.1 (Finset.mem_filter.1 hb).2).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have h1 : a.1 < b.1 := (Finset.mem_filter.1 hb).2
    have h2 : (a.1 : ℝ) < b.1 := by exact_mod_cast h1
    linarith

theorem deg_set_bound {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) : ∀ I : Finset (Fin N), IsHCParam (μ + epsI I) →
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + epsI I) / fdegHC μ ∧ fdegHC (μ + epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  have h0 := deg_fdeg_pos hμ
  refine deg_ind_up hμ _ ?_ ?_
  · rw [deg_epsI_empty, add_zero, div_self h0.ne']
    simp
  · intro I a ha h1 h2 ih
    obtain ⟨ihl, ihu⟩ := ih
    have hr := Formalism.QuantumDeterminants.fdegRatio N (μ + epsI I) a h1.1.injective (deg_hc_diff h1) h2.1.injective
    have hb := (Formalism.HermitianLatticeCounting.Final.ExpansionTerms.degStepBound N (μ + epsI I) a h1.1.injective (deg_hc_diff h1)).1 h2.1.injective
    rw [← hr] at hb
    have hN : (0 : ℝ) < N := by
      have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.2
      exact_mod_cast this
    have hp1 := deg_fdeg_pos h1
    have e : fdegHC (μ + epsI I + Pi.single a 1) / fdegHC μ =
        (fdegHC (μ + epsI I) / fdegHC μ) * (fdegHC (μ + epsI I + Pi.single a 1) / fdegHC (μ + epsI I)) := by
      field_simp
    rw [deg_epsI_insert I a ha, ← add_assoc, Finset.card_insert_of_notMem ha, pow_succ, e, mul_inv]
    have hq : 0 ≤ fdegHC (μ + epsI I) / fdegHC μ := (div_pos hp1 h0).le
    constructor
    · refine mul_le_mul ihl ?_ (by positivity) hq
      rw [← one_div]; exact hb.1
    · exact mul_le_mul ihu hb.2 (le_trans (by positivity) hb.1) (by positivity)

theorem deg_set_bound' {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (I : Finset (Fin N)) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (h' : IsHCParam (μ + s • epsI I)) :
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + s • epsI I) / fdegHC μ ∧ fdegHC (μ + s • epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  rcases hs with rfl | rfl
  · rw [one_smul] at h' ⊢
    exact deg_set_bound hμ I h'
  · have e : μ + (-1 : ℝ) • epsI I + epsI I = μ := by
      rw [neg_one_smul, neg_add_cancel_right]
    have h := deg_set_bound h' I (by rw [e]; exact hμ)
    rw [e] at h
    have h0 := deg_fdeg_pos hμ
    have h1 := deg_fdeg_pos h'
    have hx : 0 < fdegHC μ / fdegHC (μ + (-1 : ℝ) • epsI I) := div_pos h0 h1
    rw [← inv_div (fdegHC μ) (fdegHC (μ + (-1 : ℝ) • epsI I))]
    refine ⟨inv_anti₀ hx h.2, ?_⟩
    have h5 := inv_anti₀ (lt_of_lt_of_le (by
      have := hx
      exact inv_pos.2 (lt_of_lt_of_le hx h.2)) le_rfl) h.1
    rwa [inv_inv] at h5

def deg_VandLine (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (I : Finset (Fin (2 * D.R.rS + D.R.k + 1))) (s : ℝ), (s = 1 ∨ s = -1) →
        ∀ A' : LocS W, GoodS D (lam' + s • epsI I) A' →
          A'.deg / A.deg = fdegHC (lam' + s • epsI I) / fdegHC lam'

theorem deg_cast_r (D : D7) : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]

theorem degree_ratio_one_of_vandermonde (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ)
    (h : deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1) : DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 1 := by
  intro hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA'
  rw [h hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA', one_mul, Real.rpow_natCast, ← deg_cast_r]
  exact (deg_set_bound' hA.1 I s hs hA'.1).2

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory
open scoped InnerProductSpace ENNReal Matrix

section Gen

variable {n : ℕ} {ε : Fin n → Bool}

theorem deg_fdegOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (w : H)
    (h : IsFdeg μ σ d) (hw : w ≠ 0) : fdegOf μ σ w = d := by
  obtain ⟨hd, hall⟩ := h
  have hint := (hall w w w w).2
  have e1 : ∀ g : Formalism.REAL.UJ ε, coefOn σ w w g * star (coefOn σ w w g) =
      (((‖coefOn σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    intro g
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast
    rfl
  simp only [e1] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have key : (∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ : ℝ) = ‖w‖ ^ 4 / d := by
    have h3 : ((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / (d : ℂ)) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      push_cast
      ring
    have h2 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := hint.trans h3
    exact_mod_cast h2
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  unfold fdegOf
  rw [key]
  field_simp

theorem deg_fdegOf_equiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (m : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)) (v : H) : fdegOf m σ v = fdegOf m σ' (U v) := by
  have hi : ∀ g : Formalism.REAL.UJ ε, coefOn σ' (U v) (U v) g = coefOn σ v v g := by
    intro g
    unfold coefOn
    rw [← hU (umat g) (by exact g.2) v, U.inner_map_map]
  unfold fdegOf
  simp only [hi, U.norm_map]

theorem deg_fdegOf_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : NNReal) (hc : 0 < c)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) :
    fdegOf (Formalism.REAL.muG ε) σ v = (c : ℝ) * fdegOf (((c : NNReal) : ℝ≥0∞) • Formalism.REAL.muG ε) σ v := by
  unfold fdegOf
  rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← mul_div_assoc, mul_div_mul_left _ _ hc']

theorem deg_inner_isom {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  let T' : H →ₗᵢ[ℂ] H := { toLinearMap := T.toLinearMap, norm_map' := hT }
  T'.inner_map_map x y

theorem deg_UJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq] at *
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc] at *
  rw [← Matrix.mul_assoc _ a b, ← Matrix.mul_assoc aᴴ _ b, ha]
  exact hb

end Gen

theorem deg_isFdeg_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (P P' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayley k r ε P) (hP' : IsCayley k r ε P')
    (hrep : IsURepOn (UJset ε) (fun g => σ (P'⁻¹ * g * P'))) (d : ℝ)
    (hd : IsFdeg m (fun g => σ (P⁻¹ * g * P)) d) : IsFdeg m (fun g => σ (P'⁻¹ * g * P')) d := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hPu', hPJ'⟩ := hP'
  obtain ⟨⟨hσ1, hσmul⟩, hiso, -⟩ := hrep
  have h1 : σ (P'⁻¹ * 1 * P') = 1 := hσ1
  have hm : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P'⁻¹ * (a * b) * P') = (σ (P'⁻¹ * a * P')).comp (σ (P'⁻¹ * b * P')) := hσmul
  have hiso' : ∀ g ∈ UJset ε, ∀ x : H, ‖σ (P'⁻¹ * g * P') x‖ = ‖x‖ := hiso
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hdet' : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det P').1 hPu'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPPi' : P' * P'⁻¹ = 1 := Matrix.mul_nonsing_inv P' hdet'
  have hPiP' : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul P' hdet'
  have hmem : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Aᴴ * Formalism.REAL.Jm ε * A = Formalism.QuantumDeterminants.Hpk k r → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.QuantumDeterminants.Hpk k r →
      B * B⁻¹ = 1 → A * B⁻¹ ∈ UJset ε := by
    intro A B hA hB hBB
    show (A * B⁻¹)ᴴ * Formalism.REAL.Jm ε * (A * B⁻¹) = Formalism.REAL.Jm ε
    have hB1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc (A * B⁻¹)ᴴ * Formalism.REAL.Jm ε * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * B⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm ε * B) * B⁻¹ := by rw [hA, hB]
      _ = ((B⁻¹)ᴴ * Bᴴ) * Formalism.REAL.Jm ε * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hB1, hBB, Matrix.one_mul, Matrix.mul_one]
  have hQ : P * P'⁻¹ ∈ UJset ε := hmem P P' hPJ hPJ' hPPi'
  have hQi : P' * P⁻¹ ∈ UJset ε := hmem P' P hPJ' hPJ hPPi
  have hQQi : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹, hPiP', Matrix.one_mul, hPPi]
  have hBC : ∀ x : H, σ (P'⁻¹ * (P * P'⁻¹) * P') (σ (P'⁻¹ * (P' * P⁻¹) * P') x) = x := by
    intro x
    have e := congrArg (fun T : H →L[ℂ] H => T x) (hm _ hQ _ hQi)
    simp only [ContinuousLinearMap.comp_apply, hQQi, h1, one_apply_eq_self] at e
    exact e.symm
  have hcoef : ∀ a b : H, coefOn (ε := ε) (fun g => σ (P'⁻¹ * g * P')) a b =
      coefOn (ε := ε) (fun g => σ (P⁻¹ * g * P)) (σ (P'⁻¹ * (P' * P⁻¹) * P') a)
        (σ (P'⁻¹ * (P' * P⁻¹) * P') b) := by
    intro a b
    funext g
    unfold coefOn
    beta_reduce
    have hg : umat g ∈ UJset ε := by exact g.2
    have hconj : P⁻¹ * umat g * P = P'⁻¹ * (P' * P⁻¹ * umat g * (P * P'⁻¹)) * P' := by
      simp only [← Matrix.mul_assoc, hPiP', Matrix.one_mul]
      rw [Matrix.mul_assoc _ P'⁻¹ P', hPiP', Matrix.mul_one]
    rw [hconj, hm _ (deg_UJ_mul hQi hg) _ hQ, hm _ hQi _ hg]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hBC a, deg_inner_isom _ (hiso' _ hQi)]
  refine ⟨hd.1, fun v w v' w' => ?_⟩
  have hv := hd.2 (σ (P'⁻¹ * (P' * P⁻¹) * P') v) (σ (P'⁻¹ * (P' * P⁻¹) * P') w)
    (σ (P'⁻¹ * (P' * P⁻¹) * P') v') (σ (P'⁻¹ * (P' * P⁻¹) * P') w')
  rw [hcoef v w, hcoef v' w']
  refine ⟨hv.1, ?_⟩
  rw [hv.2, deg_inner_isom _ (hiso' _ hQi), deg_inner_isom _ (hiso' _ hQi)]

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory
open scoped InnerProductSpace ENNReal

def DegreeL2RangeHypothesis (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (τ : D.what₂.Tau) (ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), IsHCParam ν →
    l1dist ν (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) ν σ → ∀ v w : H, IsKFin (epsSH D.R) σ v → IsKFin (epsSH D.R) σ w →
        MemLp (fun g : Formalism.REAL.UJ (epsSH D.R) => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG (epsSH D.R))

theorem deg_hc_add_single {n : ℕ} {μ : Fin n → ℝ} (h : IsHCParam μ) (hg : AllGaps μ 2) (s : Fin n) :
    IsHCParam (μ + Pi.single s 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h1 := h.1 hab
    have h2 := hg a b (ne_of_lt hab)
    rw [abs_of_pos (by linarith)] at h2
    have ha : (0 : ℝ) ≤ (Pi.single s (1 : ℝ) : Fin n → ℝ) a := by by_cases e : a = s <;> simp [Pi.single_apply, e]
    have hb : (Pi.single s (1 : ℝ) : Fin n → ℝ) b ≤ 1 := by by_cases e : b = s <;> simp [Pi.single_apply, e]
    simp only [Pi.add_apply]
    linarith
  · obtain ⟨m, hm⟩ := h.2 a
    by_cases e : a = s
    · subst e
      exact ⟨m + 1, by simp only [Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m, by simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]; exact hm⟩

theorem deg_chain {n : ℕ} {ε : Fin n → Bool} (D : D7) (h18 : OnePlaceEstimates.adm18 D) (h90 : OnePlaceEstimates.FormalDegreeRatioAlt D) {μ : Fin n → ℝ}
    (hμ : IsHCParam μ) (hgap : ∀ I : Finset (Fin n), AllGaps (μ + epsI I) 2)
    (hL2 : ∀ I : Finset (Fin n), IsHCParam (μ + epsI I) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε (μ + epsI I) σ →
      ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
        MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε))
    (H0 : Type) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] [CompleteSpace H0]
    (σ0 : Matrix (Fin n) (Fin n) ℂ → (H0 →L[ℂ] H0)) (hDS0 : IsDS ε μ σ0) (v0 : H0) (hv0 : v0 ≠ 0)
    (hd0 : fdegOf (Formalism.REAL.muG ε) σ0 v0 ≠ 0) :
    ∀ I : Finset (Fin n), IsHCParam (μ + epsI I) →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), v ≠ 0 ∧ IsDS ε (μ + epsI I) σ ∧
          fdegOf (Formalism.REAL.muG ε) σ v / fdegOf (Formalism.REAL.muG ε) σ0 v0 = fdegHC (μ + epsI I) / fdegHC μ := by
  have hf0 := deg_fdeg_pos hμ
  refine deg_ind_up hμ _ ?_ ?_
  · refine ⟨H0, inferInstance, inferInstance, inferInstance, σ0, v0, hv0, ?_, ?_⟩
    · rw [deg_epsI_empty, add_zero]; exact hDS0
    · rw [deg_epsI_empty, add_zero, div_self hd0, div_self hf0.ne']
  · intro I a ha h1 h2 ih
    obtain ⟨H, i1, i2, i3, σ, v, hv, hDS, hr⟩ := ih
    obtain ⟨X, hX⟩ := h18 n ε (μ + epsI I) H σ h1 hDS (fun s => deg_hc_add_single h1 (hgap I) s)
    have haS : a ∈ X.Sm := (hX a).2 h2
    have hDSa := (X.ds a haS).2
    haveI : Nontrivial (X.Hs a) := hDSa.2.1
    obtain ⟨vs, hvs⟩ := exists_ne (0 : X.Hs a)
    have h9 := h90 n ε (μ + epsI I) H σ X h1 hDS (hL2 I h1 H σ hDS) a haS v vs hv hvs
    rw [← Formalism.QuantumDeterminants.fdegRatio n (μ + epsI I) a h1.1.injective (deg_hc_diff h1) h2.1.injective] at h9
    have hp1 := deg_fdeg_pos h1
    have hp2 := deg_fdeg_pos h2
    have hne : fdegOf (Formalism.REAL.muG ε) σ v ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hr
      exact (div_pos hp1 hf0).ne hr
    refine ⟨X.Hs a, inferInstance, inferInstance, inferInstance, X.σs a, vs, hvs, ?_, ?_⟩
    · rw [deg_epsI_insert I a ha, ← add_assoc]; exact hDSa
    · rw [deg_epsI_insert I a ha, ← add_assoc]
      calc fdegOf (Formalism.REAL.muG ε) (X.σs a) vs / fdegOf (Formalism.REAL.muG ε) σ0 v0
          = (fdegOf (Formalism.REAL.muG ε) (X.σs a) vs / fdegOf (Formalism.REAL.muG ε) σ v) *
              (fdegOf (Formalism.REAL.muG ε) σ v / fdegOf (Formalism.REAL.muG ε) σ0 v0) := by field_simp
        _ = (fdegHC (μ + epsI I + Pi.single a 1) / fdegHC (μ + epsI I)) * (fdegHC (μ + epsI I) / fdegHC μ) := by
            rw [h9, hr]
        _ = fdegHC (μ + epsI I + Pi.single a 1) / fdegHC μ := by field_simp

theorem deg_datum (D : D7) {W : LocW D.R.k D.R.rS} {ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (hA : GoodS D ν A) : ∃ P : MatKR D.R.k D.R.rS, IsDS (epsSH D.R) ν (fun g => A.σ (P⁻¹ * g * P)) ∧
      ∀ v : A.H, v ≠ 0 → fdegOf (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (P⁻¹ * g * P)) v =
        ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ) * A.deg := by
  obtain ⟨_, ⟨P', hP', hDS⟩, _, _, _, _, _, _, _, _, P, hP, hF⟩ := hA
  refine ⟨P', hDS, fun v hv => ?_⟩
  have h1 := deg_isFdeg_cayley _ A.σ P P' hP hP'.1 hDS.2.2.1 A.deg hF
  rw [deg_fdegOf_smul (D.s.cdScale _ (epsSH D.R)) (D.s.cdScale_pos _ _), deg_fdegOf _ _ A.deg v h1 hv]

end Formalism.MainNotions.BridgeLemma₂

end
end
