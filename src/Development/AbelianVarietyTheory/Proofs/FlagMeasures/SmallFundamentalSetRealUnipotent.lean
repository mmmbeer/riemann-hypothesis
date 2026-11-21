import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiiIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubquotientCoveringRadiusRealPlaces

section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.NilLie

open GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.UG

section Algebra

variable {K : Type} [Field K] {n : ℕ} {s : K →+* K} {J : Matrix (Fin n) (Fin n) K}
  {W : Submodule K (Fin n → K)}

def ex (Y : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := 1 + Y + (2 : K)⁻¹ • (Y * Y)

theorem ext_mulVec {M N : Matrix (Fin n) (Fin n) K} (h : ∀ u, M *ᵥ u = N *ᵥ u) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun u => by simpa using h u)

theorem perp_add {u u' : Fin n → K} (h : u ∈ perpSet s J W) (h' : u' ∈ perpSet s J W) :
    u + u' ∈ perpSet s J W := fun w hw => by
  have h1 := h w hw
  have h2 := h' w hw
  rw [GlobalTheory.CoverRadiiEq.hform_eq_dot] at *
  rw [mulVec_add, dotProduct_add, h1, h2, add_zero]

theorem perp_smul (c : K) {u : Fin n → K} (h : u ∈ perpSet s J W) :
    c • u ∈ perpSet s J W := fun w hw => by
  have h1 := h w hw
  rw [GlobalTheory.CoverRadiiEq.hform_eq_dot] at *
  rw [mulVec_smul, dotProduct_smul, h1, smul_zero]

theorem cT_add (M N : Matrix (Fin n) (Fin n) K) : cT s (M + N) = cT s M + cT s N := by
  ext i j; simp [cT]

theorem cT_sub (M N : Matrix (Fin n) (Fin n) K) : cT s (M - N) = cT s M - cT s N := by
  ext i j; simp [cT]

theorem cT_smul (c : K) (M : Matrix (Fin n) (Fin n) K) : cT s (c • M) = s c • cT s M := by
  ext i j; simp [cT]

theorem cT_zero : cT s (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  ext i j; simp [cT]

theorem skew_eq {Y : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) : cT s Y * J = -(J * Y) :=
  eq_neg_of_add_eq_zero_left ((GlobalTheory.CoverRadiiEq.skew_iff s J Y).2 h.1)

theorem nil_add {Y Y' : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) (h' : InNil s J W Y') :
    InNil s J W (Y + Y') := by
  refine ⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [cT_add, add_mul, skew_eq h, skew_eq h', mul_add]; abel
  · rw [add_mulVec]; exact perp_add (h.2.1 u) (h'.2.1 u)
  · rw [add_mulVec]; exact W.add_mem (h.2.2.1 u hu) (h'.2.2.1 u hu)
  · rw [add_mulVec, h.2.2.2 u hu, h'.2.2.2 u hu, add_zero]

theorem nil_smul {c : K} (hc : s c = c) {Y : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) :
    InNil s J W (c • Y) := by
  refine ⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [cT_smul, hc, smul_mul_assoc, skew_eq h, mul_smul_comm, smul_neg, neg_add_cancel]
  · rw [smul_mulVec]; exact perp_smul c (h.2.1 u)
  · rw [smul_mulVec]; exact W.smul_mem c (h.2.2.1 u hu)
  · rw [smul_mulVec, h.2.2.2 u hu, smul_zero]

theorem nil_neg {Y : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) : InNil s J W (-Y) := by
  simpa using nil_smul (c := -1) (by simp) h

theorem nil_sub {Y Y' : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) (h' : InNil s J W Y') :
    InNil s J W (Y - Y') := by
  rw [sub_eq_add_neg]; exact nil_add h (nil_neg h')

theorem cen_add {Y Y' : Matrix (Fin n) (Fin n) K} (h : InCen s J W Y) (h' : InCen s J W Y') :
    InCen s J W (Y + Y') :=
  ⟨nil_add h.1 h'.1, fun u hu => by rw [add_mulVec, h.2 u hu, h'.2 u hu, add_zero]⟩

theorem cen_smul {c : K} (hc : s c = c) {Y : Matrix (Fin n) (Fin n) K} (h : InCen s J W Y) :
    InCen s J W (c • Y) :=
  ⟨nil_smul hc h.1, fun u hu => by rw [smul_mulVec, h.2 u hu, smul_zero]⟩

theorem cen_sub {Y Y' : Matrix (Fin n) (Fin n) K} (h : InCen s J W Y) (h' : InCen s J W Y') :
    InCen s J W (Y - Y') :=
  ⟨nil_sub h.1 h'.1, fun u hu => by rw [sub_mulVec, h.2 u hu, h'.2 u hu, sub_zero]⟩

theorem isInStabilizerNilradicalLie_triple_mul_eq_zero {a b c : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) (hb : InNil s J W b)
    (hc : InNil s J W c) : a * (b * c) = 0 :=
  ext_mulVec fun u => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, zero_mulVec]
    exact ha.2.2.2 _ (hb.2.2.1 _ (hc.2.1 u))

theorem cen_mul_nil {Z Y : Matrix (Fin n) (Fin n) K} (hZ : InCen s J W Z) (hY : InNil s J W Y) :
    Z * Y = 0 :=
  ext_mulVec fun u => by
    rw [← mulVec_mulVec, zero_mulVec]
    exact hZ.2 _ (hY.2.1 u)

theorem nil_mul_cen (hJ : IsUnit J) {Z Y : Matrix (Fin n) (Fin n) K} (hY : InNil s J W Y)
    (hZ : InCen s J W Z) : Y * Z = 0 := by
  have h : cT s (Z * Y) * J = J * (Y * Z) := by
    rw [cT_mul, mul_assoc, skew_eq hZ.1, mul_neg, ← mul_assoc, skew_eq hY, neg_mul, neg_neg, mul_assoc]
  rw [cen_mul_nil hZ hY, cT_zero, zero_mul] at h
  exact hJ.mul_right_eq_zero.1 h.symm

theorem cen_comm {a b : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) (hb : InNil s J W b) :
    InCen s J W (a * b - b * a) := by
  have h0 : ∀ u ∈ perpSet s J W, (a * b - b * a) *ᵥ u = 0 := fun u hu => by
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ha.2.2.2 _ (hb.2.2.1 _ hu),
      hb.2.2.2 _ (ha.2.2.1 _ hu), sub_zero]
  refine ⟨⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩, h0⟩
  · rw [cT_sub, cT_mul, cT_mul, sub_mul, mul_assoc, mul_assoc, skew_eq ha, skew_eq hb, mul_neg, mul_neg,
      ← mul_assoc, ← mul_assoc, skew_eq ha, skew_eq hb]
    noncomm_ring
  · rw [sub_eq_add_neg, add_mulVec, ← neg_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact perp_add (ha.2.1 _) ((nil_neg hb).2.1 _)
  · rw [h0 u hu]; exact W.zero_mem
  · rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ha.2.2.2 u hu, hb.2.2.2 u hu, mulVec_zero,
      mulVec_zero, sub_zero]

variable [CharZero K]

theorem map_half : s (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]

theorem ex_mul_ex {a b : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) (hb : InNil s J W b) :
    ex a * ex b = 1 + a + b + (2 : K)⁻¹ • (a * a) + (2 : K)⁻¹ • (b * b) + a * b := by
  have h1 := isInStabilizerNilradicalLie_triple_mul_eq_zero ha ha hb
  have h2 := isInStabilizerNilradicalLie_triple_mul_eq_zero ha hb hb
  simp only [ex, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc, h1, h2,
    mul_zero, smul_zero, add_zero]
  abel

theorem ex_mul_ex_neg {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) : ex a * ex (-a) = 1 := by
  rw [ex_mul_ex ha (nil_neg ha)]
  simp only [neg_mul, mul_neg, neg_neg]
  module

theorem ex_neg_mul_ex {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) : ex (-a) * ex a = 1 := by
  simpa using ex_mul_ex_neg (nil_neg ha)

theorem ex_add_cen (hJ : IsUnit J) {Y Z : Matrix (Fin n) (Fin n) K} (hY : InNil s J W Y)
    (hZ : InCen s J W Z) : ex (Y + Z) = ex Y + Z := by
  simp only [ex, add_mul, mul_add, cen_mul_nil hZ hY, nil_mul_cen hJ hY hZ, cen_mul_nil hZ hZ.1, add_zero]
  abel

theorem ex_mul_ex_cen (hJ : IsUnit J) {Y Z : Matrix (Fin n) (Fin n) K} (hY : InNil s J W Y)
    (hZ : InCen s J W Z) : ex Y * ex Z = ex (Y + Z) := by
  rw [ex_add_cen hJ hY hZ, ex_mul_ex hY hZ.1, nil_mul_cen hJ hY hZ, cen_mul_nil hZ hZ.1, ex]
  simp only [smul_zero, add_zero]
  abel

theorem ex_factor (hJ : IsUnit J) {Y₀ A Z₁ Z' : Matrix (Fin n) (Fin n) K} (h₀ : InNil s J W Y₀)
    (hA : InNil s J W A) (h₁ : InCen s J W Z₁) (h' : InCen s J W Z') :
    ex (Y₀ + A + (Z₁ + Z' - (2 : K)⁻¹ • (A * Y₀ - Y₀ * A))) = ex (Y₀ + Z₁) * ex A * ex Z' := by
  rw [ex_add_cen hJ (nil_add h₀ hA) (cen_sub (cen_add h₁ h') (cen_smul map_half (cen_comm hA h₀))),
    mul_assoc, ex_mul_ex_cen hJ hA h', ex_mul_ex (nil_add h₀ h₁.1) (nil_add hA h'.1), ex]
  simp only [add_mul, mul_add, cen_mul_nil h₁ h₀, cen_mul_nil h₁ hA, cen_mul_nil h₁ h₁.1,
    cen_mul_nil h₁ h'.1, cen_mul_nil h' hA, cen_mul_nil h' h'.1, nil_mul_cen hJ h₀ h₁,
    nil_mul_cen hJ h₀ h', nil_mul_cen hJ hA h', add_zero]
  module

theorem ex_unitary {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) : cT s (ex a) * J * ex a = J := by
  have h : cT s (ex a) * J = J * ex (-a) := by
    rw [ex, cT_add, cT_add, cT_one, cT_smul, map_half, cT_mul, add_mul, add_mul, smul_mul_assoc, mul_assoc,
      skew_eq ha, mul_neg, ← mul_assoc, skew_eq ha, ex]
    simp only [mul_add, neg_mul, mul_neg, neg_neg, one_mul, mul_one, mul_smul_comm, mul_assoc]
  rw [h, mul_assoc, ex_neg_mul_ex ha, mul_one]

theorem ex_unip {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) :
    (∀ x ∈ W, (ex a - 1) *ᵥ x = 0) ∧ (∀ y ∈ perpSet s J W, (ex a - 1) *ᵥ y ∈ W) ∧
      ∀ y, (ex a - 1) *ᵥ y ∈ perpSet s J W := by
  have h : ∀ y, (ex a - 1) *ᵥ y = a *ᵥ y + (2 : K)⁻¹ • (a *ᵥ (a *ᵥ y)) := fun y => by
    rw [mulVec_mulVec, ← smul_mulVec, ← add_mulVec, ex]; congr 1; abel
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y => ?_⟩
  · rw [h, ha.2.2.2 x hx]; simp
  · rw [h, ha.2.2.2 _ (ha.2.2.1 y hy)]; simpa using ha.2.2.1 y hy
  · rw [h]; exact perp_add (ha.2.1 _) (perp_smul _ (ha.2.1 _))

theorem exists_log {g : Matrix (Fin n) (Fin n) K} (hU : cT s g * J * g = J)
    (h : (∀ x ∈ W, (g - 1) *ᵥ x = 0) ∧ (∀ y ∈ perpSet s J W, (g - 1) *ᵥ y ∈ W) ∧
      ∀ y, (g - 1) *ᵥ y ∈ perpSet s J W) : ∃ Y, InNil s J W Y ∧ ex Y = g := by
  obtain ⟨N, rfl⟩ : ∃ N, g = 1 + N := ⟨g - 1, by abel⟩
  rw [add_sub_cancel_left] at h
  have h3 : N * (N * N) = 0 := ext_mulVec fun u => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, zero_mulVec]
    exact h.1 _ (h.2.1 _ (h.2.2 u))
  have hv : ∀ y, (N - (2 : K)⁻¹ • (N * N)) *ᵥ y = N *ᵥ y + (-(2 : K)⁻¹) • (N *ᵥ (N *ᵥ y)) := fun y => by
    rw [mulVec_mulVec, ← smul_mulVec, ← add_mulVec, neg_smul, sub_eq_add_neg]
  have hinv : (1 + N) * (1 - N + N * N) = 1 := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, h3]; abel
  have hN : cT s N * J = J * (N * N - N) := by
    have h1 : cT s (1 + N) * J = J * (1 - N + N * N) := by
      conv_rhs => rw [← hU]
      rw [mul_assoc, hinv, mul_one]
    rw [cT_add, cT_one, add_mul, one_mul] at h1
    rw [eq_sub_of_add_eq' h1]; noncomm_ring
  refine ⟨N - (2 : K)⁻¹ • (N * N),
    ⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩, ?_⟩
  · rw [cT_sub, cT_smul, map_half, cT_mul, sub_mul, smul_mul_assoc, mul_assoc, hN, ← mul_assoc, hN]
    simp only [mul_sub, sub_mul, mul_assoc, h3, mul_zero, mul_smul_comm]
    module
  · rw [hv]; exact perp_add (h.2.2 _) (perp_smul _ (h.2.2 _))
  · rw [hv, h.1 _ (h.2.1 u hu)]; simpa using h.2.1 u hu
  · rw [hv, h.1 u hu]; simp
  · simp only [ex, mul_sub, sub_mul, mul_assoc, h3, mul_zero, mul_smul_comm, smul_mul_assoc]
    module

end Algebra

section Complex

variable {n : ℕ}

theorem exp_eq_ex {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y * (Y * Y) = 0) : NormedSpace.exp Y = ex Y := by
  have h3 : Y ^ 3 = 0 := by rw [pow_succ', pow_two, h]
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  dsimp only
  rw [tsum_eq_sum (s := range 3)]
  · simp [Finset.sum_range_succ, ex, pow_two, Nat.factorial]
  · intro k hk
    have : 3 ≤ k := by simpa using hk
    rw [pow_eq_zero_of_le this h3, smul_zero]

theorem ex_conj {G Gi : Matrix (Fin n) (Fin n) ℂ} (h : G * Gi = 1) (h' : Gi * G = 1)
    (Y : Matrix (Fin n) (Fin n) ℂ) : ex (Gi * Y * G) = Gi * ex Y * G := by
  have : Gi * Y * G * (Gi * Y * G) = Gi * (Y * Y) * G := by
    calc _ = Gi * Y * (G * Gi) * Y * G := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc, one_mul]
  simp only [ex, this, mul_add, add_mul, mul_one, h', mul_smul_comm, smul_mul_assoc]

theorem exp_conj {G Gi : Matrix (Fin n) (Fin n) ℂ} (h : G * Gi = 1) (h' : Gi * G = 1)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y * (Y * Y) = 0) :
    NormedSpace.exp (Gi * Y * G) = Gi * ex Y * G := by
  rw [exp_eq_ex, ex_conj h h']
  calc _ = Gi * Y * (G * Gi) * Y * (G * Gi) * Y * G := by simp only [mul_assoc]
    _ = Gi * (Y * (Y * Y)) * G := by rw [h]; simp only [mul_assoc, one_mul]
    _ = 0 := by rw [hY, mul_zero, zero_mul]

theorem cT_conj (M : Matrix (Fin n) (Fin n) ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [cT]

theorem hs_smul (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : hs (c • M) = ‖c‖ ^ 2 * hs M := by
  simp [hs, Finset.mul_sum, mul_pow]

end Complex

section Point

variable (I : AutInst)

theorem normAt_smul (x : I.GA) (c : ℝ) (hc : 0 ≤ c) (D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :
    normAt I x (fun v => (c : ℂ) • D v) = c * normAt I x D := by
  unfold normAt
  simp only [mul_smul_comm, smul_mul_assoc, hs_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem P_mul_inv (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem inv_mul_P (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (u : Formalism.REAL.UJ ε) : uMat u * uMat u⁻¹ = 1 := by
  simp [uMat]

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (u : Formalism.REAL.UJ ε) : uMat u⁻¹ * uMat u = 1 := by
  simp [uMat]

theorem frame_mul (x : I.GA) (v : InfinitePlace I.F) :
    I.P v * uMat (x.1 v) * (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) = 1 := by
  rw [mul_assoc, ← mul_assoc (uMat (x.1 v)), uMat_mul_inv, one_mul, P_mul_inv]

theorem mul_frame (x : I.GA) (v : InfinitePlace I.F) :
    uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * (I.P v * uMat (x.1 v)) = 1 := by
  rw [mul_assoc, ← mul_assoc (I.P v)⁻¹, inv_mul_P, one_mul, uMat_inv_mul]

theorem isUnit_Jv (v : InfinitePlace I.F) : IsUnit (I.J.map (I.φ v)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have := (I.φ v).map_det I.J
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact (map_ne_zero _).2 I.J_det

theorem inG_frame (x : I.GA) (v : InfinitePlace I.F) {W : Submodule ℂ (Fin I.n → ℂ)}
    {A : Matrix (Fin I.n) (Fin I.n) ℂ} (hA : InNil (starRingEnd ℂ) (I.J.map (I.φ v)) W A) :
    inG (I.ε v) (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A * (I.P v * uMat (x.1 v))) := by
  have hx : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  have h0 : (I.P v * uMat (x.1 v))ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v)) = Jm (I.ε v) := by
    rw [← hx, ← I.P_spec v, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h1 := frame_mul I x v
  have h2 := skew_eq hA
  rw [cT_conj] at h2
  unfold inG
  rw [← h0]
  generalize I.P v * uMat (x.1 v) = G at *
  generalize uMat (x.1 v)⁻¹ * (I.P v)⁻¹ = Gi at *
  calc _ = Gᴴ * Aᴴ * (G * Gi)ᴴ * I.J.map (I.φ v) * G + Gᴴ * I.J.map (I.φ v) * (G * Gi) * A * G := by
        simp only [conjTranspose_mul, mul_assoc]
    _ = Gᴴ * (Aᴴ * I.J.map (I.φ v)) * G + Gᴴ * (I.J.map (I.φ v) * A) * G := by
        rw [h1]; simp only [conjTranspose_one, mul_one, mul_assoc]
    _ = 0 := by rw [h2]; simp

end Point

end GlobalTheory.NilLie
end
end

section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotentRadical_mem_adelic : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E) → ∃ a ∈ I.GFset ∩ I.NA W, (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧ I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  first | exact @GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | exact GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | (intros; apply GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic <;> assumption)
end

section
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PointLattice

theorem conj_mulVec_eq_smul (I : AutInst) (x : I.GA) (c : ℕ) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (hM : ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, M *ᵥ y = (c : I.E) • z)
    (w : Fin I.n → I.E ⊗[I.F] Af I.F) (hw : w ∈ I.Lf) :
    ∃ z ∈ I.Lf, (I.fmat x.2⁻¹ * M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x.2) *ᵥ w =
      (c : I.E ⊗[I.F] Af I.F) • z := by
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    rw [Set.image_eq_range]
    rfl
  have hfin := Module.Finite.iff_fg.2 I.L_fg
  have hu := Formalism.UG.P.csSpan_back Formalism.UG.P.csGlob_intAdApprox I.L hfin I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (I.fmat x.2 *ᵥ w)
    (by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]; exact e1.symm ▸ hw)
  rw [← lamX_eq_globLat] at hu
  rw [← mulVec_mulVec]
  generalize I.fmat x.2 *ᵥ w = u at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨z, hz, e⟩ := hM y hy
    refine ⟨_, (GlobalTheory.Count.Test.mem_lamX I x z).1 hz, ?_⟩
    rw [← mulVec_mulVec, ← mulVec_smul]
    congr 1
    funext i
    have h := (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F) : I.E →+* _) M y i).symm
    rw [e] at h
    refine h.trans ?_
    simp
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨z, hz, e⟩ := hu
    obtain ⟨z', hz', e'⟩ := hv
    exact ⟨z + z', add_mem hz hz', by rw [mulVec_add, e, e', smul_add]⟩
  | smul s u _ hu =>
    obtain ⟨z, hz, e⟩ := hu
    refine ⟨s • z, Submodule.smul_mem _ s hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, mulVec_smul, e, smul_comm]

theorem conj_mem_Kg_of_congr : ∀ (I : AutInst) (x a : I.GA) (g : ℕ) (γ : GL (Fin I.n) I.E), I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (∀ y ∈ lamX I x, ∃ z ∈ lamX I x, ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y = (g : I.E) • z) → (∀ y ∈ lamX I x, ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) → (x⁻¹ * a * x).2 ∈ I.Kg g := by
  intro I x a g γ ha h1 h2
  have hk : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hx1 : I.fmat x.2⁻¹ * I.fmat x.2 = 1 := Units.inv_mul _
  have hx2 : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := Units.mul_inv _
  have hc : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (x⁻¹ * a * x).2 - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x g _ h1 y hy
    refine ⟨z, hz, ?_⟩
    rw [← e, hk, ha, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      mul_sub, sub_mul, mul_one, hx1]
  refine ⟨fun y => ?_, hc⟩
  symm
  show I.fmat (x⁻¹ * a * x).2 *ᵥ y ∈ I.Lf ↔ y ∈ I.Lf
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x 1 _
      (fun y hy => ⟨_, h2 y hy, by rw [Nat.cast_one, one_smul]⟩) _ hy
    rw [Nat.cast_one, one_smul, mulVec_mulVec, hk, ha] at e
    have hγ : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map
        (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : ∀ A B C D : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F), A * B = 1 → B * A = 1 →
        C * D = 1 → A * C * B * (A * D * B) = 1 := by
      intro A B C D p q r
      calc A * C * B * (A * D * B) = A * (C * (B * A) * D) * B := by simp only [mul_assoc]
        _ = 1 := by rw [q, mul_one, r, mul_one, p]
    rw [h3 _ _ _ _ hx1 hx2 hγ, one_mulVec] at e
    exact e ▸ hz
  · obtain ⟨z, hz, e⟩ := hc y hy
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add, Nat.cast_smul_eq_nsmul] at e
    rw [e]
    exact add_mem (nsmul_mem hz g) hy

end GlobalTheory.PointLattice
end
end

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointConj_mem_congruenceSubgroup_of_congr_lattice : ∀ (I : AutInst) (x a : I.GA) (g : ℕ) (γ : GL (Fin I.n) I.E), I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (∀ y ∈ lamX I x, ∃ z ∈ lamX I x, ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y = (g : I.E) • z) → (∀ y ∈ lamX I x, ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) → (x⁻¹ * a * x).2 ∈ I.Kg g := by
  atlas_forward_decl GlobalTheory.PointLattice.conj_mem_Kg_of_congr
end

section
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.PerpSize

open GlobalTheory.Count.PerpStep

theorem inv_le_sizeQ_perp : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  intro I x R hi hR hhi hL N hPN hNA
  obtain ⟨-, hA, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨htc, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hm⟩ := GlobalTheory.Count.PerpStep.main I x
  obtain ⟨N', n1, n2, n3, n4⟩ := nd_sat (bas I) (frm I x) hX hA hNA
  obtain ⟨sP, rP, ppR, -, -⟩ := hm R R hR hR le_rfl
  obtain ⟨sS, rS, ppN, -, -⟩ := hm N' N' n2 n2 le_rfl
  have hPN' : perpIn I x R ≤ N' := hPN.le.trans n1
  obtain ⟨-, -, -, hle, hq⟩ := hm _ N' sP n2 hPN'
  rw [ppR] at hle hq
  have hfg : ∀ {M}, M ≤ lamX I x → M.FG := fun h => Submodule.FG.of_le hA h
  have hR0 : R ≠ ⊥ := by
    intro e
    have h1 : perpIn I x N' = R := by
      rw [e] at hle ⊢
      exact le_bot_iff.1 hle
    rw [h1] at ppN
    exact (lt_of_lt_of_le hPN n1).ne ppN
  rw [htQ_eq _ _ hX _ _ (hfg hR.1) (sat_mono _ _ sS hle hR.1),
    htQ_eq _ _ hX _ _ (hfg n2.1) (sat_mono _ _ sP hPN' n2.1), ← Real.exp_neg] at hq
  have hq' := Real.exp_injective hq
  obtain ⟨l0, lb⟩ := largest_bound (bas I) (frm I x) hX (hfg hR.1) hR0 hle
  have hd := rk_lt (bas I) (frm I x) hX hA sP hPN hNA
  have r1 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg hR.1)).2.1
  have r2 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sP.1)).2.1
  have r3 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sS.1)).2.1
  have r4 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg n2.1)).2.1
  have hrk : rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R =
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N := by
    rw [← n3, r1, r2, r3, r4, ← mul_add, ← mul_add, rP, rS]
  have hrk' : (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') =
      (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hrk
    push_cast at h
    linarith
  rw [hrk'] at lb
  rw [log_sizeQ (bas I) (frm I x) hX hA sP hPN hNA, ← Real.log_le_iff_le_exp (inv_pos.2 hhi),
    le_div_iff₀ (sub_pos.2 hd), Real.log_inv]
  have h4 := Real.log_le_log l0 hL
  have h5 := mul_le_mul_of_nonneg_right h4 (sub_pos.2 hd).le
  linarith

end GlobalTheory.Count.PerpSize
end

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_le_sizeQ_above_orthogonal_saturated : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  atlas_forward_decl GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp
end

section
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.Count.CentralCover

section Form

variable {K : Type} [Field K] [StarRing K] {n : ℕ}

local notation "h" => Formalism.UG.hform (starRingEnd K)

theorem hform_eq (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    h J x y = star x ⬝ᵥ J *ᵥ y := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

def adj (J M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := J⁻¹ * Mᴴ * J

theorem adj_left {J : Matrix (Fin n) (Fin n) K} (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) K)
    (u v : Fin n → K) : h J (M *ᵥ u) v = h J u (adj J M *ᵥ v) := by
  rw [hform_eq, hform_eq, adj, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, star_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec (star u) Mᴴ]

theorem adj_right {J : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) K)
    (u v : Fin n → K) : h J (adj J M *ᵥ u) v = h J u (M *ᵥ v) := by
  rw [PerpStep.hform_swap hJ, ← adj_left hd, ← PerpStep.hform_swap hJ]

theorem mem_of_perp_perp {J : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (W : Submodule K (Fin n → K)) (y : Fin n → K)
    (hy : ∀ p ∈ perpSet (starRingEnd K) J W, h J p y = 0) : y ∈ W := by
  by_contra hn
  obtain ⟨f, hf, hW⟩ := W.exists_dual_map_eq_bot_of_notMem hn inferInstance
  set c : Fin n → K := fun j => f (Pi.single j 1) with hc
  have key : ∀ z, h J (star (c ᵥ* J⁻¹)) z = f z := by
    intro z
    rw [hform_eq, star_star, dotProduct_mulVec, vecMul_vecMul,
      Matrix.nonsing_inv_mul _ (Ne.isUnit hd), vecMul_one]
    conv_rhs => rw [← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (Pi.single j (z j) : Fin n → K) = z j • (Pi.single j 1 : Fin n → K) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  refine hf ?_
  rw [← key]
  refine hy _ fun w hw => ?_
  have h0 : f w = 0 := by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rwa [hW, Submodule.mem_bot] at this
  rw [PerpStep.hform_swap hJ, key, h0, star_zero]

theorem eq_zero_of_perp {J : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (y : Fin n → K) (hy : ∀ p, h J p y = 0) : y = 0 :=
  (Submodule.mem_bot K).1 (mem_of_perp_perp hJ hd ⊥ y fun p _ => hy p)

theorem adj_of_skew {J Z : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (hZ : IsSkew (starRingEnd K) J Z) : adj J Z = -Z := by
  refine Matrix.ext_iff_mulVec.2 fun u => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_perp hJ hd _ fun p => ?_
  have h1 := hZ p u
  rw [adj_left hd, hform_eq, hform_eq] at h1
  rw [hform_eq, neg_mulVec, sub_neg_eq_add, mulVec_add, dotProduct_add, h1]

theorem range_of_inCen {J Z : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) {W : Submodule K (Fin n → K)} (hZ : InCen (starRingEnd K) J W Z)
    (u : Fin n → K) : Z *ᵥ u ∈ W := by
  refine mem_of_perp_perp hJ hd W _ fun p hp => ?_
  have h1 := hZ.1.1 p u
  rw [hZ.2 p hp] at h1
  simpa [hform_eq] using h1

theorem inCen_sub_adj {J Φ : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) {W : Submodule K (Fin n → K)} (hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd K) J W)
    (h1 : ∀ u, Φ *ᵥ u ∈ W) (h2 : ∀ p ∈ perpSet (starRingEnd K) J W, Φ *ᵥ p = 0) :
    InCen (starRingEnd K) J W (Φ - adj J Φ) := by
  have h3 : ∀ u, (Φ - adj J Φ) *ᵥ u ∈ W := by
    intro u
    rw [sub_mulVec]
    refine sub_mem (h1 u) (mem_of_perp_perp hJ hd W _ fun p hp => ?_)
    rw [← adj_left hd, h2 p hp]
    simp [hform_eq]
  have h4 : ∀ p ∈ perpSet (starRingEnd K) J W, (Φ - adj J Φ) *ᵥ p = 0 := by
    intro p hp
    rw [sub_mulVec, h2 p hp, eq_zero_of_perp hJ hd (adj J Φ *ᵥ p) fun u => ?_, sub_zero]
    rw [← adj_left hd]
    exact hp _ (h1 u)
  refine ⟨⟨fun u u' => ?_, fun u => hW _ (h3 u), fun u _ => h3 u, fun u hu => h4 u (hW u hu)⟩, h4⟩
  have e1 := adj_left hd Φ u u'
  have e2 := adj_right hJ hd Φ u u'
  simp only [hform_eq] at e1 e2 ⊢
  simp only [sub_mulVec, star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
  rw [e1, e2]
  ring

theorem adj_map {J : Matrix (Fin n) (Fin n) K} (hd : J.det ≠ 0) (φ : K →+* ℂ)
    (hs : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) (M : Matrix (Fin n) (Fin n) K) :
    (adj J M).map φ = adj (J.map φ) (M.map φ) := by
  have e1 : (J.map φ)⁻¹ = J⁻¹.map φ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hd), Matrix.map_one φ φ.map_zero φ.map_one]
  have e2 : Mᴴ.map φ = (M.map φ)ᴴ := by
    ext i j
    simp [hs]
  rw [adj, adj, Matrix.map_mul, Matrix.map_mul, e1, e2]

end Form

section Norm

variable {n : ℕ}

theorem hs_sub_le (a b : Matrix (Fin n) (Fin n) ℂ) : hs (a - b) ≤ 2 * hs a + 2 * hs b := by
  unfold hs
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 : ‖(a - b) i j‖ ≤ ‖a i j‖ + ‖b i j‖ := norm_sub_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a i j‖ - ‖b i j‖)]

theorem hs_flip (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : hs (Jm ε * aᴴ * Jm ε) = hs a := by
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp

theorem hs_adj (ε : Fin n → Bool) {J A G : Matrix (Fin n) (Fin n) ℂ} (hd : J.det ≠ 0)
    (hGA : G * A = 1) (hG : Gᴴ * J * G = Jm ε) (D : Matrix (Fin n) (Fin n) ℂ) :
    hs (A * adj J D * G) = hs (A * D * G) := by
  have e1 : J * G = Aᴴ * Jm ε := by
    rw [← hG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, hGA, conjTranspose_one,
      Matrix.one_mul]
  have e2 : A = Jm ε * Gᴴ * J := by
    have : Jm ε * (Gᴴ * J * G) * A = A := by rw [hG, Jm_mul_self, Matrix.one_mul]
    rw [← this]
    simp only [Matrix.mul_assoc, hGA, Matrix.mul_one]
  have e3 : A * J⁻¹ = Jm ε * Gᴴ := by
    rw [e2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.mul_one]
  rw [← hs_flip ε (A * D * G)]
  congr 1
  calc A * adj J D * G = (A * J⁻¹) * Dᴴ * (J * G) := by simp only [adj, Matrix.mul_assoc]
    _ = _ := by rw [e1, e3]; simp only [conjTranspose_mul, Matrix.mul_assoc]

end Norm

section Main

variable (I : AutInst) (x : I.GA)

theorem det_map_ne (v : InfinitePlace I.F) : (I.J.map (I.φ v)).det ≠ 0 := by
  have := (I.φ v).map_det I.J
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact (map_ne_zero _).2 I.J_det

theorem herm_map (v : InfinitePlace I.F) : Formalism.UG.IsHerm (starRingEnd ℂ) (I.J.map (I.φ v)) := by
  ext i j
  have h1 : star (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  have h2 := I.cm.cmUnram.2.1 (I.φ v) (I.J j i)
  change starRingEnd ℂ (I.φ v (I.J j i)) = I.φ v (I.J i j)
  rw [← h1, h2]

theorem normAt_sub_adj (D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :
    normAt I x (fun v => D v - adj (I.J.map (I.φ v)) (D v)) ≤ 2 * normAt I x D := by
  unfold normAt
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num),
    Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => ?_)
  have hx : uMat (x.1 v) * uMat (x.1 v)⁻¹ = 1 := Units.mul_inv _
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hU : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  have key := hs_adj (I.ε v) (A := uMat (x.1 v)⁻¹ * (I.P v)⁻¹) (G := I.P v * uMat (x.1 v))
    (det_map_ne I v)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uMat (x.1 v)), hx, Matrix.one_mul, hP])
    (by rw [← hU, ← I.P_spec v]; simp only [conjTranspose_mul, Matrix.mul_assoc]) (D v)
  have h2 := hs_sub_le (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * D v * (I.P v * uMat (x.1 v)))
    (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * adj (I.J.map (I.φ v)) (D v) * (I.P v * uMat (x.1 v)))
  rw [key, ← Matrix.sub_mul, ← Matrix.mul_sub] at h2
  simp only [Matrix.mul_assoc] at h2 ⊢
  linarith

end Main

theorem main : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → hi ^ 2 ≤ rho / 4 → ∀ Z ∈ cenReal I R, ∃ Z₀ ∈ cenInt I x R, normAt I x (Z - diagEmb I Z₀) ≤ ((I.n : ℝ) ^ 2 * I.f) * I.rd * rho / (16 * Real.sqrt I.f) := by
  intro I x R hi rho hR hRp hhi hls hrho Z hZ
  obtain ⟨-, hA, hsp, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨hS, hrk, -⟩ := (PerpStep.main I x).2.2.2 R R hR hR le_rfl
  obtain ⟨-, htop, hperp, -⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  have hmem : ∀ y, y ∈ perpIn I x R ↔
      y ∈ lamX I x ∧ ∀ s ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
    intro y
    rw [PerpStep.perpIn_eq, PerpStep.mem_perp]
  obtain ⟨Φ, hΦS, hΦA, D, hD, hn⟩ := GlobalTheory.T.subquotient_covering_radius_real_places I x (lamX I x) (perpIn I x R) R hi⁻¹ hi hA hS
    (Submodule.FG.of_le hA hR.1) (inv_pos.2 hhi) hhi (GlobalTheory.T.inv_le_sizeQ_above_orthogonal_saturated I x R hi hR hhi hls) hls
    (fun v => (1 / 2 : ℂ) • Z v)
    (by
      intro v y hy
      have : (fun i => I.φ v (y i)) ∈ (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      rw [hperp v] at this
      rw [smul_mulVec, (hZ v).2 _ this, smul_zero])
    (by
      intro v y _
      rw [smul_mulVec]
      exact Submodule.smul_mem _ _ (range_of_inCen (herm_map I v) (det_map_ne I v) (hZ v) _))
  have hD' : ∀ v, D v = (1 / 2 : ℂ) • Z v - Φ.map (I.φ v) := fun v =>
    Matrix.ext_iff_mulVec.2 fun u => hD v u (by rw [htop v]; trivial)
  set W := Submodule.span I.E (R : Set (Fin I.n → I.E)) with hWdef
  have hpW : ∀ y, (∀ s ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0) →
      y ∈ perpSet (starRingEnd I.E) I.J W := by
    intro y hy w hw
    induction hw using Submodule.span_induction with
    | mem s hs => exact hy s hs
    | zero => simp [hform_eq]
    | add a b _ _ ha hb =>
      rw [hform_eq] at ha hb ⊢
      rw [star_add, add_dotProduct, ha, hb, add_zero]
    | smul c a _ ha =>
      rw [hform_eq] at ha ⊢
      rw [star_smul, smul_dotProduct, ha, smul_zero]
  have hWW : ∀ w ∈ W, w ∈ perpSet (starRingEnd I.E) I.J W := by
    intro w hw
    refine hpW w fun s hs => ?_
    rw [PerpStep.hform_swap I.J_herm, hpW s ((hmem s).1 (hRp hs)).2 w hw, star_zero]
  have h1 : ∀ u, Φ *ᵥ u ∈ W := by
    intro u
    have hu : u ∈ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) := by rw [hsp]; trivial
    induction hu using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (hΦA s hs)
    | zero => simp
    | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have h2 : ∀ p ∈ perpSet (starRingEnd I.E) I.J W, Φ *ᵥ p = 0 := by
    intro p hp
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 I.E)) I.E
      (lamX I x : Set (Fin I.n → I.E)) p (by rw [hsp]; trivial)
    rw [Submodule.span_eq] at ht
    have e : t • p = algebraMap (𝓞 I.E) I.E t • p := by
      rw [algebraMap_smul]; rfl
    rw [e] at ht
    have h0 : algebraMap (𝓞 I.E) I.E t ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 I.E) I.E)).2 (nonZeroDivisors.coe_ne_zero t)
    have h3 := hΦS _ ((hmem _).2 ⟨ht, fun s hs => by
      have := hp s (Submodule.subset_span hs)
      rw [hform_eq] at this ⊢
      rw [mulVec_smul, dotProduct_smul, this, smul_zero]⟩)
    rw [mulVec_smul] at h3
    exact (smul_eq_zero.1 h3).resolve_left h0
  refine ⟨Φ - adj I.J Φ, ⟨inCen_sub_adj I.J_herm I.J_det hWW h1 h2, fun u hu => ?_⟩, ?_⟩
  · rw [sub_mulVec]
    refine sub_mem (hR.1 (hΦA u hu)) ((hdual _).2 fun z hz => ?_)
    rw [← adj_left I.J_det]
    exact (hdual u).1 hu _ (hR.1 (hΦA z hz))
  · have e : Z - diagEmb I (Φ - adj I.J Φ) = fun v => D v - adj (I.J.map (I.φ v)) (D v) := by
      funext v
      have a1 := adj_of_skew (herm_map I v) (det_map_ne I v) (hZ v).1.1
      have a2 := adj_map I.J_det (I.φ v) (I.cm.cmUnram.2.1 (I.φ v)) Φ
      have a3 : adj (I.J.map (I.φ v)) (D v) = (1 / 2 : ℂ) • adj (I.J.map (I.φ v)) (Z v) -
          adj (I.J.map (I.φ v)) (Φ.map (I.φ v)) := by
        rw [hD' v]
        simp [adj, conjTranspose_sub, conjTranspose_smul, Matrix.mul_sub, Matrix.sub_mul]
      rw [a3, a1, ← a2, hD' v, Pi.sub_apply, diagEmb, Matrix.map_sub _ (map_sub (I.φ v))]
      module
    rw [e]
    refine (normAt_sub_adj I x D).trans ?_
    have hrkA : rkK (lamX I x) = I.n := by
      unfold rkK
      rw [hsp, finrank_top]
      simp
    have hle : rkK R ≤ rkK (perpIn I x R) := Submodule.finrank_mono (Submodule.span_mono hRp)
    have r1 : (rkK (lamX I x) : ℝ) - rkK (perpIn I x R) = rkK R := by
      have : (rkK (perpIn I x R) : ℝ) + rkK R = I.n := by exact_mod_cast hrk
      rw [hrkA]
      linarith
    have r2 : 2 * (rkK R : ℝ) ≤ I.n := by
      have : 2 * rkK R ≤ I.n := by omega
      exact_mod_cast this
    rw [r1] at hn
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    have hj : (0 : ℝ) ≤ rkK R := Nat.cast_nonneg _
    have r3 : (rkK R : ℝ) ^ 2 ≤ (I.n : ℝ) ^ 2 / 4 := by nlinarith
    have r4 : ((I.n : ℝ) ^ 2 * I.f) * I.rd * rho / (16 * Real.sqrt I.f) =
        (I.n : ℝ) ^ 2 / 4 * (rho / 4) * (Real.sqrt I.f * I.rd) := by
      conv_rhs => rw [← Real.div_sqrt]
      ring
    have r5 : 2 * ((rkK R : ℝ) * rkK R * Real.sqrt I.f * I.rd * hi / (2 * hi⁻¹)) =
        (rkK R : ℝ) ^ 2 * hi ^ 2 * (Real.sqrt I.f * I.rd) := by
      field_simp
    rw [r4]
    refine (mul_le_mul_of_nonneg_left hn (by norm_num)).trans ?_
    rw [r5]
    exact mul_le_mul_of_nonneg_right (mul_le_mul r3 hrho (sq_nonneg _) (by positivity))
      (mul_nonneg (Real.sqrt_nonneg _) hrd)

end GlobalTheory.Count.CentralCover
end
end

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradicalCenter_integral_covering_radius : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → hi ^ 2 ≤ rho / 4 → ∀ Z ∈ cenReal I R, ∃ Z₀ ∈ cenInt I x R, normAt I x (Z - diagEmb I Z₀) ≤ ((I.n : ℝ) ^ 2 * I.f) * I.rd * rho / (16 * Real.sqrt I.f) := by
  atlas_forward_decl GlobalTheory.Count.CentralCover.main
end

section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SmallFund

open GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.UG GlobalTheory.NilLie

section Point

variable (I : AutInst)

theorem exists_real (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (B : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) (hB : B ∈ nilReal I R) :
    ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) ∧
      ∀ v, uMat (m v) = (I.P v)⁻¹ * ex (B v) * I.P v := by
  have hc : ∀ v (a b : Matrix (Fin I.n) (Fin I.n) ℂ), a * b = 1 →
      (I.P v)⁻¹ * a * I.P v * ((I.P v)⁻¹ * b * I.P v) = 1 := fun v a b h => by
    calc _ = (I.P v)⁻¹ * (a * (I.P v * (I.P v)⁻¹) * b) * I.P v := by simp only [mul_assoc]
      _ = 1 := by rw [P_mul_inv, mul_one, h, mul_one, inv_mul_P]
  refine ⟨fun v => ⟨⟨(I.P v)⁻¹ * ex (B v) * I.P v, (I.P v)⁻¹ * ex (-B v) * I.P v,
    hc v _ _ (ex_mul_ex_neg (hB v)), hc v _ _ (ex_neg_mul_ex (hB v))⟩, ?_⟩, ⟨fun v => ?_, ?_⟩, fun v => rfl⟩
  · have h := ex_unitary (hB v)
    rw [cT_conj] at h
    show ((I.P v)⁻¹ * ex (B v) * I.P v)ᴴ * Jm (I.ε v) * ((I.P v)⁻¹ * ex (B v) * I.P v) = Jm (I.ε v)
    rw [← I.P_spec v]
    calc _ = (I.P v)ᴴ * ((ex (B v))ᴴ * (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) *
          ex (B v)) * I.P v := by simp only [conjTranspose_mul, mul_assoc]
      _ = _ := by rw [P_mul_inv, conjTranspose_one, mul_one, mul_one, h]
  · have h : I.P v * ((I.P v)⁻¹ * ex (B v) * I.P v) * (I.P v)⁻¹ = ex (B v) := by
      calc _ = (I.P v * (I.P v)⁻¹) * ex (B v) * (I.P v * (I.P v)⁻¹) := by simp only [mul_assoc]
        _ = _ := by rw [P_mul_inv, one_mul, mul_one]
    show I.InUnipRad _ _ _ (I.P v * ((I.P v)⁻¹ * ex (B v) * I.P v) * (I.P v)⁻¹)
    rw [h, ← (GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R).1 v]
    exact ex_unip (hB v)
  · have h : I.fmat (1 : I.Gf) = 1 := by simp [AutInst.fmat]
    simp only [h, AutInst.InUnipRad, sub_self, Matrix.zero_mulVec]
    refine ⟨fun _ _ => trivial, fun _ _ => zero_mem _, fun _ => ?_⟩
    simp [hform]

theorem exists_real_log (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (ν : I.Ginf)
    (hν : ((ν, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E)))) :
    ∃ Y ∈ nilReal I R, ∀ v, uMat (ν v) = (I.P v)⁻¹ * ex (Y v) * I.P v := by
  have key : ∀ v, ∃ Y, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) Y ∧
      ex Y = I.P v * uMat (ν v) * (I.P v)⁻¹ := fun v => by
    have h := hν.1 v
    rw [← (GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R).1 v] at h
    refine exists_log ?_ h
    have hx : (uMat (ν v))ᴴ * Jm (I.ε v) * uMat (ν v) = Jm (I.ε v) := (ν v).2
    rw [cT_conj]
    calc _ = ((I.P v)⁻¹)ᴴ * ((uMat (ν v))ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * uMat (ν v)) * (I.P v)⁻¹ := by
          simp only [conjTranspose_mul, mul_assoc]
      _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
          rw [I.P_spec, hx, ← I.P_spec]; simp only [conjTranspose_mul, mul_assoc]
      _ = _ := by rw [P_mul_inv, conjTranspose_one, one_mul, mul_one]
  choose Y hY hY' using key
  refine ⟨Y, hY, fun v => ?_⟩
  rw [hY']
  calc _ = ((I.P v)⁻¹ * I.P v) * uMat (ν v) * ((I.P v)⁻¹ * I.P v) := by rw [inv_mul_P, one_mul, mul_one]
    _ = _ := by simp only [mul_assoc]

theorem exists_rat (x : I.GA) (g : ℕ) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    {Y₀ Z₀ : Matrix (Fin I.n) (Fin I.n) I.E} (hY : Y₀ ∈ nilInt I x R) (hZ : Z₀ ∈ cenInt I x R) :
    ∃ γ ∈ I.GFset ∩ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))), (x⁻¹ * γ * x).2 ∈ I.Kg g ∧
      ∀ v, uMat (γ.1 v) = (I.P v)⁻¹ *
        ex (((2 * g : ℝ) : ℂ) • Y₀.map (I.φ v) + ((g : ℝ) : ℂ) • Z₀.map (I.φ v)) * I.P v := by
  have hJ : IsUnit I.J := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]; exact I.J_det
  have hcong : ∀ {Y Z : Matrix (Fin I.n) (Fin I.n) I.E}, Y ∈ nilInt I x R → Z ∈ cenInt I x R →
      ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, (ex ((2 * g : I.E) • Y + (g : I.E) • Z) - 1) *ᵥ y = (g : I.E) • z := by
    intro Y Z hY hZ y hy
    refine ⟨2 • (Y *ᵥ y) + (2 * g) • (Y *ᵥ (Y *ᵥ y)) + Z *ᵥ y, ?_, ?_⟩
    · exact add_mem (add_mem (nsmul_mem (hY.2 y hy) _) (nsmul_mem (hY.2 _ (hY.2 y hy)) _)) (hZ.2 y hy)
    · rw [ex_add_cen hJ (nil_smul (by simp [map_ofNat]) hY.1) (cen_smul (by simp) hZ.1), ex]
      simp only [add_mulVec, sub_mulVec, smul_mulVec, smul_mul_assoc, mul_smul_comm, one_mulVec,
        ← mulVec_mulVec]
      simp only [← Nat.cast_smul_eq_nsmul I.E]
      push_cast
      match_scalars <;> first | ring1 | field_simp
  have hN : InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E)))
      ((2 * g : I.E) • Y₀ + (g : I.E) • Z₀) :=
    nil_add (nil_smul (by simp [map_ofNat]) hY.1) (cen_smul (by simp) hZ.1).1
  let γ : GL (Fin I.n) I.E := ⟨ex ((2 * g : I.E) • Y₀ + (g : I.E) • Z₀), ex (-((2 * g : I.E) • Y₀ + (g : I.E) • Z₀)),
    ex_mul_ex_neg hN, ex_neg_mul_ex hN⟩
  obtain ⟨a, ha, h1, h2⟩ := GlobalTheory.T.rational_unipotentRadical_mem_adelic I _ γ (ex_unitary hN) (ex_unip hN)
  refine ⟨a, ha, GlobalTheory.T.pointConj_mem_congruenceSubgroup_of_congr_lattice I x a g γ h2 (hcong hY hZ) fun y hy => ?_, fun v => ?_⟩
  · have hY' : -Y₀ ∈ nilInt I x R :=
      ⟨nil_neg hY.1, fun u hu => by rw [neg_mulVec]; exact neg_mem (hY.2 u hu)⟩
    have hZ' : -Z₀ ∈ cenInt I x R :=
      ⟨by simpa using cen_smul (c := -1) (by simp) hZ.1,
        fun u hu => by rw [neg_mulVec]; exact neg_mem (hZ.2 u hu)⟩
    obtain ⟨z, hz, e⟩ := hcong hY' hZ' y hy
    rw [smul_neg, smul_neg, ← neg_add, sub_mulVec, one_mulVec, sub_eq_iff_eq_add] at e
    show ex (-((2 * g : I.E) • Y₀ + (g : I.E) • Z₀)) *ᵥ y ∈ _
    rw [e, Nat.cast_smul_eq_nsmul]
    exact add_mem (nsmul_mem hz _) hy
  · rw [h1]
    congr 2
    ext i j
    by_cases hij : i = j <;>
      simp [γ, ex, Matrix.mul_apply, Matrix.one_apply, hij, map_ofNat]

end Point

theorem radius_le (N f g rd rho : ℝ) (hN : 0 ≤ N) (hf : 0 < f) (hg : 0 ≤ g) (hrd : 0 ≤ rd) (hrho : 0 ≤ rho) :
    2 * g * (N * f / 8 * rd * rho / Real.sqrt (2 * f)) + g * (N * f * rd * rho / (16 * Real.sqrt f)) ≤
      N * Real.sqrt f * g * rd * rho / 4 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ f = t ^ 2 := ⟨Real.sqrt f, Real.sqrt_pos.2 hf, (Real.sq_sqrt hf.le).symm⟩
  have h2 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq ht.le]
  have hc : 0 ≤ N * t * g * rd * rho := by positivity
  have e : 2 * g * (N * t ^ 2 / 8 * rd * rho / (Real.sqrt 2 * t)) + g * (N * t ^ 2 * rd * rho / (16 * t)) =
      N * t * g * rd * rho / (4 * Real.sqrt 2) + N * t * g * rd * rho / 16 := by
    field_simp
    ring
  have h3 : N * t * g * rd * rho / (4 * Real.sqrt 2) ≤ N * t * g * rd * rho / (4 * (4 / 3)) := by
    gcongr
  rw [e]
  generalize N * t * g * rd * rho = c at *
  have h4 : c / (4 * (4 / 3)) = 3 / 16 * c := by ring
  linarith

theorem small_fundamental_set : ∀ (I : AutInst) (x : I.GA) (g : ℕ) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), 1 ≤ g → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≠ ⊥ → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → hi ≤ rho * lo → hi ^ 2 ≤ rho / 4 → ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) → ∃ γ ∈ I.GFset ∩ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))), (x⁻¹ * γ * x).2 ∈ I.Kg g ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * rho / 4 ∧ ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) ∧ ∀ v, uMat (m v) * uMat (x.1 v) = uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v) := by
  intro I x g R lo hi rho hg hsat _ hiso hhi hlarge hlo hhl hh2 ν hν
  have hrho : 0 < rho := by nlinarith [sq_pos_of_pos hhi]
  have hlo0 : 0 < lo := by
    by_contra h
    nlinarith [mul_nonneg hrho.le (neg_nonneg.2 (not_lt.1 h))]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hgc : ((g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hreal : ∀ c : ℝ, starRingEnd ℂ (c : ℂ) = c := Complex.conj_ofReal
  obtain ⟨-, -, -, hnil, hcen⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  obtain ⟨Y, hY, hνY⟩ := exists_real_log I x R ν hν
  obtain ⟨Y₀, hY₀, Z, hZ, hA⟩ := GlobalTheory.T.nilradical_first_layer_covering_radius_le I x R lo hi rho hsat hiso hhi hlarge hlo hlo0 hhl
    (fun v => (((2 * g : ℝ)⁻¹ : ℝ) : ℂ) • Y v) (fun v => nil_smul (hreal _) (hY v))
  have hY₀' := hnil Y₀ hY₀.1
  set A : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((2 * g : ℝ) : ℂ) •
    ((fun v => (((2 * g : ℝ)⁻¹ : ℝ) : ℂ) • Y v) - diagEmb I Y₀ - Z) v with hAdef
  have hAn : A ∈ nilReal I R := fun v =>
    nil_smul (hreal _) (nil_sub (nil_sub (nil_smul (hreal _) (hY v)) (hY₀' v)) (hZ v).1)
  set Z'' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((2 * g : ℝ) : ℂ) • Z v +
    (2 : ℂ)⁻¹ • (A v * (((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v) - (((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v) * A v)
    with hZ''def
  have hZ''c : Z'' ∈ cenReal I R := fun v =>
    cen_add (cen_smul (hreal _) (hZ v)) (cen_smul map_half (cen_comm (hAn v) (nil_smul (hreal _) (hY₀' v))))
  obtain ⟨Z₀, hZ₀, hZ'⟩ := GlobalTheory.T.nilradicalCenter_integral_covering_radius I x R hi rho hsat hiso hhi hlarge hh2
    (fun v => (((g : ℝ)⁻¹ : ℝ) : ℂ) • Z'' v) (fun v => cen_smul (hreal _) (hZ''c v))
  have hZ₀' := hcen Z₀ hZ₀.1
  set Z' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => ((g : ℝ) : ℂ) •
    ((fun v => (((g : ℝ)⁻¹ : ℝ) : ℂ) • Z'' v) - diagEmb I Z₀) v with hZ'def
  have hZ'c : Z' ∈ cenReal I R := fun v =>
    cen_smul (hreal _) (cen_sub (cen_smul (hreal _) (hZ''c v)) (hZ₀' v))
  obtain ⟨γ, hγ, hγK, hγv⟩ := exists_rat I x g R hY₀ hZ₀
  have hfac : ∀ v, ex (Y v) = ex (((2 * g : ℝ) : ℂ) • Y₀.map (I.φ v) + ((g : ℝ) : ℂ) • Z₀.map (I.φ v)) *
      ex (A v) * ex (Z' v) := fun v => by
    have := ex_factor (isUnit_Jv I v) (nil_smul (hreal (2 * g)) (hY₀' v)) (hAn v)
      (cen_smul (hreal g) (hZ₀' v)) (hZ'c v)
    refine Eq.trans ?_ this
    congr 1
    have e1 : ((g : ℝ) : ℂ) • diagEmb I Z₀ v + Z' v = Z'' v := by
      simp only [hZ'def, Pi.sub_apply, smul_sub, smul_smul]
      rw [Complex.ofReal_inv, mul_inv_cancel₀ hgc, one_smul]; abel
    have e2 : ((2 * g : ℝ) : ℂ) • diagEmb I Y₀ v + A v + ((2 * g : ℝ) : ℂ) • Z v = Y v := by
      simp only [hAdef, Pi.sub_apply, smul_sub, smul_smul]
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast (by positivity : (2 * g : ℝ) ≠ 0)), one_smul]
      abel
    rw [e1, ← e2, hZ''def]
    simp only [add_sub_cancel_right]
  have hprod : ∀ v (a b : Matrix (Fin I.n) (Fin I.n) ℂ), a * (a * a) = 0 → b * (b * b) = 0 →
      uMat (x.1 v) * NormedSpace.exp (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * a * (I.P v * uMat (x.1 v))) *
        NormedSpace.exp (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * b * (I.P v * uMat (x.1 v))) =
      (I.P v)⁻¹ * (ex a * ex b) * I.P v * uMat (x.1 v) := fun v a b ha hb => by
    rw [exp_conj (frame_mul I x v) (mul_frame I x v) ha, exp_conj (frame_mul I x v) (mul_frame I x v) hb]
    calc _ = (uMat (x.1 v) * uMat (x.1 v)⁻¹) * (I.P v)⁻¹ * ex a *
          (I.P v * uMat (x.1 v) * (uMat (x.1 v)⁻¹ * (I.P v)⁻¹)) * ex b * (I.P v * uMat (x.1 v)) := by
          simp only [mul_assoc]
      _ = _ := by rw [uMat_mul_inv, frame_mul]; simp only [mul_assoc, one_mul]
  refine ⟨γ, hγ, hγK, fun v => uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A v * (I.P v * uMat (x.1 v)),
    fun v => uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Z' v * (I.P v * uMat (x.1 v)),
    fun v => ⟨inG_frame I x v (hAn v), inG_frame I x v (hZ'c v).1⟩, fun v => ?_, ?_, fun s t => ?_⟩
  · have := hprod v _ _ (isInStabilizerNilradicalLie_triple_mul_eq_zero (hAn v) (hAn v) (hAn v)) (isInStabilizerNilradicalLie_triple_mul_eq_zero (hZ'c v).1 (hZ'c v).1 (hZ'c v).1)
    rw [mul_assoc (uMat (γ.1 v)), mul_assoc (uMat (γ.1 v)), this, hνY, hγv, hfac]
    calc _ = (I.P v)⁻¹ * ex (((2 * g : ℝ) : ℂ) • Y₀.map (I.φ v) + ((g : ℝ) : ℂ) • Z₀.map (I.φ v)) *
          (I.P v * (I.P v)⁻¹) * (ex (A v) * ex (Z' v)) * I.P v * uMat (x.1 v) := by
          rw [P_mul_inv]; simp only [mul_assoc, one_mul]
      _ = _ := by simp only [mul_assoc]
  · have n1 : Real.sqrt (∑ v, hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A v * (I.P v * uMat (x.1 v)))) =
        normAt I x A := by simp only [normAt, mul_assoc]
    have n2 : Real.sqrt (∑ v, hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Z' v * (I.P v * uMat (x.1 v)))) =
        normAt I x Z' := by simp only [normAt, mul_assoc]
    rw [n1, n2, hAdef, hZ'def, normAt_smul I x _ (by positivity), normAt_smul I x _ hg0.le]
    have hf : (0 : ℝ) < I.f := by exact_mod_cast (Module.finrank_pos : 0 < I.f)
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    refine le_trans ?_ (radius_le ((I.n : ℝ) ^ 2) I.f g I.rd rho (by positivity) hf hg0.le hrd hrho.le)
    gcongr
  · have hs' : ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ((s : ℂ) • A v) :=
      fun v => nil_smul (hreal s) (hAn v)
    have ht' : ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ((t : ℂ) • Z' v) :=
      fun v => cen_smul (hreal t) (hZ'c v)
    obtain ⟨m, hm, hmv⟩ := exists_real I x R (fun v => (s : ℂ) • A v + (t : ℂ) • Z' v)
      (fun v => nil_add (hs' v) (ht' v).1)
    refine ⟨m, hm, fun v => ?_⟩
    have := hprod v _ _ (isInStabilizerNilradicalLie_triple_mul_eq_zero (hs' v) (hs' v) (hs' v)) (isInStabilizerNilradicalLie_triple_mul_eq_zero (ht' v).1 (ht' v).1 (ht' v).1)
    rw [ex_mul_ex_cen (isUnit_Jv I v) (hs' v) (ht' v), ← hmv] at this
    rw [← this]
    simp only [mul_smul_comm, smul_mul_assoc]

end GlobalTheory.SmallFund
end
end
