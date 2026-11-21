import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.EqSmulOfSub
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd

section
noncomputable section

namespace PI.IwaMeasEx.KV

open MeasureTheory
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
  Formalism.L2.S.S7.PositiveOrthantChangeOfVariables
open Formalism.HermitianLatticeCounting.S7 (dimN Vsph)
open PI.IwaMeasEx.Sk

structure admitted {X : CData} {J : ℕ} (c : Composition J) (D : BaseDatum X.I J) where
  μK : Measure X.I.GA
  μN : Measure X.I.GA
  μM : Measure X.I.GA
  cIw : ℝ≥0∞
  FN : Set X.I.GA
  FM : Set X.I.GA
  Om : Set X.I.GA
  VM : ℝ≥0∞
  hK : PK D μK
  hN : PN D c μN
  hM : PM D c μM
  hI : IntF μK (muP D c μN μM) cIw
  hF : FdP D c μN μM FN FM Om
  hL : LeviP D c μM FM VM

structure Sc where
  s : ℝ≥0∞
  sN : ℝ≥0∞
  sM : ℝ≥0∞
  vU0 : ℝ

abbrev GPred : Type 1 :=
  ∀ (X : CData) (J : ℕ) (c : Composition J) (D : BaseDatum X.I J), admitted c D → Sc → Prop

def n0 (X : CData) (J : ℕ) : ℕ := X.I.n - 2 * J

def volU (i : ℕ) : ℝ := Vsph i * (2 : ℝ) ^ ((i : ℝ) * ((i : ℝ) - 1) / 2)

def cIG (X : CData) (J : ℕ) (c : Composition J) : ℝ :=
  ((2 : ℝ) ^ (-(dimN c.blocksFun (n0 X J) : ℝ) / 2) * (volU (X.I.n - X.qq) * volU X.qq) /
    ((∏ i, volU (c.blocksFun i) * (2 : ℝ) ^ ((c.blocksFun i : ℝ) ^ 2 / 2)) *
      volU (X.I.n - X.qq - J) * volU (X.qq - J))) ^ X.I.f

def nBound (X : CData) (J : ℕ) (c : Composition J) : ℝ :=
  X.I.rd ^ ((X.I.f : ℝ) * (dimN c.blocksFun (n0 X J) : ℝ) / 2)

def glG (X : CData) (j : ℕ) : ℝ :=
  X.I.rd ^ ((X.I.f : ℝ) * (j : ℝ) ^ 2) * cn_res X *
    ∏ l ∈ Finset.Icc 2 j, ‖NumberField.dedekindZeta X.I.E (l : ℂ)‖

def lProd (X : CData) (J : ℕ) : ℝ :=
  ∏ M ∈ Finset.Ioc (n0 X J) X.I.n, Formalism.HermitianLatticesTheory.lValEta X.I.E M

def gRatio (X : CData) (J : ℕ) : ℝ :=
  X.I.rd ^ ((X.I.f : ℝ) * ((X.I.n : ℝ) ^ 2 - (n0 X J : ℝ) ^ 2) / 2) * lProd X J

def StepEx (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2) → Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c) →
    ∀ a : admitted c D, ∃ sc : Sc, sc.s ≠ 0 ∧ sc.s ≠ ⊤ ∧ sc.sN ≠ 0 ∧ sc.sN ≠ ⊤ ∧ sc.sM ≠ 0 ∧ sc.sM ≠ ⊤ ∧
      G X J c D a sc

def StepB (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    a.cIw * sc.s = ENNReal.ofReal (cIG X J c) * (sc.sN * sc.sM)

def StepC (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    sc.sN * a.μN a.FN ≤ ENNReal.ofReal (nBound X J c)

def StepD (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    0 < sc.vU0 ∧ sc.sM * a.VM = ENNReal.ofReal ((∏ i, glG X (c.blocksFun i)) * sc.vU0)

def StepE (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    sc.s * X.I.muA X.μf X.fund = ENNReal.ofReal (sc.vU0 * gRatio X J)

def LPos : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → 0 < lProd X J

def StepF : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ c : Composition J, 0 < lProd X J →
    cIG X J c * nBound X J c * (∏ i, glG X (c.blocksFun i)) ≤
      gRatio X J * Formalism.L2.S.S7.DensityConstant.densityConstant X J c


theorem rd_nonneg (X : CData) : 0 ≤ X.I.rd := by
  unfold AutInst.rd
  exact Real.rpow_nonneg (abs_nonneg _) _


end PI.IwaMeasEx.KV

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Gauge

open MeasureTheory Topology Filter Set
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S

section Riem

variable {n : ℕ}

abbrev MatR (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin n × Bool)

def realifyM (X : Matrix (Fin n) (Fin n) ℂ) : MatR n :=
  WithLp.toLp 2 (fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re)

def toMat (x : MatR n) : Matrix (Fin n) (Fin n) ℂ := fun i j => ⟨x.ofLp (i, j, false), x.ofLp (i, j, true)⟩

def expU (x : MatR n) : (Matrix (Fin n) (Fin n) ℂ)ˣ := (Matrix.isUnit_exp (toMat x)).unit

variable {ε : Fin n → Bool}

def lieOf (H : Subgroup (Formalism.REAL.UJ ε)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, ∃ h ∈ H, uMat h = NormedSpace.exp ((t : ℂ) • X)}

def lieSp (H : Subgroup (Formalism.REAL.UJ ε)) : Submodule ℝ (MatR n) :=
  Submodule.span ℝ (realifyM '' lieOf H)

def conjInv (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) : Subgroup (Formalism.REAL.UJ ε) :=
  H.map (MulAut.conj y⁻¹).toMonoidHom

def expSetY (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) (T : Set (lieSp (conjInv H y))) :
    Set (Formalism.REAL.UJ ε) :=
  {g | ∃ x ∈ T, uMat g = uMat y * NormedSpace.exp (toMat (x : MatR n)) * uMat y⁻¹}

structure IsRiem (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) (R : Measure (Formalism.REAL.UJ ε)) : Prop where
  sfin : SigmaFinite R
  ne : R ≠ 0
  supp : R (H : Set (Formalism.REAL.UJ ε))ᶜ = 0
  cpt : ∀ s : Set (Formalism.REAL.UJ ε), IsCompact s → R s ≠ ⊤
  inv : ∀ h ∈ H, R.map (fun x => h * x) = R
  dens : ∀ S : Set (lieSp (conjInv H y)), MeasurableSet S → Bornology.IsBounded S →
    0 < (volume : Measure (lieSp (conjInv H y))) S → (volume : Measure (lieSp (conjInv H y))) (frontier S) = 0 →
    Tendsto (fun r : ℝ => R (expSetY H y (r • S)) / (volume : Measure (lieSp (conjInv H y))) (r • S)) (𝓝[>] 0) (𝓝 1)

end Riem

end PI.IwaMeasEx.Gauge

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open MeasureTheory Topology Filter Set Metric
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S PI.IwaMeasEx.Gauge

section Ratio

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

end Ratio

variable {n : ℕ} {ε : Fin n → Bool}

end PI.IwaMeasEx.Gauge.ZetaZeros

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open MeasureTheory Topology Filter Set Metric
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S PI.IwaMeasEx.Gauge

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_conjInv (H : Subgroup (Formalism.REAL.UJ ε)) (y g : Formalism.REAL.UJ ε) :
    g ∈ conjInv H y ↔ y * g * y⁻¹ ∈ H := by
  unfold conjInv
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have e : y * (MulAut.conj y⁻¹).toMonoidHom h * y⁻¹ = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hh
  · intro hg
    refine ⟨y * g * y⁻¹, hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

def conjE (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) : H ≃ₜ* conjInv H y where
  toFun h := ⟨y⁻¹ * h * y, (mem_conjInv H y _).2 (by
    rw [show y * (y⁻¹ * (h : Formalism.REAL.UJ ε) * y) * y⁻¹ = h by group]
    exact h.2)⟩
  invFun k := ⟨y * k * y⁻¹, (mem_conjInv H y _).1 k.2⟩
  left_inv h := Subtype.ext (show y * (y⁻¹ * (h : Formalism.REAL.UJ ε) * y) * y⁻¹ = h by group)
  right_inv k := Subtype.ext (show y⁻¹ * (y * (k : Formalism.REAL.UJ ε) * y⁻¹) * y = k by group)
  map_mul' a b := Subtype.ext (show y⁻¹ * ((a : Formalism.REAL.UJ ε) * b) * y = (y⁻¹ * a * y) * (y⁻¹ * b * y) by group)
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end PI.IwaMeasEx.Gauge.ZetaZeros

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open MeasureTheory Topology Filter Set Metric
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S PI.IwaMeasEx.Gauge

def LieAdd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (K : Subgroup (Formalism.REAL.UJ ε)), IsClosed (K : Set (Formalism.REAL.UJ ε)) →
    ∀ X ∈ lieOf K, ∀ Y ∈ lieOf K, X + Y ∈ lieOf K

def LocUniq : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure]
    (W : Set G), IsOpen W → (1 : G) ∈ W → ν W ≠ ⊤ →
    (∀ (x : G) (T : Set G), MeasurableSet T → T ⊆ W → x • T ⊆ W → ν (x • T) = ν T) →
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V ⊆ W ∧ ∃ κ : ℝ≥0∞, κ ≠ ⊤ ∧
      ∀ S : Set G, MeasurableSet S → S ⊆ V → ν S = κ * μ S

end PI.IwaMeasEx.Gauge.ZetaZeros

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open Filter Topology Formalism.MainNotions.S

section Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem norm_exp_sub_partial_le (x : 𝔸) (m : ℕ) :
    ‖NormedSpace.exp x - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) • x ^ i‖ ≤
      Real.exp ‖x‖ - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i := by
  have h1 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • x ^ i) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • ‖x‖ ^ i) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have h1' := (hasSum_nat_add_iff' m).mpr h1
  have h2' := (hasSum_nat_add_iff' m).mpr h2
  simp only [smul_eq_mul] at h2'
  refine h1'.norm_le_of_bounded h2' (fun i => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)

theorem exp_pow_eqA (c : 𝔸) (j : ℕ) : NormedSpace.exp c ^ j = NormedSpace.exp (j • c) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hb : ∀ z : 𝔸, z ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius := by
      intro z
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _
    rw [pow_succ, ih, succ_nsmul,
      NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) ((Commute.refl c).smul_left j) (hb _) (hb _)]

theorem norm_exp_le' (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa using norm_exp_sub_partial_le x 0

theorem norm_exp_sub_one_le' (x : 𝔸) (hx : ‖x‖ ≤ 1) : ‖NormedSpace.exp x - 1‖ ≤ 2 * ‖x‖ := by
  have e1 : ∑ i ∈ Finset.range 1, ((i.factorial : ℝ)⁻¹) • x ^ i = 1 := by simp
  have e2 : ∑ i ∈ Finset.range 1, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i = 1 := by simp
  have key := norm_exp_sub_partial_le x 1
  rw [e1, e2] at key
  have hr := Real.abs_exp_sub_one_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])
  rw [abs_of_nonneg (norm_nonneg x), abs_le] at hr
  linarith [hr.2]

theorem norm_exp_sub_one_sub_le' (x : 𝔸) (hx : ‖x‖ ≤ 1) : ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := by
  have e1 : ∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) • x ^ i = 1 + x := by simp [Finset.sum_range_succ]
  have e2 : ∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i = 1 + ‖x‖ := by simp [Finset.sum_range_succ]
  have key := norm_exp_sub_partial_le x 2
  rw [e1, e2] at key
  have hr := Real.abs_exp_sub_one_sub_id_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])
  rw [abs_le] at hr
  rw [sub_sub]
  linarith [hr.2]

theorem norm_pow_sub_pow_le' (S T : 𝔸) {M : ℝ} (hM : 0 ≤ M) (hS : ‖S‖ ≤ M) (hT : ‖T‖ ≤ M) (k : ℕ) :
    ‖S ^ (k + 1) - T ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * M ^ k * ‖S - T‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : S ^ (k + 1 + 1) - T ^ (k + 1 + 1) =
        S * (S ^ (k + 1) - T ^ (k + 1)) + (S - T) * T ^ (k + 1) := by
      rw [pow_succ' S (k + 1), pow_succ' T (k + 1)]
      simp only [mul_sub, sub_mul]
      abel
    rw [e]
    have hTk : ‖T ^ (k + 1)‖ ≤ M ^ (k + 1) :=
      (norm_pow_le T _).trans (pow_le_pow_left₀ (norm_nonneg _) hT _)
    have hD0 : 0 ≤ ‖S - T‖ := norm_nonneg _
    have hMk : 0 ≤ M ^ k := pow_nonneg hM k
    have i1 : ‖S * (S ^ (k + 1) - T ^ (k + 1))‖ ≤ M * (((k : ℝ) + 1) * M ^ k * ‖S - T‖) :=
      (norm_mul_le _ _).trans (mul_le_mul hS ih (norm_nonneg _) hM)
    have i2 : ‖(S - T) * T ^ (k + 1)‖ ≤ ‖S - T‖ * M ^ (k + 1) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hTk hD0)
    calc ‖S * (S ^ (k + 1) - T ^ (k + 1)) + (S - T) * T ^ (k + 1)‖
        ≤ M * (((k : ℝ) + 1) * M ^ k * ‖S - T‖) + ‖S - T‖ * M ^ (k + 1) :=
          (norm_add_le _ _).trans (add_le_add i1 i2)
      _ = (((k + 1 : ℕ) : ℝ) + 1) * M ^ (k + 1) * ‖S - T‖ := by push_cast; ring

theorem trotter (A B : 𝔸) :
    Tendsto (fun k : ℕ => (NormedSpace.exp ((k : ℝ)⁻¹ • A) * NormedSpace.exp ((k : ℝ)⁻¹ • B)) ^ k) atTop
      (𝓝 (NormedSpace.exp (A + B))) := by
  set r := ‖A‖ + ‖B‖ with hr
  have hr0 : 0 ≤ r := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hC : Tendsto (fun k : ℕ => 7 * r ^ 2 * Real.exp r / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hC
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * r)
  filter_upwards [eventually_ge_atTop (N + 1)] with k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hkc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hkpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hN' : ((N : ℝ) + 1) ≤ (m : ℝ) + 1 := by exact_mod_cast hk
  have hk2 : 2 * r < (m : ℝ) + 1 := by linarith
  rw [hkc]
  set κ : ℝ := (m : ℝ) + 1 with hκ
  set a := κ⁻¹ • A with ha_def
  set b := κ⁻¹ • B with hb_def
  set ρ := κ⁻¹ * r with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, inv_mul_le_iff₀ hkpos]
    linarith
  have hna : ‖a‖ = κ⁻¹ * ‖A‖ := by
    rw [ha_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hkpos]
  have hnb : ‖b‖ = κ⁻¹ * ‖B‖ := by
    rw [hb_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hkpos]
  have hsum : ‖a‖ + ‖b‖ = ρ := by rw [hna, hnb, hρ, hr]; ring
  have haρ : ‖a‖ ≤ ρ := by linarith [norm_nonneg b]
  have hbρ : ‖b‖ ≤ ρ := by linarith [norm_nonneg a]
  have habρ : ‖a + b‖ ≤ ρ := (norm_add_le a b).trans hsum.le
  have ha1 : ‖a‖ ≤ 1 := haρ.trans hρ1
  have hb1 : ‖b‖ ≤ 1 := hbρ.trans hρ1
  have hab1 : ‖a + b‖ ≤ 1 := habρ.trans hρ1

  have hid : NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b) =
      (NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1) + (NormedSpace.exp a - 1 - a) * NormedSpace.exp b -
        (NormedSpace.exp (a + b) - 1 - (a + b)) := by
    noncomm_ring
  have q1 : ‖NormedSpace.exp b - 1 - b‖ ≤ ρ ^ 2 :=
    (norm_exp_sub_one_sub_le' b hb1).trans (pow_le_pow_left₀ (norm_nonneg _) hbρ 2)
  have q2 : ‖a * (NormedSpace.exp b - 1)‖ ≤ ρ * (2 * ρ) :=
    (norm_mul_le _ _).trans (mul_le_mul haρ ((norm_exp_sub_one_le' b hb1).trans (by linarith))
      (norm_nonneg _) hρ0)
  have hexpb : ‖NormedSpace.exp b‖ ≤ 3 :=
    (norm_exp_le' b).trans ((Real.exp_le_exp.mpr hb1).trans
      ((Real.exp_one_lt_d9).le.trans (by norm_num)))
  have q3 : ‖(NormedSpace.exp a - 1 - a) * NormedSpace.exp b‖ ≤ ρ ^ 2 * 3 :=
    (norm_mul_le _ _).trans (mul_le_mul ((norm_exp_sub_one_sub_le' a ha1).trans
      (pow_le_pow_left₀ (norm_nonneg _) haρ 2)) hexpb (norm_nonneg _) (by positivity))
  have q4 : ‖NormedSpace.exp (a + b) - 1 - (a + b)‖ ≤ ρ ^ 2 :=
    (norm_exp_sub_one_sub_le' (a + b) hab1).trans (pow_le_pow_left₀ (norm_nonneg _) habρ 2)
  have hD : ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤ 7 * ρ ^ 2 := by
    rw [hid]
    have := norm_sub_le ((NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1) +
      (NormedSpace.exp a - 1 - a) * NormedSpace.exp b) (NormedSpace.exp (a + b) - 1 - (a + b))
    have := norm_add_le ((NormedSpace.exp b - 1 - b) + a * (NormedSpace.exp b - 1))
      ((NormedSpace.exp a - 1 - a) * NormedSpace.exp b)
    have := norm_add_le (NormedSpace.exp b - 1 - b) (a * (NormedSpace.exp b - 1))
    nlinarith

  set M := Real.exp ρ with hMdef
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  have hS : ‖NormedSpace.exp a * NormedSpace.exp b‖ ≤ M := by
    refine (norm_mul_le _ _).trans ?_
    have := mul_le_mul (norm_exp_le' a) (norm_exp_le' b) (norm_nonneg _) (Real.exp_pos _).le
    rw [← Real.exp_add, hsum] at this
    exact this
  have hT : ‖NormedSpace.exp (a + b)‖ ≤ M := (norm_exp_le' _).trans (Real.exp_le_exp.mpr habρ)
  have hTk : NormedSpace.exp (a + b) ^ (m + 1) = NormedSpace.exp (A + B) := by
    rw [exp_pow_eqA, ha_def, hb_def, ← smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hkc,
      mul_inv_cancel₀ hkpos.ne', one_smul]
  have hmain := norm_pow_sub_pow_le' _ _ hM0 hS hT m
  rw [hTk] at hmain
  have hMm : M ^ m ≤ Real.exp r := by
    rw [hMdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hρ, ← mul_assoc]
    have : (m : ℝ) * κ⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hkpos]
      linarith
    nlinarith
  have hfin : ((m : ℝ) + 1) * M ^ m * ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤
      7 * r ^ 2 * Real.exp r / κ := by
    have h1 : ((m : ℝ) + 1) * M ^ m * ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤
        κ * Real.exp r * (7 * ρ ^ 2) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hMm hkpos.le) hD (norm_nonneg _)
      positivity
    have h2 : κ * Real.exp r * (7 * ρ ^ 2) = 7 * r ^ 2 * Real.exp r / κ := by
      rw [hρ]
      field_simp
    linarith
  exact hmain.trans hfin

end Trotter

section Mat

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra



end Mat




end PI.IwaMeasEx.Gauge.ZetaZeros

end
end
