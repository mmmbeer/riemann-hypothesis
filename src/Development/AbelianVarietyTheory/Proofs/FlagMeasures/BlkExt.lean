import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SnMass
open scoped ENNReal

namespace GlobalTheory.GramExp

def GDef {N a : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (X : Fin N → Fin a → ℂ) : Prop :=
  ((Matrix.of X)ᴴ * H * Matrix.of X).det ≠ 0 ∧ PosOnPerp H (Matrix.of X)

def GGram {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (a : ℕ) : Set (HCo a) :=
  {t | ∃ X : Fin N → Fin a → ℂ, (Matrix.of X)ᴴ * H * Matrix.of X = hOf t ∧ GDef H X}

def GLaw {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (a : ℕ) (μ : Measure (Fin N → Fin N → ℂ)) (C : ℝ) : Prop :=
  0 < C ∧ ∀ Φ : (Fin N → Fin a → ℂ) → ℝ≥0∞, Measurable Φ → ∀ s : HCo a → Fin N → Fin a → ℂ,
    (∀ t ∈ GGram H a, (Matrix.of (s t))ᴴ * H * Matrix.of (s t) = hOf t) →
    (2 : ℝ≥0∞) ^ (N * a) * ∫⁻ X in {X | GDef H X}, Φ X =
      (2 : ℝ≥0∞) ^ (a * (a - 1) / 2) * ∫⁻ t in GGram H a,
        ENNReal.ofReal (C * ‖(hOf t).det‖ ^ (N - a)) *
          ∫⁻ g, Φ (Matrix.of.symm (Matrix.of g * Matrix.of (s t))) ∂μ




def Sgn {a : ℕ} (d : Fin a → ℂ) : Prop := ∀ i, d i = 1 ∨ d i = -1

def Dg {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  Matrix.diagonal (Fin.append d fun _ : Fin m => (1 : ℂ))

def E0 (a m : ℕ) : Matrix (Fin (a + m)) (Fin a) ℂ := fun i j => if i = Fin.castAdd m j then 1 else 0

def embB (a : ℕ) {m : ℕ} (b : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  blockM 1 0 0 b

abbrev MP (a m : ℕ) : Type := (Fin m → Fin a → ℂ) × HCo a

def Ym {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (y : MP a m) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  Dg d m * (Complex.I • blockM (hOf y.2) (Matrix.of y.1)ᴴ (Matrix.of y.1) 0)

def xu {a : ℕ} (d : Fin a → ℂ) (u : HCo a) : Matrix (Fin a) (Fin a) ℂ :=
  1 + (1 / 2 : ℂ) • (Matrix.diagonal d * hOf u)

def tau {a : ℕ} (d : Fin a → ℂ) (u : HCo a) : HCo a := coOf ((xu d u)ᴴ * Matrix.diagonal d * xu d u)

def chi {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (p : MP a m × HCo a) : Fin (a + m) → Fin a → ℂ :=
  Matrix.of.symm (NormedSpace.exp (Ym d m p.1) * E0 a m * xu d p.2)

def psiB (m : ℕ) (v : HCo m) : Matrix (Fin m) (Fin m) ℂ := NormedSpace.exp (Complex.I • hOf v)

def phiG {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (p : MP a m × HCo m) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  NormedSpace.exp (Ym d m p.1) * embB a (psiB m p.2)

theorem sgn_append {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) : Sgn (Fin.append d fun _ : Fin m => (1 : ℂ)) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using hd j
  · simp

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.diag_sq {a : ℕ} {d : Fin a → ℂ}
    (hd : _root_.GlobalTheory.GramExp.Sgn d) : Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]

theorem diag_herm {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) : (Matrix.diagonal d)ᴴ = Matrix.diagonal d := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext i; rcases hd i with h | h <;> simp [h]

theorem Dg_sq {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) : Dg d m * Dg d m = 1 := diag_sq (sgn_append hd m)

theorem Dg_herm {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) : (Dg d m)ᴴ = Dg d m := diag_herm (sgn_append hd m)

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.GramExp.isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H * H = 1) : _root_.PI.IsMatGroup (_root_.Formalism.QuantumDeterminants.UH H) := by
  unfold _root_.PI.IsMatGroup _root_.Formalism.QuantumDeterminants.UH
  have hdetH : H.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hH
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hunit : ∀ a : Matrix (Fin N) (Fin N) ℂ, aᴴ * H * a = H → IsUnit a.det := by
    intro a ha
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul] at this
    have h1 : aᴴ.det * a.det = 1 := by
      have : (aᴴ.det * a.det) * H.det = 1 * H.det := by linear_combination this
      exact mul_right_cancel₀ hdetH this
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · simp
  · intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hu := hunit a ha
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    have hc : (a⁻¹)ᴴ * aᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = ((a⁻¹)ᴴ * aᴴ) * H * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hc, hr, Matrix.one_mul, Matrix.mul_one]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.exp_cont {n : ℕ} :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous

theorem blockM_herm {a b : ℕ} (P : Matrix (Fin a) (Fin a) ℂ) (Q : Matrix (Fin a) (Fin b) ℂ)
    (R : Matrix (Fin b) (Fin a) ℂ) (S : Matrix (Fin b) (Fin b) ℂ) :
    (blockM P Q R S)ᴴ = blockM Pᴴ Rᴴ Qᴴ Sᴴ := by
  simp only [blockM, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]

theorem blockM_mul {a b : ℕ} (P P' : Matrix (Fin a) (Fin a) ℂ) (Q Q' : Matrix (Fin a) (Fin b) ℂ)
    (R R' : Matrix (Fin b) (Fin a) ℂ) (S S' : Matrix (Fin b) (Fin b) ℂ) :
    blockM P Q R S * blockM P' Q' R' S' =
      blockM (P * P' + Q * R') (P * Q' + Q * S') (R * P' + S * R') (R * Q' + S * S') := by
  simp only [blockM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem Dg_eq {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : Dg d m = blockM (Matrix.diagonal d) 0 0 1 := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [Dg, blockM, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> omega

theorem lie_of_herm {N : ℕ} {H A : Matrix (Fin N) (Fin N) ℂ} (h1 : Hᴴ = H) (h2 : H * H = 1) (hA : Aᴴ = A) :
    (H * (Complex.I • A))ᴴ * H + H * (H * (Complex.I • A)) = 0 := by
  rw [Matrix.conjTranspose_mul, h1, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h2, Matrix.conjTranspose_smul, hA]
  simp

theorem exp_Ym_mem {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) (y : MP a m) :
    NormedSpace.exp (Ym d m y) ∈ UH (Dg d m) :=
  CCRuleCW.exp_mem_UH _ _ (lie_of_herm (Dg_herm hd m) (Dg_sq hd m) (by
    rw [blockM_herm, (hOf_isHermitian y.2).eq]; simp))

theorem psiB_mem (m : ℕ) (v : HCo m) : psiB m v ∈ UH (1 : Matrix (Fin m) (Fin m) ℂ) := by
  have := lie_of_herm (H := (1 : Matrix (Fin m) (Fin m) ℂ)) (by simp) (by simp) (hOf_isHermitian v).eq
  rw [Matrix.one_mul (Complex.I • hOf v)] at this
  exact CCRuleCW.exp_mem_UH _ _ this


theorem embB_mem {a : ℕ} (d : Fin a → ℂ) {m : ℕ} {b : Matrix (Fin m) (Fin m) ℂ}
    (hb : b ∈ UH (1 : Matrix (Fin m) (Fin m) ℂ)) : embB a b ∈ UH (Dg d m) := by
  have hb' : bᴴ * 1 * b = 1 := hb
  show (embB a b)ᴴ * Dg d m * embB a b = Dg d m
  rw [Dg_eq, embB, blockM_herm, blockM_mul, blockM_mul]
  simp only [Matrix.mul_one] at hb'
  simp [hb']

theorem phiG_mem {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) (p : MP a m × HCo m) : phiG d m p ∈ UH (Dg d m) :=
  CCRuleCW.UH_mul _ _ _ (exp_Ym_mem hd m _) (embB_mem d (psiB_mem m _))







open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.GramExp.measurableSet_image_ball {X Y : Type} [PseudoMetricSpace X] [ProperSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X → Y}
    (hf : Continuous f) (x : X) (ρ : ℝ) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have hb : Metric.ball x ρ = ⋃ k : ℕ, Metric.closedBall x (ρ - 1 / ((k : ℝ) + 1)) := by
    ext y
    simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hb, Set.image_iUnion]
  exact MeasurableSet.iUnion fun k =>
    ((isCompact_closedBall x _).image hf).isClosed.measurableSet

end GlobalTheory.GramExp
end
end

section
namespace GlobalTheory.MatrixExtLast

theorem matrix_ext_last {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h₁ : ∀ i j : Fin k, M (Fin.castSucc i) (Fin.castSucc j) = N (Fin.castSucc i) (Fin.castSucc j))
    (h₂ : ∀ i : Fin k, M (Fin.castSucc i) (Fin.last k) = N (Fin.castSucc i) (Fin.last k))
    (h₃ : ∀ j : Fin k, M (Fin.last k) (Fin.castSucc j) = N (Fin.last k) (Fin.castSucc j))
    (h₄ : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h₄
    | cast j => exact h₃ j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h₂ i
    | cast j => exact h₁ i j

end GlobalTheory.MatrixExtLast
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.Tube

def Hd (k : ℕ) (η : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1

def blk {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => Fin.lastCases (motive := fun _ => ℂ) (Fin.lastCases (motive := fun _ => ℂ) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => ℂ) (b i') (A i') j) i

@[simp] theorem blk_ll {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) :
    blk A b r d (Fin.last k) (Fin.last k) = d := by simp [blk]

@[simp] theorem blk_lc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (j : Fin k) :
    blk A b r d (Fin.last k) j.castSucc = r j := by simp [blk]

@[simp] theorem blk_cl {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i : Fin k) :
    blk A b r d i.castSucc (Fin.last k) = b i := by simp [blk]

@[simp] theorem blk_cc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i j : Fin k) :
    blk A b r d i.castSucc j.castSucc = A i j := by simp [blk]

theorem blk_ext {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h1 : ∀ i j : Fin k, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin k, M i.castSucc (Fin.last k) = N i.castSucc (Fin.last k))
    (h3 : ∀ j : Fin k, M (Fin.last k) j.castSucc = N (Fin.last k) j.castSucc)
    (h4 : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  first
  | exact @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | (apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last ..)

theorem Hd_eq (k : ℕ) (η : ℝ) : Hd k η = blk 1 0 0 (η : ℂ) := by
  refine blk_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_
  · simp [Hd, Matrix.diagonal_apply, Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, (Fin.castSucc_ne_last _).symm]
  · simp [Hd]

theorem Hd_sq (k : ℕ) {η : ℝ} (hη : η = 1 ∨ η = -1) : Hd k η * Hd k η = 1 := by
  refine GlobalTheory.GramExp.diag_sq fun i => ?_
  split_ifs
  · rcases hη with h | h <;> simp [h]
  · simp

def nsq {k : ℕ} (β : Fin k → ℂ) : ℝ := ∑ j, ‖β j‖ ^ 2

def dd {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : ℝ := Real.sqrt (1 - η * nsq β)

def sec {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j - ((η / (1 + dd η β) : ℝ) : ℂ) * (conj (β i) * β j))
    (fun i => -(η : ℂ) * conj (β i)) β (dd η β : ℂ)

def kap {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := blk A 0 0 u

def row {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => g (Fin.last k) j.castSucc

def ph {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ :=
  g (Fin.last k) (Fin.last k) / (‖g (Fin.last k) (Fin.last k)‖ : ℂ)

def bet {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => conj (ph g) * row g j

def top {k : ℕ} (η : ℝ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => (g * sec η (-bet g)) i.castSucc j.castSucc

abbrev Par (k : ℕ) : Type := lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) × ℝ × EuclideanSpace ℂ (Fin k)

def hv {k : ℕ} (w : EuclideanSpace ℂ (Fin k)) : Fin k → ℂ := fun j => w j / (Real.sqrt 2 : ℂ)

def chart {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  kap (NormedSpace.exp (unrealify (x.1 : EuclideanSpace ℝ _))) (Complex.exp (x.2.1 * Complex.I)) * sec η (hv x.2.2)

def tang {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (unrealify (x.1 : EuclideanSpace ℝ _)) (fun i => -(η : ℂ) * conj (hv x.2.2 i)) (hv x.2.2) (x.2.1 * Complex.I)

def tubeO (k : ℕ) (η t : ℝ) : Set (PI.MtM (k + 1)) :=
  {g | Matrix.of g ∈ UH (Hd k η) ∧ nsq (row (Matrix.of g)) < t}

end GlobalTheory.Tube
end
end
