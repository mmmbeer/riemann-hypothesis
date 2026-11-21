import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

namespace ReciprocityTheory.AnForm.M

open OnePoint

noncomputable section

section Alg

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem FinHolAtlas.HoloOn.mono' {A : FinHolAtlas e X} {U V : Set X} {g : X → ℂ}
    (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem FinHolAtlas.SmoothOn.mono' {A : FinHolAtlas e X} {U V : Set X} {f : X → ℝ}
    (h : A.SmoothOn U f) (hVU : V ⊆ U) : A.SmoothOn V f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem FinHolAtlas.HoloOn.add' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x + g x) :=
  fun j => (hf j).add (hg j)

theorem FinHolAtlas.HoloOn.mul' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x * g x) :=
  fun j => (hf j).mul (hg j)

theorem FinHolAtlas.SmoothOn.add' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℝ}
    (hf : A.SmoothOn U f) (hg : A.SmoothOn U g) : A.SmoothOn U (fun x => f x + g x) :=
  fun j => (hf j).add (hg j)

end Alg

namespace CompatibleChartOperations


def shearLE : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 0 - v 1, v 1]
  invFun v := ![v 0 + v 1, v 1]
  map_add' u v := by ext i; fin_cases i <;> simp [add_sub_add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp [mul_sub]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

def shearCLE : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) := shearLE.toContinuousLinearEquiv


open scoped Classical in
theorem projLineChart1_symm_ite (t : Fin 1 → ℂ) :
    projectiveLineChartAtInfinity.symm t = if t 0 = 0 then ∞ else (((t 0)⁻¹ : ℂ) : OnePoint ℂ) := rfl

open scoped Classical in
theorem fsPot_U_ite (a : OnePoint ℂ) :
    fsPot.U a = if a = ∞ then projectiveLineChartAtInfinity.source else projectiveLineChartAtZero.source := rfl

open scoped Classical in
theorem fsPot_φ_ite (a p : OnePoint ℂ) : fsPot.φ a p = if a = ∞ then (1 / 2) * Real.log (1 + ‖crd1 p‖ ^ 2)
    else (1 / 2) * Real.log (1 + ‖crd0 p‖ ^ 2) := rfl

def homogeneousCoord (p : OnePoint ℂ) : ℂ × ℂ := p.elim (0, 1) (fun z => (1, z))

open scoped Classical in

def homogeneousLift (a p : OnePoint ℂ) : ℂ × ℂ := if a = ∞ then (crd1 p, 1) else (1, crd0 p)

def det2 (u v : ℂ × ℂ) : ℂ := u.1 * v.2 - u.2 * v.1

def nrm2 (u : ℂ × ℂ) : ℝ := Real.sqrt (‖u.1‖ ^ 2 + ‖u.2‖ ^ 2)

open scoped Classical in

def chartIndexAt (a : OnePoint ℂ) : Fin 2 := if a = ∞ then 1 else 0

def chartCoordAt (a p : OnePoint ℂ) : ℂ := (p1.chart (chartIndexAt a) p) 0



theorem pairDet_smul (c d : ℂ) (u v : ℂ × ℂ) : det2 (c • u) (d • v) = c * d * det2 u v := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem fsPot_φ_eq (a p : OnePoint ℂ) : fsPot.φ a p = Real.log (nrm2 (homogeneousLift a p)) := by
  rw [fsPot_φ_ite]
  unfold nrm2 homogeneousLift
  split_ifs <;> simp only [norm_one, one_pow] <;> rw [Real.log_sqrt (by positivity)] <;> ring_nf



theorem chart_chartIndexAt_infty {a : OnePoint ℂ} (ha : a = ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtInfinity := by
  rw [chartIndexAt, if_pos ha]
  rfl

theorem chart_chartIndexAt_fin {a : OnePoint ℂ} (ha : a ≠ ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtZero := by
  rw [chartIndexAt, if_neg ha]
  rfl


open scoped Classical in
theorem pairDet_homogeneousLift_same (a p q : OnePoint ℂ) :
    det2 (homogeneousLift a p) (homogeneousLift a q) = (if a = ∞ then 1 else -1) * (chartCoordAt a p - chartCoordAt a q) := by
  by_cases ha : a = ∞
  · simp only [det2, homogeneousLift, chartCoordAt, if_pos ha, chart_chartIndexAt_infty ha]
    show crd1 p * 1 - 1 * crd1 q = 1 * (crd1 p - crd1 q)
    ring
  · simp only [det2, homogeneousLift, chartCoordAt, if_neg ha, chart_chartIndexAt_fin ha]
    show 1 * crd0 q - crd0 p * 1 = -1 * (crd0 p - crd0 q)
    ring



end CompatibleChartOperations

end

end ReciprocityTheory.AnForm.M
