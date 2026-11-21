import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.GramStrictPos
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrMulK

section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxe

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem contDiff_entry (i : ι) (j : κ) : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i j) := by
  have h1 : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i) := contDiff_pi.mp contDiff_id i
  exact contDiff_pi.mp h1 j

theorem contDiffOn_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (f : E → Matrix ι κ ℂ) : ContDiffOn ℝ ∞ f s ↔ ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s := by
  constructor
  · intro h i j
    exact contDiffOn_pi.mp (contDiffOn_pi.mp h i) j
  · intro h
    exact contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => h i j

theorem contDiff_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → Matrix ι κ ℂ) : ContDiff ℝ ∞ f ↔ ∀ i j, ContDiff ℝ ∞ (fun x => f x i j) := by
  constructor
  · intro h i j
    exact contDiff_pi.mp (contDiff_pi.mp h i) j
  · intro h
    exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => h i j

theorem contDiff_det : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have e : (fun x : Matrix ι ι ℂ => x.det) =
      fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x; exact Matrix.det_apply' x
  rw [e]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry _ _)

theorem contDiff_adjugate : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.adjugate) := by
  rw [contDiff_matrix_iff]
  intro i j
  simp only [Matrix.adjugate_apply]
  refine contDiff_det.comp ?_
  rw [contDiff_matrix_iff]
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

theorem isOpen_det_ne : IsOpen {x : Matrix ι ι ℂ | x.det ≠ 0} :=
  isOpen_ne_fun (contDiff_det (ι := ι)).continuous continuous_const

theorem contDiffOn_inv : ContDiffOn ℝ ∞ (fun x : Matrix ι ι ℂ => x⁻¹) {x | x.det ≠ 0} := by
  have h : ∀ x ∈ {x : Matrix ι ι ℂ | x.det ≠ 0}, x⁻¹ = (x.det)⁻¹ • x.adjugate := fun x _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContDiffOn.congr ?_ h
  rw [contDiffOn_matrix_iff]
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (contDiff_det.contDiffOn.inv fun x hx => hx).mul (contDiff_matrix_iff _ |>.mp contDiff_adjugate i j).contDiffOn

def entL (a : ι) (k : κ) : Matrix ι κ ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap { toFun := fun x => x a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] theorem entL_apply (a : ι) (k : κ) (x : Matrix ι κ ℂ) : entL a k x = x a k := rfl

theorem hasFDerivAt_inv_one :
    HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹) (-ContinuousLinearMap.id ℝ (Matrix ι ι ℂ)) 1 := by
  have hd : DifferentiableAt ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 :=
    (contDiffOn_inv.contDiffAt (isOpen_det_ne.mem_nhds (by simp))).differentiableAt (by simp)
  have hL := hd.hasFDerivAt
  set L := fderiv ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 with hLdef
  suffices hLe : L = -ContinuousLinearMap.id ℝ (Matrix ι ι ℂ) by rwa [hLe] at hL
  have hev : ∀ a b : ι, (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b) =ᶠ[nhds 1] fun _ => (1 : Matrix ι ι ℂ) a b := by
    intro a b
    filter_upwards [isOpen_det_ne.mem_nhds (show (1 : Matrix ι ι ℂ).det ≠ 0 by simp)] with x hx
    rw [Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)]
  have hent : ∀ a b : ι, HasFDerivAt (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b)
      (∑ k, ((1 : Matrix ι ι ℂ) a k • (entL k b).comp L + ((1 : Matrix ι ι ℂ)⁻¹ k b) • entL a k)) 1 := by
    intro a b
    simp only [Matrix.mul_apply]
    refine HasFDerivAt.fun_sum (u := Finset.univ) (A := fun k (x : Matrix ι ι ℂ) => x a k * x⁻¹ k b) fun k _ => ?_
    have h1 : HasFDerivAt (fun x : Matrix ι ι ℂ => x a k) (entL a k) 1 := (entL a k).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹ k b) ((entL k b).comp L) 1 := (entL k b).hasFDerivAt.comp 1 hL
    exact h1.mul h2
  ext X i j
  have h0 := (hent i j).unique ((hasFDerivAt_const ((1 : Matrix ι ι ℂ) i j) (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq (hev i j))
  have h0X := congrArg (fun T : Matrix ι ι ℂ →L[ℝ] ℂ => T X) h0
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, entL_apply, smul_eq_mul, inv_one,
    ContinuousLinearMap.zero_apply, Finset.sum_add_distrib] at h0X
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq'] at h0X
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Matrix.neg_apply]
  linear_combination h0X

end PositivityTheory.RgBcC.Cxe
end
end

section
noncomputable section

open Matrix
open scoped ContDiff Kronecker

namespace PositivityTheory.RgBcC.Cxe

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem contDiffOn_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f g : E → Matrix ι ι ℂ} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) : ContDiffOn ℝ ∞ (fun x => f x * g x) s := by
  rw [contDiffOn_matrix_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf i k).mul (hg k j)

theorem contDiffOn_kron {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f : E → Matrix ι ι ℂ} {g : E → Matrix κ κ ℂ} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) :
    ContDiffOn ℝ ∞ (fun x => f x ⊗ₖ g x) s := by
  rw [contDiffOn_matrix_iff] at hf hg ⊢
  rintro ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.kroneckerMap_apply]
  exact (hf i k).mul (hg j l)

theorem contDiffOn_transpose {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f : E → Matrix ι ι ℂ} (hf : ContDiffOn ℝ ∞ f s) : ContDiffOn ℝ ∞ (fun x => (f x)ᵀ) s := by
  rw [contDiffOn_matrix_iff] at hf ⊢
  intro i j
  exact hf j i

theorem contDiff_conjTranspose : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => xᴴ) := by
  rw [contDiff_matrix_iff]
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp (contDiff_entry j i)

def cTL : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => xᴴ, map_add' := fun x y => Matrix.conjTranspose_add x y,
      map_smul' := fun r x => by ext i j; simp [Matrix.conjTranspose_apply] }

@[simp] theorem cTL_apply (x : Matrix ι ι ℂ) : cTL x = xᴴ := rfl

def mulLL (S : Matrix κ κ ℂ) : Matrix κ κ ℂ →L[ℝ] Matrix κ κ ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => S * M, map_add' := fun M N => Matrix.mul_add S M N,
      map_smul' := fun r M => by ext i j; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm] }

def mulRL (S : Matrix κ κ ℂ) : Matrix κ κ ℂ →L[ℝ] Matrix κ κ ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * S, map_add' := fun M N => Matrix.add_mul M N S,
      map_smul' := fun r M => by ext i j; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

@[simp] theorem mulLL_apply (S M : Matrix κ κ ℂ) : mulLL S M = S * M := rfl
@[simp] theorem mulRL_apply (S M : Matrix κ κ ℂ) : mulRL S M = M * S := rfl

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := isOpen_det_ne

theorem mem_GLs {x : Mat n} : x ∈ GLs n ↔ IsUnit x.det := by
  simp [GLs, isUnit_iff_ne_zero]

theorem contDiff_Mt : ContDiff ℝ ∞ (fun y : Mat n => Mt y) := by
  rw [contDiff_matrix_iff]
  intro p q
  simp only [Mt, cf, LinearMap.coe_mk, AddHom.coe_mk]
  refine Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp ?_)
  simp only [Matrix.trace]
  refine ContDiff.sum fun i _ => ?_
  have h : ContDiff ℝ ∞ (fun y : Mat n => y * hbM q * yᴴ * hbM p) := by
    have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => y * hbM q * yᴴ * hbM p) Set.univ :=
      contDiffOn_mul (contDiffOn_mul (contDiffOn_mul contDiffOn_id contDiffOn_const) contDiff_conjTranspose.contDiffOn)
        contDiffOn_const
    exact contDiffOn_univ.mp h1
  exact (contDiff_matrix_iff _).mp h i i

theorem rm_inv (hR : RmLaws) (lam : Fin n → ℤ) {x : Mat n} (hx : IsUnit x.det) : Rm lam x⁻¹ = (Rm lam x)⁻¹ := by
  have hx' : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hx
  have h : Rm lam x⁻¹ * Rm lam x = 1 := by
    rw [← (hR n lam).2.1 _ _ hx' hx, Matrix.nonsing_inv_mul x hx, (hR n lam).1]
  exact (Matrix.inv_eq_left_inv h).symm

theorem rm_det (hR : RmLaws) (lam : Fin n → ℤ) {x : Mat n} (hx : IsUnit x.det) : (Rm lam x).det ≠ 0 := by
  have hx' : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hx
  have h : Rm lam x * Rm lam x⁻¹ = 1 := by
    rw [← (hR n lam).2.1 _ _ hx hx', Matrix.mul_nonsing_inv x hx, (hR n lam).1]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem isUnit_det_cT {x : Mat n} (hx : IsUnit x.det) : IsUnit xᴴ.det := by
  rw [Matrix.det_conjTranspose]; exact hx.star

theorem rhoW_contDiffOn (hR : RmLaws) (lam : Fin n → ℤ) : ContDiffOn ℝ ∞ (rhoW lam) (GLs n) := by
  have hRm := (hR n lam).2.2
  have h1 : ContDiffOn ℝ ∞ (fun x : Mat n => (Rm lam x)⁻¹) (GLs n) :=
    contDiffOn_inv.comp hRm fun x hx => rm_det hR lam (mem_GLs.mp hx)
  have h2 : ContDiffOn ℝ ∞ (fun x : Mat n => Rm lam xᴴ) (GLs n) :=
    hRm.comp contDiff_conjTranspose.contDiffOn fun x hx => mem_GLs.mpr (isUnit_det_cT (mem_GLs.mp hx))
  exact contDiffOn_kron (contDiffOn_transpose h1) (contDiffOn_transpose h2)

theorem frame_zero_contDiffOn (hR : RmLaws) (hD : GamDer) (lam : Fin n → ℤ) : ContDiffOn ℝ ∞ (fr0 lam) (GLs n) := by
  have hg : ContDiff ℝ ∞ (gamM (n := n)) := (hD n).1.restrict_scalars ℝ
  have hinv : ContDiffOn ℝ ∞ (fun x : Mat n => (Mt x⁻¹)ᵀ) (GLs n) :=
    contDiffOn_transpose (contDiff_Mt.comp_contDiffOn contDiffOn_inv)
  exact contDiffOn_kron (hg.comp_contDiffOn hinv) (rhoW_contDiffOn hR lam)

theorem fr0Laws_of (hR : RmLaws) (hG : GamMul) (hM : MtLaws) (hD : GamDer) : MatrixFrechetDerivativeAtZeroLaws := by
  intro n lam
  refine ⟨?_, ?_, frame_zero_contDiffOn hR hD lam⟩
  · simp only [fr0, rhoW, inv_one, (hM n).1, Matrix.transpose_one, (hG n).1, (hR n lam).1, Matrix.conjTranspose_one,
      Matrix.one_kronecker_one]
  · intro x y hx hy
    have hxy := (hR n lam).2.1 x y hx hy
    have hyx := (hR n lam).2.1 yᴴ xᴴ (isUnit_det_cT hy) (isUnit_det_cT hx)
    simp only [fr0, rhoW]
    rw [Matrix.mul_inv_rev, (hM n).2.1, Matrix.transpose_mul, (hG n).2, Matrix.conjTranspose_mul, hxy, hyx,
      Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

theorem swap_kron (lam : Fin n → ℤ) (A B : Matrix (Jd n lam) (Jd n lam) ℂ) :
    swapJ lam * (A ⊗ₖ B) = (B ⊗ₖ A) * swapJ lam := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swapJ, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem swap_swap (lam : Fin n → ℤ) : swapJ lam * swapJ lam = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swapJ, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, ite_and, Matrix.one_apply,
    Prod.mk.injEq]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2, eq_comm]

theorem swap_cT (lam : Fin n → ℤ) : (swapJ lam)ᴴ = swapJ lam := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.conjTranspose_apply, swapJ]
  by_cases h : k = j ∧ l = i
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2.symm, h'.1.symm⟩]; simp

theorem trace_kron_swap (lam : Fin n → ℤ) (A B : Matrix (Jd n lam) (Jd n lam) ℂ) :
    ((A ⊗ₖ B) * swapJ lam).trace = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, swapJ, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem swap_rhoW (hR : RmLaws) (lam : Fin n → ℤ) {x : Mat n} (hx : IsUnit x.det) :
    swapJ lam * rhoW lam (xᴴ)⁻¹ = rhoW lam x * swapJ lam := by
  have hxc := isUnit_det_cT hx
  have e1 : ((xᴴ)⁻¹)ᴴ = x⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]
  have e2 : (Rm lam (xᴴ)⁻¹)⁻¹ = Rm lam xᴴ := by rw [rm_inv hR lam hxc, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (rm_det hR lam hxc))]
  simp only [rhoW]
  rw [e1, e2, rm_inv hR lam hx, swap_kron]

theorem swapLaws_of (hR : RmLaws) : SwapLaws := by
  intro n lam
  refine ⟨swap_swap lam, ?_, fun x hx => swap_rhoW hR lam hx, ?_, trace_kron_swap lam⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, swap_cT, swap_swap]
  · intro X hXh0
    have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
    have hd : DifferentiableAt ℝ (rhoW lam) 1 :=
      ((rhoW_contDiffOn hR lam).contDiffAt (isOpen_GLs.mem_nhds h1)).differentiableAt (by simp)
    set D := fderiv ℝ (rhoW lam) 1
    have hD : HasFDerivAt (rhoW lam) D 1 := hd.hasFDerivAt
    have hθ : HasFDerivAt (fun x : Mat n => (xᴴ)⁻¹) ((-ContinuousLinearMap.id ℝ (Mat n)).comp cTL) 1 := by
      have h' : HasFDerivAt (fun x : Mat n => x⁻¹) (-ContinuousLinearMap.id ℝ (Mat n)) (cTL (1 : Mat n)) := by
        rw [cTL_apply, Matrix.conjTranspose_one]; exact hasFDerivAt_inv_one
      exact h'.comp (1 : Mat n) (cTL.hasFDerivAt (x := (1 : Mat n)))
    have hF : HasFDerivAt (fun x : Mat n => swapJ lam * rhoW lam (xᴴ)⁻¹)
        ((mulLL (swapJ lam)).comp (D.comp ((-ContinuousLinearMap.id ℝ (Mat n)).comp cTL))) 1 := by
      have hc : HasFDerivAt (fun x : Mat n => rhoW lam (xᴴ)⁻¹) (D.comp ((-ContinuousLinearMap.id ℝ (Mat n)).comp cTL)) 1 := by
        have e : (((1 : Mat n))ᴴ)⁻¹ = 1 := by simp
        have hD' : HasFDerivAt (rhoW lam) D (((1 : Mat n))ᴴ)⁻¹ := by rw [e]; exact hD
        exact hD'.comp (1 : Mat n) hθ
      exact (mulLL (swapJ lam)).hasFDerivAt.comp (1 : Mat n) hc
    have hG : HasFDerivAt (fun x : Mat n => rhoW lam x * swapJ lam) ((mulRL (swapJ lam)).comp D) 1 :=
      (mulRL (swapJ lam)).hasFDerivAt.comp (1 : Mat n) hD
    have hev : (fun x : Mat n => swapJ lam * rhoW lam (xᴴ)⁻¹) =ᶠ[nhds 1] fun x => rhoW lam x * swapJ lam := by
      filter_upwards [isOpen_GLs.mem_nhds h1] with x hx
      exact swap_rhoW hR lam (mem_GLs.mp hx)
    have huniq := hF.unique (hG.congr_of_eventuallyEq hev)
    have hX := congrArg (fun T : Mat n →L[ℝ] Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ => T X) huniq
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, cTL_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, mulLL_apply, mulRL_apply, map_neg] at hX
    rw [hXh0.eq] at hX
    rw [← hX, neg_neg]

end PositivityTheory.RgBcC.Cxe
end
end

section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxeeig

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem inf_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  show (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1) ≤ ⊤)

theorem diffAt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : DifferentiableAt ℝ f g :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hg)

theorem rd_std (F : Mat n → ℂ) (g X : Mat n) : Rd X F g = fderiv ℝ F g (g * X) := rfl

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

theorem rd_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) := by
  exact (hf.fderiv_of_isOpen isOpen_GLs inf_add_one_le).clm_apply (mulR X).contDiff.contDiffOn

theorem eu_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (b c : Fin n) : ContDiffOn ℝ ∞ (Eu s b c f) (GLs n) := by
  unfold Eu
  exact ((rd_contDiffOn hf _).add ((rd_contDiffOn hf _).const_smul _)).const_smul _

theorem epow_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) : ∀ m b c, ContDiffOn ℝ ∞ (Epow s m b c f) (GLs n) := by
  intro m
  induction m with
  | zero =>
    intro b c
    simp only [Epow]
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    intro b c
    have e : Epow s (m + 1) b c f = fun x => ∑ d, Eu s b d (Epow s m d c f) x := by
      funext x; simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun d _ => eu_contDiffOn (ih d c) s b d

theorem eu_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f₁ f₂ : Mat n → V} {g : Mat n}
    (h : f₁ =ᶠ[𝓝 g] f₂) (s : Bool) (b c : Fin n) : Eu s b c f₁ g = Eu s b c f₂ g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, h.fderiv_eq]

theorem eu_mul {F a : Mat n → ℂ} {g : Mat n} (hF : DifferentiableAt ℝ F g) (ha : DifferentiableAt ℝ a g)
    (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => F x * a x) g = F g * Eu s b c a g + a g * Eu s b c F g := by
  have hm : fderiv ℝ (fun x => F x * a x) g = F g • fderiv ℝ a g + a g • fderiv ℝ F g :=
    (hF.hasFDerivAt.fun_mul ha.hasFDerivAt).fderiv
  have key : ∀ X : Mat n, Rd X (fun x => F x * a x) g = F g * Rd X a g + a g * Rd X F g := by
    intro X
    rw [rd_std, rd_std, rd_std, hm]
    simp [smul_eq_mul]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, smul_eq_mul]
  ring

theorem eu_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (ψ : ι → Mat n → ℂ) (v : ι → V)
    {g : Mat n} (hψ : ∀ i, DifferentiableAt ℝ (ψ i) g) (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => ∑ i, ψ i x • v i) g = ∑ i, Eu s b c (ψ i) g • v i := by
  have key : ∀ X : Mat n, Rd X (fun x => ∑ i, ψ i x • v i) g = ∑ i, Rd X (ψ i) g • v i := by
    intro X
    simp only [rd_std]
    have h : HasFDerivAt (fun x => ∑ i, ψ i x • v i) (∑ i, (fderiv ℝ (ψ i) g).smulRight (v i)) g :=
      HasFDerivAt.fun_sum fun i _ => (hψ i).hasFDerivAt.smul_const (v i)
    unfold Rd
    rw [h.fderiv]
    simp [ContinuousLinearMap.smulRight_apply]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul _ (Rd (Matrix.single b c Complex.I) (ψ i) g), ← add_smul, smul_smul]
  congr 1

theorem epow_mul_of_kill {F G : Mat n → ℂ} (hF : ContDiffOn ℝ ∞ F (GLs n)) (hG : ContDiffOn ℝ ∞ G (GLs n)) (s : Bool)
    (hk : ∀ g ∈ GLs n, ∀ b c, Eu s b c F g = 0) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => F x * G x) g = F g * Epow s m b c G g := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have he : Epow s m d c (fun x => F x * G x) =ᶠ[𝓝 g] fun x => F x * Epow s m d c G x :=
      Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
    rw [eu_congr he, eu_mul (diffAt hF hg) (diffAt (epow_contDiffOn hG s m d c) hg), hk g hg, mul_zero, add_zero]

theorem epow_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : ι → Mat n → ℂ) (v : ι → V)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (GLs n)) (s : Bool) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => ∑ i, φ i x • v i) g = ∑ i, Epow s m b c (φ i) g • v i := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply]
    have step : ∀ d, Eu s b d (Epow s m d c fun x => ∑ i, φ i x • v i) g =
        ∑ i, Eu s b d (Epow s m d c (φ i)) g • v i := by
      intro d
      have he : (Epow s m d c fun x => ∑ i, φ i x • v i) =ᶠ[𝓝 g] fun x => ∑ i, Epow s m d c (φ i) x • v i :=
        Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
      rw [eu_congr he, eu_sum_smul _ _ (fun i => diffAt (epow_contDiffOn (hφ i) s m d c) hg)]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]

end PositivityTheory.RgBcC.Cxeeig

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC.Cxeeig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eigProd : EigProd := by
  intro n χ ι V _ _ _ h a v hh ha hhe hae
  have hφ : ∀ i, ContDiffOn ℝ ∞ (fun x => h i x * a i x) (GLs n) := fun i => (hh i).mul (ha i)
  intro s m g hg
  have hsum : gel s m (fun x => ∑ i, (h i x * a i x) • v i) g =
      ∑ i, gel s m (fun x => h i x * a i x) g • v i := by
    simp only [gel, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun b _ => epow_sum_smul (fun i x => h i x * a i x) v hφ s m b b g hg, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
  have hone : ∀ i, gel s m (fun x => h i x * a i x) g = GlobalTheory.Dec.gelfVal (χ s) m * (h i g * a i g) := by
    intro i
    cases s with
    | true =>
      have e : (fun x => h i x * a i x) = fun x => a i x * h i x := by funext x; ring
      simp only [gel, Finset.sum_apply]
      rw [e, Finset.sum_congr rfl fun b _ => epow_mul_of_kill (ha i) (hh i) true (fun g hg b c => (hae i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hhe i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
    | false =>
      simp only [gel, Finset.sum_apply]
      rw [Finset.sum_congr rfl fun b _ => epow_mul_of_kill (hh i) (ha i) false (fun g hg b c => (hhe i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hae i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hone i, smul_smul]

end PositivityTheory.RgBcC
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgBcC.CxeAvg

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem lefFr_eq (lam : Fin n → ℤ) (x : Mat n) :
    lefFr n lam x = sqQ lam * (clm lam (fr0 lam x) * Ring.inverse (sqQ lam)) := rfl

theorem sq_inv (hA : Avg) (lam : Fin n → ℤ) :
    sqQ lam * Ring.inverse (sqQ lam) = 1 ∧ Ring.inverse (sqQ lam) * sqQ lam = 1 :=
  ⟨Ring.mul_inverse_cancel _ (hA n lam).1, Ring.inverse_mul_cancel _ (hA n lam).1⟩

theorem adjoint_inv (hA : Avg) (lam : Fin n → ℤ) :
    ContinuousLinearMap.adjoint (Ring.inverse (sqQ (n := n) lam)) = Ring.inverse (sqQ lam) := by
  obtain ⟨h1, _⟩ := sq_inv hA lam
  have hs : star (sqQ (n := n) lam) = sqQ lam := (hA n lam).2.1.star_eq
  rw [← ContinuousLinearMap.star_eq_adjoint]
  have key : star (Ring.inverse (sqQ (n := n) lam)) * star (sqQ lam) = 1 := by
    rw [← star_mul, h1, star_one]
  rw [hs] at key
  calc star (Ring.inverse (sqQ (n := n) lam))
      = star (Ring.inverse (sqQ (n := n) lam)) * (sqQ lam * Ring.inverse (sqQ lam)) := by
        rw [h1, mul_one]
    _ = (star (Ring.inverse (sqQ (n := n) lam)) * sqQ lam) * Ring.inverse (sqQ lam) := by
        rw [mul_assoc]
    _ = Ring.inverse (sqQ lam) := by rw [key, one_mul]

theorem clm_mul' (lam : Fin n → ℤ) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    clm lam (A * B) = clm lam A * clm lam B := by simp only [clm, map_mul]

end PositivityTheory.RgBcC.CxeAvg

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.CxeAvg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frOne' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrOne := by
  intro n lam
  rw [lefFr_eq, (hF n lam).1]
  simp only [clm, map_one, one_mul]
  exact (sq_inv hA lam).1

theorem frMulK' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrMulK := by
  intro n lam k k'
  have h2 := (sq_inv hA lam).2
  rw [CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, Submonoid.coe_mul,
    (hF n lam).2.1 _ _ (Matrix.UnitaryGroup.det_isUnit k) (Matrix.UnitaryGroup.det_isUnit k'),
    clm_mul']
  simp only [mul_assoc]
  rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), h2, one_mul]

theorem frIso' (_hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrIso := by
  intro n lam k v
  obtain ⟨h1, h2⟩ := sq_inv hA lam
  have hs : star (sqQ (n := n) lam) = sqQ lam := (hA n lam).2.1.star_eq
  have hr : star (Ring.inverse (sqQ (n := n) lam)) = Ring.inverse (sqQ lam) := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact adjoint_inv hA lam
  set C := clm lam (fr0 lam (k : Matrix (Fin n) (Fin n) ℂ)) with hCdef
  have hC : star C * gramQ lam * C = gramQ lam := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact (hA n lam).2.2.2.1 k
  have hg : sqQ lam * sqQ lam = gramQ lam := (hA n lam).2.2.1
  have hTT : star (sqQ lam * (C * Ring.inverse (sqQ lam))) * (sqQ lam * (C * Ring.inverse (sqQ lam))) = 1 := by
    rw [star_mul, star_mul, hs, hr]
    calc Ring.inverse (sqQ lam) * star C * sqQ lam * (sqQ lam * (C * Ring.inverse (sqQ lam)))
        = Ring.inverse (sqQ lam) * (star C * (sqQ lam * sqQ lam) * C) * Ring.inverse (sqQ lam) := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [hg, hC, ← hg, ← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam) (sqQ lam), h2, one_mul, h1]
  rw [CxeAvg.lefFr_eq]
  set T := sqQ lam * (C * Ring.inverse (sqQ lam)) with hT
  have hin : inner ℂ (T v) (T v) = inner ℂ v v := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_apply, hTT, ContinuousLinearMap.one_apply]
  have h3 : ‖T v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hin]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

theorem frCont' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrCont := by
  intro n lam
  simp only [lefFr_eq]
  have h1 : ContinuousOn (fr0 (n := n) lam) (GLs n) := ((hF n lam).2.2).continuousOn
  have h2 : Continuous fun k : UK n => fr0 lam k.1 := h1.comp_continuous continuous_subtype_val mem_GLs
  exact continuous_const.mul (((clm_continuous lam).comp h2).mul continuous_const)

end PositivityTheory.RgBcC
end
end

section
namespace PositivityTheory.RgBcC

theorem fr0Laws_of (hR : RmLaws) (hG : GamMul) (hM : MtLaws) (hD : GamDer) : MatrixFrechetDerivativeAtZeroLaws := Cxe.fr0Laws_of hR hG hM hD

theorem swapLaws_of (hR : RmLaws) : SwapLaws := Cxe.swapLaws_of hR

example : EigProd := eigProd
example : MatrixFrechetDerivativeAtZeroLaws → Avg := avg_of
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrOne := frOne'
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrMulK := frMulK'
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrIso := frIso'
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrCont := frCont'

end PositivityTheory.RgBcC
end
