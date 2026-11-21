import Mathlib
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.PairValDefs

section
noncomputable section

open scoped Classical

namespace PI.NRCW

open Formalism.MainNotions.S PI.PairValDefs Matrix

section Mat

variable {K : Type} [Field K] [NumberField K]

theorem isUpUni_mul {N : ℕ} {U V : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (hV : IsUpUni V) :
    IsUpUni (U * V) := by
  intro i j
  constructor
  · intro hji
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hU i k).1 hk, zero_mul]
    · rw [(hV k j).1 (lt_of_lt_of_le hji (not_lt.mp hk)), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hU i i).2 rfl, (hV i i).2 rfl, mul_one]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hU i k).1 h, zero_mul]
      · rw [(hV k i).1 h, mul_zero]
    · simp

theorem sgUp_mul {N : ℕ} {U V : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (hV : IsUpUni V) :
    sgUp (U * V) = sgUp U + sgUp V := by
  unfold sgUp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [Matrix.mul_apply, Fintype.sum_eq_add a ⟨a.val + 1, h⟩]
    · rw [(hU a a).2 rfl, (hV ⟨a.val + 1, h⟩ ⟨a.val + 1, h⟩).2 rfl, one_mul, mul_one, add_comm]
    · intro e
      rw [Fin.ext_iff] at e
      simp at e
    · rintro x ⟨hxa, hxb⟩
      rcases lt_or_gt_of_ne hxa with hx | hx
      · rw [(hU a x).1 hx, zero_mul]
      · have hne : x.val ≠ a.val + 1 := fun e => hxb (Fin.ext e)
        have hx' : (⟨a.val + 1, h⟩ : Fin N) < x := by
          rw [Fin.lt_def] at hx ⊢
          show a.val + 1 < x.val
          omega
        rw [(hV x ⟨a.val + 1, h⟩).1 hx', mul_zero]
  · simp

theorem sgUp_one {N : ℕ} : sgUp (1 : Matrix (Fin N) (Fin N) K) = 0 := by
  unfold sgUp
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro e
    rw [Fin.ext_iff] at e
    simp at e
  · rfl

theorem det_upUni {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => (hU i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl

theorem isUpUni_inv {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U * U⁻¹ = 1 := by
  have hdet : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdet
  haveI : Invertible U := Matrix.invertibleOfIsUnitDet U hdet
  have htri : (U⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j h => (hU i j).1 h)
  refine ⟨fun i j => ⟨fun h => htri h, fun h => ?_⟩, hmul⟩
  subst h
  have hii := congrFun (congrFun hmul i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (hU i i).2 rfl, one_mul, Matrix.one_apply_eq] at hii
  · exact hii
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [(hU i k).1 h, zero_mul]
    · rw [htri h, mul_zero]
  · simp

theorem sgUp_inv {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : sgUp U⁻¹ = - sgUp U := by
  obtain ⟨hI, hmul⟩ := isUpUni_inv hU
  have hs := sgUp_mul hU hI
  rw [hmul, sgUp_one] at hs
  linear_combination -hs

variable [StarRing K]

theorem isLoUni_conjTranspose {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : IsLoUni Uᴴ := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Matrix.conjTranspose_apply, (hU j i).1 h, star_zero]
  · subst h
    rw [Matrix.conjTranspose_apply, (hU i i).2 rfl, star_one]

theorem sgLo_conjTranspose {N : ℕ} (U : Matrix (Fin N) (Fin N) K) : sgLo Uᴴ = star (sgUp U) := by
  unfold sgLo sgUp
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · exact Matrix.conjTranspose_apply _ _ _
  · rw [star_zero]

def epsM (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.diagonal fun b => (-1) ^ (r - b.val)

theorem epsM_mul_self (r : ℕ) : (epsM r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * epsM r = 1 := by
  rw [epsM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext b
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem zhatOM_eq {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ZhatOM Z = Z * epsM r := by
  ext a b
  simp only [ZhatOM, epsM, Matrix.mul_diagonal]
  ring

theorem isUpUni_eps {r : ℕ} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hM : IsUpUni M) :
    IsUpUni (epsM r * M * epsM r) := by
  intro i j
  simp only [epsM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [(hM i j).1 h]
    ring
  · subst h
    rw [(hM i i).2 rfl, mul_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgUp_eps {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    sgUp (epsM r * M * epsM r) = - sgUp M := by
  unfold sgUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · simp only [epsM, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hra : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have hx : ((-1 : K) ^ (r - (a.val + 1))) * (-1) ^ (r - (a.val + 1)) = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    show (-1 : K) ^ (r - a.val) * M a ⟨a.val + 1, h⟩ * (-1) ^ (r - (a.val + 1)) = -M a ⟨a.val + 1, h⟩
    rw [hra, pow_succ]
    linear_combination (-(M a ⟨a.val + 1, h⟩)) * hx
  · simp

theorem core_Z {r : ℕ} (Z₁ Z₂ N M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hN : IsUpUni N) (hM : IsUpUni M)
    (h : Nᴴ * Z₂ = Z₁ * M) :
    ∃ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K, IsLoUni A ∧ IsUpUni B ∧
      ZhatOM Z₂ = A * ZhatOM Z₁ * B ∧ sgLo A + sgUp B = -(star (sgUp N) + sgUp M) := by
  obtain ⟨hNi, hNN⟩ := isUpUni_inv hN
  refine ⟨(N⁻¹)ᴴ, epsM r * M * epsM r, isLoUni_conjTranspose hNi, isUpUni_eps hM, ?_, ?_⟩
  · have hinv : (N⁻¹)ᴴ * Nᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hNN, Matrix.conjTranspose_one]
    have hZ2 : Z₂ = (N⁻¹)ᴴ * (Z₁ * M) := by
      rw [← h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    rw [zhatOM_eq, zhatOM_eq, hZ2]
    have hee := epsM_mul_self (K := K) r
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (epsM r) (epsM r), hee, Matrix.one_mul]
  · rw [sgLo_conjTranspose, sgUp_inv hN, sgUp_eps, star_neg]
    ring

end Mat

end PI.NRCW
end
end

section
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def fmat {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : MatR D :=
  fun c b => (if c = b then 1 else 0) +
    (if h : c.val < D.R.rS then G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, h⟩ else 0)

def StepExp : Prop := ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
  (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam Λ G →
    IsUpUni (fmat D G n) ∧ ∀ b, n (frame G b) = ∑ c, fmat D G n c b • frame G c

def StepGram : Prop := ∀ {T T' : D.host.E} (G : LFlag (VS D) D.R.rS T) (G₁ G₂ : LFlag (VS D) D.R.rS T')
  (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (N M : MatR D), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    (∀ b, n (frame G b) = ∑ c, N c b • frame G c) → (∀ b, m (frame G₁ b) = ∑ c, M c b • frame G₁ c) →
    (∀ a, frame G₂ a = n (m (frame G₁ a))) → Nᴴ * ZhatL G G₂ = ZhatL G G₁ * M

def StepGlob : Prop := ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
  (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam Λ G → XLam Λ G = XS D G.fl → G.fl.z ∈ Λ →
    ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = sgUp (fmat D G n) * δ

def StepLoc : Prop := ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (VS D) D.R.rS T)
  (G₁ G₂ : LFlag (VS D) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam Λ G → m ∈ NLam Λ G₁ →
    (∀ a, frame G₂ a = n (m (frame G₁ a))) → IsFixedConv Λ (gS D) G → IsFixedConv Λ (gS D) G₁ →
    AdmWit Λ (gS D) G G₁ 1 → AdmWit Λ (gS D) G G₂ 1 → G.fl.z ∈ Λ → G₁.fl.z ∈ Λ →
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E ((sgUp (fmat D G n) + sgUp (fmat D G₁ m)) / (gS D : D.host.E)) ≤ 1

def StepTr : Prop := ∀ y : D.host.E, (∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y * δ) →
  (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E (y / (gS D : D.host.E)) ≤ 1) →
    ∃ k : ℤ, Algebra.trace ℚ D.host.E y = (gS D : ℚ) * k

section Phase

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem trace_star (a : K) : Algebra.trace ℚ K (star a) = Algebra.trace ℚ K a := by
  have h := Algebra.trace_eq_of_algEquiv ((starRingAut : RingAut K).toRatAlgEquiv) a
  simpa using h

theorem psiInf_of_trace (g : ℕ) (a b : K) (k : ℤ) (hk : Algebra.trace ℚ K (a + b) = (g : ℚ) * k) :
    psiInf g (-(star a + b)) = 1 := by
  unfold psiInf
  have htr : Algebra.trace ℚ K (-(star a + b)) = -((g : ℚ) * k) := by
    rw [map_neg, map_add, trace_star, ← map_add, hk]
  rw [htr]
  by_cases hg : (g : ℂ) = 0
  · simp [hg]
  · rw [show (((-((g : ℚ) * k) : ℚ) : ℂ) / (g : ℂ)) = -(k : ℂ) by push_cast; field_simp]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * -(k : ℂ) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)

end Phase

end PI.NRCW
end
end
