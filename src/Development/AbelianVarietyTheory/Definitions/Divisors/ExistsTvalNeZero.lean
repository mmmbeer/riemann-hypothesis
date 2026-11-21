import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne

noncomputable section

namespace GlobalTheory.DefPt.Model

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial GlobalTheory.DefPt
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]


theorem finite_not_le (a : K) : {w : HeightOneSpectrum (𝓞 K) | ¬ w.valuation K a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · simp [ha]
  refine (GlobalTheory.FlatLine.finite_vAdd ha).subset fun w hw h0 => hw ?_
  have h1 : vAdd w a = 0 := Int.cast_eq_zero.1 h0
  have h2 : w.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [vAdd, neg_eq_zero] at h1
  rw [← WithZero.exp_log h2, h1]; simp

theorem finite_not_intAt (g : Matrix ι ι K) : {w : HeightOneSpectrum (𝓞 K) | ¬ IntAt w g}.Finite := by
  refine (Set.finite_iUnion fun p : ι × ι => finite_not_le (g p.1 p.2)).subset fun w hw => ?_
  simp only [IntAt, Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨i, j, h⟩ := hw
  exact Set.mem_iUnion.2 ⟨(i, j), h⟩


open Classical in

theorem isAdelic_single (v : HeightOneSpectrum (𝓞 K)) {g : Matrix ι ι K} (hg : g.det ≠ 0) :
    IsAdelic (fun w : HeightOneSpectrum (𝓞 K) => if w = v then g else 1) := by
  refine ⟨fun w => by by_cases h : w = v <;> simp [h, hg], (Set.finite_singleton v).subset fun w hw => ?_⟩
  by_contra h
  have h' : w ≠ v := h
  have h1 : IntAt w (1 : Matrix ι ι K) := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  exact hw (by simp [h', h1])





end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

theorem rhoMat_one (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : rhoMat la (1 : Matrix _ _ K) = 1 := by
  simp [rhoMat, ← Module.End.one_eq_id, LinearMap.toMatrix_one]

theorem rhoMat_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la (g * h) = rhoMat la h * rhoMat la g := by
  simp [rhoMat, Matrix.transpose_mul, LinearMap.toMatrix_mul]

theorem rhoMat_scalar (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (t : K) :
    rhoMat la (t • (1 : Matrix _ _ K)) = t ^ size la • 1 := by
  have : rho la K (t • 1) = t ^ size la • LinearMap.id := LinearMap.ext fun f => rho_scalar t f
  simp [rhoMat, this]

theorem evalAt_eq_sum (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (y : Matrix (Fin n) (Fin n) K) (f : nabla la K) :
    evalAt y f.1 = ∑ i, (basis la K).repr f i * evalAt y (map (Int.castRingHom K) (intVec la i)) := by
  have h := congrArg (fun f : nabla la K => evalAt y f.1) ((basis la K).sum_repr f)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul, coe_basis] at h
  exact h.symm

theorem evalAt_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g y : Matrix (Fin n) (Fin n) K) (j : Idx la) :
    evalAt (g * y) (map (Int.castRingHom K) (intVec la j)) =
      ∑ i, rhoMat la g i j * evalAt y (map (Int.castRingHom K) (intVec la i)) := by
  have h1 := evalAt_rho y gᵀ (basis la K j)
  rw [Matrix.transpose_transpose, coe_basis] at h1
  rw [← h1, evalAt_eq_sum]
  simp only [rhoMat, LinearMap.toMatrix_apply]

theorem tval_mul (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (x : TIdx la → K)
    (g y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) :
    tval la x (fun t => g t * y t) = tval la (fibA la 1 g *ᵥ x) y := by
  simp only [tval, evalAt_mul, fibA, one_smul, Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]; ring

theorem kron_mul {J : T → Type} [∀ t, Fintype (J t)] {R : Type} [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R) :
    kron M * kron M' = kron fun t => M t * M' t := by
  ext I I'
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]




theorem exists_tval_ne_zero (la : Fin n → ℕ) (h : Antitone la) :
    ∃ x : TIdx (fun _ : Unit => la) → ℚ, tval (fun _ : Unit => la) x (fun _ => 1) = 1 := by
  refine ⟨fun I => (basis la ℚ).repr ⟨extremal la ℚ, extremal_mem h⟩ (I ()), ?_⟩
  have h2 := evalAt_eq_sum la 1 (⟨extremal la ℚ, extremal_mem h⟩ : nabla la ℚ)
  rw [evalAt_one_extremal] at h2
  rw [h2, tval, ← (Equiv.funUnique Unit (Idx la)).symm.sum_comp]
  simp




end Tensor

end GlobalTheory.DefPt.Model

end
