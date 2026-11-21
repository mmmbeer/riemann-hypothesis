import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt.Model

def linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) : MvPolynomial (Fin 1 × Fin N) R :=
  ∑ j, C (c j) * X (0, j)

theorem linSubst_linForm {R : Type} [CommRing R] {N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (c : Fin N → R) : linSubst M (linForm c) = linForm (fun k => ∑ j, M j k * c j) := by
  simp only [linSubst, linForm, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

set_option autoImplicit false in
open MvPolynomial NumberField in
theorem _root_.GlobalTheory.ChowHt.Model.coeff_linForm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R)
    (k : Fin N) :
    (_root_.GlobalTheory.ChowHt.Model.linForm c).coeff (Finsupp.single (0, k) 1) = c k := by
  classical
  simp only [_root_.GlobalTheory.ChowHt.Model.linForm, coeff_sum, coeff_C_mul, coeff_X']
  have key : ∀ j : Fin N,
      (Finsupp.single ((0 : Fin 1), j) 1 = Finsupp.single ((0 : Fin 1), k) 1) ↔ j = k := by
    intro j
    constructor
    · intro h
      have := Finsupp.single_left_injective (one_ne_zero) h
      simpa using this
    · rintro rfl; rfl
  simp [key]




theorem isChowForm_line (k : Type) [Field k] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) k)) 1 1
      (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs b
    rw [Matrix.det_fin_two] at hs
    simp only [Matrix.of_apply, X, monomial_mul, mul_one] at hs
    have h1 := support_sub _ _ _ hs
    rw [Finset.mem_union] at h1
    rcases h1 with h | h <;>
    · have := support_monomial_subset h
      rw [Finset.mem_singleton] at this
      subst this
      fin_cases b <;> simp [Fin.sum_univ_two, Finsupp.single_apply]
  · have := GlobalTheory.BorelAlg.irreducible_det' (R := AlgebraicClosure k) (k := 2) (by norm_num) id
      Function.injective_id
    convert this using 1
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  · intro u
    have : MvPolynomial.aeval u
        (Matrix.of fun i j : Fin 2 => (X (i, j) : MvPolynomial (Fin 2 × Fin 2) k)).det =
        (Matrix.of fun i j : Fin 2 => u (i, j)).det := by
      simp [Matrix.det_fin_two]
    rw [this, ← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, fun g hg => by simp [Ideal.mem_bot.1 hg], fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using congrFun h i
    · rintro ⟨y, hy, -, h⟩
      refine ⟨y, hy, funext fun i => ?_⟩
      simpa [Matrix.mulVec, dotProduct] using h i


end GlobalTheory.ChowHt.Model
