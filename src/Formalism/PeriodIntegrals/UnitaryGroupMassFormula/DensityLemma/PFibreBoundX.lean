import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundVDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists

section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def skewOf {r : ℕ} (T : Fin r → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => ((T a b - T b a : ℝ) : ℂ) + Complex.I * ((T a b + T b a : ℝ) : ℂ)

def Pz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  1 - ((∑ j, Complex.normSq (zW k r z j) : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (zW k r z) (star (zW k r z))

def psiZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : (Fin r → Fin (k + 1) → ℂ) × (Fin r → Fin r → ℝ)) : Mt k r :=
  unipotentBlockMatrix k r (Matrix.of p.1 * Pz k r z) (skewOf p.2)

def rhoZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (B0 : Fin r → Fin (k + 1) → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ a, Complex.normSq ((Matrix.of B0 *ᵥ zW k r z) a))))

def nuZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Measure (Mt k r) :=
  (((volume : Measure (Fin r → Fin (k + 1) → ℂ)).withDensity (rhoZ k r z)).prod
    (volume : Measure (Fin r → Fin r → ℝ))).map (psiZ k r z)

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def UnipotentSetIsClosedSubgroup : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → B2.IsClosedSubgroup (C2.N0set k r z)

def NuFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z →
    ∀ K : Set (Mt k r), IsCompact K → nuZ k r z K < ∞

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

namespace NBk

variable {k r : ℕ}

lemma mul_diagonal_conjTranspose_apply (P Q : Matrix (Fin r) (Fin (k + 1)) ℂ) (a b : Fin r) :
    (P * Matrix.diagonal (hW k) * Qᴴ) a b = ∑ j, P a j * hW k j * star (Q b j) := by
  rw [Matrix.mul_apply]; simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

lemma nbm_cm (Ba B : Matrix (Fin r) (Fin (k + 1)) ℂ) (Sa S : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    cmOf k r (Ba + B) (Sa + S + (1 / 2 : ℂ) •
        (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ)) a b =
      cmOf k r B S a b + -(Ba * Matrix.diagonal (hW k) * Bᴴ) a b + cmOf k r Ba Sa a b := by
  unfold cmOf
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem nbm_mul (Ba B : Matrix (Fin r) (Fin (k + 1)) ℂ) (Sa S : Matrix (Fin r) (Fin r) ℂ) :
    unipotentBlockMatrix k r Ba Sa * unipotentBlockMatrix k r B S =
      unipotentBlockMatrix k r (Ba + B) (Sa + S + (1 / 2 : ℂ) •
        (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ)) := by
  ext p q
  rw [Matrix.mul_apply, sum_split]
  induction p using cases3 <;> induction q using cases3 <;>
    simp only [nb_ee, nb_we, nb_se, nb_ew, nb_ww, nb_sw, nb_es, nb_ws, nb_ss, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, ite_mul, mul_ite, one_mul, mul_one, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.add_apply, star_add]
  all_goals first
    | done
    | (rw [nbm_cm, mul_diagonal_conjTranspose_apply, ← Finset.sum_neg_distrib]; ring)
    | ring

end NBk

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

namespace HBx

variable {k r : ℕ}

end HBx

namespace HBx

variable {k r : ℕ}

lemma uMap_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous fun s : B.Mat k r => C2.uMap k r z s := by
  unfold C2.uMap herm
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : a.val < r
  · simp only [dif_pos h]
    exact continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))
  · simp only [dif_neg h]
    exact (continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))).div_const _

lemma isClosed_N0set (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (C2.N0set k r z) := by
  have hU : IsClosed (UH (Hpk k r)) := by
    show IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hA : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0} := by
    have e : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        g i (eI k r a) = if i = eI k r a then 1 else 0} =
        ⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : a.val ≤ i.val),
          {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g i (eI k r a) = if i = eI k r a then 1 else 0} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  have hB : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0} := by
    have e : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        g i j = if i = j then 1 else 0} =
        ⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)) (_ : r ≤ j.val) (_ : j.val ≤ r + k)
          (_ : r ≤ i.val), {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g i j = if i = j then 1 else 0} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  have hu : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | C2.uMap k r z g = 1} := isClosed_eq (uMap_cont z) continuous_const
  have e : C2.N0set k r z = ((UH (Hpk k r) ∩ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)),
      a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0}) ∩
      {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        g i j = if i = j then 1 else 0}) ∩ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | C2.uMap k r z g = 1} := by
    ext g
    unfold C2.N0set Formalism.QuantumDeterminants.Nset
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [e]
  exact ((hU.inter hA).inter hB).inter hu

lemma blk_zero : unipotentBlockMatrix k r 0 0 = 1 := by
  ext i j
  simp [unipotentBlockMatrix, cmOf, Matrix.one_apply]

lemma skew_mul (Ba B : Matrix (Fin r) (Fin (k + 1)) ℂ) (Sa S : Matrix (Fin r) (Fin r) ℂ) (hSa : Saᴴ = -Sa)
    (hS : Sᴴ = -S) :
    (Sa + S + (1 / 2 : ℂ) • (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ))ᴴ =
      -(Sa + S + (1 / 2 : ℂ) • (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ)) := by
  have hD : (Matrix.diagonal (hW k))ᴴ = Matrix.diagonal (hW k) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    unfold hW
    split_ifs with hj <;> simp [hj]
  have hX : (B * Matrix.diagonal (hW k) * Baᴴ)ᴴ = Ba * Matrix.diagonal (hW k) * Bᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  have hY : (Ba * Matrix.diagonal (hW k) * Bᴴ)ᴴ = B * Matrix.diagonal (hW k) * Baᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, hX, hY, hSa, hS, hc,
    ← neg_sub (B * Matrix.diagonal (hW k) * Baᴴ) (Ba * Matrix.diagonal (hW k) * Bᴴ), smul_neg]
  abel

end HBx

theorem unipotent_integral_closed : UnipotentSetIsClosedSubgroup := by
  intro k r z hz
  have key : ∀ (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ),
      unipotentBlockMatrix k r Bm S * unipotentBlockMatrix k r (-Bm) (-S) = 1 := by
    intro Bm S
    rw [NBk.nbm_mul]
    have e1 : Bm + -Bm = 0 := add_neg_cancel Bm
    have e2 : S + -S + (1 / 2 : ℂ) • (-Bm * Matrix.diagonal (hW k) * Bmᴴ -
        Bm * Matrix.diagonal (hW k) * (-Bm)ᴴ) = 0 := by
      simp [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
    rw [e1, e2, HBx.blk_zero]
  refine ⟨?_, ?_, ?_, ?_, HBx.isClosed_N0set z⟩
  · rw [← HBx.blk_zero]
    exact NBk.nb_mem _ _ hz (Matrix.zero_mulVec _) (by simp)
  · intro a ha b hb
    obtain ⟨Ba, Sa, hBa, hSa, rfl⟩ := unipotent_eq_block k r z hz a ha
    obtain ⟨B, S, hB, hS, rfl⟩ := unipotent_eq_block k r z hz b hb
    rw [NBk.nbm_mul]
    exact NBk.nb_mem _ _ hz (by rw [Matrix.add_mulVec, hBa, hB, add_zero]) (HBx.skew_mul Ba B Sa S hSa hS)
  · intro a ha
    obtain ⟨Ba, Sa, hBa, hSa, rfl⟩ := unipotent_eq_block k r z hz a ha
    rw [Matrix.inv_eq_right_inv (key Ba Sa)]
    exact NBk.nb_mem _ _ hz (by rw [Matrix.neg_mulVec, hBa, neg_zero])
      (by rw [Matrix.conjTranspose_neg, hSa])
  · intro a ha
    obtain ⟨Ba, Sa, hBa, hSa, rfl⟩ := unipotent_eq_block k r z hz a ha
    exact Matrix.isUnit_det_of_right_inverse (key Ba Sa)

end PI.UnitaryGroupMassFormula.DLm
end
end
