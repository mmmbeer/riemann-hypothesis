import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGram

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem entries_bounded_of_conj_spanning_bounded :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  intro ι _ _ σ _ g hg C
  have hmem : ∀ k l : ι, ∃ a : σ → ℂ, ∑ s, a s • g s = Matrix.single k l (1 : ℂ) := by
    intro k l
    have : Matrix.single k l (1 : ℂ) ∈ Submodule.span ℂ (Set.range g) := by
      rw [hg]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
  choose a ha using hmem
  set C₁ : ℝ := ∑ k, ∑ l, ∑ s, ‖a k l s‖ * |C| with hC₁
  refine ⟨max 1 ((Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι), ?_⟩
  intro P hP hb i k
  have hent : ∀ l j, ‖P i k * P⁻¹ l j‖ ≤ C₁ := by
    intro l j
    have h1 : P i k * P⁻¹ l j = ∑ s, a k l s * (P * g s * P⁻¹) i j := by
      have h2 : (P * Matrix.single k l (1 : ℂ) * P⁻¹) i j = P i k * P⁻¹ l j := by
        simp [Matrix.mul_apply, Matrix.single, ite_and]
      rw [← h2, ← ha k l, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    have h3 : ‖P i k * P⁻¹ l j‖ ≤ ∑ s, ‖a k l s‖ * |C| := by
      rw [h1]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hb s i j).trans (le_abs_self C)) (norm_nonneg _)
    refine h3.trans ?_
    calc ∑ s, ‖a k l s‖ * |C| ≤ ∑ l, ∑ s, ‖a k l s‖ * |C| :=
          Finset.single_le_sum (f := fun l => ∑ s, ‖a k l s‖ * |C|)
            (fun l _ => by positivity) (Finset.mem_univ l)
      _ ≤ C₁ :=
          Finset.single_le_sum (f := fun k => ∑ l, ∑ s, ‖a k l s‖ * |C|)
            (fun k _ => by positivity) (Finset.mem_univ k)
  have hdetinv : (P⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, hP]; simp
  have hdet := Matrix.det_le (A := P i k • P⁻¹) (abv := NormedField.toAbsoluteValue ℂ) (x := C₁)
    (fun l j => hent l j)
  rw [Matrix.det_smul, hdetinv, mul_one] at hdet
  have hdet' : ‖P i k‖ ^ Fintype.card ι ≤
      (Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι := by
    rw [← norm_pow]; exact hdet
  have hN : Fintype.card ι ≠ 0 := (Fintype.card_pos_iff.2 ⟨i⟩).ne'
  rcases le_total ‖P i k‖ 1 with h | h
  · exact h.trans (le_max_left _ _)
  · exact ((le_self_pow₀ h hN).trans hdet').trans (le_max_right _ _)

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  atlas_forward_decl GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isClosed_isLog : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by
  intro ι _ _
  let K : Set (Matrix ι ι ℂ) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D : K × (Matrix ι ι ℂ × Matrix ι ι ℂ) → ι → ℝ :=
    fun q i => (((q.1 : Matrix ι ι ℂ)ᴴ * q.2.1 * (q.1 : Matrix ι ι ℂ)) i i).re
  have hU : Continuous (fun q : K × (Matrix ι ι ℂ × Matrix ι ι ℂ) => (q.1 : Matrix ι ι ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hD : ∀ i, Continuous (fun q => D q i) := by
    intro i
    refine Complex.continuous_re.comp ?_
    exact ((hU.matrix_conjTranspose.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      hU).matrix_elem i i
  let S : Set (K × (Matrix ι ι ℂ × Matrix ι ι ℂ)) :=
    {q | (q.1 : Matrix ι ι ℂ) * (q.1 : Matrix ι ι ℂ)ᴴ = 1 ∧
      q.2.1 = (q.1 : Matrix ι ι ℂ) * diagonal (fun i => (D q i : ℂ)) * (q.1 : Matrix ι ι ℂ)ᴴ ∧
      q.2.2 = (q.1 : Matrix ι ι ℂ) * diagonal (fun i => (Real.exp (D q i) : ℂ)) *
        (q.1 : Matrix ι ι ℂ)ᴴ}
  have hS : IsClosed S := by
    refine IsClosed.inter (isClosed_eq (hU.matrix_mul hU.matrix_conjTranspose) continuous_const)
      (IsClosed.inter (isClosed_eq (continuous_fst.comp continuous_snd) ?_)
        (isClosed_eq (continuous_snd.comp continuous_snd) ?_))
    · refine (hU.matrix_mul (Continuous.matrix_diagonal ?_)).matrix_mul hU.matrix_conjTranspose
      exact continuous_pi fun i => Complex.continuous_ofReal.comp (hD i)
    · refine (hU.matrix_mul (Continuous.matrix_diagonal ?_)).matrix_mul hU.matrix_conjTranspose
      exact continuous_pi fun i =>
        Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hD i))
  have key : {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} = Prod.snd '' S := by
    ext p
    constructor
    · rintro ⟨U, d, h1, h2, h3⟩
      have hUK : U ∈ K := by
        intro i _ j _
        have hu : U ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff.mpr h1
        simpa using entry_norm_bound_of_unitary hu i j
      have h1' : Uᴴ * U = 1 := mul_eq_one_comm.mp h1
      have hd : D (⟨U, hUK⟩, p) = d := by
        funext i
        show ((Uᴴ * p.1 * U) i i).re = d i
        have : Uᴴ * p.1 * U = diagonal (fun i => (d i : ℂ)) := by
          rw [h2]
          calc Uᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ) * U
              = (Uᴴ * U) * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [h1']; simp
        rw [this]; simp
      refine ⟨(⟨U, hUK⟩, p), ⟨h1, ?_, ?_⟩, rfl⟩
      · rw [hd]; exact h2
      · rw [hd]; exact h3
    · rintro ⟨q, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨q.1, D q, h1, h2, h3⟩
  rw [key]
  exact isClosedMap_snd_of_compactSpace S hS

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_isHermitianLogOfPosDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by
  atlas_forward_decl GlobalTheory.ClassFin.isClosed_isLog
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma energy_entry_sq_le {ι : Type} [Fintype ι] (x : Matrix ι ι ℂ) (i j : ι) :
    ‖x i j‖ ^ 2 ≤ (Matrix.trace (xᴴ * x)).re := by
  have h : (Matrix.trace (xᴴ * x)).re = ∑ b, ∑ a, ‖x a b‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [h]
  calc ‖x i j‖ ^ 2 ≤ ∑ a, ‖x a j‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ‖x a j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun b => ∑ a, ‖x a b‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

private lemma energy_trace_conj {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1)
    (d : ι → ℝ) : (Matrix.trace (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)).re = ∑ i, d i := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.trace_mul_cycle, hU', one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem entries_le_of_energy_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : ℝ), ∃ C : ℝ, ∀ x H : Matrix ι ι ℂ, IsLog H (xᴴ * x) → (Matrix.trace (H * H)).re ≤ E → ∀ i j, ‖x i j‖ ≤ C ∧ ‖H i j‖ ≤ C := by
  intro ι _ _ E
  refine ⟨max (√E) (√(Fintype.card ι * Real.exp (√E))), ?_⟩
  rintro x H ⟨U, d, hU, hH, hA⟩ hE i j
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hherm : Hᴴ = H := by
    rw [hH]
    simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def]
  have hHH : H * H = U * diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hH]
    calc U * diagonal (fun i => (d i : ℂ)) * Uᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)
        = U * (diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU', Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          congr 3
          funext k
          push_cast
          ring
  have hd : ∀ k, d k ≤ √E := by
    intro k
    have h1 : ∑ k, d k ^ 2 ≤ E := by
      rw [hHH, energy_trace_conj U hU] at hE
      exact hE
    have h2 : d k ^ 2 ≤ ∑ k, d k ^ 2 :=
      Finset.single_le_sum (f := fun k => d k ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
    exact Real.le_sqrt_of_sq_le (h2.trans h1)
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le x i j).trans ?_
    rw [hA, energy_trace_conj U hU (fun i => Real.exp (d i))]
    calc ∑ k, Real.exp (d k) ≤ ∑ _k : ι, Real.exp (√E) :=
          Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr (hd k)
      _ = _ := by simp
  · refine le_trans ?_ (le_max_left _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le H i j).trans ?_
    rwa [hherm]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : ℝ), ∃ C : ℝ, ∀ x H : Matrix ι ι ℂ, IsLog H (xᴴ * x) → (Matrix.trace (H * H)).re ≤ E → ∀ i j, ‖x i j‖ ≤ C ∧ ‖H i j‖ ≤ C := by
  atlas_forward_decl GlobalTheory.ClassFin.entries_le_of_energy_le
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EnergyMin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem energy_nonneg {H A : Matrix ι ι ℂ} (h : IsLog H A) : 0 ≤ (Matrix.trace (H * H)).re := by
  obtain ⟨U, d, -, hH, -⟩ := h
  have hh : Hᴴ = H := by
    rw [hH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext i
    simp
  have h1 := (Matrix.posSemidef_conjTranspose_mul_self H).trace_nonneg
  rw [hh] at h1
  exact (Complex.le_def.mp h1).1

omit [Fintype ι] [DecidableEq ι] in

theorem isCompact_box (C : ℝ) : IsCompact {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {x : ι → ι → ℂ | ∀ i j, ‖x i j‖ ≤ C} =
      Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C := by
    ext x
    simp [Set.mem_pi]
  rw [← e] at h
  exact h

theorem exists_det_one (P : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    ∃ Q : Matrix ι ι ℂ, Q.det = 1 ∧ ∀ x : Matrix ι ι ℂ, Q * x * Q⁻¹ = P * x * P⁻¹ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨P, Matrix.det_isEmpty, fun _ => rfl⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq P.det (Fintype.card_pos (α := ι))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow Fintype.card_ne_zero] at hc
    exact hP.ne_zero hc.symm
  refine ⟨c⁻¹ • P, ?_, fun x => ?_⟩
  · rw [Matrix.det_smul, ← hc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  · have : (c⁻¹ • P)⁻¹ = c • P⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mul_nonsing_inv _ hP]
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem inv_eq_adj {P : Matrix ι ι ℂ} (hP : P.det = 1) : P⁻¹ = P.adjugate := by
  rw [Matrix.inv_def, hP]
  simp

end GlobalTheory.ClassFin.EnergyMin

open GlobalTheory.ClassFin.EnergyMin in

theorem GlobalTheory.ClassFin.exists_energy_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), (∀ s, IsUnit (g s).det) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ (P : Matrix ι ι ℂ) (H : σ → Matrix ι ι ℂ), IsUnit P.det ∧ (∀ s, IsLog (H s) ((P * g s * P⁻¹)ᴴ * (P * g s * P⁻¹))) ∧ ∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re := by
  intro ι _ _ σ _ g hg hspan
  choose H₀ hH₀ using fun s => GlobalTheory.T.exists_isHermitianLogOfPosDef_gram ι (g s) (hg s)
  let En : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) → ℝ := fun p => ∑ s, (Matrix.trace (p.2 s * p.2 s)).re
  have hEn : Continuous En := by
    refine continuous_finset_sum _ fun s _ => Complex.continuous_re.comp ?_
    have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
      (continuous_apply s).comp continuous_snd
    exact (h.matrix_mul h).matrix_trace
  let E₀ : ℝ := En (1, H₀)
  let Z : Set (Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) := {p | p.1.det = 1 ∧
    (∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))) ∧ En p ≤ E₀}
  have hZc : IsClosed Z := by
    refine IsClosed.inter (isClosed_eq continuous_fst.matrix_det continuous_const)
      (IsClosed.inter ?_ (isClosed_le hEn continuous_const))
    have : IsClosed (⋂ s, {p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) |
        IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))}) := by
      refine isClosed_iInter fun s => ?_
      have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
        (continuous_apply s).comp continuous_snd
      have h2 : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.1 * g s * p.1.adjugate :=
        (continuous_fst.matrix_mul continuous_const).matrix_mul continuous_fst.matrix_adjugate
      exact (GlobalTheory.T.isClosed_isHermitianLogOfPosDef ι).preimage (h.prodMk (h2.matrix_conjTranspose.matrix_mul h2))
    rw [← Set.setOf_forall] at this
    exact this
  obtain ⟨C, hC⟩ := GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le ι E₀
  obtain ⟨C', hC'⟩ := GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' ι σ g hspan C
  have hK : IsCompact ({x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C'} ×ˢ
      (Set.pi Set.univ fun _ : σ => {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C})) :=
    (isCompact_box C').prod (isCompact_univ_pi fun _ => isCompact_box C)
  have hZ : IsCompact Z := by
    refine hK.of_isClosed_subset hZc ?_
    rintro ⟨P, H⟩ ⟨hd, hl, hE⟩
    have hb : ∀ s i j, ‖(P * g s * P.adjugate) i j‖ ≤ C ∧ ‖H s i j‖ ≤ C := by
      intro s
      refine hC _ _ (hl s) (le_trans ?_ hE)
      exact Finset.single_le_sum (f := fun s => (Matrix.trace (H s * H s)).re)
        (fun t _ => energy_nonneg (hl t)) (Finset.mem_univ s)
    refine ⟨hC' P hd fun s i j => ?_, fun s _ i j => (hb s i j).2⟩
    rw [inv_eq_adj hd]
    exact (hb s i j).1
  have h0 : ((1, H₀) : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) ∈ Z := by
    refine ⟨Matrix.det_one, fun s => ?_, le_rfl⟩
    simpa using hH₀ s
  obtain ⟨⟨P, H⟩, ⟨hd, hl, hE⟩, hmin⟩ := hZ.exists_isMinOn ⟨_, h0⟩ hEn.continuousOn
  have hd' : P.det = 1 := hd
  refine ⟨P, H, by rw [hd']; exact isUnit_one, fun s => by rw [inv_eq_adj hd']; exact hl s, ?_⟩
  intro P' H' hP' hl'
  obtain ⟨Q, hQ, hQx⟩ := exists_det_one P' hP'
  change En (P, H) ≤ En (Q, H')
  by_cases hle : En (Q, H') ≤ E₀
  · refine hmin (a := (Q, H')) ⟨hQ, fun s => ?_, hle⟩
    have := hl' s
    rw [← hQx, inv_eq_adj hQ] at this
    exact this
  · exact hE.trans (not_le.mp hle).le
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem log_sq_le_tangent_add_sq :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ x → a ≤ y →
      (Real.log y) ^ 2 ≤ (Real.log x) ^ 2 + 2 * Real.log x / x * (y - x) + C * (y - x) ^ 2 := by
  intro a ha
  refine ⟨(2 + 2 * |Real.log a|) / a ^ 2, by positivity, ?_⟩
  intro x y hx hy
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hy0 : 0 < y := lt_of_lt_of_le ha hy
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = Real.log y - Real.log x := ⟨_, rfl⟩
  have hlogy : Real.log y = Real.log x + d := by rw [hd]; ring
  have hup : d ≤ (y - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have e : y / x - 1 = (y - x) / x := by field_simp
    rw [hd]; linarith
  have hlow : (y - x) / y ≤ d := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h
    have e : (y - x) / y = 1 - x / y := by field_simp
    rw [hd, e]; linarith
  have hxy : a ^ 2 ≤ x * y := by nlinarith
  have hxx : a ^ 2 ≤ x ^ 2 := by nlinarith
  have hyy : a ^ 2 ≤ y ^ 2 := by nlinarith
  have ha2 : 0 < a ^ 2 := by positivity
  have hK0 : 0 ≤ (y - x) ^ 2 / a ^ 2 := by positivity
  have hgap : (y - x) / x - d ≤ (y - x) ^ 2 / a ^ 2 := by
    have e : (y - x) / x - (y - x) / y = (y - x) ^ 2 / (x * y) := by
      field_simp
    have h : (y - x) ^ 2 / (x * y) ≤ (y - x) ^ 2 / a ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxy
    linarith
  have hq2 : ((y - x) / x) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxx
  have hp2 : ((y - x) / y) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hyy
  have hd2 : d ^ 2 ≤ 2 * ((y - x) ^ 2 / a ^ 2) := by
    rcases le_total 0 d with h | h
    · nlinarith [sq_nonneg ((y - x) / y)]
    · nlinarith [sq_nonneg ((y - x) / x)]
  have hu : -Real.log x ≤ |Real.log a| := by
    have := Real.log_le_log ha hx
    have := neg_le_abs (Real.log a)
    linarith
  have hL0 : 0 ≤ |Real.log a| := abs_nonneg _
  have he0 : 0 ≤ (y - x) / x - d := by linarith
  have h3 : -Real.log x * ((y - x) / x - d) ≤ |Real.log a| * ((y - x) ^ 2 / a ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_right hu he0) (mul_le_mul_of_nonneg_left hgap hL0)
  have e1 : 2 * Real.log x / x * (y - x) = 2 * Real.log x * ((y - x) / x) := by ring
  have e2 : (2 + 2 * |Real.log a|) / a ^ 2 * (y - x) ^ 2
      = (2 + 2 * |Real.log a|) * ((y - x) ^ 2 / a ^ 2) := by ring
  rw [hlogy, e1, e2]
  nlinarith [h3, hd2]

end GlobalTheory.ClassFin
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.LogSqVar

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma sum_normSq_apply_right_eq_one_of_mul_conjTranspose (W : Matrix ι ι ℂ) (h : W * Wᴴ = 1) (i : ι) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h1 := congrArg (fun M : Matrix ι ι ℂ => Complex.re (M i i)) h
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma sum_normSq_apply_left_eq_one_of_conjTranspose_mul (W : Matrix ι ι ℂ) (h : Wᴴ * W = 1) (j : ι) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h1 := sum_normSq_apply_right_eq_one_of_mul_conjTranspose Wᴴ (by rw [conjTranspose_conjTranspose]; exact h) j
  simpa [conjTranspose_apply, Complex.normSq_conj] using h1

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma norm_apply_le_one_of_conjTranspose_mul_eq_one (V : Matrix ι ι ℂ) (hV : Vᴴ * V = 1) (k j : ι) : ‖V k j‖ ≤ 1 := by
  have h1 : Complex.normSq (V k j) ≤ 1 := by
    rw [← sum_normSq_apply_left_eq_one_of_conjTranspose_mul V hV j]
    exact Finset.single_le_sum (f := fun i => Complex.normSq (V i j))
      (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ k)
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (V k j)]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma norm_conj_diag_apply_le (V Y : Matrix ι ι ℂ) (hV : Vᴴ * V = 1) (δ : ℝ)
    (hY : ∀ i j, ‖Y i j‖ ≤ δ) (j : ι) :
    ‖(Vᴴ * Y * V) j j‖ ≤ (Fintype.card ι : ℝ) * Fintype.card ι * δ := by
  simp only [Matrix.mul_apply, conjTranspose_apply]
  calc ‖∑ l, (∑ k, star (V k j) * Y k l) * V l j‖
      ≤ ∑ l, ∑ k, ‖star (V k j) * Y k l‖ * ‖V l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)).trans_eq
          (Finset.sum_mul _ _ _)
    _ ≤ ∑ l : ι, ∑ k : ι, δ := by
        refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        have h1 := norm_apply_le_one_of_conjTranspose_mul_eq_one V hV k j
        have h2 := norm_apply_le_one_of_conjTranspose_mul_eq_one V hV l j
        have h3 := hY k l
        have h4 := norm_nonneg (Y k l)
        have h5 := norm_nonneg (V k j)
        have h6 := norm_nonneg (V l j)
        calc ‖V k j‖ * ‖Y k l‖ * ‖V l j‖ ≤ 1 * ‖Y k l‖ * 1 := by gcongr
          _ ≤ δ := by linarith
    _ = (Fintype.card ι : ℝ) * Fintype.card ι * δ := by
        simp [Finset.sum_const, Finset.card_univ]; ring

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma le_eigenvalue_of_add (U V Y : Matrix ι ι ℂ) (x y : ι → ℝ) (m δ : ℝ)
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) (hx : ∀ i, m ≤ x i) (hY : ∀ i j, ‖Y i j‖ ≤ δ)
    (hB : U * diagonal (fun i => (x i : ℂ)) * Uᴴ + Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ)
    (j : ι) : m - (Fintype.card ι : ℝ) * Fintype.card ι * δ ≤ y j := by
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have hW : (Uᴴ * V)ᴴ * (Uᴴ * V) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose,
      show Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one, hV']
  have hdiag : Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V = diagonal (fun j => (y j : ℂ)) := by
    rw [show Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V
        = (Vᴴ * V) * diagonal (fun j => (y j : ℂ)) * (Vᴴ * V) by simp only [Matrix.mul_assoc], hV',
      Matrix.one_mul, Matrix.mul_one]
  have hsplit : Vᴴ * (V * diagonal (fun j => (y j : ℂ)) * Vᴴ) * V
      = (Uᴴ * V)ᴴ * diagonal (fun i => (x i : ℂ)) * (Uᴴ * V) + Vᴴ * Y * V := by
    rw [← hB, Matrix.mul_add, Matrix.add_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [hdiag] at hsplit
  have hj := congrArg (fun M : Matrix ι ι ℂ => Complex.re (M j j)) hsplit
  simp only [diagonal_apply_eq, Complex.ofReal_re, Matrix.add_apply, Complex.add_re] at hj
  have hA : Complex.re (((Uᴴ * V)ᴴ * diagonal (fun i => (x i : ℂ)) * (Uᴴ * V)) j j)
      = ∑ i, x i * Complex.normSq ((Uᴴ * V) i j) := by
    generalize Uᴴ * V = W
    have hd : Wᴴ * diagonal (fun i => (x i : ℂ)) = Matrix.of fun a b => Wᴴ a b * (x b : ℂ) := by
      ext a b; simp [Matrix.mul_diagonal]
    rw [hd]
    simp only [Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_apply]
    simp [Complex.mul_re]
    ring
  have hlow : m ≤ ∑ i, x i * Complex.normSq ((Uᴴ * V) i j) := by
    calc m = ∑ i, m * Complex.normSq ((Uᴴ * V) i j) := by
          rw [← Finset.mul_sum, sum_normSq_apply_left_eq_one_of_conjTranspose_mul _ hW j, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hx i) (Complex.normSq_nonneg _)
  have hsmall := norm_conj_diag_apply_le V Y hV' δ hY j
  have hre := Complex.abs_re_le_norm ((Vᴴ * Y * V) j j)
  have hre' := neg_abs_le ((Vᴴ * Y * V) j j).re
  linarith

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma conj_real_diagonal_mul_conj_real_diagonal (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (a b : ι → ℝ) :
    U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (U * diagonal (fun i => (b i : ℂ)) * Uᴴ)
      = U * diagonal (fun i => ((a i * b i : ℝ) : ℂ)) * Uᴴ := by
  have : U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (U * diagonal (fun i => (b i : ℂ)) * Uᴴ)
      = U * (diagonal (fun i => (a i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (b i : ℂ))) * Uᴴ := by
    simp only [Matrix.mul_assoc]
  rw [this, hU, Matrix.mul_one, diagonal_mul_diagonal]
  simp

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma re_trace_conj_diagonal_mul (U V : Matrix ι ι ℂ) (a b : ι → ℝ) :
    Complex.re (Matrix.trace (U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (V * diagonal (fun j => (b j : ℂ)) * Vᴴ)))
      = ∑ i, ∑ j, a i * b j * Complex.normSq ((Uᴴ * V) i j) := by
  have h : U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (V * diagonal (fun j => (b j : ℂ)) * Vᴴ)
      = U * (diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * Vᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm]
  have h2 : diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * Vᴴ * U
      = diagonal (fun i => (a i : ℂ)) * (Uᴴ * V) * diagonal (fun j => (b j : ℂ)) * (Uᴴ * V)ᴴ := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  rw [h2]
  generalize Uᴴ * V = W
  have h3 : diagonal (fun i => (a i : ℂ)) * W * diagonal (fun j => (b j : ℂ))
      = Matrix.of fun i j => (a i : ℂ) * W i j * b j := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [h3]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h4 : (W i j) * star (W i j) = (Complex.normSq (W i j) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]; rfl
  calc ((a i : ℂ) * W i j * b j * star (W i j)).re
      = ((a i * b j : ℝ) * (W i j * star (W i j)) : ℂ).re := by push_cast; ring_nf
    _ = _ := by rw [h4, ← Complex.ofReal_mul, Complex.ofReal_re]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma sum_norm_sq_eq_re_trace_mul_conjTranspose (Y : Matrix ι ι ℂ) :
    ∑ i, ∑ j, ‖Y i j‖ ^ (2 : ℕ) = Complex.re (Matrix.trace (Y * Yᴴ)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

open Matrix in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma conjTranspose_unitary_conj_real_diagonal (U : Matrix ι ι ℂ) (a : ι → ℝ) :
    (U * diagonal (fun i => (a i : ℂ)) * Uᴴ)ᴴ = U * diagonal (fun i => (a i : ℂ)) * Uᴴ := by
  have h : (star fun i => (a i : ℂ)) = fun i => (a i : ℂ) := funext fun i => by simp
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose, h]

open Matrix in
theorem _root_.GlobalTheory.ClassFin.LogSqVar.first_variation (ι : Type) [Fintype ι] [DecidableEq ι]
    (H A : Matrix ι ι ℂ) :
    _root_.GlobalTheory.ClassFin.IsLog H A →
      ∃ (C : ℝ) (δ : ℝ), (0 : ℝ) < δ ∧
        ∀ (Y H' : Matrix ι ι ℂ), (∀ (i j : ι), ‖Y i j‖ ≤ δ) →
          _root_.GlobalTheory.ClassFin.IsLog H' (A + Y) →
            Complex.re (Matrix.trace (H' * H')) ≤
              Complex.re (Matrix.trace (H * H)) + (2 : ℝ) * Complex.re (Matrix.trace (H * A⁻¹ * Y)) +
                C * ∑ i : ι, ∑ j : ι, ‖Y i j‖ ^ (2 : ℕ) := by
  rintro ⟨U, d, hU, hH, hA⟩
  obtain ⟨x, hx⟩ : ∃ x : ι → ℝ, x = fun i => Real.exp (d i) := ⟨_, rfl⟩
  have hA' : A = U * diagonal (fun i => (x i : ℂ)) * Uᴴ := by subst hx; exact hA
  have hxpos : ∀ i, 0 < x i := fun i => by rw [hx]; exact Real.exp_pos _
  have hlogx : ∀ i, Real.log (x i) = d i := fun i => by rw [hx]; exact Real.log_exp _
  set m := Real.exp (-∑ i, |d i|) with hmdef
  have hm : 0 < m := Real.exp_pos _
  have hmx : ∀ i, m ≤ x i := fun i => by
    rw [hx]
    refine Real.exp_le_exp.mpr ?_
    have h1 := Finset.single_le_sum (f := fun i => |d i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h2 := neg_abs_le (d i)
    linarith
  obtain ⟨C, hC0, hg⟩ := _root_.GlobalTheory.ClassFin.log_sq_le_tangent_add_sq (m / 2) (by positivity)
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  have hn : 0 ≤ n * n := mul_self_nonneg n
  refine ⟨C, (m / 2) / (n * n + 1), by positivity, ?_⟩
  rintro Y H' hY ⟨V, e, hV, hH', hB⟩
  obtain ⟨y, hy⟩ : ∃ y : ι → ℝ, y = fun j => Real.exp (e j) := ⟨_, rfl⟩
  have hB' : A + Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ := by subst hy; exact hB
  have hlogy : ∀ j, Real.log (y j) = e j := fun j => by rw [hy]; exact Real.log_exp _
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have hylow : ∀ j, m / 2 ≤ y j := by
    intro j
    have h1 := le_eigenvalue_of_add U V Y x y m _ hU hV hmx hY (by rw [← hA']; exact hB') j
    have h2 : n * n * ((m / 2) / (n * n + 1)) ≤ m / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    rw [← hndef] at h1
    linarith
  have honeU : U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ = 1 := by
    simp [hU]
  have honeV : V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ = 1 := by
    simp [hV]

  have T1 : Complex.re (Matrix.trace (H' * H'))
      = ∑ i, ∑ j, 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j) := by
    rw [hH', conj_real_diagonal_mul_conj_real_diagonal V hV' e e,
      show V * diagonal (fun i => ((e i * e i : ℝ) : ℂ)) * Vᴴ
        = U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun i => ((e i * e i : ℝ) : ℂ)) * Vᴴ) by rw [honeU, Matrix.one_mul],
      re_trace_conj_diagonal_mul]
  have T2 : Complex.re (Matrix.trace (H * H))
      = ∑ i, ∑ j, (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j) := by
    rw [hH, conj_real_diagonal_mul_conj_real_diagonal U hU' d d,
      show U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * Uᴴ
        = U * diagonal (fun i => ((d i * d i : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one],
      re_trace_conj_diagonal_mul]
  have hAinv : A⁻¹ = U * diagonal (fun i => ((x i)⁻¹ : ℂ)) * Uᴴ := by
    have h : U * diagonal (fun i => ((x i)⁻¹ : ℂ)) * Uᴴ
        = U * diagonal (fun i => (((x i)⁻¹ : ℝ) : ℂ)) * Uᴴ := by simp
    rw [h]
    refine Matrix.inv_eq_right_inv ?_
    rw [hA', conj_real_diagonal_mul_conj_real_diagonal U hU',
      show (fun i => ((x i * (x i)⁻¹ : ℝ) : ℂ)) = fun _ => ((1 : ℝ) : ℂ) from
        funext fun i => by rw [mul_inv_cancel₀ (hxpos i).ne'], honeU]
  have hYeq : Y = V * diagonal (fun j => (y j : ℂ)) * Vᴴ - U * diagonal (fun i => (x i : ℂ)) * Uᴴ := by
    rw [← hB', hA', add_sub_cancel_left]
  have hHA : H * A⁻¹ = U * diagonal (fun i => ((d i * (x i)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    rw [hAinv, hH, ← conj_real_diagonal_mul_conj_real_diagonal U hU']
    simp
  have T3 : Complex.re (Matrix.trace (H * A⁻¹ * Y))
      = ∑ i, ∑ j, (d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j)
        - ∑ i, ∑ j, d i * 1 * Complex.normSq ((Uᴴ * V) i j) := by
    rw [hHA, hYeq, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, re_trace_conj_diagonal_mul,
      conj_real_diagonal_mul_conj_real_diagonal U hU',
      show (fun i => ((d i * (x i)⁻¹ * x i : ℝ) : ℂ)) = fun i => (d i : ℂ) from
        funext fun i => by rw [inv_mul_cancel_right₀ (hxpos i).ne'],
      show U * diagonal (fun i => (d i : ℂ)) * Uᴴ
        = U * diagonal (fun i => (d i : ℂ)) * Uᴴ
          * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one],
      re_trace_conj_diagonal_mul]
  have T4 : ∑ i : ι, ∑ j : ι, ‖Y i j‖ ^ (2 : ℕ)
      = ∑ i, ∑ j, 1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j)
        - ∑ i, ∑ j, x i * y j * Complex.normSq ((Uᴴ * V) i j)
        - ∑ i, ∑ j, x i * y j * Complex.normSq ((Uᴴ * V) i j)
        + ∑ i, ∑ j, (x i * x i) * 1 * Complex.normSq ((Uᴴ * V) i j) := by
    rw [sum_norm_sq_eq_re_trace_mul_conjTranspose, hYeq, conjTranspose_sub, conjTranspose_unitary_conj_real_diagonal,
      conjTranspose_unitary_conj_real_diagonal, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Complex.sub_re, Complex.sub_re,
      Complex.sub_re, Matrix.trace_mul_comm (V * _ * Vᴴ) (U * _ * Uᴴ),
      conj_real_diagonal_mul_conj_real_diagonal V hV' y y, conj_real_diagonal_mul_conj_real_diagonal U hU' x x,
      show V * diagonal (fun i => ((y i * y i : ℝ) : ℂ)) * Vᴴ
        = U * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun i => ((y i * y i : ℝ) : ℂ)) * Vᴴ) by rw [honeU, Matrix.one_mul],
      show U * diagonal (fun i => ((x i * x i : ℝ) : ℂ)) * Uᴴ
        = U * diagonal (fun i => ((x i * x i : ℝ) : ℂ)) * Uᴴ
          * (V * diagonal (fun _ => ((1 : ℝ) : ℂ)) * Vᴴ) by rw [honeV, Matrix.mul_one],
      re_trace_conj_diagonal_mul, re_trace_conj_diagonal_mul, re_trace_conj_diagonal_mul]
    ring
  rw [T1, T2, T3, T4]
  have hpt : ∀ i j, 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j)
      ≤ (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j)
        + 2 * ((d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j)
          - d i * 1 * Complex.normSq ((Uᴴ * V) i j))
        + C * (1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          + (x i * x i) * 1 * Complex.normSq ((Uᴴ * V) i j)) := by
    intro i j
    have hb := hg (x i) (y j) ((div_le_self hm.le one_le_two).trans (hmx i)) (hylow j)
    rw [hlogx, hlogy] at hb
    have hw := Complex.normSq_nonneg ((Uᴴ * V) i j)
    have hxne := (hxpos i).ne'
    have key : (d i * d i) * 1 * Complex.normSq ((Uᴴ * V) i j)
        + 2 * ((d i * (x i)⁻¹) * y j * Complex.normSq ((Uᴴ * V) i j)
          - d i * 1 * Complex.normSq ((Uᴴ * V) i j))
        + C * (1 * (y j * y j) * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          - x i * y j * Complex.normSq ((Uᴴ * V) i j)
          + (x i * x i) * 1 * Complex.normSq ((Uᴴ * V) i j))
        - 1 * (e j * e j) * Complex.normSq ((Uᴴ * V) i j)
        = Complex.normSq ((Uᴴ * V) i j)
          * (d i ^ 2 + 2 * d i / x i * (y j - x i) + C * (y j - x i) ^ 2 - e j ^ 2) := by
      field_simp
      ring
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hb)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j

end GlobalTheory.ClassFin.LogSqVar
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_log_trace_sq_first_variation_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H A : Matrix ι ι ℂ), IsLog H A → ∃ C δ : ℝ, 0 < δ ∧ ∀ Y H' : Matrix ι ι ℂ, (∀ i j, ‖Y i j‖ ≤ δ) → IsLog H' (A + Y) → (Matrix.trace (H' * H')).re ≤ (Matrix.trace (H * H)).re + 2 * (Matrix.trace (H * A⁻¹ * Y)).re + C * ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.ClassFin.LogSqVar.first_variation
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mul_diagonal_eq_neg_of_exp {ι : Type} [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) (d d' : ι → ℝ)
    (h : diagonal (fun i => (Real.exp (d' i) : ℂ)) * y * diagonal (fun i => (Real.exp (d i) : ℂ)) = y) :
    y * diagonal (fun i => (d i : ℂ)) = -(diagonal (fun i => (d' i : ℂ)) * y) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at hij
  rw [neg_apply, mul_diagonal, diagonal_mul]
  by_cases hy : y i j = 0
  · simp [hy]
  · have h1 : ((Real.exp (d' i) : ℝ) : ℂ) * (Real.exp (d j) : ℝ) = 1 := by
      apply mul_left_cancel₀ hy
      linear_combination hij
    have h2 : Real.exp (d' i + d j) = 1 := by
      rw [Real.exp_add]
      exact_mod_cast h1
    have h3 : d' i + d j = 0 := by simpa using h2
    have h4 : (d' i : ℂ) + (d j : ℂ) = 0 := by exact_mod_cast h3
    linear_combination (y i j) * h4

theorem mul_log_eq_neg_log_mul : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x x' H H' : Matrix ι ι ℂ), IsLog H (xᴴ * x) → IsLog H' (x'ᴴ * x') → x' * x = 1 → x * H = -(H' * x) := by
  intro ι _ _ x x' H H' ⟨U, d, hU, hH, hA⟩ ⟨V, d', hV, hH', hA'⟩ hx
  have hx' : x * x' = 1 := mul_eq_one_comm.mp hx
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have key : (x'ᴴ * x') * x * (xᴴ * x) = x := by
    calc (x'ᴴ * x') * x * (xᴴ * x) = x'ᴴ * (x' * x) * xᴴ * x := by simp only [Matrix.mul_assoc]
      _ = (x * x')ᴴ * x := by rw [hx, Matrix.mul_one, conjTranspose_mul]
      _ = x := by rw [hx', conjTranspose_one, Matrix.one_mul]
  rw [hA, hA'] at key
  have hy := mul_diagonal_eq_neg_of_exp (Vᴴ * x * U) d d' (by
    calc _ = (Vᴴ * V) * diagonal (fun i => (Real.exp (d' i) : ℂ)) * (Vᴴ * x * U) *
            diagonal (fun i => (Real.exp (d i) : ℂ)) * (Uᴴ * U) := by
          rw [hV', hU', Matrix.one_mul, Matrix.mul_one]
      _ = Vᴴ * (V * diagonal (fun i => (Real.exp (d' i) : ℂ)) * Vᴴ * x *
            (U * diagonal (fun i => (Real.exp (d i) : ℂ)) * Uᴴ)) * U := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * x * U := by rw [key])
  calc x * H = (V * Vᴴ) * x * H := by rw [hV, Matrix.one_mul]
    _ = V * (Vᴴ * x * U * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
        rw [hH]; simp only [Matrix.mul_assoc]
    _ = -(H' * x * (U * Uᴴ)) := by
        rw [hy, hH']; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    _ = -(H' * x) := by rw [hU, Matrix.mul_one]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_log_eq_neg_log_mul' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x x' H H' : Matrix ι ι ℂ), IsLog H (xᴴ * x) → IsLog H' (x'ᴴ * x') → x' * x = 1 → x * H = -(H' * x) := by
  atlas_forward_decl GlobalTheory.ClassFin.mul_log_eq_neg_log_mul
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HarmMin

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma log_herm {H A : Matrix ι ι ℂ} (h : IsLog H A) : Hᴴ = H := by
  obtain ⟨U, d, -, rfl, -⟩ := h
  have : (diagonal (fun i => (d i : ℂ)))ᴴ = diagonal (fun i => (d i : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; ext i; simp
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, this, Matrix.mul_assoc]

lemma log_comm {H A : Matrix ι ι ℂ} (h : IsLog H A) : A * H = H * A := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  have e : ∀ Z : Matrix ι ι ℂ, Uᴴ * (U * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
  simp only [Matrix.mul_assoc, e]
  congr 1
  simp only [← Matrix.mul_assoc, diagonal_mul_diagonal]
  congr 2
  ext i
  ring

lemma trace_id {g g' H H' X : Matrix ι ι ℂ} (hg : g' * g = 1) (hc : (gᴴ * g) * H = H * (gᴴ * g))
    (hi : g * H = -(H' * g)) :
    Matrix.trace (H * (gᴴ * g)⁻¹ * (-X * (gᴴ * g) + gᴴ * X * g + gᴴ * X * g - (gᴴ * g) * X)) =
      -2 * Matrix.trace (H * X) - 2 * Matrix.trace (H' * X) := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg
  have hg3 : g'ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hg2, conjTranspose_one]
  have hA : (g' * g'ᴴ) * (gᴴ * g) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g'ᴴ, hg3, Matrix.one_mul, hg]
  have hinv : (gᴴ * g)⁻¹ = g' * g'ᴴ := Matrix.inv_eq_left_inv hA
  have hA' : (gᴴ * g) * (g' * g'ᴴ) = 1 := mul_eq_one_comm.1 hA
  rw [hinv]
  have e1 : Matrix.trace (H * (g' * g'ᴴ) * (X * (gᴴ * g))) = Matrix.trace (H * X) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc (gᴴ * g) H, hc,
      Matrix.mul_assoc H, hA', Matrix.mul_one]
  have e2 : Matrix.trace (H * (g' * g'ᴴ) * ((gᴴ * g) * X)) = Matrix.trace (H * X) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc H, hA, Matrix.mul_one]
  have e3 : Matrix.trace (H * (g' * g'ᴴ) * (gᴴ * X * g)) = - Matrix.trace (H' * X) := by
    have : H * (g' * g'ᴴ) * (gᴴ * X * g) = (H * g' * X) * g := by
      calc _ = H * g' * (g'ᴴ * gᴴ) * X * g := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hg3, Matrix.mul_one]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hi, Matrix.neg_mul,
      Matrix.mul_assoc H', hg2, Matrix.mul_one, Matrix.neg_mul, Matrix.trace_neg]
  rw [Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add, Matrix.mul_neg, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_neg, e1, e2, e3]
  ring

end GlobalTheory.ClassFin.HarmMin
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma unitary_conj_pow {ι : Type} [Fintype ι] [DecidableEq ι] (U D : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) (n : ℕ) :
    (U * D * Uᴴ) ^ n = U * D ^ n * Uᴴ := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  induction n with
  | zero => simp [hU]
  | succ n ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma aeval_unitary_conj_eq_conj_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (U D : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) (p : ℂ[X]) :
    aeval (U * D * Uᴴ) p = U * aeval D p * Uᴴ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, unitary_conj_pow U D hU]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma aeval_diagonal_adelic_lattice {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) (p : ℂ[X]) :
    aeval (diagonal f) p = diagonal fun i => p.eval (f i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial, diagonal_pow, Algebra.algebraMap_eq_smul_one]; ext i j; by_cases h : i = j <;> simp [h, diagonal_apply]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_interp_aeval_eq_of_isLog {ι : Type} [Fintype ι] [DecidableEq ι] {H A : Matrix ι ι ℂ} (h : _root_.GlobalTheory.ClassFin.IsLog H A) :
    ∃ S : Finset ℝ, ∀ p : ℂ[X], (∀ x ∈ S, p.eval ((Real.exp x : ℝ) : ℂ) = x) → aeval A p = H := by
  obtain ⟨U, d, hU, hH, hA⟩ := h
  refine ⟨Finset.univ.image d, fun p hp => ?_⟩
  rw [hA, aeval_unitary_conj_eq_conj_aeval _ _ hU, aeval_diagonal_adelic_lattice, hH,
    show (fun i => p.eval ((Real.exp (d i) : ℝ) : ℂ)) = fun i => ((d i : ℝ) : ℂ) from
      funext fun i => hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_poly_eval_exp_eq (S : Finset ℝ) : ∃ p : ℂ[X], ∀ x ∈ S, p.eval ((Real.exp x : ℝ) : ℂ) = x := by
  classical
  let T : Finset ℂ := S.image fun x => ((Real.exp x : ℝ) : ℂ)
  refine ⟨Lagrange.interpolate T id (fun z => ((Real.log z.re : ℝ) : ℂ)), fun x hx => ?_⟩
  have hmem : ((Real.exp x : ℝ) : ℂ) ∈ T := Finset.mem_image_of_mem _ hx
  have := Lagrange.eval_interpolate_at_node (v := id) (r := fun z : ℂ => ((Real.log z.re : ℝ) : ℂ))
    (Set.injOn_id _) hmem
  simp only [id] at this
  rw [this, Complex.ofReal_re, Real.log_exp]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma aeval_conj_eq_conj_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (k D : Matrix ι ι ℂ) (hk : IsUnit k.det) (p : ℂ[X]) :
    aeval (k⁻¹ * D * k) p = k⁻¹ * aeval D p * k := by
  have hk1 : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv k hk
  have hpow : ∀ n : ℕ, (k⁻¹ * D * k) ^ n = k⁻¹ * D ^ n * k := by
    intro n
    induction n with
    | zero => simp [Matrix.nonsing_inv_mul k hk]
    | succ n ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc k k⁻¹, hk1, Matrix.one_mul]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, hpow n]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isLog_eq_conj_of_conj {ι : Type} [Fintype ι] [DecidableEq ι] {H A H' B k : Matrix ι ι ℂ}
    (hH : _root_.GlobalTheory.ClassFin.IsLog H A) (hH' : _root_.GlobalTheory.ClassFin.IsLog H' B) (hk : IsUnit k.det)
    (hB : B = k⁻¹ * A * k) : H' = k⁻¹ * H * k := by
  obtain ⟨S, hS⟩ := exists_interp_aeval_eq_of_isLog hH
  obtain ⟨S', hS'⟩ := exists_interp_aeval_eq_of_isLog hH'
  obtain ⟨p, hp⟩ := exists_poly_eval_exp_eq (S ∪ S')
  rw [← hS' p (fun x hx => hp x (Finset.mem_union_right _ hx)), ← hS p (fun x hx => hp x (Finset.mem_union_left _ hx)),
    hB, aeval_conj_eq_conj_aeval k A hk]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isLog_neg_inv {ι : Type} [Fintype ι] [DecidableEq ι] {H A : Matrix ι ι ℂ}
    (hH : _root_.GlobalTheory.ClassFin.IsLog H A) : _root_.GlobalTheory.ClassFin.IsLog (-H) A⁻¹ := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := hH
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  refine ⟨U, fun i => -d i, hU, ?_, ?_⟩
  · simp [Matrix.neg_mul, Matrix.mul_neg, ← diagonal_neg]
  · apply Matrix.inv_eq_right_inv
    calc (U * diagonal (fun i => ((Real.exp (d i) : ℝ) : ℂ)) * Uᴴ) * (U * diagonal (fun i => ((Real.exp (-d i) : ℝ) : ℂ)) * Uᴴ)
        = U * (diagonal (fun i => ((Real.exp (d i) : ℝ) : ℂ)) * diagonal (fun i => ((Real.exp (-d i) : ℝ) : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]
      _ = 1 := by
          rw [diagonal_mul_diagonal]
          simp [← Complex.exp_add, hU]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isLog_isHermitian {ι : Type} [Fintype ι] [DecidableEq ι] {H A : Matrix ι ι ℂ}
    (hH : _root_.GlobalTheory.ClassFin.IsLog H A) : Hᴴ = H := by
  obtain ⟨U, d, hU, rfl, -⟩ := hH
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose]
  congr 3
  funext i
  simp

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma eq_zero_of_trace_zero_of_re_trace_squareZero {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (htr : M.trace = 0)
    (hV : ∀ N : Matrix ι ι ℂ, N * N = 0 → Complex.re (Matrix.trace (M * (N + Nᴴ))) = 0) : M = 0 := by
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have h1 := hV (single i j 1) (single_mul_single_of_ne 1 i j i hij.symm 1)
    have h2 := hV (single i j Complex.I) (single_mul_single_of_ne _ i j i hij.symm _)
    have hc : M j i = star (M i j) := by
      have := congrFun (congrFun hM j) i
      simpa [conjTranspose_apply] using this.symm
    simp [conjTranspose_single, Matrix.mul_add, trace_add, trace_mul_single, hc] at h1 h2
    apply Complex.ext <;> simp <;> linarith
  have hdiag : ∀ i j, M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    set N : Matrix ι ι ℂ := single i i 1 - single i j 1 + single j i 1 - single j j 1 with hN
    have hNN : N * N = 0 := by
      simp only [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, single_mul_single_same,
        single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ (Ne.symm hij), mul_one]
      abel
    have h1 := hV N hNN
    have hc : ∀ k, (M k k).im = 0 := by
      intro k
      have := congrFun (congrFun hM k) k
      have h' : star (M k k) = M k k := by simpa [conjTranspose_apply] using this
      have := congrArg Complex.im h'
      simp at this
      linarith
    simp [hN, conjTranspose_single, Matrix.mul_add, Matrix.mul_sub, trace_add, trace_sub, trace_mul_single,
      hoff i j hij, hoff j i (Ne.symm hij)] at h1
    apply Complex.ext
    · linarith
    · rw [hc i, hc j]
  ext i j
  by_cases hij : i = j
  · subst hij
    have ht : M.trace = (Fintype.card ι : ℂ) * M i i := by
      rw [Matrix.trace]
      simp [hdiag _ i]
    rw [htr] at ht
    have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
      exact_mod_cast this.ne'
    simpa [hcard] using ht.symm
  · exact hoff i j hij

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma norm_add_add_add_le (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  linarith [norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma re_trace_isLog_sq_le_second_order {ι : Type} [Fintype ι] [DecidableEq ι] (H A Y1 Y2 Y3 Y4 : Matrix ι ι ℂ)
    (hH : _root_.GlobalTheory.ClassFin.IsLog H A) :
    ∃ K ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ H' : Matrix ι ι ℂ,
      _root_.GlobalTheory.ClassFin.IsLog H' (A + ((t : ℂ) • Y1 + (t : ℂ) ^ 2 • Y2 + (t : ℂ) ^ 3 • Y3 + (t : ℂ) ^ 4 • Y4)) →
      Complex.re (Matrix.trace (H' * H')) ≤ Complex.re (Matrix.trace (H * H)) +
        t * (2 * Complex.re (Matrix.trace (H * A⁻¹ * Y1))) + t ^ 2 * K := by
  obtain ⟨C, δ, hδ, hb⟩ := _root_.GlobalTheory.ClassFin.LogSqVar.first_variation ι H A hH
  set b : ι → ι → ℝ := fun i j => ‖Y1 i j‖ + ‖Y2 i j‖ + ‖Y3 i j‖ + ‖Y4 i j‖ with hb_def
  set B : ℝ := ∑ i, ∑ j, b i j with hB_def
  set l2 := Complex.re (Matrix.trace (H * A⁻¹ * Y2))
  set l3 := Complex.re (Matrix.trace (H * A⁻¹ * Y3))
  set l4 := Complex.re (Matrix.trace (H * A⁻¹ * Y4))
  have hb0 : ∀ i j, 0 ≤ b i j := fun i j => by simp only [hb_def]; positivity
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hb0 i j
  have hbB : ∀ i j, b i j ≤ B := fun i j =>
    (Finset.single_le_sum (f := fun j => b i j) (fun j _ => hb0 i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, b i j) (fun i _ => Finset.sum_nonneg fun j _ => hb0 i j)
        (Finset.mem_univ i))
  refine ⟨2 * (|l2| + |l3| + |l4|) + |C| * ∑ i, ∑ j, b i j ^ 2, min 1 (δ / (B + 1)),
    lt_min one_pos (div_pos hδ (by linarith)), ?_⟩
  intro t ht H' hH'
  have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht (min_le_left _ _)).le
  have htδ : |t| < δ / (B + 1) := lt_of_lt_of_le ht (min_le_right _ _)
  set Y := (t : ℂ) • Y1 + (t : ℂ) ^ 2 • Y2 + (t : ℂ) ^ 3 • Y3 + (t : ℂ) ^ 4 • Y4 with hY
  have ht2 : t ^ 2 ≤ |t| := by nlinarith [sq_abs t, abs_nonneg t]
  have ht3 : |t| ^ 3 ≤ |t| := by nlinarith [abs_nonneg t, pow_le_one₀ (abs_nonneg t) ht1 (n := 2)]
  have ht4 : |t| ^ 4 ≤ |t| := by nlinarith [abs_nonneg t, pow_le_one₀ (abs_nonneg t) ht1 (n := 3)]
  have hentry : ∀ i j, ‖Y i j‖ ≤ |t| * b i j := by
    intro i j
    simp only [hY, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine (norm_add_add_add_le _ _ _ _).trans ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hb_def]
    have := sq_abs t
    nlinarith [norm_nonneg (Y1 i j), norm_nonneg (Y2 i j), norm_nonneg (Y3 i j), norm_nonneg (Y4 i j),
      mul_le_mul_of_nonneg_right ht2 (norm_nonneg (Y2 i j)), mul_le_mul_of_nonneg_right ht3 (norm_nonneg (Y3 i j)),
      mul_le_mul_of_nonneg_right ht4 (norm_nonneg (Y4 i j))]
  have hsmall : ∀ i j, ‖Y i j‖ ≤ δ := by
    intro i j
    refine (hentry i j).trans ?_
    have h1 : |t| * (B + 1) < δ := by rwa [lt_div_iff₀ (by linarith)] at htδ
    nlinarith [hbB i j, abs_nonneg t]
  have key := hb Y H' hsmall hH'
  have htr : Complex.re (Matrix.trace (H * A⁻¹ * Y)) =
      t * Complex.re (Matrix.trace (H * A⁻¹ * Y1)) + t ^ 2 * l2 + t ^ 3 * l3 + t ^ 4 * l4 := by
    rw [hY]
    simp only [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul, Complex.add_re,
      ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    all_goals rfl
  have hsq : ∑ i, ∑ j, ‖Y i j‖ ^ 2 ≤ t ^ 2 * ∑ i, ∑ j, b i j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := hentry i j
    have h0 := norm_nonneg (Y i j)
    calc ‖Y i j‖ ^ 2 ≤ (|t| * b i j) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = t ^ 2 * b i j ^ 2 := by rw [mul_pow, sq_abs]
  have hC : C * ∑ i, ∑ j, ‖Y i j‖ ^ 2 ≤ |C| * (t ^ 2 * ∑ i, ∑ j, b i j ^ 2) := by
    have hS0 : 0 ≤ ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by positivity
    calc C * ∑ i, ∑ j, ‖Y i j‖ ^ 2 ≤ |C| * ∑ i, ∑ j, ‖Y i j‖ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (abs_nonneg C)
  have hl : t ^ 2 * l2 + t ^ 3 * l3 + t ^ 4 * l4 ≤ t ^ 2 * (|l2| + |l3| + |l4|) := by
    have ha : |t| ^ 3 = t ^ 2 * |t| := by rw [pow_succ, sq_abs]
    have hb4 : t ^ 4 ≤ t ^ 2 := by nlinarith [sq_nonneg t, sq_abs t]
    have e3 : t ^ 3 * l3 ≤ t ^ 2 * |l3| := by
      calc t ^ 3 * l3 ≤ |t ^ 3 * l3| := le_abs_self _
        _ = |t| ^ 3 * |l3| := by rw [abs_mul, abs_pow]
        _ ≤ t ^ 2 * |l3| := by rw [ha]; nlinarith [mul_le_mul_of_nonneg_left ht1 (mul_nonneg (sq_nonneg t) (abs_nonneg l3))]
    have e4 : t ^ 4 * l4 ≤ t ^ 2 * |l4| := by
      calc t ^ 4 * l4 ≤ t ^ 4 * |l4| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _ ≤ t ^ 2 * |l4| := mul_le_mul_of_nonneg_right hb4 (abs_nonneg _)
    nlinarith [le_abs_self l2, sq_nonneg t, mul_le_mul_of_nonneg_left (le_abs_self l2) (sq_nonneg t)]
  rw [htr] at key
  linarith [key, hC, hl]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma gram_expansion_quartic_in_t {ι : Type} [Fintype ι] [DecidableEq ι] (h N : Matrix ι ι ℂ) (hNN : N * N = 0) (t : ℝ) :
    ((1 + (t : ℂ) • N) * h * (1 - (t : ℂ) • N))ᴴ * ((1 + (t : ℂ) • N) * h * (1 - (t : ℂ) • N)) - hᴴ * h =
      (t : ℂ) • (hᴴ * (N + Nᴴ) * h - Nᴴ * (hᴴ * h) - hᴴ * h * N) +
      (t : ℂ) ^ 2 • (hᴴ * Nᴴ * N * h - Nᴴ * (hᴴ * (N + Nᴴ) * h) - hᴴ * (N + Nᴴ) * h * N + Nᴴ * (hᴴ * h) * N) +
      (t : ℂ) ^ 3 • (-(Nᴴ * (hᴴ * Nᴴ * N * h)) - hᴴ * Nᴴ * N * h * N + Nᴴ * (hᴴ * (N + Nᴴ) * h) * N) +
      (t : ℂ) ^ 4 • (Nᴴ * (hᴴ * Nᴴ * N * h) * N) := by
  have hNN' : ∀ X : Matrix ι ι ℂ, N * (N * X) = 0 := fun X => by rw [← Matrix.mul_assoc, hNN, Matrix.zero_mul]
  simp only [conjTranspose_mul, conjTranspose_add, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, hNN', hNN, smul_zero, Matrix.mul_zero]
  module

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma eq_zero_of_nonneg_linear_add_quadratic {a K ε : ℝ} (hε : 0 < ε) (h : ∀ t : ℝ, |t| < ε → 0 ≤ t * a + t ^ 2 * K) :
    a = 0 := by
  by_contra ha
  set s := min (ε / 2) (|a| / (|K| + 1)) with hs
  have hs0 : 0 < s := lt_min (by linarith) (div_pos (abs_pos.mpr ha) (by positivity))
  have hsε : s < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsa : s * (|K| + 1) ≤ |a| := by
    have := min_le_right (ε / 2) (|a| / (|K| + 1))
    rw [← hs] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hK : K ≤ |K| := le_abs_self K
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have h1 := h s (by rw [abs_of_pos hs0]; exact hsε)
    rw [abs_of_neg hneg] at hsa
    nlinarith
  · have h1 := h (-s) (by rw [abs_neg, abs_of_pos hs0]; exact hsε)
    rw [abs_of_pos hpos] at hsa
    nlinarith

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isLog_commute {ι : Type} [Fintype ι] [DecidableEq ι] {H A : Matrix ι ι ℂ}
    (hH : _root_.GlobalTheory.ClassFin.IsLog H A) : H * A = A * H := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := hH
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal _) (diagonal _), ← Matrix.mul_assoc (diagonal _) (diagonal _),
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  simp only [mul_comm]

open Matrix Polynomial in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.exists_conj_harm_of_span : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ P : Matrix ι ι ℂ, IsUnit P.det ∧ _root_.GlobalTheory.ClassFin.Harm (fun s => P * g s * P⁻¹) := by
  intro ι _ _ σ _ τ g hτ hspan
  have hdet : ∀ s, IsUnit (g s).det := fun s => Matrix.isUnit_det_of_left_inverse (hτ s)
  obtain ⟨P, H, hP, hH, hmin⟩ := _root_.GlobalTheory.ClassFin.exists_energy_min ι σ g hdet hspan
  refine ⟨P, hP, H, hH, ?_⟩
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  obtain ⟨h, hh⟩ : ∃ h : σ → Matrix ι ι ℂ, h = fun s => P * g s * P⁻¹ := ⟨_, rfl⟩
  have hH' : ∀ s, _root_.GlobalTheory.ClassFin.IsLog (H s) ((h s)ᴴ * h s) := by intro s; rw [hh]; exact hH s
  have hτh : ∀ s, h (τ s) * h s = 1 := by
    intro s
    simp only [hh, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul, ← Matrix.mul_assoc (g (τ s)), hτ s, Matrix.one_mul, hPP']
  have hhdet : ∀ s, IsUnit (h s).det := fun s => Matrix.isUnit_det_of_left_inverse (hτh s)
  have hinv2 : ∀ s, (h (τ s))⁻¹ = h s := fun s => Matrix.inv_eq_right_inv (hτh s)
  have hhs : ∀ s, h s * (h s)⁻¹ = 1 := fun s => Matrix.mul_nonsing_inv _ (hhdet s)
  have hhs' : ∀ s, (h s)⁻¹ * h s = 1 := fun s => Matrix.nonsing_inv_mul _ (hhdet s)
  have hconj : ∀ s, -H (τ s) = h s * H s * (h s)⁻¹ := by
    intro s
    have hk : IsUnit ((h s)⁻¹).det := by
      rw [Matrix.det_nonsing_inv]; exact (hhdet s).ringInverse
    have := isLog_eq_conj_of_conj (hH' s) (isLog_neg_inv (hH' (τ s))) hk ?_
    · rwa [Matrix.nonsing_inv_nonsing_inv _ (hhdet s)] at this
    · rw [Matrix.nonsing_inv_nonsing_inv _ (hhdet s), Matrix.mul_inv_rev, hinv2, ← Matrix.conjTranspose_nonsing_inv,
        hinv2]
      simp only [Matrix.mul_assoc, hhs, Matrix.mul_one]
  have hHerm : ∀ s, (H s)ᴴ = H s := fun s => isLog_isHermitian (hH' s)
  have htrτ : ∀ s, Matrix.trace (H (τ s)) = -Matrix.trace (H s) := by
    intro s
    have := congrArg Matrix.trace (hconj s)
    rw [trace_neg, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hhs', Matrix.mul_one] at this
    linear_combination -this
  apply eq_zero_of_trace_zero_of_re_trace_squareZero
  · rw [conjTranspose_sum]
    exact Finset.sum_congr rfl fun s _ => hHerm s
  · rw [trace_sum]
    have h1 : ∑ s, Matrix.trace (H (τ s)) = ∑ s, Matrix.trace (H s) := Equiv.sum_comp τ (fun s => Matrix.trace (H s))
    simp only [htrτ, Finset.sum_neg_distrib] at h1
    linear_combination -h1 / 2
  · intro N hNN
    have hb := fun s => re_trace_isLog_sq_le_second_order (H s) ((h s)ᴴ * h s)
      ((h s)ᴴ * (N + Nᴴ) * h s - Nᴴ * ((h s)ᴴ * h s) - (h s)ᴴ * h s * N)
      ((h s)ᴴ * Nᴴ * N * h s - Nᴴ * ((h s)ᴴ * (N + Nᴴ) * h s) - (h s)ᴴ * (N + Nᴴ) * h s * N + Nᴴ * ((h s)ᴴ * h s) * N)
      (-(Nᴴ * ((h s)ᴴ * Nᴴ * N * h s)) - (h s)ᴴ * Nᴴ * N * h s * N + Nᴴ * ((h s)ᴴ * (N + Nᴴ) * h s) * N)
      (Nᴴ * ((h s)ᴴ * Nᴴ * N * h s) * N) (hH' s)
    choose K ε hε hK using hb
    set ℓ : σ → ℝ := fun s => Complex.re (Matrix.trace (H s * ((h s)ᴴ * h s)⁻¹ *
      ((h s)ᴴ * (N + Nᴴ) * h s - Nᴴ * ((h s)ᴴ * h s) - (h s)ᴴ * h s * N))) with hℓ
    set ε0 : ℝ := 1 / (1 + ∑ s, 1 / ε s) with hε0_def
    have hS0 : 0 ≤ ∑ s, 1 / ε s := Finset.sum_nonneg fun s _ => (one_div_pos.mpr (hε s)).le
    have hε0 : 0 < ε0 := by positivity
    have hε0s : ∀ s, ε0 ≤ ε s := by
      intro s
      have h1 : 1 / ε s ≤ ∑ s, 1 / ε s :=
        Finset.single_le_sum (f := fun s => 1 / ε s) (fun s _ => (one_div_pos.mpr (hε s)).le) (Finset.mem_univ s)
      rw [hε0_def, div_le_iff₀ (by positivity)]
      have := hε s
      rw [div_le_iff₀ this] at h1
      nlinarith
    have hlin : ∀ t : ℝ, |t| < ε0 → 0 ≤ t * (2 * ∑ s, ℓ s) + t ^ 2 * ∑ s, K s := by
      intro t ht
      have hQQ : (1 + (t : ℂ) • N) * (1 - (t : ℂ) • N) = 1 := by
        simp [Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNN]
      have hQdet : IsUnit (1 + (t : ℂ) • N).det := Matrix.isUnit_det_of_right_inverse hQQ
      have hQ'det : IsUnit (1 - (t : ℂ) • N).det := Matrix.isUnit_det_of_left_inverse hQQ
      have hP' : IsUnit ((1 + (t : ℂ) • N) * P).det := by rw [Matrix.det_mul]; exact hQdet.mul hP
      have hinvQP : ((1 + (t : ℂ) • N) * P)⁻¹ = P⁻¹ * (1 - (t : ℂ) • N) := Matrix.inv_eq_right_inv (by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hQQ])
      have hconjQ : ∀ s, (1 + (t : ℂ) • N) * P * g s * ((1 + (t : ℂ) • N) * P)⁻¹ =
          (1 + (t : ℂ) • N) * h s * (1 - (t : ℂ) • N) := by
        intro s; rw [hinvQP, hh]; simp only [Matrix.mul_assoc]
      have hex : ∀ s, ∃ H'' : Matrix ι ι ℂ, _root_.GlobalTheory.ClassFin.IsLog H''
          (((1 + (t : ℂ) • N) * P * g s * ((1 + (t : ℂ) • N) * P)⁻¹)ᴴ *
            ((1 + (t : ℂ) • N) * P * g s * ((1 + (t : ℂ) • N) * P)⁻¹)) := by
        intro s
        rw [hconjQ]
        refine _root_.GlobalTheory.ClassFin.exists_isLog_gram ι _ ?_
        rw [Matrix.det_mul, Matrix.det_mul]
        exact (hQdet.mul (hhdet s)).mul hQ'det
      choose H'' hH'' using hex
      have hm := hmin ((1 + (t : ℂ) • N) * P) H'' hP' hH''
      have hbound : ∀ s, Complex.re (Matrix.trace (H'' s * H'' s)) ≤ Complex.re (Matrix.trace (H s * H s)) +
          t * (2 * ℓ s) + t ^ 2 * K s := by
        intro s
        apply hK s t (lt_of_lt_of_le ht (hε0s s))
        have h1 := hH'' s
        rw [hconjQ s] at h1
        have he := gram_expansion_quartic_in_t (h s) N hNN t
        rw [sub_eq_iff_eq_add'] at he
        rw [he] at h1
        exact h1
      have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hbound s
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
      have hm' : ∑ s, Complex.re (Matrix.trace (H s * H s)) ≤ ∑ s, Complex.re (Matrix.trace (H'' s * H'' s)) := hm
      linarith
    have hL := eq_zero_of_nonneg_linear_add_quadratic hε0 hlin
    have hℓs : ∀ s, Matrix.trace (H s * ((h s)ᴴ * h s)⁻¹ *
        ((h s)ᴴ * (N + Nᴴ) * h s - Nᴴ * ((h s)ᴴ * h s) - (h s)ᴴ * h s * N)) =
        -Matrix.trace (H (τ s) * (N + Nᴴ)) - Matrix.trace (H s * (N + Nᴴ)) := by
      intro s
      have hcdet : IsUnit ((h s)ᴴ).det := by rw [Matrix.det_conjTranspose]; exact (hhdet s).star
      have hAdet : IsUnit ((h s)ᴴ * h s).det := by rw [Matrix.det_mul]; exact hcdet.mul (hhdet s)
      have hAinv : ((h s)ᴴ * h s)⁻¹ = (h s)⁻¹ * ((h s)ᴴ)⁻¹ := Matrix.mul_inv_rev _ _
      have hc' : ((h s)ᴴ)⁻¹ * (h s)ᴴ = 1 := Matrix.nonsing_inv_mul _ hcdet
      have hA1 : ((h s)ᴴ * h s)⁻¹ * ((h s)ᴴ * h s) = 1 := Matrix.nonsing_inv_mul _ hAdet
      have hA2 : ((h s)ᴴ * h s) * ((h s)ᴴ * h s)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hAdet
      have hcomm := isLog_commute (hH' s)
      have t1 : Matrix.trace (H s * ((h s)ᴴ * h s)⁻¹ * ((h s)ᴴ * (N + Nᴴ) * h s)) =
          -Matrix.trace (H (τ s) * (N + Nᴴ)) := by
        have hτ' : H (τ s) = -(h s * H s * (h s)⁻¹) := by rw [← hconj s, neg_neg]
        rw [hAinv, hτ', Matrix.neg_mul, trace_neg, neg_neg,
          show H s * ((h s)⁻¹ * ((h s)ᴴ)⁻¹) * ((h s)ᴴ * (N + Nᴴ) * h s) = (H s * (h s)⁻¹ * (N + Nᴴ)) * h s by
            simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc ((h s)ᴴ)⁻¹, hc', Matrix.one_mul],
          trace_mul_comm]
        simp only [Matrix.mul_assoc]
      have t2 : Matrix.trace (H s * ((h s)ᴴ * h s)⁻¹ * (Nᴴ * ((h s)ᴴ * h s))) = Matrix.trace (H s * Nᴴ) := by
        rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcomm,
          Matrix.mul_assoc (H s), hA2, Matrix.mul_one]
      have t3 : Matrix.trace (H s * ((h s)ᴴ * h s)⁻¹ * ((h s)ᴴ * h s * N)) = Matrix.trace (H s * N) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ N, hA1, Matrix.one_mul]
      rw [Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub, t1, t2, t3, Matrix.mul_add (H s) N Nᴴ, trace_add]
      ring
    have hsumℓ : ∑ s, ℓ s = -2 * Complex.re (Matrix.trace ((∑ s, H s) * (N + Nᴴ))) := by
      simp only [hℓ, hℓs, Complex.sub_re, Complex.neg_re, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      have e := Equiv.sum_comp τ (fun s => Complex.re (Matrix.trace (H s * (N + Nᴴ))))
      rw [e, Finset.sum_mul, trace_sum, Complex.re_sum]
      ring
    linarith

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_harm_of_span' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ P : Matrix ι ι ℂ, IsUnit P.det ∧ Harm (fun s => P * g s * P⁻¹) := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_conj_harm_of_span
end
