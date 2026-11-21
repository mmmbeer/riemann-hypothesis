import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.VnuMapZero

noncomputable section

open Matrix Classical Finset PI.IsoInvMetric Polynomial

namespace PI.IsoInvMetricW

theorem star_mul_self_of_norm {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  have h := Complex.conj_mul' z
  rw [hz] at h
  simpa using h

theorem emb_ge {h N : ℕ} (J : Fin h ↪o Fin N) (i : Fin h) : (i : ℕ) ≤ J i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 : J ⟨n, by omega⟩ < J ⟨n + 1, hi⟩ := J.lt_iff_lt.mpr (by simp [Fin.lt_def])
    have h3 : ((J ⟨n, by omega⟩ : Fin N) : ℕ) < ((J ⟨n + 1, hi⟩ : Fin N) : ℕ) := h2
    simp only at h1 ⊢
    omega

section
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

def wt (J : ColChoice N nu) : ℕ := ∑ s, ∑ c, ∑ i, (N - ((J s c i : Fin N) : ℕ))

theorem column_index_val (hle : ∀ z, (nu z).colLen 0 ≤ N) (s : Lt) (c : Fin ((nu s).rowLen 0))
    (i : Fin ((nu s).colLen c)) : ((J0 nu hle s c i : Fin N) : ℕ) = i := by
  simp [J0]

theorem wt_lt (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) (hJ : J ≠ J0 nu hle) :
    wt J < wt (J0 nu hle) := by
  have hex : ∃ s c i, J s c i ≠ J0 nu hle s c i := by
    by_contra hc
    push Not at hc
    apply hJ
    funext s c
    exact DFunLike.ext _ _ (hc s c)
  obtain ⟨s0, c0, i0, h0⟩ := hex
  have hv : ((J s0 c0 i0 : Fin N) : ℕ) ≠ i0 := by
    intro e; apply h0; apply Fin.ext; rw [e, column_index_val]
  have hterm : ∀ s c i, N - ((J s c i : Fin N) : ℕ) ≤ N - ((J0 nu hle s c i : Fin N) : ℕ) := by
    intro s c i; rw [column_index_val]; have := emb_ge (J s c) i; omega
  unfold wt
  apply Finset.sum_lt_sum (fun s _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i _ => hterm s c i)
  refine ⟨s0, Finset.mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun c _ => Finset.sum_le_sum fun i _ => hterm s0 c i)
  refine ⟨c0, Finset.mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun i _ => hterm s0 c0 i)
  refine ⟨i0, Finset.mem_univ _, ?_⟩
  rw [column_index_val]
  have := emb_ge (J s0 c0) i0
  have := (J s0 c0 i0).isLt
  omega

def dz (z : ℂ) (_s : Lt) (a : Fin N) : ℂ := z ^ (N - (a : ℕ))

theorem torus_unitary {z : ℂ} (hz : ‖z‖ = 1) (s : Lt) :
    Matrix.diagonal (dz (N := N) z s) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp only [dz, Pi.star_apply, star_pow]
  rw [← mul_pow, star_mul_self_of_norm hz, one_pow]

end

end PI.IsoInvMetricW
