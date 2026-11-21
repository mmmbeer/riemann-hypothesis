import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype

section
noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

theorem oe_eq_of_range_sub {h N : ℕ} (I J : Fin h ↪o Fin N) (hs : ∀ i, ∃ k, J k = I i) :
    I = J := by
  classical
  have h1 : Finset.univ.image I ⊆ Finset.univ.image J := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact hs i
  have h2 : Finset.univ.image I = Finset.univ.image J :=
    Finset.eq_of_subset_of_card_le h1 (by
      rw [Finset.card_image_of_injective _ J.injective,
        Finset.card_image_of_injective _ I.injective])
  apply OrderEmbedding.range_inj.mp
  have := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) h2
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using this

theorem metric_diagonal : EDiag := by
  intro Lt _ _ N nu d I J
  unfold E
  split_ifs with hIJ
  · subst hIJ
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    have : (Matrix.of fun i k : Fin ((nu s).colLen c) =>
        Matrix.diagonal (d s) (I s c i) (I s c k)) = Matrix.diagonal (fun i => d s (I s c i)) := by
      ext i k
      simp [Matrix.diagonal_apply, (I s c).injective.eq_iff]
    rw [this, Matrix.det_diagonal]
  · have : ∃ s c, I s c ≠ J s c := by
      by_contra hne
      push_neg at hne
      exact hIJ (funext fun s => funext fun c => hne s c)
    obtain ⟨s, c, hsc⟩ := this
    have : ∃ i, ∀ k, J s c k ≠ I s c i := by
      by_contra hne
      push_neg at hne
      exact hsc (oe_eq_of_range_sub _ _ hne)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro k
    simp [Matrix.diagonal_apply_ne _ (hi k).symm]

def J0 {Lt : Type} {N : ℕ} (nu : Lt → YoungDiagram) (hle : ∀ z, (nu z).colLen 0 ≤ N) :
    ColChoice N nu :=
  fun s c => Fin.castLEOrderEmb (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))

end PI.IsoInvMetricW
end
end

section
noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

section
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem vnuMap_eq (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu f φ I = ∑ J, E nu f I J * φ J := by
  unfold VnuMap
  rw [finsum_eq_sum_of_fintype]
  rfl

theorem vnuMap_smul (f : Lt → Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (φ : LaC N nu) :
    VnuMap nu f (a • φ) = a • VnuMap nu f φ := by
  funext I
  simp only [vnuMap_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun J _ => by ring

theorem eStar (k : Lt → Matrix (Fin N) (Fin N) ℂ) (I J : ColChoice N nu) :
    starRingEnd ℂ (E nu k I J) = E nu (fun s => star (k s)) J I := by
  unfold E
  simp only [map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [starRingEnd_apply, ← Matrix.det_conjTranspose]
  congr 1

theorem e_one (g : Lt → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ s, g s = 1) (I J : ColChoice N nu) :
    E nu g I J = if I = J then 1 else 0 := by
  have : g = fun s => Matrix.diagonal (fun _ => (1 : ℂ)) := by
    funext s
    rw [hg, Matrix.diagonal_one]
  rw [this, metric_diagonal]
  split_ifs <;> simp
end

theorem unit_of (hE : EMul) : Unit := by
  intro Lt _ _ N nu k hk φ ψ
  have hkk : ∀ z, star (k z) * k z = 1 := fun z => Matrix.mem_unitaryGroup_iff'.mp (hk z)
  have h1 : ∀ J J' : ColChoice N nu,
      ∑ I, starRingEnd ℂ (E nu k I J) * E nu k I J' = if J = J' then 1 else 0 := by
    intro J J'
    simp only [eStar]
    rw [hE]
    exact e_one _ hkk J J'
  have step : ∀ J J' : ColChoice N nu, ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') =
      star (φ J) * ψ J' * (if J = J' then 1 else 0) := by
    intro J J'
    rw [← h1 J J', Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [star_mul', starRingEnd_apply]
    ring
  unfold ipl
  simp only [vnuMap_eq]
  calc ∑ I, star (∑ J, E nu k I J * φ J) * ∑ J', E nu k I J' * ψ J'
      = ∑ I, ∑ J, ∑ J', star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ J, ∑ J', ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ J, star (φ J) * ψ J := by
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [step, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp

end PI.IsoInvMetricW
end
end
