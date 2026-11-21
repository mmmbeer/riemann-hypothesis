import Formalism.SatakeDualWeyl.Statement

namespace Formalism.UG.P

open MvPolynomial

section

variable (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]

noncomputable def monFam (k : ℕ) : {d : n →₀ ℕ | d.degree = k} → MvPolynomial n O :=
  fun d => monomial (d : n →₀ ℕ) 1

end

section

variable (n : Type) [Fintype n] [DecidableEq n]

theorem degree_eq_one_iff (d : n →₀ ℕ) : d.degree = 1 ↔ ∃ i, d = Finsupp.single i 1 := by
  constructor
  · intro hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Finsupp.ext h)
    have hle : d i ≤ 1 := hd ▸ Finsupp.le_degree i d
    have hi1 : d i = 1 := by omega
    have hsle : Finsupp.single i 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      omega
    have hsplit : d = Finsupp.single i 1 + (d - Finsupp.single i 1) :=
      (add_tsub_cancel_of_le hsle).symm
    have hdeg : (d - Finsupp.single i 1).degree = 0 := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this
      omega
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    refine ⟨i, ?_⟩
    rw [hdeg, add_zero] at hsplit
    exact hsplit
  · rintro ⟨i, rfl⟩
    simp

noncomputable def idx1 : n ≃ {d : n →₀ ℕ | d.degree = 1} :=
  Equiv.ofBijective (fun i => ⟨Finsupp.single i 1, by simp⟩)
    ⟨fun i j h => by
      have h' : Finsupp.single i 1 = Finsupp.single j 1 := congrArg Subtype.val h
      exact (Finsupp.single_left_inj one_ne_zero).mp h',
     fun d => by
      obtain ⟨i, hi⟩ := (degree_eq_one_iff n d).mp d.2
      exact ⟨i, Subtype.ext hi.symm⟩⟩

end

end Formalism.UG.P
