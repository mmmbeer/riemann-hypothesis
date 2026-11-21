import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CuspFormNormData

open NumberField Matrix Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

namespace GlobalTheory.CuspCharLattice

section General

variable {K : Type} [Field K] [NumberField K]

theorem exists_smul_mem {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {M : Submodule (𝓞 K) W}
    {x : W} (hx : x ∈ Submodule.span K (M : Set W)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨⟨e, he⟩, b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) a
    refine ⟨d * e, mul_ne_zero hd (nonZeroDivisors.ne_zero he), ?_⟩
    have hb' : algebraMap (𝓞 K) K b = e • a := hb
    have : (d * e) • a • x = b • d • x := by
      rw [mul_smul, ← smul_assoc e a x, ← hb', algebraMap_smul, smul_comm]
    rw [this]
    exact M.smul_mem _ hx

end General

variable {R : Ranks} {H : Host R} {n : ℕ}

theorem host_AA_ne_zero (H : Host R) : H.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact H.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := H.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

end GlobalTheory.CuspCharLattice
