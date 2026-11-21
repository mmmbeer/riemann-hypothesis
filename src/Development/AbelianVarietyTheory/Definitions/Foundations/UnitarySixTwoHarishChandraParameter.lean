import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Finset

namespace GlobalTheory.SignedHC.Model

def grid4 : GridData where
  k := 4
  m := 4
  t := 3
  s := 3
  ga := 9
  v := fun i => if i = 2 then 7 else if i = 3 then 3 else 4 - i
  b := fun l => 6 * l - 5
  e := fun j => 6 * j - 2
  cen := fun i => 56 - 9 * i
  two_le_k := by norm_num
  v_anti := by intro i j _ _ _; split_ifs <;> omega
  b_mono := by intro i j _ _ _; omega






theorem nMinus_parD (G : GridData) (i j : ℕ) : nMinus (G.parD i j) = (G.m - j) / 2 := by
  have : (G.parD i j).filter (fun x => x.2 = false) =
      (range ((G.m - j) / 2)).image fun a => (-(G.b (j + 2 + 2 * a) : ℚ), false) := by
    ext ⟨x, s⟩
    simp only [mem_filter, GridData.mem_parD, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨h | ⟨l, h1, h2, h3, h4⟩ | ⟨l, -, -, -, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩
      · simp at h
      · have h5 : ¬ (l ≤ j + 1 ∨ Even (l - j - 1)) := by simpa using h4.symm
        rw [Nat.even_iff] at h5
        refine ⟨(l - j - 2) / 2, by omega, ?_, rfl⟩
        rw [show j + 2 + 2 * ((l - j - 2) / 2) = l by omega, h3]
      · simp at h
      · simp at h
    · rintro ⟨a, ha, rfl, rfl⟩
      refine ⟨Or.inr (Or.inl ⟨j + 2 + 2 * a, by omega, by omega, rfl, ?_⟩), rfl⟩
      symm; rw [decide_eq_false_iff_not, Nat.even_iff]; omega
  rw [nMinus, this, card_image_of_injOn, card_range]
  intro a ha a' ha' h
  simp only [coe_range, Set.mem_Iio] at ha ha'
  have h1 : G.b (j + 2 + 2 * a) = G.b (j + 2 + 2 * a') := by
    have := congrArg Prod.fst h
    simpa using this
  by_contra hne
  rcases lt_or_gt_of_ne hne with h2 | h2
  · have := G.b_mono (j + 2 + 2 * a) (j + 2 + 2 * a') (by omega) (by omega) (by omega); omega
  · have := G.b_mono (j + 2 + 2 * a') (j + 2 + 2 * a) (by omega) (by omega) (by omega); omega


end GlobalTheory.SignedHC.Model
