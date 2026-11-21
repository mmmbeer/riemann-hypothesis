import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower
open Module TopologicalSpace GlobalTheory.FlagPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts.SphericalEisensteinCover

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]

theorem two_avoid (S H₁ H₂ : Submodule k W) (h₁ : ¬ S ≤ H₁) (h₂ : ¬ S ≤ H₂) :
    ∃ v ∈ S, v ∉ H₁ ∧ v ∉ H₂ := by
  obtain ⟨x, hxS, hx1⟩ := SetLike.not_le_iff_exists.1 h₁
  obtain ⟨y, hyS, hy2⟩ := SetLike.not_le_iff_exists.1 h₂
  by_cases hx2 : x ∈ H₂
  · by_cases hy1 : y ∈ H₁
    · refine ⟨x + y, S.add_mem hxS hyS, fun h => hx1 ?_, fun h => hy2 ?_⟩
      · simpa using H₁.sub_mem h hy1
      · simpa using H₂.sub_mem h hx2
    · exact ⟨y, hyS, hy1, hy2⟩
  · exact ⟨x, hxS, hx1, hx2⟩

variable (k) in

def spanFrom (f : ℕ → W) (N m : ℕ) : Submodule k W := Submodule.span k (f '' {a | m ≤ a ∧ a < N})

theorem spanFrom_update_of_lt (f : ℕ → W) (N m m' : ℕ) (v : W) (h : m < m') :
    spanFrom k (Function.update f m v) N m' = spanFrom k f N m' := by
  unfold spanFrom
  congr 1
  refine Set.image_congr fun a ha => ?_
  rw [Function.update_of_ne]
  exact (lt_of_lt_of_le h ha.1).ne'

theorem spanFrom_update_self (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    spanFrom k (Function.update f m v) N m = spanFrom k f N (m + 1) ⊔ k ∙ v := by
  rw [← spanFrom_update_of_lt (k := k) f N m (m + 1) v (Nat.lt_succ_self m)]
  unfold spanFrom
  have : {a | m ≤ a ∧ a < N} = insert m {a | m + 1 ≤ a ∧ a < N} := by
    ext a; simp only [Set.mem_setOf_eq, Set.mem_insert_iff]; omega
  rw [this, Set.image_insert_eq, Submodule.span_insert, Function.update_self, sup_comm]

theorem spanFrom_ge (f : ℕ → W) (N m : ℕ) (h : N ≤ m) : spanFrom k f N m = ⊥ := by
  unfold spanFrom
  have : {a | m ≤ a ∧ a < N} = ∅ := by ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]; omega
  rw [this, Set.image_empty, Submodule.span_empty]

end GlobalTheory.FlagPts.SphericalEisensteinCover

namespace GlobalTheory.FlagPts.SphericalEisensteinCover

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem mem_spanFrom_update (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    v ∈ spanFrom k (Function.update f m v) N m := by
  rw [spanFrom_update_self f N m v h]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

end GlobalTheory.FlagPts.SphericalEisensteinCover

namespace GlobalTheory.FlagPts

end GlobalTheory.FlagPts
