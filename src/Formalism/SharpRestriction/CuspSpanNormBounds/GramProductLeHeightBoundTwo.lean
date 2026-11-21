import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InertPrimesSquareNormOfGeneral
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minors

variable {K : Type} [Field K]

theorem sum_castLE {n l : ℕ} (hl : l ≤ n) (g : Fin n → K) (hg : ∀ k : Fin n, l ≤ k.val → g k = 0) :
    ∑ k, g k = ∑ k' : Fin l, g (Fin.castLE hl k') := by
  symm
  rw [show (∑ k' : Fin l, g (Fin.castLE hl k')) = ∑ k ∈ Finset.univ.map (Fin.castLEEmb hl), g k by
    rw [Finset.sum_map]; rfl]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply hg
  by_contra h
  push Not at h
  exact hk (Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem submatrix_triple_mul_of_triangular {n l : ℕ} (hl : l ≤ n) (A Z B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ a b : Fin n, a < b → A a b = 0) (hB : ∀ a b : Fin n, b < a → B a b = 0) :
    (A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_castLE hl]
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    rw [sum_castLE hl]
    intro k hk
    rw [hA _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega)), zero_mul]
  · intro m hm
    rw [hB _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega)), mul_zero]


end Minors

section Class

variable (D : D7) (u u' : D.what₂.Word)




end Class

end Formalism.MainNotions.GramProductBounds

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_prod_max {ι : Type} (s : Finset ι) (f : ι → ℝ) : 1 ≤ ∏ l ∈ s, max 1 (f l) := by
  calc (1 : ℝ) = ∏ _l ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => le_max_left _ _)

theorem le_prod_max {ι : Type} [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∈ s) (f : ι → ℝ) :
    max 1 (f a) ≤ ∏ l ∈ s, max 1 (f l) := by
  rw [← Finset.mul_prod_erase s _ ha]
  exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) (one_le_prod_max _ _)

section Bound

variable (D : D7) (u u' : D.what₂.Word)


theorem one_le_sizeZ (b C : ℝ) (Z : GramM D) : 1 ≤ Cnt.sizeZ D b C Z := by
  unfold Cnt.sizeZ
  calc (1 : ℝ) = ∏ _τ : D.what₂.Tau, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => one_le_prod_max _ _)

end Bound

section Fam

end Fam

end Formalism.MainNotions.GramProductBounds

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Formalism.MainNotions.GramProductBounds

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  unfold Scale.b Scale.L
  have h1 : 1 ≤ s.x ^ s.eps := Real.one_le_rpow (le_of_lt s.one_lt_alt) s.eps_pos.le
  have h2 := Real.add_one_le_exp (s.x ^ s.eps)
  linarith


section Bound

variable (D : D7) (u u' : D.what₂.Word)

def Pt (b C : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))




end Bound

section Fam

def LatticeIdentityGeneric : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F')



end Fam

end Formalism.MainNotions.GramProductBounds

end
end
