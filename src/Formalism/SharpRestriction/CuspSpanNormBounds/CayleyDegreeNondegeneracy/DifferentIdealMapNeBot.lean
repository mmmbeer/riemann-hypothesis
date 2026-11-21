import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LretrCancel
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LadjFrame
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LFrame

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

open scoped Classical Pointwise

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Carry

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T' : E}

structure c3eqv_Carry (Λ : Submodule (𝓞 E) S.V) (φ : S.V ≃ₗ[E] S.V) (F₁ F₂ : LFlag S r T') : Prop where
  iso : φ ∈ Formalism.HermitianLatticesTheory.isom S.hT
  lam : ∀ y ∈ Λ, φ y ∈ Λ
  lam' : ∀ y ∈ Λ, φ.symm y ∈ Λ
  X : ∀ x ∈ Xsp F₁, φ x ∈ Xsp F₂
  X' : ∀ x ∈ Xsp F₂, φ.symm x ∈ Xsp F₁
  z : φ F₁.fl.z - F₂.fl.z ∈ Xsp F₂

variable {Λ : Submodule (𝓞 E) S.V} {φ ψ : S.V ≃ₗ[E] S.V} {F₁ F₂ F₃ : LFlag S r T'}

theorem c3eqv_Carry.symm (h : c3eqv_Carry Λ φ F₁ F₂) : c3eqv_Carry Λ φ.symm F₂ F₁ where
  iso := c3eqv_isom_symm h.iso
  lam := h.lam'
  lam' := by simpa using h.lam
  X := h.X'
  X' := by simpa using h.X
  z := by
    have h1 := h.X' _ h.z
    have : φ.symm F₂.fl.z - F₁.fl.z = -(φ.symm (φ F₁.fl.z - F₂.fl.z)) := by simp
    rw [this]
    exact Submodule.neg_mem _ h1

theorem c3eqv_Carry.trans (h : c3eqv_Carry Λ φ F₁ F₂) (h' : c3eqv_Carry Λ ψ F₂ F₃) :
    c3eqv_Carry Λ (φ.trans ψ) F₁ F₃ where
  iso := c3eqv_isom_trans h.iso h'.iso
  lam := fun y hy => h'.lam _ (h.lam y hy)
  lam' := fun y hy => h.lam' _ (h'.lam' y hy)
  X := fun x hx => h'.X _ (h.X x hx)
  X' := fun x hx => h.X' _ (h'.X' x hx)
  z := by
    have h1 := h'.X _ h.z
    have : (φ.trans ψ) F₁.fl.z - F₃.fl.z = ψ (φ F₁.fl.z - F₂.fl.z) + (ψ F₂.fl.z - F₃.fl.z) := by simp
    rw [this]
    exact Submodule.add_mem _ h1 h'.z

variable {T : E} {F : LFlag S r T}

end Carry

section D7

variable (D : D7)

end D7

section Main

variable (D : D7)

end Main

section Step4

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Step4

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

open scoped Classical Pointwise

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}



variable {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

end Gen

section Fin

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Fin

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped ENNReal

section GenG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}


end GenG

section GenG2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}



end GenG2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenericIndexOne (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    La Λ (gS D) (lf D F0) F' ≤ Thp Λ (lf D F0) F'


end Gen

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenericTermDetProductBound (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z : GramM D, RelZ D Z →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → ZEquiv (ZhatL (lf D F0) F') Z →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' Z ∧
    1 ≤ localGramProduct D u u' Z ∧ localGramProduct D u u' Z ≤ HHZ D large₂.sc.b C Z

end Gen

section Det

variable (D : D7) (u : D.what₂.Word)

end Det

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped nonZeroDivisors

theorem one_mem_ideal_zpow_neg {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : I ≠ ⊥) (n : ℕ) : (1 : K) ∈ ((I : FractionalIdeal R⁰ K) ^ (-(n : ℤ))) := by
  have hI0 : (I : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  have h1 : ((I : FractionalIdeal R⁰ K) ^ n) ≤ 1 := pow_le_one' FractionalIdeal.coeIdeal_le_one n
  have h2 : (1 : FractionalIdeal R⁰ K) ≤ ((I : FractionalIdeal R⁰ K) ^ n)⁻¹ := by
    have h3 := FractionalIdeal.inv_anti_mono (pow_ne_zero n hI0) one_ne_zero h1
    rwa [inv_one] at h3
  rw [zpow_neg, zpow_natCast]
  exact h2 (FractionalIdeal.one_mem_one _)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fr

variable (D : D7)

theorem different_ideal_map_ne_bot : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) ≠ ⊥ := by
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
  exact differentIdeal_ne_bot

theorem basis_vector_mem_span {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F0.e a ∈ XS D F0 := by
  refine Submodule.subset_span ⟨a, 1, ?_, by simp⟩
  have h : -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = -(((D.R.rS - (a : ℕ) : ℕ)) : ℤ) := by
    have := a.2
    omega
  rw [h]
  exact one_mem_ideal_zpow_neg _ (different_ideal_map_ne_bot D) _

end Fr

end Formalism.MainNotions.BridgeLemma₂

end
end
