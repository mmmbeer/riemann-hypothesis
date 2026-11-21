import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

section
noncomputable section

namespace PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def HasWallD (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) (D : ℂ → ℂ) : Prop :=
  ∃ R Op H, Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H

def HasWallU (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) (D : ℂ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ, StripEntire M ∧ (∀ z, M z ≠ 0) ∧ HasWallD Γ K P P' c η η' β ρ fun z => M z * D z

def Triv (K₀ : Subgroup G) {K : Subgroup G} (ρ : K →* (W →L[ℂ] W)) : Prop := ∀ k : K, (k : G) ∈ K₀ → ρ k = 1

def AllRepT (K K₀ : Subgroup G) (Q : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W], (K →* (W →L[ℂ] W)) → Prop) :
    Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (ρ : K →* (W →L[ℂ] W)), Continuous ρ →
    Triv K₀ ρ → Q ρ

end PositivityTheory.RgEis
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgEis

variable {E R : Type} [Field E] [CommRing R]

namespace Ad

variable (A : Ad E R)

structure IsIdem (e : R) : Prop where
  sq : e * e = e
  σ : A.σ e = e
  O : e ∈ A.O
  φ : ∀ w, A.φ w e = 1

def k0GL (e : R) (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (GL ι R) where
  carrier := {k | k ∈ A.kGL ι ∧ e • (k : Matrix ι ι R) = e • 1 ∧ e • ((k⁻¹ : GL ι R) : Matrix ι ι R) = e • 1}
  one_mem' := ⟨one_mem _, by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [Units.val_mul, ← smul_mul_assoc, ha.2.1, smul_mul_assoc,
      Matrix.one_mul, hb.2.1], by rw [_root_.mul_inv_rev, Units.val_mul, ← smul_mul_assoc, hb.2.2, smul_mul_assoc,
      Matrix.one_mul, ha.2.2]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

def unitaryIntegralLevel (e : R) (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (A.U ε ι) := (A.k0GL e (ι ⊕ ι)).subgroupOf _

variable [TopologicalSpace R]

def MirGLU (e : R) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι), 2 ≤ Fintype.card ι → ∃ D : ℂ → ℂ,
    AllRepT (A.kGL ι) (A.k0GL e ι) fun ρ => HasWallU (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (stab R {i₀}) 1
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) ρ D

end Ad

open Classical in

def LeviQU : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (s : Set ι) (e : R), A.IsIdem e →
  Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) →
  ∃ (π : A.uQ ε s →* A.U ε (sᶜ : Set ι)) (j : A.U ε (sᶜ : Set ι) →* A.uQ ε s) (c₀ : A.U ε ι → ℂ),
    IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uΓ ε _) (A.uK ε _) π j c₀ ∧
    IsPull (A.uQ ε s) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε Set.univ) π c₀ (A.uC ε ι) (A.uC ε _) ∧
    Iwa (A.uQ ε (Set.univ : Set (sᶜ : Set ι))) (A.uK ε _) ∧
    PullHt (A.uK ε ι) (A.uQ ε s) π (fun g => A.uH ε Set.univ g - A.uH ε s g) (A.uH ε Set.univ) ∧
    ∀ m ∈ A.unitaryIntegralLevel e ε (sᶜ : Set ι), ((j m : A.uQ ε s) : A.U ε ι) ∈ A.unitaryIntegralLevel e ε ι

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

def eSF {F : Type} [Field F] [NumberField F] (S : Finset (Pl F)) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) 1 + LinearMap.inr F (Ainf F) (Af F) (∑ v ∈ S, singleFin v 1)

end PositivityTheory.RgEis
end
end
