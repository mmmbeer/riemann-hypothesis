import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

section
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
namespace PI.GreenHCLabel

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def HCDisjoint : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (lam' : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K)),
    Function.Surjective b → Function.Surjective b' →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) →
    ∀ τ : FDRep ℂ (GL (Fin n) K), Simple τ → IsConstituent τ (hcRep K b lam) → IsConstituent τ (hcRep K b' lam') →
    ∃ (π : Fin s ≃ Fin s') (e : ∀ c, {i // b i = c} ≃ {i // b' i = π c}), ∀ c, Nonempty (transp (e c) (lam c) ≅ lam' (π c))

variable {K}

end PI.GreenHCLabel
end

section
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
open scoped TensorProduct
namespace PI.GreenHCLabel

def SimpleIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrrRep τ.ρ

def ConstSymm : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V), Simple τ → (IsConstituent τ ρ ↔ ∃ ψ ∈ Intw ρ τ.ρ, ψ ≠ 0)

def ProdSimple : Prop :=
  ∀ (s : ℕ) (L : Fin s → Type) [∀ c, Group (L c)] [∀ c, Fintype (L c)] (W : Type) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Nontrivial W] (ρ : Representation ℂ (∀ c, L c) W),
    ∃ (lam : ∀ c, FDRep ℂ (L c)) (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] W), (∀ c, Simple (lam c)) ∧ Φ ≠ 0 ∧
      ∀ g : ∀ c, L c, Φ ∘ₗ PiTensorProduct.map (fun c => (lam c).ρ (g c)) = ρ g ∘ₗ Φ

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def Frob : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (τ : FDRep ℂ (GL ι K)) (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ), Φ ≠ 0 →
    (∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) → ∃ ψ ∈ Intw (hcRep K b lam) τ.ρ, ψ ≠ 0

def HCFin : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    FiniteDimensional ℂ (hcSpace K b lam)

def Jacquet : Prop :=
  ∀ (n : ℕ) (τ : FDRep ℂ (GL (Fin n) K)), Simple τ →
    ∃ (s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
      (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ),
      Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧ Φ ≠ 0 ∧
      ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ

variable {K}


end PI.GreenHCLabel
end
