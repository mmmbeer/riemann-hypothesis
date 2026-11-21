import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.ConstantCoeffRhoOneCanonMonomial
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.DSInfCharCap

open GroundTheory.Automorphic.HarishChandra Finset

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.CompanionTheory.DS

abbrev Pr (n : ℕ) := Fin n × Fin n

abbrev Coch (n : ℕ) (X : Type) := Finset (Pr n) → X

variable {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

def sgn (S : Finset (Pr n)) (α : Pr n) : ℂ := (-1) ^ (S.filter fun β => toLex β < toLex α).card

def wedge (α : Pr n) : Module.End ℂ (Coch n X) :=
  LinearMap.pi fun S => if α ∈ S then sgn S α • LinearMap.proj (S.erase α) else 0

def contr (α : Pr n) : Module.End ℂ (Coch n X) :=
  LinearMap.pi fun S => if α ∈ S then 0 else sgn S α • LinearMap.proj (insert α S)

def ptw (T : Module.End ℂ X) : Module.End ℂ (Coch n X) := T.compLeft (Finset (Pr n))

def dC (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) : Module.End ℂ (Coch n X) :=
  ∑ α ∈ Φ, wedge α * ptw (x α) -
    ∑ α ∈ Φ, ∑ β ∈ Φ.filter (fun β => α.2 = β.1), wedge α * wedge β * contr (α.1, β.2)

def Supp (c Φ : Finset (Pr n)) (f : Coch n X) : Prop := ∀ S, f S ≠ 0 → c ⊆ S ∧ S ⊆ Φ

def Exact (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) (j : ℕ) (f : Coch n X) : Prop :=
  ∃ η : Coch n X, (∀ S, η S ≠ 0 → S ⊆ Φ ∧ S.card + 1 = j) ∧ dC Φ x η = f

def wtS (S : Finset (Pr n)) : Fin n → ℝ :=
  fun k => ∑ α ∈ S, ((if k = α.1 then 1 else 0) - (if k = α.2 then 1 else 0))

def eOp (φ : U n →ₐ[ℂ] Module.End ℂ X) : Pr n → Module.End ℂ X := fun α => φ (e α)

def IsWt (φ : U n →ₐ[ℂ] Module.End ℂ X) (μ : Fin n → ℝ) (v : X) : Prop :=
  ∀ a, φ (e (a, a)) v = (μ a : ℂ) • v

def twist {m : ℕ} (φ : U n →ₐ[ℂ] Module.End ℂ X) (A : Pr n → Matrix (Fin m) (Fin m) ℂ) :
    Pr n → Module.End ℂ (Fin m → X) := fun α =>
  LinearMap.pi fun i => φ (e α) ∘ₗ LinearMap.proj i - ∑ k, A α i k • LinearMap.proj k

def posAll (n : ℕ) : Finset (Pr n) := univ.filter fun α => α.1 < α.2

def KStab (ε : Fin n → Bool) (φ : U n →ₐ[ℂ] Module.End ℂ X) (S : Submodule ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ v ∈ S, φ (e (a, b)) v ∈ S

def InPosCone (δ : Fin n → ℝ) : Prop :=
  ∃ c : Pr n → ℕ, δ = ∑ α ∈ posAll n, (c α : ℝ) • wtS {α}

section Unitary

open scoped InnerProductSpace

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

def IsStar (ε : Fin n → Bool) (φ : U n →ₐ[ℂ] Module.End ℂ Y) : Prop :=
  ∀ a b, ∀ v w : Y, ⟪φ (e (a, b)) v, w⟫_ℂ = (if ε a = ε b then 1 else -1) * ⟪v, φ (e (b, a)) w⟫_ℂ

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def smV (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  PI.PhMeasCore.smoothVecs (PI.UpqRep.Jm ε) σ

end Unitary

def DSUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ' → PI.UpqRep.IsEquiv ε σ' σ

def KTypePosCone : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
    ∀ (ν : Fin n → ℝ) (S : Submodule ℂ H), PI.UpqRep.IsKTypeOf ε σ ν S → InPosCone (ν - PI.UpqRep.lowK ε lam)

end GlobalTheory.CompanionTheory.DS
