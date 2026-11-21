import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsUnramUnitary (η : kˣ →* ℂˣ) : Prop := IsUnram η ∧ ∀ x, ‖(η x : ℂ)‖ = 1

def omTw {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ η' η : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : Matrix b a k → ℂ := fun x =>
  (η' (Matrix.GeneralLinearGroup.det g) : ℂ) * ((η (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) * om μ g h Φ x

def perp {m : Type} [Fintype m] (ψ : AddChar k Circle) (U₀ : Submodule 𝒪[k] (m → k)) : AddSubgroup (m → k) where
  carrier := {β | ∀ u ∈ U₀, ψ (u ⬝ᵥ β) = 1}
  add_mem' := fun {x y} hx hy u hu => by
    rw [dotProduct_add, AddChar.map_add_eq_mul, hx u hu, hy u hu, one_mul]
  zero_mem' := fun u _ => by simp
  neg_mem' := fun {x} hx u hu => by rw [dotProduct_neg, AddChar.map_neg_eq_inv, hx u hu, inv_one]

def IsReps {V : Type} [AddCommGroup V] (D B : AddSubgroup V) (T : Finset V) : Prop :=
  (∀ t ∈ T, t ∈ D) ∧ ∀ β ∈ D, ∃! t, t ∈ T ∧ β - t ∈ B

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

def IsPosTw (ψ : AddChar k Circle) (η : kˣ →* ℂˣ) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ, IsNEquiv ψ p σ (b φ)) ∧ ∀ (g : GL n k) φ v, b (π g φ) (σ (embX c g) v) =
    (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b φ v

variable [MeasurableSpace k] [BorelSpace k]

def avg (ν : Measure k) (μ η' η : kˣ →* ℂˣ) (p : ℕ) (C : Submodule 𝒪[k] (n' → k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ := fun x =>
  ∫ u in (C : Set (n' → k)), omTw μ η' η (rowE (c + 1) p u) 1 Φ x ∂(Measure.pi fun _ => ν)

omit [MeasurableSpace k] [BorelSpace k] in

theorem omTw_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : omTw μ 1 1 g h Φ = om μ g h Φ := by
  funext x; simp [omTw]

omit [MeasurableSpace k] [BorelSpace k] in

theorem isPosTw_one (ψ : AddChar k Circle) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    IsPosTw ψ 1 p π σ b ↔ IsPos ψ p π σ b := by
  simp [IsPosTw, IsPos]

omit [MeasurableSpace k] [BorelSpace k] in

theorem isUnramUnitary_one : IsUnramUnitary (1 : kˣ →* ℂˣ) := ⟨fun _ _ => rfl, fun _ => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
