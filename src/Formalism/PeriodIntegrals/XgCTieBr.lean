import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgTie

section
namespace PI.XgNamed

def BrauerSplit : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] (σ : K →+* ℂ) (z : K),
    IsPrimitiveRoot z (Fintype.card Γ) →
    ∀ (n : ℕ) (ρ : Representation ℂ Γ (Fin n → ℂ)), ρ.IsIrreducible →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K))
        (τb : Representation (AlgebraicClosure K) Γ (Fin m → AlgebraicClosure K)),
        τb.IsIrreducible ∧
        (∀ t, LinearMap.toMatrix' (τb t) = (LinearMap.toMatrix' (τ t)).map (algebraMap K (AlgebraicClosure K))) ∧
        ∀ t, σ (τ.character t) = ρ.character t

end PI.XgNamed
end

section
namespace PI

def XgCTieBr : Prop :=
  PI.XgNamed.BrauerSplit →
  ∀ {X : Formalism.L2.Col.Fields} (Pr : Formalism.L2.Col.Primes X) {m : ℕ} (Ch : Formalism.L2.Col.Chars X Pr m) (r : ℕ)
    [∀ i, Fact (Pr.g i).Prime] (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ)
    (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i)),
    Formalism.L2.Col.XgCTie Pr Ch r σ teich ζ

end PI
end
