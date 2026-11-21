import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Abstract

variable {k Γ I : Type} [Field k] [Group Γ] {a c : ℕ}

abbrev mat (ρ : Γ →* GL (Fin a) k) (g : Γ) : Matrix (Fin a) (Fin a) k := ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)

def word (ρ : Γ →* GL (Fin a) k) (L : List (Γ × k)) : Matrix (Fin a) (Fin a) k :=
  (L.map fun p => mat ρ p.1 - p.2 • (1 : Matrix (Fin a) (Fin a) k)).prod

def Kills (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (χ : I → k) (ω : Fin c → I → k) : Prop :=
  ∀ (σ : Fin c → I) (s : I), word ρ (List.ofFn (fun b => (j (σ b), ω b (σ b))) ++ [(j s, χ s)]) = 0

def TrSum (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (κ : Fin a → I → k) : Prop :=
  ∀ s, trc ρ (j s) = ∑ i, κ i s

theorem word_append (ρ : Γ →* GL (Fin a) k) (L M : List (Γ × k)) : word ρ (L ++ M) = word ρ L * word ρ M := by
  simp [word]

end Abstract

section Limit

variable {k Γ I : Type} [NormedField k] [Group Γ] {a c : ℕ}

structure Near (r : Γ →* GL (Fin a) k) (H : Subgroup Γ) (ε : ℝ) where

  n : ℕ

  c : Fin n → k

  z : Fin n → k

  ρ : Fin n → (H →* GL (Fin a) k)
  le : ∀ (m : ℕ) (g : H), ‖trc r g - ∑ i, c i * z i ^ m * trc (ρ i) g‖ ≤ ε

end Limit

section Weil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def EigZero (x : WD h) (ξ : ↥(Ine (F := E) A) → ℂ) : Prop :=
  ∀ (n : ℕ) (x' : WDRep h (Fin n → ℂ)), WD.mk x' = x → ∀ v, (∀ s, x'.ρ (ineIncl h s) v = ξ s • v) → x'.N v = 0

end Weil

end UpperTheory.Gal.NearKilling
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Weil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure IneRel (x y : WD h) : Prop where
  pol : ∀ s, x.charPol (ineIncl h s) = y.charPol (ineIncl h s)
  eig : ∀ ξ, EigZero y ξ → EigZero x ξ

theorem IneRel.refl (x : WD h) : IneRel x x := ⟨fun _ => rfl, fun _ k => k⟩

end Weil

end UpperTheory.Gal.NearKilling
end
end
