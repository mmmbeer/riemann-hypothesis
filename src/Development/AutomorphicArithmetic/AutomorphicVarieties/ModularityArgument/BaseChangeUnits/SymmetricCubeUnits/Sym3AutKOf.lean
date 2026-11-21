import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Base

namespace UpperTheory.V.Z.Bc

def AdAutK : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IsAutR ι ρ → IrrOpen ρ → IsAutQ ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹)

def Sym3AutK : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IsAutR ι ρ → IrrOpen ρ → IsIrr (sym3 ρ) → IsAutQ ι (sym3 ρ)

def UpAll : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutR ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))




structure HypothesesZ : Prop where
  af : Af.Hypotheses₂
  eg : PropEG
  up : UpSol

end UpperTheory.V.Z.Bc
