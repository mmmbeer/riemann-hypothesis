import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RW
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.EndoscopicGroupCriteria.UnitaryUp3OfUpAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

namespace UpperTheory.GalN.V

def PropEGN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)

def Wts0 (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ v i, ∀ s ∈ U ⊓ Ine (F := T.F) (T.pl v),
    P.ψ v i s ^ 2 = ((cycBar T.F Ω l s ^ h i : (PadicAlgCl l)ˣ) : PadicAlgCl l)

variable {T} {h : Fin 4 → ℤ} {P : PD T.ι (G T.F Ω) (PadicAlgCl l)}

theorem mkWts (k : Wts0 T h P) (_ : h 1 + 4 ≤ h 0 → haveI := T.nF; Unlinked P.r.toHomUnits) : T.Wts h P := k
theorem mkWts4 (k : Wts0 T (fun i => 2 * D.wts4 i) P) : T.Wts (fun i => 2 * D.wts4 i) P :=
  mkWts k fun hb => absurd hb (by simp [Raw.wts4]; omega)
end

end UpperTheory.GalN.V
