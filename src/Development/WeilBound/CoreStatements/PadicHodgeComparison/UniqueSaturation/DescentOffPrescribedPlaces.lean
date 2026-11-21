import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescOffT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.D

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def BCAt (π : CuspSub E n) (σ : Submodule ℂ (UA E n → ℂ)) (w : Pl E) : Prop :=
  ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt σ w s ϖ q α → (CG.mk π).HasSat w (GlobalTheory.LGrp.bcParam n α)

def IsExtOf2 (π : CuspSub E n) (w : Pl E) (β : Fin (n / 2) → ℂˣ) : Prop :=
  (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧ (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧
    ∃ α, (CG.mk π).HasSat w (GlobalTheory.LGrp.bcParam n α) ∧ GlobalTheory.LGrp.WeylConjU α β

def InertBC (π : CuspSub E n) : Prop := ∀ w : Pl E, ¬ IsSplitAt w → ∃ α, (CG.mk π).HasSat w (GlobalTheory.LGrp.bcParam n α)

def WDAt (π : CuspSub E n) (Z : Finset (Pl E)) : Prop :=
  ∃ T : Finset (Pl E), Disjoint T Z ∧ (∀ w ∈ T, ¬ IsSplitAt w) ∧
    ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
      (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) ∧
      (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Comp σ w τ) ∧
      (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU σ w) ∧
      (∀ w ∈ T, ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ), IsWitt n w b → IsUnifAt ϖ →
        ∃ β, IsExtOf2 π w β ∧ ExtExp σ w b ϖ β) ∧
      ∀ w, ¬ IsSplitAt w → w ∉ T → BCAt π σ w

def DescentOffPlacesAt (π : CuspSub E n) (Z T₀ : Finset (Pl E)) : Prop :=
  ∃ T : Finset (Pl E), T₀ ⊆ T ∧ Disjoint T Z ∧ (∀ w ∈ T, ¬ IsSplitAt w) ∧
    ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
      (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) ∧
      (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Comp σ w τ) ∧
      (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU σ w) ∧
      ∀ w ∈ T, ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ), IsWitt n w b → IsUnifAt ϖ → ∃ β, IsExtOf2 π w β ∧ ExtExp σ w b ϖ β

def RigidAt (π : CuspSub E n) (T₀ : Finset (Pl E)) : Prop :=
    ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) →
      (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Comp σ w τ) →
    ∀ D : Pre E n, PositivityTheory.Rg.BcB.One.Base σ D → (∀ w, IsSplitAt w → D.SplitAt σ w) → D.ThetaStable →
      (∀ w, ¬ IsSplitAt w → ∃ B, D.Sat w B) →
      (∀ w ∈ T₀, ∀ B, (CG.mk π).HasSat w B → D.Sat w B) →
      ∀ w, ¬ IsSplitAt w → ∀ B, D.Sat w B → (CG.mk π).HasSat w B

def WeakDesc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) →
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) → InertBC π →
  ∀ Z : Finset (Pl E), WDAt π Z

def DescentOffPrescribedPlaces : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) →
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) → InertBC π →
  ∀ Z T₀ : Finset (Pl E), Disjoint T₀ Z → (∀ w ∈ T₀, ¬ IsSplitAt w) →
  DescentOffPlacesAt π Z T₀

def RigidT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) →
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) → InertBC π →
  ∀ Z : Finset (Pl E), ∃ T₀ : Finset (Pl E), Disjoint T₀ Z ∧ (∀ w ∈ T₀, ¬ IsSplitAt w) ∧
    RigidAt π T₀

def WeakDescμ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) →
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) → ∀ μ : Formalism.L2.Host.HChar E,
  Formalism.L2.Host.HChar.ResEta (maximalRealSubfield E) μ → InertBC (π.twist μ⁻¹) →
  ∀ Z : Finset (Pl E), WDAt (π.twist μ⁻¹) Z

def DescOffTμ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) →
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) → ∀ μ : Formalism.L2.Host.HChar E,
  Formalism.L2.Host.HChar.ResEta (maximalRealSubfield E) μ → InertBC (π.twist μ⁻¹) →
  ∀ Z T₀ : Finset (Pl E), Disjoint T₀ Z → (∀ w ∈ T₀, ¬ IsSplitAt w) → DescentOffPlacesAt (π.twist μ⁻¹) Z T₀

def RigidTμ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) →
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) → ∀ μ : Formalism.L2.Host.HChar E,
  Formalism.L2.Host.HChar.ResEta (maximalRealSubfield E) μ → InertBC (π.twist μ⁻¹) →
  ∀ Z : Finset (Pl E), ∃ T₀ : Finset (Pl E), Disjoint T₀ Z ∧ (∀ w ∈ T₀, ¬ IsSplitAt w) ∧ RigidAt (π.twist μ⁻¹) T₀

open PositivityTheory.Rg.Rs

def FrameTyped (D : Pre E n) (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
  ∀ j, ∃ K' ∈ Θ (D.N j), ∃ W' ∈ Ω (D.N j), PositivityTheory.Rg.BcB.SpectralAccumulation.HasType K' W' (D.V j)

def RigidAt2 (π : CuspSub E n) (T₀ : Finset (Pl E)) (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
    ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) →
      (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Comp σ w τ) →
    ∀ D : Pre E n, PositivityTheory.Rg.BcB.One.Base σ D → (∀ w, IsSplitAt w → D.SplitAt σ w) → D.ThetaStable → FrameTyped D Θ Ω →
      (∀ w, ¬ IsSplitAt w → ∃ B, D.Sat w B) →
      (∀ w ∈ T₀, ∀ B, (CG.mk π).HasSat w B → D.Sat w B) →
      ∀ w, ¬ IsSplitAt w → ∀ B, D.Sat w B → (CG.mk π).HasSat w B

def RigidTμ2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) →
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) → ∀ μ : Formalism.L2.Host.HChar E,
  Formalism.L2.Host.HChar.ResEta (maximalRealSubfield E) μ → InertBC (π.twist μ⁻¹) →
  ∀ (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))),
    PositivityTheory.Rg.BcB.SpectralAccumulation.Levels E Θ → PositivityTheory.Rg.BcB.SpectralAccumulation.KTypes E Ω →
  ∀ Z : Finset (Pl E), ∃ T₀ : Finset (Pl E), Disjoint T₀ Z ∧ (∀ w ∈ T₀, ¬ IsSplitAt w) ∧ RigidAt2 (π.twist μ⁻¹) T₀ Θ Ω

end PositivityTheory.AutomorphicGaloisHodgeTate.D

end
