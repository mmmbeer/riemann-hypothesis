import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Complex
open scoped Classical

namespace GlobalTheory.CompanionTheory.OM

abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

abbrev W (κ R : Type) : Type := (κ → R) × (κ → R)

instance invTwoAf : Invertible (2 : Af) := (Invertible.map (algebraMap ℚ Af) (2 : ℚ)).copy 2 (map_ofNat _ 2).symm

def psiR : AddChar ℝ ℂ := Circle.coeHom.compAddChar Real.fourierChar

def Zhat : Set Af := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}

variable {κ : Type} [Fintype κ]

def IsHaarF (μ : @Measure (κ → Af) (borel _)) : Prop :=
  @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ μ {x | ∀ i, x i ∈ Zhat} = 1

def EF {R : Type} [CommRing R] (w w' : W κ R) : R := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def stdD (κ R : Type) [Fintype κ] [CommRing R] : GlobalTheory.WeilM.Darboux (EF (κ := κ) (R := R)) κ where
  e := LinearEquiv.refl R _
  form _ _ := rfl

def ofQ (κ R : Type) [CommRing R] [Algebra ℚ R] : W κ ℚ →+ W κ R where
  toFun w := (fun i => algebraMap ℚ R (w.1 i), fun i => algebraMap ℚ R (w.2 i))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

structure IsCx (J : W κ ℝ →L[ℝ] W κ ℝ) : Prop where
  sq : ∀ u, J (J u) = -u
  keeps : ∀ u v, EF (J u) (J v) = EF u v
  pos : ∀ u, u ≠ 0 → 0 < EF (J u) u

def HJ (J : W κ ℝ →L[ℝ] W κ ℝ) (u v : W κ ℝ) : ℂ := (EF (J u) v : ℝ) + I * (EF u v : ℝ)

def rhoR (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ := GlobalTheory.WeilM.schr psiR w f

def rhoF (ψ : AddChar Af ℂ) (w : W κ Af) (Φ : (κ → Af) → ℂ) : (κ → Af) → ℂ := GlobalTheory.WeilM.schr ψ w Φ

def drho (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ :=
  fun x => 2 * Real.pi * I * ((x ⬝ᵥ w.2 : ℝ) : ℂ) * f x + fderiv ℝ f x w.1

def ann (J : W κ ℝ →L[ℝ] W κ ℝ) (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ :=
  (-1 / 2 : ℂ) • (drho w f + I • drho (J w) f)

structure IsVac (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) : Prop where
  sch : v ∈ GlobalTheory.WeilM.schFun (κ → ℝ)
  killed : ∀ w, ann J w v = 0
  unit : ∫ x, ‖v x‖ ^ 2 = 1

def Theta (f : (κ → ℝ) → ℂ) (Φ : (κ → Af) → ℂ) : ℂ :=
  ∑' ξ : κ → ℚ, f (fun i => (ξ i : ℝ)) * Φ (fun i => algebraMap ℚ Af (ξ i))

def Gth (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) (Φ : (κ → Af) → ℂ) : W κ ℝ → ℂ :=
  fun z => cexp (Real.pi * HJ J z z / 2) * Theta (rhoR z v) Φ

def hat (Γ : AddSubgroup (W κ ℚ)) : AddSubgroup (W κ Af) := (Γ.map (ofQ κ Af)).topologicalClosure

def re (Γ : AddSubgroup (W κ ℚ)) : AddSubgroup (W κ ℝ) := Γ.map (ofQ κ ℝ)

def HasLaw (ψ : AddChar Af ℂ) (L : AddSubgroup (W κ Af)) (α : W κ Af → ℂ) (Φ : (κ → Af) → ℂ) : Prop :=
  ∀ γ ∈ L, rhoF ψ γ Φ = (α γ)⁻¹ • Φ

def conjJ (s : W κ ℝ ≃L[ℝ] W κ ℝ) (J : W κ ℝ →L[ℝ] W κ ℝ) : W κ ℝ →L[ℝ] W κ ℝ :=
  (s : W κ ℝ →L[ℝ] W κ ℝ) ∘L J ∘L (s.symm : W κ ℝ →L[ℝ] W κ ℝ)

def frame {G G' : Type} [Group G] [Group G'] (s : G →* (W κ ℝ ≃L[ℝ] W κ ℝ)) (om : G →* Module.End ℂ ((κ → ℝ) → ℂ))
    (om' : G' →* Module.End ℂ ((κ → Af) → ℂ)) (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) (φ : (κ → Af) → ℂ)
    (g : G) (g' : G') : W κ ℝ → ℂ :=
  Gth (conjJ (s g) J) (om g v) (om' g' φ)

end GlobalTheory.CompanionTheory.OM

end
