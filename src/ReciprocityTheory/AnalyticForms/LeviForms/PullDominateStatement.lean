import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def PullPshStatement : Prop :=
  ∀ {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h) (P : LocPot X) (U : Set X)
    (f : X → ℝ), IsOpen U → IsPotential A P →
      (A.SmoothOn U f → A'.SmoothOn (h ⁻¹' U) (f ∘ h)) ∧
      (IsPsh A P → IsPsh A' (P.pullback h hh.1)) ∧
      (A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) →
        IsPshOn A' (h ⁻¹' U) (P.pullback h hh.1 + LocPot.ofFun (f ∘ h)))

def PullDominateStatement : Prop :=
  ∀ {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X']
    [T2Space X'] (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (Θ : LocPot X) (Θ' : LocPot X'), IsPotential A Θ → IsPotential A' Θ' → IsPosPot A' Θ' →
      ∃ K : ℝ, 0 ≤ K ∧ IsPsh A' (Θ'.rsmul K + (Θ.pullback h hh.1).rsmul (-1))

end

end ReciprocityTheory.AnForm.P
