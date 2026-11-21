import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnTwoPowMul
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.DedekindResidueLeOfAdmitted
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDAll
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurablePsi

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cn_isNear (X : CData) (εN : ℝ) (x : X.I.GA) (γ : X.I.GFset) : Prop :=
  (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0

def CSize.NearLayers {X : CData} (S : CSize X) (εN δ : ℝ) : Prop :=
  (∀ x ∈ S.I0, ∀ γ : X.I.GFset, γ ≠ X.one' → (∀ v, X.dist x γ v ≤ εN) → X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0) ∧
    ∀ (J : ℕ) (c : Composition J), ∀ x ∈ S.str J c, S.tau J c x ∈ cn_Reg c.length ∧
      ∃ (e : Fin (Fintype.card (cn_Root c.length)) ≃ cn_Root c.length) (β : ℕ → Type) (π : ∀ i, X.I.GFset → β i),
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' → π 0 γ = π 0 γ') ∧
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' →
          π (Fintype.card (cn_Root c.length)) γ = π (Fintype.card (cn_Root c.length)) γ' → γ = γ') ∧
        ∀ (i : Fin (Fintype.card (cn_Root c.length))) (T : Finset X.I.GFset), (∀ γ ∈ T, cn_isNear X εN x γ) →
          (∀ y ∈ T, ∀ z ∈ T, π i y = π i z) → (∀ y ∈ T, ∀ z ∈ T, π (i + 1) y = π (i + 1) z → y = z) →
          ∃ laM : ℝ, cn_la (S.tau J c x) (e i) / 2 ≤ laM ∧
            (T.card : ℝ) ≤ (1 + 2 * (∏ _v : InfinitePlace X.I.F, 3 * δ) ^ (1 / (Fintype.card (InfinitePlace X.I.F) : ℝ)) / laM) ^
              (cn_dim c.blocksFun (X.I.n - 2 * J) (e i) * Fintype.card (InfinitePlace X.I.F))


end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cn_eps (X : CData) (cε : ℝ) : ℝ := Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f

def GeoS (X : CData) (cε Cv Cd Cq : ℝ) : Prop :=
  ∃ (S : CSize X) (volK : ℝ), S.Strata ∧ S.Density ∧ S.KappaVol Cv ∧
    S.NearLayers (cn_eps X cε) (3 * Real.sqrt ((X.I.n : ℝ) * cn_eps X cε)) ∧ S.SepStep ∧
    (1 ≤ X.qq → S.DeepStepsQ volK Cd Cq)

def GeoC (X : CData) (Cres cε Cv Cd Cq : ℝ) : Prop := cn_ResBound X Cres ∧ GeoS X cε Cv Cd Cq







def StepsG (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.OpExists ∧ X.KernelDiag ∧ X.FinVol ∧ X.LowProj ∧ GeoS X cε Cv Cd Cq

def StepsG'' (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.RegRep ∧ X.KernelDiag ∧ X.FinVol ∧ GeoS X cε Cv Cd Cq


end Formalism.MainNotions.LeviCoordinates

end
end
