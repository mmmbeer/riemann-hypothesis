import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement

namespace ReciprocityTheory.ChartRestriction.G.AR

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

def mono {n : ℕ} {ι Y : Type*} (s : Fin n → ι → Y → ℂ) (α : Fin n → ℕ) (j : ι) (y : Y) : ℂ :=
  ∏ k, s k j y ^ α k

def lead {n δ : ℕ} {ι Y : Type*} (s : Fin n → ι → Y → ℂ) (w0 : ι → Y → ℂ)
    (t : Fin δ → ι → Y → ℂ) (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) : ι → Y → ℂ :=
  fun j y => ∑ α ∈ multiLt n a0, ∑ k,
    cc α k * mono s α j y * w0 j y ^ (T - ∑ q, α q) * t k j y

def IndependentSectionsUpperCount (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ),
    FlatDatum A C X w0 s De → ∀ (r : ℕ) (f : Fin r → ι → Y → ℂ),
      (∀ q, A.IsSec (X.Fp + X.T • X.L) (f q)) → (∀ q, Bdd A (X.Fp + X.T • X.L) (f q)) →
      (∀ a : Fin r → ℂ, (∀ j y, y ∈ (A.chart j).source → ∑ q, a q * f q j y = 0) → a = 0) →
      r ≤ (A.zeroSet s).ncard * (X.T + 2 * n + 6).choose n

end

end ReciprocityTheory.ChartRestriction.G.AR
