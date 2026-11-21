import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt

namespace GlobalTheory.Published.Amb

def MixOn {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ) (ι : Type) [Fintype ι]
    (M : HermLB p) (L : ι → HermLB p) : Prop :=
  ∀ (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ →
    ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h →
    ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr

def Heights : Prop := ∀ (k : Type) [CommRing k] (P : Scheme.{0}) [IsIntegral P] (q : P ⟶ Sp k) (N : ℕ),
  IsArithVar q N → GenSmooth q N → ∀ M : HermLB q, ∃ h, M.IsArithHeight h

def Proj : Prop := ∀ (k : Type) [CommRing k] (P Q : Scheme.{0}) [IsIntegral P] [IsIntegral Q] (p : P ⟶ Sp k)
  (q : Q ⟶ Sp k) (N N' : ℕ), IsArithVar p N → GenSmooth p N → IsArithVar q N' → GenSmooth q N' →
    ∀ (F : Q ⟶ P) (hF : F ≫ p = q) (Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ Q) [IsClosedImmersion j] (e : ℕ),
      IsArithVar (j ≫ q) e → topologicalKrullDim (closure ({F (j (genericPoint Y))} : Set P)) = (e + 1 : ℕ) →
      F.residueDegree (j (genericPoint Y)) ≠ 0 → ∀ (M : HermLB p) (h : P → ℝ) (h' : Q → ℝ), M.IsArithHeight h →
        (M.pull F hF).IsArithHeight h' →
          h' (j (genericPoint Y)) = (F.residueDegree (j (genericPoint Y)) : ℝ) * h (F (j (genericPoint Y)))

end GlobalTheory.Published.Amb
