import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDualBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.W1.Lef

def GermCompat {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) (ψ : Z.functionField → Y.functionField) : Prop :=
  ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
    ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g)

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in

theorem _root_.GlobalTheory.W1.Lef.germCompat_id (Z : Scheme.{0}) [IsIntegral Z] :
    _root_.GlobalTheory.W1.Lef.GermCompat (𝟙 Z) (fun y => y) := by
  intro V hV hV' g
  rfl

abbrev omCx {K : Type} [Field K] [Algebra ℂ K] {ι : Type} [LinearOrder ι] (B : Finset ι → Subalgebra ℂ K) (a : ℕ) :
    Cx ℂ (Finset ι → DR ℂ K) := GlobalTheory.PD.cech fun I => omB ℂ K (B I) a

def mapL (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] :
    DR ℂ K →ₗ[ℂ] DR ℂ L := (mapDR ℂ K L).toLinearMap.restrictScalars ℂ

theorem mapL_apply (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    (ω : DR ℂ K) : mapL K L ω = mapDR ℂ K L ω := rfl

def locTerm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℕ) : ℂ :=
  (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a / (1 - A).det

example (A : Matrix (Fin 0) (Fin 0) ℂ) : locTerm A 0 = 1 := by simp [locTerm]

end GlobalTheory.W1.Lef
