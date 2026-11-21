import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CM

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hostChar (H : Host E) : DirichletCharacter ℂ H.d :=
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)

end Period

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter
end
