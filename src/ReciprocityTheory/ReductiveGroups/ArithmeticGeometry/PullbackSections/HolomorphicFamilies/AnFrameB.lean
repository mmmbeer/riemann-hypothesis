import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (ε : K → ℤ)
  {N : ℕ} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
