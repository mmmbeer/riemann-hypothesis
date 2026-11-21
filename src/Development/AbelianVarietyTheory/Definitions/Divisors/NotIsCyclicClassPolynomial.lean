import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HT

section Examples

open Quaternion

instance quaternion_isCentral : Algebra.IsCentral ℝ ℍ[ℝ] := ⟨fun z hz => by
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨i, i1, i2, i3, i4⟩ : ∃ i : ℍ[ℝ], i.re = 0 ∧ i.imI = 1 ∧ i.imJ = 0 ∧ i.imK = 0 :=
    ⟨⟨0, 1, 0, 0⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨j, j1, j2, j3, j4⟩ : ∃ j : ℍ[ℝ], j.re = 0 ∧ j.imI = 0 ∧ j.imJ = 1 ∧ j.imK = 0 :=
    ⟨⟨0, 0, 1, 0⟩, rfl, rfl, rfl, rfl⟩
  have hi := hz i
  have hj := hz j
  rw [Quaternion.ext_iff] at hi hj
  simp [i1, i2, i3, i4, j1, j2, j3, j4] at hi hj
  refine Algebra.mem_bot.2 ⟨z.re, ?_⟩
  ext <;> simp <;> linarith⟩

end Examples

end GlobalTheory.HT
