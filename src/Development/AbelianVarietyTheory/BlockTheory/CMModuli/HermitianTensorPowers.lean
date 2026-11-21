import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

def factor {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (l z : Fin g → ℂ) : ℂ :=
  c * Complex.exp (Real.pi * herm Hm z l + Real.pi / 2 * herm Hm l l)

lemma herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    herm Hm (z + z') w = herm Hm z w + herm Hm z' w := add_dotProduct _ _ _

lemma herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v w : Fin g → ℂ) :
    herm Hm w v = starRingEnd ℂ (herm Hm v w) := by
  simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : starRingEnd ℂ (Hm a b) = Hm b a := h.apply b a
  rw [this]; ring

def shift {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    (Fin g → ℂ) → ℂ := fun z => Complex.exp (-(k * Real.pi * herm Hm z v)) * θ (z + v)

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
