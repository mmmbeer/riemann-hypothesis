import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

noncomputable section

open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.CoVD

abbrev E : Type := Fin 2 → ℝ

def mk (a b : E) : M22 := fun i => ![a i, b i]

def hOf (κ : M22) (v t : ℝ) : M22 := Matrix.of.symm (Matrix.of κ * !![0, v; 1, t])

def xOf (v t : ℝ) : E := ![-t / v, 1 / v]

def covMap (w : M22 × ℝ × E) : ℝ × (M22 × E) :=
  (w.2.2 0 - w.2.1, hOf w.1 w.2.1 (w.2.2 1), xOf w.2.1 (w.2.2 1))

end GlobalTheory.CompanionTheory.CoVD

noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C
namespace GlobalTheory.CompanionTheory.CoVD

def swapL : M22 →ₗ[ℝ] M22 where
  toFun h := fun i j => h j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.CompanionTheory.CoVD
