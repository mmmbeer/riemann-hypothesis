import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SuccessiveMinima.StatementMink

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions

def MinkowskiFinGL : Prop :=
  ∀ (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)), Finite G →
    Nat.card G ∣ ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime,
      p ^ (∑ i ∈ Finset.range (n + 1), n / (p ^ i * (p - 1)))

def Transference : Prop :=
  ∀ (r : ℕ) (L Ld : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology L] [IsZLattice ℝ L],
    (∀ x, x ∈ Ld ↔ ∀ y ∈ L, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) →
    ∀ i : ℕ, 1 ≤ i → i ≤ r →
      Formalism.FN.succMinBall L i * Formalism.FN.succMinBall Ld (r + 1 - i) ≤ (r : ℝ)

def Link3 : Prop := ∀ D : D7, Formalism.MainNotions.flipTwoThree.PointsLemma D

def Link3F : Prop := ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), Formalism.MainNotions.flipTwoThree.ConclusionF3 Fm

def ClassCompatibilityOfRowCompatibility : Prop :=
  ∀ D : D7, Formalism.L2.Herm.FullTied D → ∀ u : D.what₂.Word, Formalism.MainNotions.flipTwoThree.ClsTie D u

def Link1F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    Transference → Formalism.MainNotions.flipTwoThree.ConclusionF1 Fm

def Link5F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    Formalism.GradedWeylDivisibility.NablaEqDualWeyl → Formalism.MainNotions.flipTwoThree.ConclusionF5 Fm

def Link6F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    Transference → Formalism.MainNotions.flipTwoThree.ConclusionF6 Fm

def KudlaFamilyOfMinkowskiTransference : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    MinkowskiFinGL → Transference → Formalism.GradedWeylDivisibility.NablaEqDualWeyl → Formalism.MainNotions.flipTwoThree.KudlaFamilyStatement Fm

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
