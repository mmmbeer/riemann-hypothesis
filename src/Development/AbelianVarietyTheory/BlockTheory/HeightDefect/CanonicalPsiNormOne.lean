import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalPsiTorsionNorm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Can

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def canφ (k : ℕ) : Fin 8 → ((A ⊗ A).left ⟶ A.left) :=
  ![(padd A (fst A A ^ k) (snd A A ^ k)).left, (fst A A ^ k).left, (snd A A ^ k).left, (pzero A (A ⊗ A)).left,
    (padd A (fst A A) (snd A A)).left, (fst A A).left, (snd A A).left, (pzero A (A ⊗ A)).left]

def canε (k : ℕ) : Fin 8 → ℤ := ![1, -1, -1, 1, -(k : ℤ) ^ 2, (k : ℤ) ^ 2, (k : ℤ) ^ 2, -(k : ℤ) ^ 2]

example (k : ℕ) : ∑ i, canε k i = 0 := by simp [canε, Fin.sum_univ_succ]

def IsCanIso (L : LB A.left) (k : ℕ) (u : LB.Gen (LB.LinComb L (canφ A k) (canε k))) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (Out.zero2 A)) (LB.oneGen L)

end Can

section Out

variable {R : Type} [CommRing R] [IsDomain R]

def TauPowCan (D : Out.DegPre R) (k : ℕ) : Prop :=
  (∃ u, IsCanIso D.P.A D.P.L k u) ∧
    ∀ u, IsCanIso D.P.A D.P.L k u → ∀ y y' : D.X,
      LB.Gen.Corr D.P.L _ _ _ _ (Out.GeneratorPullback.powGen D.P.L _ _ (D.tau y y') (k ^ 2))
        (LB.pullGen D.P.L _ _ u (D.pt2 y y'))

end Out

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalPsiTorsionNorm
