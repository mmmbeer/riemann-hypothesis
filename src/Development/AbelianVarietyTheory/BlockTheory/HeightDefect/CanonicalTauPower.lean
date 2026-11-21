import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalTauPower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

def IsBaseChange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (P' : Out.PolAV (Sp R')) (rig' : LB.Gen (P'.L.pull (eSec P'.A)))
    (P : Out.PolAV (Sp R)) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull φ)) : Prop :=
  IsGrpPullback P'.A P.A (spMap f) φ ∧ w.IsGen ∧
    ∃ he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A,
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) rig'
        (rigPullOf φ (spMap f) he P.L rig)

def IsDiagPull {S : Scheme.{0}} (P : Out.PolAV S) (f : P.A ⟶ P.A) : Prop :=
  ∃ u : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(padd P.A (𝟙 _) f).left, 𝟙 P.A.left, f.left, (toUnit P.A ≫ η[P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (eSec P.A)) (LB.oneGen P.L)

def canφ {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) : Fin 8 → ((P.A ⊗ P.A).left ⟶ P.A.left) :=
  ![(padd P.A (fst P.A P.A) (snd P.A P.A)).left, (fst P.A P.A).left, (snd P.A P.A).left,
    (toUnit (P.A ⊗ P.A) ≫ η[P.A]).left,
    (padd P.A (fst P.A P.A ^ k) (snd P.A P.A ^ k)).left, (fst P.A P.A ^ k : P.A ⊗ P.A ⟶ P.A).left,
    (snd P.A P.A ^ k : P.A ⊗ P.A ⟶ P.A).left, (toUnit (P.A ⊗ P.A) ≫ η[P.A]).left]

def canε (k : ℕ) : Fin 8 → ℤ :=
  ![(k : ℤ) ^ 2, -(k : ℤ) ^ 2, -(k : ℤ) ^ 2, (k : ℤ) ^ 2, -1, 1, 1, -1]

section Data

variable {R : Type} [CommRing R] [IsDomain R]

def TauPowCan (D : Out.DegPre R) (k : ℕ) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (canφ D.P k) (canε k)), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (Out.GeneratorPullback.powGen D.P.L _ _ (D.tau y y') (k ^ 2))
        (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (LB.oneGen D.P.L)

end Data

example (k : ℕ) : ∑ i, canε k i = 0 := by
  simp [canε, Fin.sum_univ_succ]

example (S : Scheme.{0}) : IsDiagPull (Out.Inh.zeroPolAV S) (𝟙 _) :=
  ⟨⟨fun _ => 1⟩, by
    intro i j; erw [Out.Inh.linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one], by
    intro j j' _ _ _; dsimp only [LB.pullGen, LB.oneGen]; repeat erw [map_one]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalTauPower
