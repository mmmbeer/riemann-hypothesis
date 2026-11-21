import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TruncQuotSymmTruncTensor

noncomputable section

open CategoryTheory

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo

abbrev unitE (O : Type) [CommRing O] (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) O :=
  Matrix.single 0 0 1

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {n : ℕ} [NeZero n]

section OneBase

variable {S : Type} [CommRing S] [Algebra O S]

def IsHTType [Algebra ℤ_[p] O] (G : PDivGroup p S) (ι : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G) :
    Prop :=
  G.height = n * n * Module.finrank ℤ_[p] O ∧
    (∀ (a : O) (x : G.Lie), ι.onLie (Matrix.scalar (Fin n) a) x = algebraMap O S a • x) ∧
    Module.Finite S (LinearMap.range (ι.onLie (unitE O n))) ∧
    Module.Projective S (LinearMap.range (ι.onLie (unitE O n))) ∧
    ∀ q : PrimeSpectrum S, Module.rankAtStalk (LinearMap.range (ι.onLie (unitE O n))) q = 1

end OneBase

section TwoBases

variable {S S' : Type} [CommRing S] [CommRing S'] {f : S →+* S'}

variable [Algebra O S] [Algebra O S']

def IsOLinear {H : VarpiDivModule p O S} {H' : VarpiDivModule p O S'} (s : PDivGroup.SemiHom f H'.G H.G) :
    Prop :=
  ∀ (c : O) (m : ℕ) (a : H.G.A m),
    s.app m (PDivGroup.Hom.app (H.ι c) m a) = PDivGroup.Hom.app (H'.ι c) m (s.app m a)

def cornerMap {G : PDivGroup p S} {G' : PDivGroup p S'} {H : VarpiDivModule p O S}
    {H' : VarpiDivModule p O S'} (i' : H'.G ⟶ G') (r : G ⟶ H.G) (t : PDivGroup.SemiHom f G' G) :
    PDivGroup.SemiHom f H'.G H.G :=
  ((PDivGroup.SemiHom.ofHom i').comp t).comp (PDivGroup.SemiHom.ofHom r)

end TwoBases

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo CategoryTheory

section Checks

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] [Module.Free ℤ_[p] O]
  [Module.Finite ℤ_[p] O] {S : Type} [CommRing S]
  [Algebra O S]

theorem unitE_one : unitE O 1 = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [unitE]

end Checks

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo CategoryTheory

section Checks2

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] [Module.Free ℤ_[p] O]
  [Module.Finite ℤ_[p] O] {S : Type} [CommRing S] [Algebra O S]

end Checks2

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

section Checks3

example : Fact (Nat.Prime 2) ∧ Module.Free ℤ_[2] ℤ_[2] ∧ Module.Finite ℤ_[2] ℤ_[2] ∧
    Module.finrank ℤ_[2] ℤ_[2] = 1 ∧ NeZero (2 : ℕ) :=
  ⟨⟨Nat.prime_two⟩, inferInstance, inferInstance, Module.finrank_self _, inferInstance⟩

example : unitE ℤ_[2] 2 ≠ 1 ∧ unitE ℤ_[2] 2 ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrFun (congrFun h 1) 1
    simp [unitE, Matrix.single_apply] at this
  · have := congrFun (congrFun h 0) 0
    simp [unitE] at this

end Checks3

end GlobalTheory.MoritaHT
