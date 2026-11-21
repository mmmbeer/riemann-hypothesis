import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.SizeWindowBrackets.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes NumberField

def QDGood (eps C x : ℝ) (q d : ℕ) : Prop :=
  ∃ (_ : Fact q.Prime) (_ : Fact d.Prime), Formalism.LFunctionChainParameters.LBr2.PrimePairBounds eps C x q d

def QDExists (eps C x : ℝ) : Prop := ∃ q : ℕ, ∃ d : ℕ, QDGood eps C x q d

open Classical in

def qSel (eps C x : ℝ) : ℕ :=
  if h : ∃ q : ℕ, ∃ d : ℕ, QDGood eps C x q d then Nat.find h else 0

open Classical in

def dSel (eps C x : ℝ) : ℕ :=
  if h : ∃ d : ℕ, QDGood eps C x (qSel eps C x) d then Nat.find h else 0

def QDTied (D : D7) (x eps C : ℝ) : Prop :=
  D.host.q = qSel eps C x ∧ D.host.d = dSel eps C x

def TwBox (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps x : ℝ) (q d : ℕ) : Prop :=
  ∀ θ ∈ Θ, GoodAll (8 * (B : ℝ) * X1 x eps) (fun a => θ a * psDir q a) (8 * B * q * d) ∧
    GoodAll (8 * (B : ℝ) * X1 x eps * X2 x eps) (fun a => θ a * chDir d a) (8 * B * q * d) ∧
    GoodAll (8 * (B : ℝ) * X1 x eps * X2 x eps) (fun a => θ a * chDir d a * psDir q a) (8 * B * q * d)

def QDGoodH (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps C x : ℝ) (q d : ℕ) : Prop :=
  QDGood eps C x q d ∧ TwBox B Θ eps x q d ∧ Nat.Coprime B (q * d) ∧
    ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ B → jacobiSym (-(d : ℤ)) l = 1

open Classical in

def qSelH (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps C x : ℝ) : ℕ :=
  if h : ∃ q : ℕ, ∃ d : ℕ, QDGoodH B Θ eps C x q d then Nat.find h else 0

open Classical in

def dSelH (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps C x : ℝ) : ℕ :=
  if h : ∃ d : ℕ, QDGoodH B Θ eps C x (qSelH B Θ eps C x) d then Nat.find h else 0

def Yg (D : D7) (x eps : ℝ) : ℝ := ((D.R.k : ℝ) * Real.exp (x ^ eps)) ^ 8

def GPair (D : D7) (x eps : ℝ) (g1 g2 : ℕ) : Prop :=
  g1.Prime ∧ g2.Prime ∧ g1 ≠ g2 ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOne D.host.d (NE D) g1 ∧ Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOne D.host.d (NE D) g2 ∧
    Yg D x eps ≤ (g1 : ℝ) ∧ (g1 : ℝ) ≤ 2 * Yg D x eps ∧ Yg D x eps ≤ (g2 : ℝ) ∧ (g2 : ℝ) ≤ 2 * Yg D x eps ∧
    Disjoint (BB D.R.r g1) (BB D.R.r g2)

open Classical in

def chosenFirstPrime (D : D7) (x eps : ℝ) : ℕ :=
  if h : ∃ g1 : ℕ, ∃ g2 : ℕ, GPair D x eps g1 g2 then Nat.find h else 0

open Classical in

def chosenSecondPrime (D : D7) (x eps : ℝ) : ℕ :=
  if h : ∃ g2 : ℕ, GPair D x eps (chosenFirstPrime D x eps) g2 then Nat.find h else 0

def TGood (D : D7) (u : D.what₂.Word) (T : ℕ) : Prop :=
  T.Prime ∧ Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOne D.host.d (NE D * (D.host.g 0 * D.host.g 1) ^ 2) T ∧
    (D.mem u).A.Tstar ≤ (T : ℝ) ∧ (T : ℝ) ≤ (D.mem u).A.Tstar * (1 + 1 / ((D.R.f : ℝ) * D.R.k))

open Classical in

def TSel (D : D7) (u : D.what₂.Word) : ℕ := if h : ∃ T : ℕ, TGood D u T then Nat.find h else 0

def HostT (D : D7) : Prop := Nonempty (Formalism.L2.Host.HostTied D)

def CycSplit : Prop :=
  ∀ (N p : ℕ) (K : Type) [Field K] [NumberField K] [Algebra K (CyclotomicField N ℚ)], 0 < N → p.Prime →
    p % N = 1 % N →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K

def LinkPointsLemma : Prop :=
  ∀ C0 Cr cr cQ cQ' : ℝ, 0 < C0 → 0 < Cr → 0 < cr → 0 < cQ → 0 < cQ' →
    ∃ C0' c1 c2 : ℝ, 0 < C0' ∧ 0 < c1 ∧ 0 < c2 ∧ ∀ (D : D7) (cT : ℝ),
      HostT D → adm8 D C0 Cr cr cQ cT → PointsLemma D cQ' C0' Cr cr c1 c2

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end
