import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.LiftWord
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DefsCol

section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def HStrip {n : ℕ} (ν μ : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ m, μ m ≤ ν m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m) ∧ ∑ m, ν m - ∑ m, μ m = (b : ℤ)

def IsPath (n : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (N : ℕ) : Prop :=
  μ 0 = 0 ∧ (∀ i ≤ N, Antitone (μ i)) ∧
    ∀ i < N, if isVec i then HStrip (μ (i + 1)) (μ i) (B i) else HStrip (μ i) (μ (i + 1)) (B i)

def CondC {r K : ℕ} (isVec : ℕ → Bool) (ν : ℕ → Fin r → ℤ) (κ : ℕ → Fin K → ℤ) (i : ℕ) : Prop :=
  ∀ (a : Fin r) (b : Fin K), a.val + 1 = r → b.val = 0 →
    if isVec i then κ (i + 1) b ≤ ν i a else κ i b ≤ ν (i + 1) a

def colHeight {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ μ m).card

variable {ι : Type*}

def ordW (r K : ℕ) (isVec : ι → Bool) (om : ι → ℝ) : ι × Fin (r + K) → ℝ :=
  fun x => if (isVec x.1 = true ↔ r ≤ x.2.val) then om x.1 else 0

def OrdGe {σ R : Type*} [CommRing R] (w : σ → ℝ) (f : MvPolynomial σ R) (o : ℝ) : Prop :=
  ∀ e ∈ f.support, o ≤ Finsupp.weight w e

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def nthElt {n : ℕ} (J : Finset (Fin n)) (a : ℕ) : ℕ := ((J.sort (· ≤ ·)).map Fin.val).getD a n

def SemiStd {n C : ℕ} (T : Fin C → Finset (Fin n)) : Prop :=
  ∀ c c' : Fin C, c.val + 1 = c'.val → ∀ a < (T c').card, nthElt (T c) a ≤ nthElt (T c') a

def initSeg (n h : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < h

def genX (k : Type*) [CommRing k] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  Matrix.of fun a b => X (a, b)

def tabMinors (k : Type*) [CommRing k] {n C : ℕ} (T : Fin C → Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) k :=
  ∏ c, minorF (genX k n) (initSeg n (T c).card) (T c)

def tabDiag {n C : ℕ} (T : Fin C → Finset (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ c, ∑ b ∈ T c, ∑ a : Fin n,
    if a.val = ((T c).filter (· < b)).card then Finsupp.single (a, b) 1 else 0

def LeadingMinors : Prop :=
  ∀ (k : Type) [CommRing k] (n C : ℕ) (T : Fin C → Finset (Fin n)),
    coeff (tabDiag T) (tabMinors k T) = 1 ∧
    (∀ e ∈ (tabMinors k T).support, e ≠ tabDiag T →
      ∃ x : Fin n × Fin n, e x < tabDiag T x ∧
        ∀ y : Fin n × Fin n, (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 < x.2)) → e y = tabDiag T y) ∧
    (∀ T' : Fin C → Finset (Fin n), SemiStd T → SemiStd T' → tabDiag T = tabDiag T' → T = T')

def LemmaA : Prop :=
  ∀ (k : Type) [Field k] (n C : ℕ),
    LinearIndependent k (fun T : {T : Fin C → Finset (Fin n) // SemiStd T} => tabMinors k T.1)

def pathWord {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) : ℕ → Form R n
  | 0 => oneF
  | i + 1 =>
    if colHeight (μ (i + 1)) c = colHeight (μ i) c then pathWord isVec μ c Xr i
    else stepF (isVec i == decide (1 ≤ c)) (pathWord isVec μ c Xr i) (Xr i)

def canIdx {n : ℕ} (μN : Fin n → ℤ) (c : ℤ) : Finset (Fin n) :=
  if 1 ≤ c then univ.filter fun m => m.val < colHeight μN c
  else univ.filter fun m => colHeight μN c ≤ m.val

def psiPath (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ)
    (I : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) R :=
  ∏ᶠ c : ℤ, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)

def IsIndex {n : ℕ} (μN : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  ∀ c : ℤ, (I c).card = if 1 ≤ c then colHeight μN c else n - colHeight μN c

def PsiDegrees : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I →
    (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)).Finite ∧
    ∀ i : ℕ, IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (psiPath R isVec μ N I) (if i < N then B i else 0)

def PathProductLinearIndependent : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (ν : Fin n → ℤ),
    LinearIndependent k
      (fun P : {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = ν ∧ ∀ i, N < i → μ i = 0} =>
        psiPath k isVec P.1 N (canIdx ν))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end
