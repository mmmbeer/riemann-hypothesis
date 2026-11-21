import Formalism.PieriBlockIdeals.Statement
import Formalism.PieriBlockIdeals.BranchingBoundLastGradedOneRow

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.UnitNormBounds

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

def U (k j t : ℕ) (lam : Fin (k + j) → ℕ) (a : Fin (k + j)) : ℤ :=
  (lam a : ℤ) + ((k : ℤ) + (j : ℤ) + (t : ℤ) - 1 - (a.val : ℤ))

def maxB (t w : ℕ) : ℤ := (w : ℤ) + (t : ℤ) - 1

def dual {r : ℕ} (M : ℕ) (lam : Fin r → ℕ) : Fin r → ℕ := fun b => M - lam (Fin.rev b)

def label (k j t M : ℕ) (lam : Fin (k + j) → ℕ) (b : Fin (k + j)) (col : ℕ) : ℤ :=
  U k j t lam (Fin.rev b) - ((col : ℤ) - (dual M lam b : ℤ) + 1)

def cont (t w M : ℕ) (ct : ℤ) : ℤ := ((M - w : ℕ) : ℤ) - (ct - maxB t w)

structure Rows (k j t w M : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) : Prop where
  low : ∀ a, w ≤ lam a
  high : ∀ a, lam a ≤ M
  cloud : ∀ a : Fin (k + j), a.val < k → xm ≤ U k j t lam a ∧ U k j t lam a ≤ xp
  rest : ∀ a : Fin (k + j), k ≤ a.val → U k j t lam a < xm
  above : maxB t w < xm
  le : xm ≤ xp

def GoodLabels : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ), (∀ a, w ≤ lam a ∧ lam a ≤ M) →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ (b : Fin (k + j)) (col : ℕ), dual M lam b ≤ col → col < tau b →
      maxB t w < label k j t M lam b col ∧ label k j t M lam b col ≤ U k j t lam (Fin.rev b) - 1

def boxesOfLabel (t w M : ℕ) {r : ℕ} (lam tau : Fin r → ℕ) (ct : ℤ) : ℕ :=
  boxesOfContent (dual M lam) tau (cont t w M ct)

def cloudBoxes (k j t w M : ℕ) (lam tau : Fin (k + j) → ℕ) (ct : ℤ) : ℕ :=
  (Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧
    ((dual M lam b : ℤ) ≤ cont t w M ct + (b.val : ℤ) ∧ cont t w M ct + (b.val : ℤ) < (tau b : ℤ))).card

def CountsRows : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ,
      boxesOfLabel t w M lam tau ct ≤ (if ct < xm then j else 0) + cloudBoxes k j t w M lam tau ct

def CountsCloud : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ),
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ,
      cloudBoxes k j t w M lam tau ct ≤ k ∧ cloudBoxes k j t w M lam tau ct ≤ t

def CountsDeep : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ, ct < xm →
      (cloudBoxes k j t w M lam tau ct : ℤ) * (xm - ct) ≤ (i : ℤ)

def MuBound : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp → ∀ ct : ℤ,
    (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) ≤
      (if ct < xm then (j : ℝ) else 0) +
        min (min (k : ℝ) (t : ℝ)) (if ct < xm then (i : ℝ) / ((xm - ct : ℤ) : ℝ) else (k : ℝ))

def DnValSum : Prop :=
  ∀ (l k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    padicValInt l (Dn t (M - w) i (dual M lam)) =
      ∑ ct ∈ Finset.Ioo (maxB t w) xp, mu t (M - w) i (dual M lam) (cont t w M ct) * vl l (ct - maxB t w)

def FactorialValuationSum : Prop :=
  ∀ (l : ℕ) (xm mB : ℤ), l.Prime → mB < xm →
    ∑ ct ∈ Finset.Ioo mB xm, vl l (ct - mB) = padicValNat l ((xm - mB - 1).toNat).factorial ∧
      (padicValNat l ((xm - mB - 1).toNat).factorial : ℝ) ≤ (((xm - mB : ℤ) : ℝ) - 1) / ((l : ℝ) - 1)

def harm (l h : ℕ) (i : ℝ) : ℝ :=
  if h < l then 0 else (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ)))

def labelSumBoundPos (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
    harm l h i

def HarmPosLog : Prop :=
  ∀ (l h : ℕ) (i : ℝ), 0 ≤ i →
    harm l h i ≤ (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))) ∧
      (1 ≤ l → l ≤ h → harm l h i = (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))))

def LabelSumPlus : Prop :=
  ∀ (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ), l.Prime → 0 ≤ i → mB < xm → xm ≤ xp →
    xp - mB ≤ (h : ℤ) → h < l ^ 2 →
    labelLHS l k t i xm xp mB ≤ labelSumBoundPos l k t h i xm xp mB

def Step2Val : Prop :=
  ∀ (l k j t w M h i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 →
    (padicValInt l (Dn t (M - w) i (dual M lam)) : ℝ) ≤
      (j : ℝ) * ((((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1)) +
        labelSumBoundPos l k t h (i : ℝ) xm xp (maxB t w)

def Step2ValUpTo : Prop :=
  ∀ (l k j t w M h i : ℕ) (I : ℝ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 → (i : ℝ) ≤ I →
    (padicValInt l (Dn t (M - w) i (dual M lam)) : ℝ) ≤
      (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + labelSumBoundPos l k t h I xm xp (maxB t w)

def cPrime (l k j t q h ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + (ecl : ℝ) + labelSumBoundPos l k t h I xm xp mB

def cCoarse (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6) + (ecl : ℝ) +
    (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (I / (d0 l (xm - mB) : ℝ)) else 0) +
    (I / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ)))

def CPrimeLeCoarse : Prop :=
  ∀ (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ), 2 ≤ l → 0 ≤ I →
    cPrime l k j t q h ecl xm xp mB I ≤ cCoarse l k j t q h N' ecl xm xp mB I

def UN (N : ℕ) (lam : ℕ → ℕ) (a : ℕ) : ℤ := (lam a : ℤ) + (N : ℤ) - 1 - (a : ℤ)

inductive Filtered {C : Type 1} [Category.{0} C] [HasZeroMorphisms C] (P : C → Prop) : C → Prop
  | zero (Y : C) : IsZero Y → Filtered P Y
  | step (S : ShortComplex C) : S.ShortExact → Filtered P S.X₁ → P S.X₃ → Filtered P S.X₂

def chainMap {C : Type 1} [Category.{0} C] (A : ℕ → C) (inc : ∀ r, A r ⟶ A (r + 1)) : ∀ n, A 0 ⟶ A n
  | 0 => 𝟙 (A 0)
  | n + 1 => chainMap A inc n ≫ inc n

end Formalism.CohomologicalDescent.UnitNormBounds
