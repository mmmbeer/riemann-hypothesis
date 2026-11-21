import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def LemmaBLast.Statement : Prop :=
  ∀ (r a : ℕ), ∃ κ : ℚ,
    (κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) ∧
    ∀ lam : Fin r → ℕ, Antitone lam →
      dividedDifference 1 (r + a)
          (aeval (yRoot 1 r a SmallBlock.last 0) (schur (Fin r) lam) *
            vandermondeOf (yRoot 1 r a SmallBlock.last 0) *
              vandermondeOf (zRoot 1 r a SmallBlock.last 0)) =
        if ∀ i, a ≤ lam i then
          algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
            (C κ * aeval (fun i : Fin (r + a) => C SmallBlock.last.sign * X ((0 : Fin 1), i))
              (schur (Fin (r + a)) (fun i => lam i - a)))
        else 0

namespace VandermondePushforward

def emb (j k : ℕ) : Fin (j + k) → Fin 1 × Fin (k + j) :=
  fun i => (0, Fin.cast (Nat.add_comm j k) i)

end VandermondePushforward

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset FlagEq

noncomputable section

namespace DegreeValueAlt

variable (f : ℕ)

def toReal {N M : ℕ} (h : N = M) : RootRing f N →+* MvPolynomial (Fin f × Fin M) ℝ :=
  (MvPolynomial.map (algebraMap ℚ ℝ)).comp (rename (Prod.map id (Fin.cast h))).toRingHom

abbrev top (j k : ℕ) (τ : Fin f) (i : Fin j) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := X (τ, Fin.castAdd k i)

abbrev bot (j k : ℕ) (τ : Fin f) (i : Fin k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := X (τ, Fin.natAdd j i)

def rectTranspose (a r : ℕ) :
    youngCells (fun _ : Fin a => r) ≃o youngCells (fun _ : Fin r => a) where
  toFun p := ⟨(⟨p.1.2, (YoungDiagramCombinatorics.mem_youngCells _ p.1).1 p.2⟩, (p.1.1 : ℕ)),
    (YoungDiagramCombinatorics.mem_youngCells _ _).2 p.1.1.2⟩
  invFun q := ⟨(⟨q.1.2, (YoungDiagramCombinatorics.mem_youngCells _ q.1).1 q.2⟩, (q.1.1 : ℕ)),
    (YoungDiagramCombinatorics.mem_youngCells _ _).2 q.1.1.2⟩
  left_inv p := rfl
  right_inv q := rfl
  map_rel_iff' := by
    rintro ⟨⟨i, c⟩, hp⟩ ⟨⟨i', c'⟩, hq⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Prod.mk_le_mk, Fin.le_def]
    exact and_comm

end DegreeValueAlt

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset FlagEq DegreeValueAlt

noncomputable section

def SameFactorDegreeClause.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f

end

end GroundTheory.Heights₂.Heights.RestTerms
end
