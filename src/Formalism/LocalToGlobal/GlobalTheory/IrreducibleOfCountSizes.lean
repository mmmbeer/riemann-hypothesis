import Formalism.LocalToGlobal.GlobalTheory.FamRows
import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionOfProp25
import Formalism.GL3MeanSquares.HookFormulaTorsion.BoxCountAllStatement
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.MeanSquareWeakOfPrimeNumberTheorem
import Formalism.SizeWindowBrackets.Losses5OfLossHypD
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainAnalyticVariantOfTop
import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied
import Formalism.SizeWindowBrackets.FixedEpsilonConcreteGrowthBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ErrorExponentBelowOnesFalse
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBridge
import Formalism.PadicSubsetSums.CentralIdempotents.StretchedExponentialDominance
import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.MergeGL2b

open Formalism.LFunctionChainParameters Formalism.HermitianLattices Formalism.L2.GlobalTheoryTheory.MergeGL2

def AnalyticEndFinal : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x)

def AnalyticConclusionCompatible : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d

def Chain6AtFinal : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε C₄ x₄ : ℝ, 0 < ε → ε < 1 / 4 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

def AnalyticEndPNT : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x))

def AnalyticPrimeNumberTheoremCompatible : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d)

def Chain6AtPNT : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)))



theorem zeroDensityBox : ZeroDensityInBoxes.ZeroDensityBox := Ext.PrimitiveCharacterCasts.ZD.zero_density_box







theorem final_iff_closed : AnalyticEndFinal ↔ AnalyticEndClosed :=
  ⟨fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ _ hM => h ε A C₄ x₄ hε hε1 hA hC₄ hM⟩,
   fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => h ε A C₄ x₄ hε hε1 hA hC₄ zeroDensityBox hM⟩⟩

theorem finalTied_iff_closedTied : AnalyticConclusionCompatible ↔ AnalyticEndClosedTied :=
  ⟨fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ _ hM => h ε A C₄ x₄ hε hε1 hA hC₄ hM⟩,
   fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => h ε A C₄ x₄ hε hε1 hA hC₄ zeroDensityBox hM⟩⟩

theorem chain6AtFinal_iff_closed : Chain6AtFinal ↔ Chain6AtClosed :=
  ⟨fun ⟨Cord, hC, h⟩ => ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ _ hM =>
      h eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM⟩,
   fun ⟨Cord, hC, h⟩ => ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM =>
      h eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ zeroDensityBox hM⟩⟩

example : AnalyticEndFinal := final_iff_closed.2 analyticEndClosed
example : AnalyticConclusionCompatible := finalTied_iff_closedTied.2 analyticEndClosedTied
example : Chain6AtFinal := chain6AtFinal_iff_closed.2 chain6AtClosed




end Formalism.L2.GlobalTheoryTheory.MergeGL2b
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.MergeGL2c

open Formalism.LFunctionChainParameters Formalism.HermitianLattices Formalism.L2.GlobalTheoryTheory.MergeGL2 Formalism.L2.GlobalTheoryTheory.MergeGL2b

section Part2

open Formalism Formalism.D5 Formalism.HN Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7

end Part2

section Proofs

open Formalism Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6 Formalism.LFunctionChainParameters.LChain7 Formalism.LFunctionChainParameters.LTop7 Formalism.LFunctionChainParameters.LBr2

end Proofs

section Part5

example : PrimeNumberTheoremConsequences.PNTAPRelW := Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak

end Part5

end Formalism.L2.GlobalTheoryTheory.MergeGL2c
end
end

section
open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamColC

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Obj

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

abbrev eF (α : Type) [Fintype α] : α ≃ Fin (Fintype.card α) := Fintype.equivFin α

def rFr {α : Type} [Fintype α] [DecidableEq α] (X : InfinitePlace K → Matrix α α ℂ) :
    InfinitePlace K → Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℂ :=
  fun w => Matrix.reindex (eF α) (eF α) (X w)

def Jg (κ κ₁ : Type) [Fintype κ] [DecidableEq κ] [Fintype κ₁] :
    Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (Fintype.card κ)) ℂ :=
  Matrix.reindex (eF (κ ⊕ κ₁)) (eF κ) (Matrix.fromRows (1 : Matrix κ κ ℂ) (0 : Matrix κ₁ κ ℂ))

def Jo (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ₁] :
    Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (Fintype.card κ₁)) ℂ :=
  Matrix.reindex (eF (κ ⊕ κ₁)) (eF κ₁) (Matrix.fromRows (0 : Matrix κ κ₁ ℂ) (1 : Matrix κ₁ κ₁ ℂ))

def famQC [IsTotallyComplex K] (m : ℕ) (C : ColObj K I) (P : PlDat K I) (R : RowArg C) : LChain6.FamC I m where
  K := K
  Wd := R.Wd
  Dall := Fintype.card (R.κ ⊕ R.κ₁)
  D := Fintype.card R.κ
  D1 := Fintype.card R.κ₁
  V := fun u => (C.M u).V
  r := fun u => Fintype.card (C.M u).ι
  Vf := fun u => (C.Mf u).V
  d := fun u => Fintype.card (C.Mf u).ι
  b' := R.b'.reindex (eF R.κ)
  X' := rFr R.X'
  cc := R.cc
  b := fun u => (C.M u).b.reindex (eF (C.M u).ι)
  X := fun u => rFr (C.M u).X
  M := fun u => (C.M u).L
  N0 := C.Nu
  bf := fun u => (C.Mf u).b.reindex (eF (C.Mf u).ι)
  Xf := fun u => rFr (C.Mf u).X
  Mf := fun u => (C.Mf u).L
  j := C.incl
  σ := C.sgExp
  τ := C.tauExp
  B := R.B
  v := R.v
  Y := fun u => Matrix.reindex (eF (C.M u).ι) (eF (C.M u).ι) (R.Y u)
  Y' := Matrix.reindex (eF R.κ) (eF R.κ) R.Y'
  Pf := MatrixLatticeEstimates.toFin R.Bf
  Vr := MatrixLatticeEstimates.toFinV (fun u => C.Vr u R.v)
  ga := R.γ
  c := fun _ => 1
  Vrow := 1
  U := fun _ => 1
  J := Jg R.κ R.κ₁
  J1 := Jo R.κ R.κ₁
  S := (famC m C P R).S
  gain := (famC m C P R).gain
  Fj := (famC m C P R).Fj
  Ej := (famC m C P R).Ej
  iop := (famC m C P R).iop
  T := C.T
  h := R.h
  lam := C.lamT
  Dstar := C.Dstar
  η0 := R.η0
  η1 := R.η1
  e0 := R.e0

structure RowTr [Fintype I] (C : ColObj K I) (R : RowArg C) (x ε : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ LChain6.E8 x ε
  η1_le : R.η1 ≤ LChain6.E8 x ε
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ LChain6.E8 x ε
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0
  irr : (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

end Obj

section Fam7

variable {H : Type} {W : H → Type}

end Fam7

section Collected

open Formalism.L2.Indef Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.GlobalTheoryTheory.FamRows

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}
  {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}

structure ExtHyp7 [Fintype I] (C : ColObj K I) (L : ColLink C Dc) (S : IndefCols Df Dc Sp N) (X : RowExt C S.D)
    (x ε : ℝ) : Prop where
  block : ∀ u (k : Fin S.D) (j : (C.M u).ι), (X.Bf u * C.Vr u Bs.v0) (Sum.inl k) j =
    ((dualFrame S.XE Bs.v0)⁻¹ * (LinearMap.toMatrix (C.M u).b (Pi.basisFun K (Fin S.D)).dualBasis
      (colB L S u)).map Bs.v0.embedding * (C.M u).X Bs.v0) k j
  γ : ∀ u, 0 < X.γ u
  η0_ge : -1 ≤ X.η0
  η0_le : X.η0 ≤ LChain6.E8 x ε
  η1_le : X.η1 ≤ LChain6.E8 x ε
  exponent_bound_ter : 0 ≤ X.e0
  sqrt_error_le_half : Real.sqrt X.e0 ≤ LChain6.E8 x ε
  inputS : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.InputSG X.Bf X.γ C.Dstar X.η0 X.η1 X.e0
  irr : (1 - LChain6.E7 x ε) * (Fintype.card (Fin S.D ⊕ X.κ₁) : ℝ) ≤ (S.D : ℝ)

end Collected

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Family

section Core

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7 Formalism.L2.GlobalTheoryTheory.MergeGL2 Formalism.L2.GlobalTheoryTheory.MergeGL2c

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Core

end Formalism.L2.GlobalTheoryTheory.FamColC

end
end

section
open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcN

open Formalism Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

def IrrAt {C : ColObj K I} (R : RowArg C) (x ε : ℝ) : Prop :=
  (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

def ShareAt {C : ColObj K I} (R : RowArg C) (εC W₁ W₂ : ℝ) : Prop :=
  (Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (1 + εC) / (1 - εC) * (W₁ + W₂)

def CountAt {C : ColObj K I} (R : RowArg C) (εC W₁ W₂ : ℝ) : Prop :=
  ∃ PP₁ PP₂ D₁ D₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Fintype.card (R.κ ⊕ R.κ₁) : ℝ) - Dstar| ≤ εC * Dstar ∧
    |D₁ - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧ |D₂ - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar) ∧
    (Fintype.card R.κ₁ : ℝ) ≤ D₁ + D₂

end Defs

def NumbersAt (x ε εC C W₁ W₂ : ℝ) : Prop :=
  0 ≤ εC ∧ εC ≤ 1 / 2 ∧ W₁ ≤ x ^ C * Real.exp (-(x ^ (ε / 6))) ∧ W₂ ≤ x ^ C * Real.exp (-(x ^ (ε / 6)))

def IrreducibleOfShare : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
    (x ε εC W₁ W₂ : ℝ),
    ShareAt R εC W₁ W₂ → (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ LChain6.E7 x ε → IrrAt R x ε

def ShareFromCountRows : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount →
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
    (εC W₁ W₂ : ℝ), CountAt R εC W₁ W₂ → ShareAt R εC W₁ W₂

def NumbersDominantLarge : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop, ∀ εC W₁ W₂ : ℝ,
    NumbersAt x ε εC C W₁ W₂ → (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ LChain6.E7 x ε

def IrreducibleOfCount : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ C0 ε : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
      (εC W₁ W₂ : ℝ), CountAt R εC W₁ W₂ → NumbersAt x ε εC C0 W₁ W₂ → IrrAt R x ε

def Wg (f m N g q₁ d : ℕ) : ℝ :=
  3 * (f : ℝ) / (g : ℝ) +
    23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) +
    2 * (f : ℝ) * (m : ℝ) * (1 / (4 * ((min q₁ d : ℕ) : ℝ)) + (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) +
    (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f +
    Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ)))

def epsC (c : ℝ) (N f : ℕ) : ℝ := Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ)))

def SizesAt (x ε Cs : ℝ) (f m N g q₁ d : ℕ) : Prop :=
  Real.exp (8 * x ^ ε) ≤ (g : ℝ) ∧ x ^ 2 ≤ (f : ℝ) ∧ (f : ℝ) ≤ x ^ Cs ∧ (m : ℝ) ≤ x ^ Cs ∧
    100 ≤ N ∧ (N : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (ε / 6)) ≤ ((min q₁ d : ℕ) : ℝ)

def WeightNumbersBound : Prop :=
  ∀ ε Cs : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in Filter.atTop, ∀ f m N g q₁ d : ℕ,
    SizesAt x ε Cs f m N g q₁ d → Wg f m N g q₁ d ≤ x ^ (3 * Cs + 3) * Real.exp (-(x ^ (ε / 6)))

def EpsilonBoundLargeX : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in Filter.atTop, ∀ N f : ℕ, 100 ≤ N → x ^ 2 ≤ (f : ℝ) → epsC c N f ≤ 1 / 2

def IrreducibleOfCountSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ ε Cs c : ℝ, 0 < ε → ε ≤ 1 → 0 < c → ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
      (f m N g₁ g₂ q₁ d : ℕ), SizesAt x ε Cs f m N g₁ q₁ d → SizesAt x ε Cs f m N g₂ q₁ d →
      CountAt R (epsC c N f) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d) → IrrAt R x ε

def CountBoundForCompatibleRows {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {C : ColObj K I} (R : RowArg C)
    {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = Fintype.card (R.κ ⊕ R.κ₁) ∧
  Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = Fintype.card R.κ₁ ∧
  ∃ PP₁ PP₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar)

def CompatibleCountArithmetic : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion →
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
    (k : Type) [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ), CountBoundForCompatibleRows R HH e₁ e₂ εC W₁ W₂ → CountAt R εC W₁ W₂

def IrreducibleOfCompatibleSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ ε Cs c : ℝ, 0 < ε → ε ≤ 1 → 0 < c → ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
      (k : Type) [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
      (e₁ e₂ : HH →ₗ[k] HH) (f m N g₁ g₂ q₁ d : ℕ),
      SizesAt x ε Cs f m N g₁ q₁ d → SizesAt x ε Cs f m N g₂ q₁ d →
      CountBoundForCompatibleRows R HH e₁ e₂ (epsC c N f) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d) → IrrAt R x ε

section Rec

open Formalism.BasicNotions Formalism.MainNotions

def CountBoundForCompatibleRowsRecursive (D : D7) {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH]
    [FiniteDimensional k HH] (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = D.what₂.Dall ∧
  D.what₂.Drows + Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = D.what₂.Dall ∧
  ∃ PP₁ PP₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar)

def SizesRec (D : D7) (x ε Cs : ℝ) : Prop :=
  ∀ j : Fin 2, SizesAt x ε Cs D.R.f D.R.m D.R.r (D.host.g j) D.host.q D.host.d

def IrreducibleOfCompatibleForms : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps) (k : Type) [Field k]
    (HH : ∀ x, Fm.Ix x → Type) [∀ x i, AddCommGroup (HH x i)] [∀ x i, Module k (HH x i)]
    [∀ x i, FiniteDimensional k (HH x i)] (e₁ e₂ : ∀ x i, HH x i →ₗ[k] HH x i),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SizesRec (Fm.D x i) x Fm.ez Cs ∧
      CountBoundForCompatibleRowsRecursive (Fm.D x i) (HH x i) (e₁ x i) (e₂ x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f)
        (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d)
        (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x i).host.d)) →
    LinkIRR Fm

end Rec

section Inputs

open Formalism.BasicNotions Formalism.MainNotions

def AllRowsRec (D : D7) {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH]
    [FiniteDimensional k HH] (e₁ e₂ : HH →ₗ[k] HH) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = D.what₂.Dall ∧
  D.what₂.Drows + Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = D.what₂.Dall

def CountRec {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC : ℝ) (PP : Fin 2 → ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ ∃ Dstar : ℝ, 0 < Dstar ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP 0 * Dstar| ≤ εC * (PP 0 * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP 1 * Dstar| ≤ εC * (PP 1 * Dstar)

def WeightRec (D : D7) (PP : Fin 2 → ℝ) : Prop :=
  ∀ j : Fin 2, 0 ≤ PP j ∧ PP j ≤ Wg D.R.f D.R.m D.R.r (D.host.g j) D.host.q D.host.d

def LinkIrreducibleInputs : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps) (k : Type) [Field k]
    (HH : ∀ x, Fm.Ix x → Type) [∀ x i, AddCommGroup (HH x i)] [∀ x i, Module k (HH x i)]
    [∀ x i, FiniteDimensional k (HH x i)] (e₁ e₂ : ∀ x i, HH x i →ₗ[k] HH x i) (PP : ∀ x, Fm.Ix x → Fin 2 → ℝ),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      AllRowsRec (Fm.D x i) (HH x i) (e₁ x i) (e₂ x i) ∧
      CountRec (HH x i) (e₁ x i) (e₂ x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) (PP x i) ∧
      WeightRec (Fm.D x i) (PP x i) ∧
      SizesRec (Fm.D x i) x Fm.ez Cs) →
    LinkIRR Fm

end Inputs

section AllRowsIn

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

def DstarE {D : D7} (A : AllRows D) (e : A.B.I.Gf → ℂ) : ℝ :=
  A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund e

def CountAllRows {D : D7} (A : AllRows D) (εC : ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ 0 < DstarE A A.B.e ∧
    ∀ (k : Fin 2) (S : Set (Tup D k)),
      |(A.dimT (cyl D k S) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤ εC * DstarE A (A.eT (cyl D k S))

def WeightAllRows {D : D7} (A : AllRows D) : Prop :=
  (∀ (k : Fin 2) v f, 0 ≤ wtOf D k (A.eVec k v) f) ∧
    ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) →
      locShare D A.eVec k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d

def FamilyIrreducibleOfCountWeightSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧
      CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
      WeightAllRows A ∧
      SizesRec (Fm.D x i) x Fm.ez Cs) →
    LinkIRR Fm

end AllRowsIn

end Formalism.L2.GlobalTheoryTheory.ConcN
end
end
