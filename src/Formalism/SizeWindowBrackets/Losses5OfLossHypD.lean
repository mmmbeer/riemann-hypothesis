import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable

open Module NumberField Matrix IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain7

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6

section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}

abbrev PlAllD (Fm : ∀ u0, Fam (W u0) m) : Type := Σ u0 : H, slopeLatticeData.FinPl (Fm u0).K

def plEmbD (Fm : ∀ u0, Fam (W u0) m) (u0 : H) : slopeLatticeData.FinPl (Fm u0).K ↪ PlAllD Fm :=
  Function.Embedding.sigmaMk (β := fun u0 => slopeLatticeData.FinPl (Fm u0).K) u0

def ldOfD (D : ArithData H) (N : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m) (u0 : H) :
    PrimeWindowSizeBounds.LD (PlAllD Fm) (Fin m) H where
  W := (Fm u0).S.map (plEmbD Fm u0)
  below := fun z => prBelow z.2
  l := fun z => lE z.2
  cl := (Lp u0).cl
  TTp := (Lp u0).TTp
  Iex := fun _ _ p => (Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p))
  at_ := a
  wz := fun j t p i => w u0 j (partner t (i • D.frob p))
  Id := fun _ _ => Finset.Icc 1 N
  wd := fun j t i => w u0 j (partner t (gD D i))
  gainW := fun j z => (Fm z.1).gain j z.2
  tauW := fun z => (Fm z.1).tauR z.2
  gain := (Lp u0).gainP
  tau := (Lp u0).tauP
  lo := (Lp u0).lo
  fl := (Lp u0).fl
  L₁ := (Lp u0).L₁

def LossHypD (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW : ℝ) : Prop :=
  P.x = G.x ∧ P.ε = G.ε ∧ P.k = G.k ∧ P.d = D.d ∧ P.Cord = Cord ∧
  SmallOrderPrimeLosses.WindowsD P eW KW ∧
  SmallOrderPrimeLosses.PrimeClassLossHypotheses P (inertPs D N) cand PR (Finset.univ : Finset (Fin m)) TT BAD Sig
    (fun u0 p => (Fm u0).iop p) (ldOfD D N a w Fm Lp) ∧
  (∀ u0, (∀ p ∈ (Fm u0).Pr, p ∉ cand → (Fm u0).iop p = 0) ∧ ∀ p ∈ cand, 0 ≤ (Fm u0).iop p) ∧
  3 * P.C + 13 ≤ C.cLoss ∧ 0 ≤ C.eLoss

variable [∀ u0, Fintype (W u0)]

def LossesOfD : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW : ℝ),
    LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW → 1 ≤ G.x →
    SmallOrderPrimeLosses.ExcessAndPrimeLogSumUnitBounds P (inertPs D N) cand (Finset.univ : Finset (Fin m)) TT (fun u0 p => (Fm u0).iop p)
      (ldOfD D N a w Fm Lp) →
    LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C

end Loss

def Losses5OfLossHypD : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε eW KW : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₁ : ℝ,
    ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
      (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
      (TT T2 : Finset H) (a : H → ℝ)
      (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
      (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ),
      G.ε = ε → x₁ ≤ G.x → LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW →
      LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C

section Comp
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}

end Comp

section Clr
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}

end Clr

end Formalism.LFunctionChainParameters.LChain7
