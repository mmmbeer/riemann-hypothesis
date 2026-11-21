import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse

open Real

namespace Formalism.LFunctionChainParameters.LErr7

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr

noncomputable section

def CErr7 (C : Consts) : ℝ := max (C.eDiv + 1) (max (C.eLoss + 2) 3)

def ErrorFormsEventualPowerBound : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ,
    ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
      {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ),
      D.ε = ε → C.cHH = cHH → x₀ ≤ D.x → ErrWindows D C Xpp eK K →
      errorTermWith D C Xpp ≤ D.x ^ (CErr7 C * D.ε) * ErrText D ∧
      ∀ u0, ErrX5at D C Xpp u0 ≤ D.x ^ (CErr7 C * D.ε) * ErrText D

section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def LeadingTermGrowthJointExponentSeven : Prop :=
  LeadingTermTranslateMean (H := H) →
  ∀ {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    MeanBoundWith Dd C Xpp →
    Dd.HidaSetting C → Dd.DIV C → EComp5 Dd C → Dd.HComp C → Count5 Dd C → Dd.Slopes C →
    QuotientSlopeBoundsWith Dd C Xpp → LossBounds Dd C → Dd.SlopeIneq → Dd.HHBound C → Dd.FParams →
    ErrWindows Dd C Xpp eK K → LargeX Dd.x Dd.ε K C.cHH eK →
    Dd.B0 ≤ (2 * (Fintype.card H : ℝ)) * m * Dd.b * Dd.x ^ Dd.ε →
    Dd.Nc ≤ (T2.card : ℝ) * Dd.k * Dd.b * Dd.x ^ Dd.ε
      / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * Dd.x ^ (-Dd.ε))) →
    (∀ τ, Dd.aT τ = a (eT τ)) → (∀ u0 j ρ, Dd.w u0 j ρ = w u0 j (eP ρ)) →
    Dd.gam = Real.eulerMascheroniConstant → Dd.LpL = (ell chC).re →
    (∀ u0, Dd.ASK u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) →
    topExcess D N ell TT a w ≤
      Dd.x ^ (CErr7 C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a

end

end

end Formalism.LFunctionChainParameters.LErr7
