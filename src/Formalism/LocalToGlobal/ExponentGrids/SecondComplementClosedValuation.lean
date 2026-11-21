import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.SecondComplementColumnExponents
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.CG (HCdeg HCDplus HCDminus)
open Formalism.D5 (PhiSet E0)
open Formalism.LFunctionChainParameters.characterSumData (ArithData)
open Formalism.RankGapBounds.WeightedMeanData (Consts)
open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6
open Formalism.LFunctionChainParameters.LBrDiv (plOf TypePrimeCostDeviationBound)

noncomputable section

namespace Formalism.AtG

section Defs

variable {K : Type} [Field K] [NumberField K] {Pl : Type} [Fintype Pl]

def vNNg (g : ℕ) (p : Pl → K) (ν : Pl → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (∑ ρ, ν ρ * (vw w (p ρ) : ℝ)) / (vw w (g : K) : ℝ)

def EGval (g : ℕ) (p : Pl → K) (ν : Pl → ℝ) (Dpm o : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -(Dpm / 2) + vNNg g p ν w + o

end Defs

structure HarishChandraParameters (Pl : Type) where

  k : ℕ

  t : ℕ

  u : Pl → ℕ → ℚ

  v : Pl → ℕ → ℚ

  e : Pl → ℕ → ℚ
  bb : Pl → ℕ → ℚ

  a : Pl → ℚ
  bt : Pl → ℚ
  b0 : ℚ

  xq : ℚ
  S : ℚ
  η : ℚ
  C : ℚ
  N : ℝ
  w'' : ℝ
  X'' : ℝ
  logd : ℝ

namespace HarishChandraParameters

variable {Pl : Type} (P : HarishChandraParameters Pl)

def deg (j : ℕ) (ρ : Pl) : ℚ := HCdeg P.k P.t (P.u ρ) (P.e ρ) j

def Dpm [Fintype Pl] (m j : ℕ) : ℝ :=
  ((∑ ρ, (HCDplus P.k P.t m j (P.v ρ) (P.bb ρ) (P.e ρ) + HCDminus P.k P.t m j (P.v ρ) (P.bb ρ) (P.e ρ)) : ℚ) : ℝ)

end HarishChandraParameters

def ParameterSizeInequalities {Pl : Type} [Fintype Pl] (P : HarishChandraParameters Pl) (TT : Finset Pl) (m : ℕ) (x eps f b C0 lg : ℝ) : Prop :=
  HarishChandraParamConditions TT P.k P.t m P.u P.v P.e P.bb P.a P.bt P.b0 P.xq P.S P.η P.C ∧
  1 ≤ x ∧ x ≤ (P.xq : ℝ) ∧ 0 < eps ∧ 0 ≤ b ∧ (Fintype.card Pl : ℝ) ≤ f ∧ 1 ≤ m ∧ 1 ≤ f ∧ 1 ≤ P.N ∧ 0 ≤ P.logd ∧
  (∀ (j : Fin m) ρ, 0 ≤ (P.e ρ (j.val + 1) : ℝ) ∧ (P.e ρ (j.val + 1) : ℝ) ≤ 2 * b) ∧
  (P.k : ℝ) * P.S ≤ P.w'' ∧ (m : ℝ) * ((P.t : ℝ) + 1) * P.η ≤ P.w'' ∧ P.N * P.w'' ≤ b ∧ P.N * (P.N + P.t) ≤ b ∧
  (P.k : ℝ) * P.b0 ≤ b ∧ f * P.k * P.N * P.X'' ≤ b ∧ P.logd ≤ x ^ eps ∧ lg ≤ C0 * x ^ eps ∧ (P.C : ℝ) + 3 ≤ C0

def ErrorSizeConditions {Pl : Type} (P : HarishChandraParameters Pl) (TT : Finset Pl) (m : ℕ) (x eps f b C0 : ℝ) (o : Fin m → Fin 2 → ℝ)
    (Eels : Fin m → ℝ) : Prop :=
  (∀ j i, |o j i| ≤ C0 * (f * (P.N * (P.N + P.t) + (m : ℝ) ^ 2 * P.η))) ∧
  (∀ j, Eels j ≤ C0 * (f * m * b * x ^ eps) + ((TT.card : ℝ) * (2 * b + 4 * P.k * P.b0) + 4 * f * P.k * P.b0) * P.logd +
    C0 * (f * P.k * P.N * P.X''))

def SecondComplementClosedValuation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) (m : ℕ) (P : HarishChandraParameters Pl)
      (E : Fin m → HeightOneSpectrum (𝓞 K) → ℝ), (∀ j, (Function.support (E j)).Finite) →
    ∀ (p : Fin 2 → Pl → K) (Dx : Fin m → Pl → ℕ),
    (∀ i ρ, p i ρ * star (p i ρ) = (g i : K)) → (∀ j ρ, (Dx j ρ : ℚ) = P.deg (j.val + 1) ρ) →
    ∀ (o : Fin m → Fin 2 → ℝ) (Eels : Fin m → ℝ) (x eps f b C0 : ℝ),
    (∀ j i w, PlOver (g i) w → E j w = (vw w (g i : K) : ℝ) *
      EGval (g i) (p i) (fun ρ => (Dx j ρ : ℝ)) (P.Dpm m (j.val + 1)) (o j i) w) →
    (∀ j, (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), Formalism.DivisionValues.lw w * |E j w|) ≤ Eels j) →
    ParameterSizeInequalities P TT m x eps f b C0 (Real.log ((g 0 : ℝ) * (g 1 : ℝ))) → ErrorSizeConditions P TT m x eps f b C0 o Eels →
      TypePrimeCostDeviationBound TT (fun ρ => (P.a ρ : ℝ)) (fun j => ∑ᶠ w : HeightOneSpectrum (𝓞 K), Formalism.DivisionValues.lw w * E j w)
        (Real.log ((g 0 : ℝ) * (g 1 : ℝ))) (m : ℝ) (f * m * b * x ^ eps) C0

def hcU₂ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (l : ℕ) : ℚ :=
  if h : 1 ≤ l ∧ l ≤ D.R.k then (D.hcW u τ).u ⟨l - 1, by omega⟩ else 0

def hcE₂ (D : Formalism.BasicNotions.D7) (τ : D.what₂.Tau) (l : ℕ) : ℚ :=
  if h : 1 ≤ l ∧ l ≤ D.R.m then (D.hc τ).e ⟨l - 1, by omega⟩ else 0

end Formalism.AtG
