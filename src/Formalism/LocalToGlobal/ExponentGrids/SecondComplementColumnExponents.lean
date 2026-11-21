import Mathlib
import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.TranslateCocycles.Statement
import Formalism.TranslateCocycles.StatementHC
import Formalism.TranslateCocycles.StatementNet

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl lw PlOver IsConjAt)
open Formalism.CG (HCdeg HCDplus HCDminus)

noncomputable section

namespace Formalism.AtG

def HarishChandraParamConditions {Pl : Type} (TT : Finset Pl) (k t m : ℕ) (u v e bb : Pl → ℕ → ℚ) (a bt : Pl → ℚ)
    (b0 x S η C : ℚ) : Prop :=
  2 ≤ k ∧ 1 ≤ t ∧ (k : ℚ) ≤ S ∧ (k : ℚ) * t ≤ η ∧ 0 ≤ C ∧ 0 ≤ b0 ∧ 2 ≤ x ∧
  (∀ ρ i, 2 ≤ i → i ≤ k → 0 ≤ v ρ i ∧ v ρ i ≤ S) ∧
  (∀ ρ i, 1 ≤ i → i ≤ m → bb ρ i + ((t : ℚ) + 3) / 2 ≤ e ρ i) ∧
  (∀ ρ i, 1 ≤ i → i < m → e ρ i + ((t : ℚ) + 3) / 2 ≤ bb ρ (i + 1)) ∧
  (∀ ρ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → |bb ρ i - e ρ j| ≤ η) ∧
  (∀ ρ, ρ ∉ TT → ∀ i, 1 ≤ i → i ≤ k → -1 ≤ u ρ i ∧ u ρ i ≤ (C + 1) * S) ∧
  (∀ ρ ∈ TT, u ρ 1 = a ρ + ((k : ℚ) - 1) / 2 ∧ u ρ k = -bt ρ - ((k : ℚ) - 1) / 2 ∧ b0 ≤ bt ρ ∧
    (∀ i, 1 < i → i < k → 0 ≤ u ρ i ∧ u ρ i ≤ S) ∧
    ∀ j, 1 ≤ j → j ≤ m → bt ρ + b0 / x ≤ e ρ j ∧ e ρ j ≤ bt ρ + b0 / x + η)

def SecondComplementColumnExponents : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (k t m : ℕ)
      (E F : Fin m → HeightOneSpectrum (𝓞 K) → ℝ), (∀ j, (Function.support (E j)).Finite) →

    ∀ (u v e bb : Pl → ℕ → ℚ) (a bt : Pl → ℚ) (b0 x S η C : ℚ),
    HarishChandraParamConditions TT k t m u v e bb a bt b0 x S η C →

    ∀ (p : Fin 2 → Pl → K) (Dx : Fin m → Pl → ℕ),
    (∀ i ρ, p i ρ * star (p i ρ) = (g i : K)) →
    (∀ j ρ, (Dx j ρ : ℚ) = HCdeg k t (u ρ) (e ρ) (j.val + 1)) →

    ∀ (v0 : InfinitePlace K), IsConjAt v0 → ∀ (cg : Fin 2 → K), (∀ i, ‖v0.embedding (cg i)‖ = 1) →
    ∀ (er Eels : Fin m → ℝ) (eps L b B0 f N w'' X'' logd C0 : ℝ),

    (∀ j i w, PlOver (g i) w →
      |E j w - (F j w + (vw w (∏ ρ, p i ρ ^ Dx j ρ) : ℝ) - (vw w (cg i) : ℝ) / (m : ℝ))| ≤
        er j * (vw w (g i : K) : ℝ)) →
    (∀ j i w, PlOver (g i) w →
      F j w = -((((∑ ρ, HCDplus k t m (j.val + 1) (v ρ) (bb ρ) (e ρ) : ℚ) : ℝ)
        + ((∑ ρ, HCDminus k t m (j.val + 1) (v ρ) (bb ρ) (e ρ) : ℚ) : ℝ)) / 2)
          * (vw w (g i : K) : ℝ)) →

    (∀ j, (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), lw w * |E j w|) ≤ Eels j) →

    0 < eps → L = (x : ℝ) ^ eps → 0 ≤ b → B0 = f * m * b * (x : ℝ) ^ eps →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 1 ≤ N → 0 ≤ logd →
    (∀ (j : Fin m) ρ, 0 ≤ (e ρ (j.val + 1) : ℝ) ∧ (e ρ (j.val + 1) : ℝ) ≤ 2 * b) →
    (k : ℝ) * S ≤ w'' → (m : ℝ) * ((t : ℝ) + 1) * η ≤ w'' → N * w'' ≤ b → N * (N + t) ≤ b →
    (k : ℝ) * b0 ≤ b → f * k * N * X'' ≤ b → logd ≤ L →
    Real.log ((g 0 : ℝ) * (g 1 : ℝ)) ≤ C0 * L →
    (C : ℝ) + 3 ≤ C0 →
    (∀ j, er j ≤ C0 * (f * (N * (N + t) + (m : ℝ) ^ 2 * η))) →
    (∀ j, Eels j ≤ C0 * B0 + ((TT.card : ℝ) * (2 * b + 4 * k * b0) + 4 * f * k * b0) * logd +
      C0 * (f * k * N * X'')) →
      (∀ j, |2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        (∑ ρ ∈ TT, (a ρ : ℝ)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0) ∧
      |2 * (∑ j, ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        m * ((∑ ρ ∈ TT, (a ρ : ℝ)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ)))| ≤
        (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0)

end Formalism.AtG
