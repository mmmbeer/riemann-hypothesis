import Formalism.SizeWindowBrackets.SlopeHypothesesRounded
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.LogVandermondeBounds.LogRatioUpperBound

open Real

namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer

noncomputable section

section Z

variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f)

def ZiiR (cZ Sc LZ logT : ℝ) : ℝ :=
  -((∑ t, D.aT t / D.k) * logT) - cZ * D.nT * D.a * Real.log D.k
    - cZ * (f : ℝ) * D.k * (D.b' + Sc) * Real.log D.k - cZ * (f : ℝ) * Sc * logT
    - cZ * (f : ℝ) * D.k ^ 2 * LZ

def ZiiiR (cZ Sc LZ logT : ℝ) : ℝ :=
  cZ * D.nT * D.a * Real.log (D.k * D.v)
    + cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v) + logT)
    + cZ * (f : ℝ) * D.k ^ 2 * LZ

def PropZ (cZ Sc LZ : ℝ) : Prop :=
  ∀ u0 (u : W u0), ZiiR D cZ Sc LZ (Real.log (D.T u0 u)) ≤ D.muM u0 u ∧
    D.muMaxM u0 u ≤ ZiiiR D cZ Sc LZ (Real.log (D.T u0 u))

def LogTUp (cU : ℝ) : Prop :=
  ∀ u0 (u : W u0), Real.log (D.T u0 u) ≤ cU * (m : ℝ) * D.L

def ZWindows (cZ cL cU Sc LZ : ℝ) : Prop :=
  0 ≤ cZ ∧ 0 ≤ cL ∧ 0 ≤ cU ∧ 0 ≤ D.a ∧ 1 ≤ D.k ∧ (m : ℝ) ≤ D.k ∧ 0 ≤ D.b' ∧ 0 ≤ Sc ∧
  (∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a) ∧
  0 ≤ D.L ∧ D.L ≤ D.La ∧ Real.log D.k ≤ D.La ∧ Real.log (D.k * D.v) ≤ D.La ∧ LZ ≤ cL * D.La ∧
  (f : ℝ) * D.k * (D.b' + Sc) ≤ D.nT * D.a ∧ (f : ℝ) * D.k ^ 2 ≤ D.nT * D.a

def unitZ : ℝ := D.nT * D.a * D.La

end Z

def cSlopeZ (cZ cL cU : ℝ) : ℝ := cZ * (2 + cL + cU) + 2 * cU

def ZTerms : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (cZ cL cU Sc LZ logT : ℝ), ZWindows D cZ cL cU Sc LZ → logT ≤ cU * (m : ℝ) * D.L →
    (∑ t, D.aT t / D.k) * logT ≤ 2 * cU * (unitZ D * ((m : ℝ) / D.k)) ∧
    cZ * D.nT * D.a * Real.log D.k ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * D.k * (D.b' + Sc) * Real.log D.k ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * Sc * logT ≤ cZ * cU * (unitZ D * ((m : ℝ) / D.k)) ∧
    cZ * (f : ℝ) * D.k ^ 2 * LZ ≤ cZ * cL * unitZ D ∧
    cZ * D.nT * D.a * Real.log (D.k * D.v) ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v)) ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * (D.b' + Sc) * logT ≤ cZ * cU * unitZ D

def ZToSlopes : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (C : Consts) (cZ cL cU Sc LZ : ℝ), ZWindows D cZ cL cU Sc LZ → LogTUp D cU → PropZ D cZ Sc LZ →
    cSlopeZ cZ cL cU ≤ C.cSlope → D.Slopes C

section Count

variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
variable (D : Data U0 W Top m f)

def mainCount (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg

def BoundedBy' (c5 : ℝ) (X : ∀ u0, W u0 → ℝ) : Prop :=
  ∀ u0 (u : W u0),
    mainCount D u0 - c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) ≤ Real.log (X u0 u) ∧
    Real.log (X u0 u) ≤ c5 * (m : ℝ) * D.L

def Variation5 (c5 : ℝ) (X : ∀ u0, W u0 → ℝ) : Prop :=
  ∀ u0 (u u' : W u0), |Real.log (X u0 u) - Real.log (X u0 u')| ≤ c5 * Real.log D.k

def LevelWindow (Gam : ℝ) (X : ∀ u0, W u0 → ℝ) : Prop :=
  ∀ u0 (u : W u0), 0 < X u0 u ∧
    X u0 u * Gam ^ (-(2 / ((f : ℝ) * D.k))) ≤ D.T u0 u ∧
    D.T u0 u ≤ X u0 u * Gam ^ (-(2 / ((f : ℝ) * D.k))) * (1 + 1 / ((f : ℝ) * D.k))

def CountWindows (c5 Gam : ℝ) : Prop :=
  0 ≤ c5 ∧ 0 < f ∧ 1 ≤ D.k ∧ 1 ≤ Gam ∧ D.logGam = Real.log Gam ∧
  D.logGam / ((f : ℝ) * D.k) ≤ 1 ∧ 0 ≤ D.L ∧ D.L ≤ D.La ∧ 1 ≤ D.La ∧ 1 ≤ (m : ℝ) * D.L ∧
  1 ≤ Real.log D.k

end Count

def Prop5ToCount : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (C : Consts)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X → Variation5 D c5 X →
    LevelWindow D Gam X → C.cCount = c5 + 1 → D.Count C

def Prop5ToCount5 : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (C : Consts)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X → Variation5 D c5 X →
    LevelWindow D Gam X → c5 + 3 ≤ C.cCount → Count5 D C

def Prop5ToLogTUp : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X →
    LevelWindow D Gam X → LogTUp D (c5 + 1)

def LevelLowerOfCount : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X →
    LevelWindow D Gam X → (∀ u0 j ρ, 1 ≤ D.w u0 j ρ * D.v / π) → 16 * D.L ≤ D.lg →
    (m : ℝ) ^ 2 ≤ D.k → 1 ≤ D.L → 2 * c5 + 2 ≤ 15 * (m : ℝ) →
    ∀ u0 (u : W u0), (m : ℝ) * D.L / 2 ≤ Real.log (D.T u0 u)

open Formalism.LogVandermondeBounds.StandardLattice Finset in

def TranslateWordBoundHypotheses (C₀ C₃ ε x : ℝ) (f m k : ℕ) (vE Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ)
    (Dstar dstar massk massr Isig Ipi : ℝ) (Lval dsig : ℕ → ℝ) : Prop :=
  1 ≤ f ∧ 2 ≤ m ∧ Even m ∧ 2 ≤ k ∧ (m : ℝ) ^ 2 * x ^ ε ≤ k ∧ (k : ℝ) ≤ x ^ C₀ ∧
  Real.pi ≤ vE ∧ Real.log vE ≤ x ^ ε ∧ 1 ≤ Δ ∧ 1 ≤ g₁ ∧ 1 ≤ g₂ ∧
  Real.log g₁ ≤ C₀ * x ^ ε ∧ Real.log g₂ ≤ C₀ * x ^ ε ∧
  (∀ ρ, ρ < f → PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m (u ρ) (v ρ) (b ρ) (w ρ) ∧
    (∀ i j, i < j → j < k → 1 ≤ u ρ i - u ρ j)) ∧
  0 < massk ∧ 0 < massr ∧ 0 < Isig ∧ 0 < Ipi ∧
  (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) ∧
  (massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
    ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) ∧
  (((2 : ℝ) ^ (2 * f))⁻¹ * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi) ∧
  (Isig / Ipi ≤ (2 : ℝ) ^ (2 * f) * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2)) ∧
  ((2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) ≤ Dstar) ∧
  (Dstar = massr * Isig * ∏ ρ ∈ range f, dsig ρ) ∧
  (∀ ρ, ρ < f → 0 < dsig ρ ∧ dsig ρ ≤ 4 * dTau k m (rowPar k (v ρ) (b ρ)) *
    (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) *
      (v ρ 0 + b ρ (m - 1))) ^ ((k - 1 + m / 2) * (m / 2))) ∧
  (dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k)

def LevelSizes : Prop :=
  ∀ (f m : ℕ) (b T N : ℝ), 1 ≤ f → 6 ≤ m → 8 * (f : ℝ) ≤ b → b ^ ((m : ℝ) / 2) ≤ T →
    2 * (f : ℝ) * N + 1 < T → 2 ≤ N →
    2 < T ∧ 4 * (f : ℝ) ≤ T ∧ 2 * (f : ℝ) / T ≤ 1 / 2 ∧
    4 * (f : ℝ) / T * b ^ 2 + (f : ℝ) * Real.log (T - 1) / (T - 2) ≤ 1

def PowOfLog : Prop :=
  ∀ (mR b T : ℝ), 0 < b → 0 < T → (mR * Real.log b / 2 ≤ Real.log T ↔ b ^ (mR / 2) ≤ T)

def DefectBound : Prop :=
  ∀ (f : ℕ) (T : ℝ), 2 ≤ T → 1 - (1 - 1 / (T - 1)) ^ f ≤ 2 * (f : ℝ) / T

section Level

variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
variable (D : Data U0 W Top m f)

end Level

section T5

variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f)

def lambdaIndex (aM : ℝ) (VV : Finset Top) (Wt bt : Top → ℝ) : ℝ :=
  (m : ℝ) * (∑ t ∈ VV, (aM / D.k + 2 * Wt t + D.k)) + (m : ℝ) * (∑ t ∈ VV, bt t)

def IndexWindows (aM : ℝ) (Wt bt : Top → ℝ) : Prop :=
  0 < D.k ∧ D.k ≤ D.b' ∧ 0 ≤ D.a ∧ aM ≤ 2 * D.a ∧ (∀ t, Wt t ≤ 2 * D.b') ∧ (∀ t, bt t ≤ 2 * D.b')

end T5

def IndexToLengthBound : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (aM : ℝ) (VV : Finset Top) (Wt bt : Top → ℝ), IndexWindows D aM Wt bt →
    lambdaIndex D aM VV Wt bt ≤ 7 * D.nT * (m : ℝ) * (D.a / D.k + D.b')

def SmallText : Prop :=
  ∀ ε e cT c6 : ℝ, 0 < ε → 0 ≤ e → 0 < c6 → ∃ x₀ : ℝ, ∀ x k nT : ℝ, x₀ ≤ x → 0 ≤ nT → nT ≤ x ^ e →
    0 < k → nT * x ^ 2 ≤ k → cT * nT * (x / k + x / XpTx x ε) < c6

def SlopeCountJoint : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (C : Consts) (cZ cL Sc LZ c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ),
    ZWindows D cZ cL (c5 + 1) Sc LZ → PropZ D cZ Sc LZ →
    CountWindows D c5 Gam → BoundedBy' D c5 X → Variation5 D c5 X → LevelWindow D Gam X →
    cSlopeZ cZ cL (c5 + 1) ≤ C.cSlope → c5 + 3 ≤ C.cCount → D.Slopes C ∧ Count5 D C

def ExponentialPowerWindows : Prop :=
  ∀ ε e : ℝ, 0 < ε → 0 ≤ e → ∃ x₀ : ℝ, ∀ x k fR mR nT N Sc lrd v : ℝ, x₀ ≤ x →
    1 ≤ k → k ≤ x ^ e → 1 ≤ fR → fR ≤ x ^ e → 1 ≤ mR → mR ≤ x ^ e → 1 ≤ N → N ≤ x ^ e → 1 ≤ nT →
    0 ≤ Sc → Sc ≤ bpTx x ε → 0 < v → Real.log v ≤ lrd → 0 ≤ lrd →
    Real.log k ≤ Real.log (aTx x ε) + lrd ∧ Real.log (k * v) ≤ Real.log (aTx x ε) + lrd ∧
    Real.log (aTx x ε * v) ≤ Real.log (aTx x ε) + lrd ∧
    Real.log (bTx x ε) ≤ Real.log (aTx x ε) + lrd ∧ 1 ≤ Real.log (bTx x ε) ∧
    fR * k * (bpTx x ε + Sc) ≤ nT * aTx x ε ∧ fR * k ^ 2 ≤ nT * aTx x ε ∧
    k ≤ bpTx x ε ∧
    fR * mR * N ≤ nT * (aTx x ε / k) ∧ mR * bpTx x ε ≤ aTx x ε / k ∧ mR * N ≤ aTx x ε / k ∧
    8 * fR ≤ bTx x ε ∧ mR * N ≤ bTx x ε ∧ mR * bpTx x ε ≤ bTx x ε

section Exact

variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
variable (D : Data U0 W Top m f)

def exactMain (bN : U0 → Fin m → Fin f → ℝ) (u0 : U0) : ℝ :=
  (((m : ℝ) - 1) + (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π)
    - (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v)
    + ((m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg
    + ((D.k - 1) / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ))

def ExactCoeff5 (cE : ℝ) (X : ∀ u0, W u0 → ℝ) (bN : U0 → Fin m → Fin f → ℝ) : Prop :=
  ∀ u0 (u : W u0), exactMain D bN u0 - cE * D.L - 1 ≤ Real.log (X u0 u)

def ExactWindows (bN : U0 → Fin m → Fin f → ℝ) : Prop :=
  0 < f ∧ 1 ≤ m ∧ (m : ℝ) ≤ D.k ∧ (m : ℝ) ≤ D.x ∧ 1 ≤ D.L ∧ 0 < D.v ∧
  0 ≤ Real.log (D.v / π) ∧ Real.log (D.v / π) ≤ D.L ∧ Real.log (2 * D.v) ≤ D.L ∧ 0 ≤ D.lg ∧
  ∀ u0 j ρ, 0 < bN u0 j ρ ∧ 0 < D.w u0 j ρ ∧ D.w u0 j ρ ≤ bN u0 j ρ * (1 + 1 / D.x) ∧
    Real.log (bN u0 j ρ) ≤ 2 * D.L

end Exact

def ExactCoeffPrice : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (bN : U0 → Fin m → Fin f → ℝ), ExactWindows D bN →
    ∀ u0, mainCount D u0 ≤ exactMain D bN u0 + 7 / 2 * D.L + 1

def ExactCoeffToProp5 : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (cE c5 : ℝ) (X : ∀ u0, W u0 → ℝ) (bN : U0 → Fin m → Fin f → ℝ), ExactWindows D bN →
    ExactCoeff5 D cE X bN → (∀ u0 (u : W u0), Real.log (X u0 u) ≤ c5 * (m : ℝ) * D.L) →
    0 ≤ c5 → cE + 6 ≤ c5 → BoundedBy' D c5 X

def ExactCoeffDiff : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (bN : U0 → Fin m → Fin f → ℝ), ExactWindows D bN →
    ∀ u0, mainCount D u0 - exactMain D bN u0 =
      (1 - (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π)
      + (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v)
      - ((m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg
      + (1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ))
      + (1 / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ))

end

end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
