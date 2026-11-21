import Mathlib
import Formalism.MeanHeightDescent.StatementF
import Formalism.MeanHeightDescent.StatementJ

open Finset Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

def WShiftConst : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (w w0 : Pl → ℝ) (lcvD pq logOm C3 B0 llx La f m k Δ b xe CO : ℝ),
    lcvD ≤ (∑ ρ, pq * w ρ * logOm) + C3 * B0 * llx →
    (∀ ρ, |w ρ - w0 ρ| ≤ Δ) → 0 ≤ Δ → |pq - k| ≤ m → 1 ≤ CO → |logOm| ≤ CO * La → La ≤ 3 * xe →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ k → k * Δ ≤ 2 * b → B0 = f * m * b * xe → 1 ≤ llx →
    lcvD ≤ (∑ ρ, pq * w0 ρ * logOm) + (C3 + 12 * CO) * B0 * llx

def PeriodBound : Prop :=
  ∀ (logOm v rd Lc L x b a : ℝ),
    logOm = Real.eulerMascheroniConstant + Real.log (Real.pi / v) - Lc → 2 * v = rd → 4 ≤ rd →
    |Lc| ≤ L → 1 ≤ x → b = Real.exp L → a = x * b →
    |logOm| ≤ Real.log (a * rd)

def CovolumeEstimateAnchoredWeights : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d D : ℕ),
    0 < D → d = D →
    ∀ XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (XW v).det) →
    ∀ M : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K M →
    ∀ (Pl : Type) [Fintype Pl] (w w0 c1 ua : Pl → ℝ)
      (muU muA muN muG mmax dA dB dN dg db : ℝ)
      (C1 Cf Cc cfl ε δ Q P Λ G P9 : ℝ)
      (pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO : ℝ),

    -(2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4)) ≤ muU →

    cfl = (∑ τ, w τ * c1 τ) - Cf * q' * Real.log rd * (∑ τ, w τ) - Cf * L →
    muU + 2 * cfl ≤ muA →

    0 < dA → dA ≤ dB → (1 - ε) * dB ≤ dA → 0 ≤ ε → 0 ≤ P →
    dA * (muA - P) + (dB - dA) * (-Λ) ≤ dB * muN →
    |2 * cfl| ≤ Q → Λ ≤ Q → ε * Q ≤ b / 4 →

    0 < dN → dN = dg + db → 0 ≤ db → db ≤ 3 * δ * dN → 0 ≤ δ → δ ≤ 1 / 12 →
    dN * muN ≤ dg * muG + db * (mmax + G) → |muN| ≤ Q → mmax ≤ Q → G ≤ Q →

    muG - P9 ≤ Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M →
    P + 12 * δ * Q + P9 ≤ b →

    (∀ τ, |c1 τ + pq * logOm / 2| ≤ Cc * q' * (Real.log rd + Lchi)) →

    (∀ τ, m * w τ / 2 ≤ ua τ ∧ ua τ ≤ 2 * (m * w τ + k * S + k * η)) → 1 ≤ (∑ τ, ua τ) →
    (∀ τ, 0 ≤ w τ ∧ w τ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 0 ≤ q' → q' ≤ m →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L →
    0 ≤ Lchi → Lchi ≤ L → Real.log x ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    B0 = f * m * b * x ^ eps → 0 ≤ C1 → 0 ≤ Cf → 0 ≤ Cc →

    (∀ ρ, |w ρ - w0 ρ| ≤ S + R) → 0 ≤ S → 0 ≤ R → k * R ≤ b → 1 ≤ k →
    |pq - k| ≤ m → a = x * b → La = Real.log (a * rd) → 1 ≤ CO → |logOm| ≤ CO * La →
    Formalism.DivisionValues.lcv XW M / D ≤
      (∑ ρ, pq * w0 ρ * logOm) + (64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * CO) * B0 * llx

def CovolumeEstimateOfAverageDegreeWeighted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d D : ℕ),
    0 < D → d = D →
    ∀ XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (XW v).det) →
    ∀ M : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K M →
    ∀ (Pl : Type) [Fintype Pl] (w w0 c1 ua : Pl → ℝ)
      (ι : Type) [Fintype ι] [Nonempty ι] (T DY A cs X cc z ρ R1 R2 Bn δ' : ℝ)
      (h sl δc dc degc : ι → ℝ) (Ca Cb PPf e1 e2 : ℝ)
      (muU muA muN muG mmax dA dB dN dg db : ℝ)
      (Cf Cc cfl ε δ Q P Λ G P9 : ℝ)
      (pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO : ℝ),

    0 ≤ DY → 3 * DY + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δc c ∧ δc c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δc c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δc c) →
    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →
    (∀ c, Bn * δc c *
        (T * h c - 3 * (DY + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2) ≤ degc c) →
    T * X ≤ Ca * LL0 * (∑ τ, ua τ) + e1 → T * cc ≤ Cb * LL0 * (∑ τ, ua τ) + e2 →
    cs * (6 * DY + 10 + T * (z + 2 * ρ)) + (A * Real.log (max A 1) + 4) + R1 + 2 * z * R2 + PPf
      + e1 + e2 ≤ b / 4 →
    2 * ((∑ c, degc c) / (∑ c, dc c) - PPf) ≤ muU →

    cfl = (∑ τ, w τ * c1 τ) - Cf * q' * Real.log rd * (∑ τ, w τ) - Cf * L →
    muU + 2 * cfl ≤ muA →

    0 < dA → dA ≤ dB → (1 - ε) * dB ≤ dA → 0 ≤ ε → 0 ≤ P →
    dA * (muA - P) + (dB - dA) * (-Λ) ≤ dB * muN →
    |2 * cfl| ≤ Q → Λ ≤ Q → ε * Q ≤ b / 4 →

    0 < dN → dN = dg + db → 0 ≤ db → db ≤ 3 * δ * dN → 0 ≤ δ → δ ≤ 1 / 12 →
    dN * muN ≤ dg * muG + db * (mmax + G) → |muN| ≤ Q → mmax ≤ Q → G ≤ Q →

    muG - P9 ≤ Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M →
    P + 12 * δ * Q + P9 ≤ b →

    (∀ τ, |c1 τ + pq * logOm / 2| ≤ Cc * q' * (Real.log rd + Lchi)) →

    (∀ τ, m * w τ / 2 ≤ ua τ ∧ ua τ ≤ 2 * (m * w τ + k * S + k * η)) → 1 ≤ (∑ τ, ua τ) →
    (∀ τ, 0 ≤ w τ ∧ w τ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 0 ≤ q' → q' ≤ m →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L →
    0 ≤ Lchi → Lchi ≤ L → Real.log x ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    B0 = f * m * b * x ^ eps → 0 ≤ Ca → 0 ≤ Cb → 0 ≤ Cf → 0 ≤ Cc →

    (∀ σ, |w σ - w0 σ| ≤ S + R) → 0 ≤ S → 0 ≤ R → k * R ≤ b → 1 ≤ k →
    |pq - k| ≤ m → a = x * b → La = Real.log (a * rd) → 1 ≤ CO → |logOm| ≤ CO * La →
    Formalism.DivisionValues.lcv XW M / D ≤
      (∑ σ, pq * w0 σ * logOm) + (64 * (Ca + Cb + 3 * Cf) + 8 * Cc + 2 + 12 * CO) * B0 * llx

def SpreadBound : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (N m : ℕ) (T jj : ℝ) (w mx mn : Pl → ℝ) (u' : Pl → ℕ → ℝ)
    (nodes : Pl → Finset ℕ),
    0 < T → 0 ≤ jj → jj ≤ m → (∀ τ, 0 ≤ w τ) →
    (∀ τ, nodes τ ⊆ Finset.range N ∧ (nodes τ).card = m) →
    (∀ τ, mx τ - mn τ ≤ 3 / 2 * w τ / T) →
    (∀ τ, ∀ i ∈ nodes τ, w τ / (4 * T) ≤ |u' τ i|) →
    jj * (∑ τ, (mx τ - mn τ)) ≤ 6 * (∑ τ, ∑ i ∈ Finset.range N, |u' τ i|)

def SumUnits : Prop :=
  ∀ (Bd : Finset ℕ) (ad kp : ℕ → ℝ) (CL K : ℝ), Bd.card ≤ 7 → 0 ≤ CL →
    (∀ p ∈ Bd, ad p ≤ kp p + 3) → (∀ p ∈ Bd, Real.log p ≤ CL) →
    (∑ p ∈ Bd, kp p * Real.log p) ≤ K →
    (∑ p ∈ Bd, ad p * Real.log p) ≤ K + 21 * CL

end Formalism.ExtensionFiltration
