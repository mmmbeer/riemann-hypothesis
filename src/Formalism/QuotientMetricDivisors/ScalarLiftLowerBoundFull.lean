import Mathlib
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.QuotientMetricDivisors.EigenRatHermLcv
import Formalism.QuotientMetricDivisors.ClassSumDualGeF
import Formalism.QuotientMetricDivisors.UntwistedChoice
import Formalism.QuotientMetricDivisors.HeightBoundExactNorms
import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

def DivIneqRecord : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    m * lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    1 ≤ C0 → C0 ≤ ce →
    Lpass ≤ 1 + C0 * (m * lam0) →
    Eb ≤ ce * m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        ((50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
          60 * ce * (m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc)))

def GoodTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ e : Matrix (Fin n) (Fin n) K, (∀ i j, e i j ∈ K0) → e * e = e → (∀ T ∈ 𝒯, e * T = T * e) →
    (∀ x y : Fin n → K, hform H (e.mulVec x) y = hform H x (e.mulVec y)) →
    ∀ (Z : Submodule K (Fin n → K)) (Ω : Type) [Field Ω] (j : K →+* Ω)
      (S : Set (Matrix (Fin n) (Fin n) K → Ω)),
    extSpan j Z = ⨆ χ ∈ S, (simEig j 𝒯 χ).map (e.map j).mulVecLin →
    ∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z

def ScalarLiftLowerBoundFull : Prop :=
  ∀ (J Pl Emb Frm : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb]
    [Fintype Frm] [Nonempty Frm]
    (loglam : J → Frm → Emb → ℝ) (Hp Hm : J → Pl → ℕ) (mlam f m nV L' C1 : ℝ)
    (hq : ∀ j π s, (∑ ρ, Real.log ((Hp j ρ : ℝ) * (Hm j ρ : ℝ))) - C1 * f * nV ^ 2 * L' ≤ loglam j π s)
    (hp : ∀ j ρ, 0 < Hp j ρ) (hm : ∀ j ρ, 0 < Hm j ρ) (hn : 0 ≤ nV) (hL : 0 ≤ L') (hf : 0 ≤ f) (hC : 0 ≤ C1)
    (hJ : (Fintype.card J : ℝ) = m)
    (hml : mlam = (∑ s, Finset.univ.inf' Finset.univ_nonempty (fun π : Frm => ∑ j, loglam j π s)) /
      (Fintype.card Emb : ℝ)),
    (∀ j π s, (∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * f * nV ^ 2 * L' ≤ loglam j π s) ∧
    (∑ j, ((∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * f * nV ^ 2 * L')) =
      (∑ j, ∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * m * f * nV ^ 2 * L' ∧
    (∑ j, ∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * m * f * nV ^ 2 * L' ≤ mlam

end Formalism.DivisionValues
