import Mathlib
import Formalism.QuotientMetricDivisors.RatHermLcvTwist
import Formalism.QuotientMetricDivisors.DualMu
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.MirabolicMackeyTheory.StatementT

open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisorInequality

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)

def BoundsMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), 0 < D → (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ y, μ (conjPl y) = μ y) →
    {y | μ y ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J]
      (XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : J → Submodule (𝓞 K) (Fin D → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : J → Tup → Matrix (Fin D) (Fin D) K)
      (XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (Tl : J → Tup → Submodule (𝓞 K) (Fin D → K)), (∀ j t, Submodule.IsLattice K (Tl j t)) →
    ∀ (θ : J → Tup → Matrix (Fin D) (Fin D) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρt : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρt t) = (ρr t : ℂ)) → ρt μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ y, vw y (ρt (μ y)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (Gm : Tup → HeightOneSpectrum (𝓞 K) → K)
      (eb : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t y, IsLocBasis (abelian₂ t) y (eb t y)) →
    (∀ t y, v0.embedding (Gm t y) = (gram (XQ t) v0 (eb t y)).det) →
    ∀ (nH : ℕ) (Hm : Matrix (Fin nH) (Fin nH) K), (∀ i j, Hm i j ∈ K0) →
    (∀ v : InfinitePlace K, (Hm.map v.embedding).PosDef) →
    ∀ Pm : Matrix (Fin D) (Fin nH) K, Function.Surjective Pm.mulVec → IsQuotMetric Pm Hm (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin nH → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat Pm Mt →
    (∀ y, Gm μ0 y = gramR (quotGram Pm Hm) (eb μ0 y)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ y, Formalism.HermitianLatticesTheory.localization₂ y.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))) →

    ∀ (Sy Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ Sy →
    (∀ y ∉ Sy, lw y * ((vw y (Gm (μ y) y) : ℝ) + ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ))) = 0) →
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) = 0) →
    ∀ (LG E3 : ℝ) (E1 E2 : J → ℝ) (elly gy : HeightOneSpectrum (𝓞 K) → ℝ)
      (Fy erry Jy ηy : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, Fy y j = 0) →

    (∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y) → ∑ y ∈ Sy, lw y * gy y ≤ LG →

    (∀ y ∈ Tw, ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
        (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ)) ≤
      (∑ j, (2 * Fy y j + erry y j) + 2 / elly y ^ 2) * D) →

    (∀ y ∈ Tw, ∀ j, (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) ≤ Jy y j * D + ηy y j) →

    (∀ j, ∑ y ∈ Tw, lw y * (erry y j + Jy y j) ≤ E1 j) →
    (∀ j, ∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j) →
    ∑ y ∈ Sy, lw y * (2 / elly y ^ 2) ≤ E3 →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) ≤
        meanLog κ + (∑ j, lcv (XW j) (M j) / D) + 2 * (∑ j, ∑ y ∈ Tw, lw y * Fy y j) + LG +
          (∑ j, (E1 j + E2 j)) + E3 ∧
      ∀ j, lcv (XW j) (M j) / D = -Formalism.HN.muDef (Pi.basisFun K (Fin D)) (XW j) (M j)

def BaseLevelBoundsWithCovolume : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), 0 < D → (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ y, μ (conjPl y) = μ y) →
    {y | μ y ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J]
      (XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : J → Submodule (𝓞 K) (Fin D → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : J → Tup → Matrix (Fin D) (Fin D) K)
      (XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (Tl : J → Tup → Submodule (𝓞 K) (Fin D → K)), (∀ j t, Submodule.IsLattice K (Tl j t)) →
    ∀ (θ : J → Tup → Matrix (Fin D) (Fin D) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρt : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρt t) = (ρr t : ℂ)) → ρt μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ y, vw y (ρt (μ y)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (Gm : Tup → HeightOneSpectrum (𝓞 K) → K)
      (eb : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t y, IsLocBasis (abelian₂ t) y (eb t y)) →
    (∀ t y, v0.embedding (Gm t y) = (gram (XQ t) v0 (eb t y)).det) →
    ∀ (nH : ℕ) (Hm : Matrix (Fin nH) (Fin nH) K), (∀ i j, Hm i j ∈ K0) →
    (∀ v : InfinitePlace K, (Hm.map v.embedding).PosDef) →
    ∀ Pm : Matrix (Fin D) (Fin nH) K, Function.Surjective Pm.mulVec → IsQuotMetric Pm Hm (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin nH → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat Pm Mt →
    (∀ y, Gm μ0 y = gramR (quotGram Pm Hm) (eb μ0 y)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ y, Formalism.HermitianLatticesTheory.localization₂ y.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))) →

    ∀ (Sy Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ Sy →
    (∀ y ∉ Sy, lw y * ((vw y (Gm (μ y) y) : ℝ) + ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ))) = 0) →
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) = 0) →
    ∀ (LG E3 : ℝ) (E1 E2 : J → ℝ) (elly gy : HeightOneSpectrum (𝓞 K) → ℝ)
      (Fy erry Jy ηy : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, Fy y j = 0) →

    (∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y) → ∑ y ∈ Sy, lw y * gy y ≤ LG →

    (∀ y ∈ Tw, ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
        (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ)) ≤
      (∑ j, (2 * Fy y j + erry y j) + 2 / elly y ^ 2) * D) →

    (∀ y ∈ Tw, ∀ j, (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) ≤ Jy y j * D + ηy y j) →

    (∀ j, ∑ y ∈ Tw, lw y * (erry y j + Jy y j) ≤ E1 j) →
    (∀ j, ∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j) →
    ∑ y ∈ Sy, lw y * (2 / elly y ^ 2) ≤ E3 →
    ∀ (Pl : Type) [Fintype Pl] (pq : J → ℝ) (w : J → Pl → ℝ)
      (logOm x eps L b rd B0 f m k S η : ℝ)

    (q' : J → ℝ) (c1 ua : J → Pl → ℝ)
    (muU muA muN muG mmax dA dB dN dgd dbd cfl εd δd Qd Pd Λd Gd P9 : J → ℝ)
    (C1 Cf Cc Lchi llx LL0 : ℝ),

    (∀ j, -(2 * (C1 * LL0 * (∑ τ, ua j τ) + b / 4)) ≤ muU j) →
    (∀ j, cfl j =
      (∑ τ, w j τ * c1 j τ) - Cf * q' j * Real.log rd * (∑ τ, w j τ) - Cf * L) →
    (∀ j, muU j + 2 * cfl j ≤ muA j) →
    (∀ j, 0 < dA j ∧ dA j ≤ dB j ∧ (1 - εd j) * dB j ≤ dA j ∧ 0 ≤ εd j ∧ 0 ≤ Pd j) →
    (∀ j, dA j * (muA j - Pd j) + (dB j - dA j) * (-Λd j) ≤ dB j * muN j) →
    (∀ j, |2 * cfl j| ≤ Qd j ∧ Λd j ≤ Qd j ∧ εd j * Qd j ≤ b / 4) →
    (∀ j, 0 < dN j ∧ dN j = dgd j + dbd j ∧ 0 ≤ dbd j ∧ dbd j ≤ 3 * δd j * dN j ∧ 0 ≤ δd j ∧
      δd j ≤ 1 / 12) →
    (∀ j, dN j * muN j ≤ dgd j * muG j + dbd j * (mmax j + Gd j)) →
    (∀ j, |muN j| ≤ Qd j ∧ mmax j ≤ Qd j ∧ Gd j ≤ Qd j) →
    (∀ j, muG j - P9 j ≤ Formalism.HN.muDef (Pi.basisFun K (Fin D)) (XW j) (M j)) →
    (∀ j, Pd j + 12 * δd j * Qd j + P9 j ≤ b) →
    (∀ j τ, |c1 j τ + pq j * logOm / 2| ≤ Cc * q' j * (Real.log rd + Lchi)) →
    (∀ j τ, m * w j τ / 2 ≤ ua j τ ∧ ua j τ ≤ 2 * (m * w j τ + k * S + k * η)) →
    (∀ j, 1 ≤ ∑ τ, ua j τ) → (∀ j, 0 ≤ q' j ∧ q' j ≤ m) →
    0 ≤ Lchi → Lchi ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    0 ≤ C1 → 0 ≤ Cf → 0 ≤ Cc →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L →
    B0 = f * m * b * x ^ eps →
      (∀ j, lcv (XW j) (M j) / D ≤
        (∑ ρ, pq j * w j ρ * logOm) + (64 * (C1 + 3 * Cf) + 8 * Cc + 2) * B0 * llx) ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) ≤
        meanLog κ + (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * (∑ j, ∑ y ∈ Tw, lw y * Fy y j) +
          ((Fintype.card J : ℝ) * ((64 * (C1 + 3 * Cf) + 8 * Cc + 2) * B0 * llx) + LG +
            (∑ j, (E1 j + E2 j)) + E3)

end Formalism.DivisorInequality
