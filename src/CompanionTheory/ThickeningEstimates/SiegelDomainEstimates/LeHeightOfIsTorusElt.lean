import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

section
noncomputable section

namespace CompanionTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F E) in

abbrev Ten (n d : ℕ) : Type := Matrix (Fin n) (Fin d) (AE F E)

variable (σ) in

def EpsHerm {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop :=
  ((∀ i j, σ (J j i) = J i j) ∨ ∀ i j, σ (J j i) = -J i j) ∧ J.det ≠ 0

variable (F) in

def rId (t : ℝ) : AF F := 1 + realAd F (Real.exp t - 1)

variable (σ) in

structure Frame {n : ℕ} (J : Matrix (Fin n) (Fin n) E) where

  r : ℕ

  x : Fin r → Fin n → E

  y : Fin r → Fin n → E

  a : (Fin r → ℝ) → UA σ J

structure Frame.IsGood {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (fr : Frame σ J) : Prop where
  xx : ∀ i j, form σ J (fr.x i) (fr.x j) = 0
  yy : ∀ i j, form σ J (fr.y i) (fr.y j) = 0
  xy : ∀ i j, form σ J (fr.x i) (fr.y j) = if i = j then 1 else 0
  aniso : ∀ u, (∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0) → form σ J u u = 0 → u = 0
  add : ∀ s t, fr.a (s + t) = fr.a s * fr.a t
  cont : Continuous fr.a
  ax : ∀ t i, mat (fr.a t) *ᵥ incV F (fr.x i) = rId F (t i) • incV F (fr.x i)
  ay : ∀ t i, mat (fr.a t) *ᵥ incV F (fr.y i) = rId F (-t i) • incV F (fr.y i)
  a0 : ∀ t u, (∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0) → mat (fr.a t) *ᵥ incV F u = incV F u

def Cone (r : ℕ) : Set (Fin r → ℝ) := {t | Antitone t ∧ ∀ i, 0 ≤ t i}

section Pair

variable {n d : ℕ}

def sz (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : Ten F E n d) : ℝ := ∑ w, ∑ i, ∑ j, ‖piInf (τ w) (z i j)‖

open Classical in

def maj (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) : ℝ :=
  if ∃ c ∈ C, At (evI F) (z - c) then ((1 + sz τ z) ^ N)⁻¹ else 0

scoped instance measAdPi {κ : Type} : MeasurableSpace (κ → AF F) := borel _

variable (F) in

def coef {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F)) (Φ₁ Φ₂ : (κ → AF F) → ℂ)
    (w : (κ → AF F) × (κ → AF F)) : ℂ := ∫ u, schr ψ w Φ₁ u * (starRingEnd ℂ) (Φ₂ u) ∂μ

variable {X : Spc F E n} {W : Spc F E d}

end Pair

end CompanionTheory.ThKEst

end
end

section
noncomputable section

namespace CompanionTheory.ThKEst.Sieg

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem realAd_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((realAd F t).1 w) = t := by
  have hw := IsTotallyReal.isReal w
  have e := congrArg (fun z => z.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t))
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact congrArg _ e

theorem rId_snd (t : ℝ) : (rId F t).2 = 1 := add_zero _

theorem rId_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((rId F t).1 w) = Real.exp t := by
  change InfinitePlace.Completion.extensionEmbedding w (1 + (realAd F (Real.exp t - 1)).1 w) = _
  rw [map_add, map_one, realAd_inf]
  push_cast
  ring

theorem rId_add [IsTotallyReal F] (s t : ℝ) : rId F (s + t) = rId F s * rId F t := by
  refine Prod.ext (funext fun w => (InfinitePlace.Completion.extensionEmbedding w).injective ?_) ?_
  · change _ = InfinitePlace.Completion.extensionEmbedding w ((rId F s).1 w * (rId F t).1 w)
    rw [map_mul, rId_inf, rId_inf, rId_inf, Real.exp_add, Complex.ofReal_mul]
  · change _ = (rId F s).2 * (rId F t).2
    rw [rId_snd, rId_snd, rId_snd, mul_one]

theorem rId_zero' : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

variable {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

end CompanionTheory.ThKEst.Sieg

end
end
