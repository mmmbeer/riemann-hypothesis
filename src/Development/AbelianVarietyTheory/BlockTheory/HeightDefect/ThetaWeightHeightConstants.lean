import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParamsT

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

open Formalism.BasicNotions NumberField

def Lift (R : Ranks) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

def pSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).1

def qSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).2

theorem pSig_pos {R : Ranks} (j : Lift R) : 0 < pSig j := by
  have := R.m_add_three_le_k; have := j.2.1
  simp only [pSig, Ranks.sigW]; omega


def IsTotIsotropic {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (U : Submodule E S.V) : Prop := ∀ x ∈ U, ∀ y ∈ U, S.hD x y = 0

def isotropicDims {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : Set ℕ :=
  {n | ∃ U : Submodule E S.V, IsTotIsotropic S U ∧ Module.finrank E U = n}

def wittIndexOf {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : ℕ :=
  sSup (isotropicDims S)


def wittIndex (D : D7) (j : Lift D.R) : ℕ :=
  letI := D.host.cmStar; wittIndexOf (D.sp.W j.1)

def rho {R : Ranks} (j : Lift R) : ℕ := R.m - j.1


def dPrime {R : Ranks} (j : Lift R) : ℕ := 2 * R.f * rho j


def dimBase {R : Ranks} (j : Lift R) : ℕ := R.f * pSig j * qSig j

def dimFlag {R : Ranks} (j : Lift R) : ℕ :=
  dimBase j + R.f * (pSig j * (pSig j - 1) / 2 + qSig j * (qSig j - 1) / 2)

def RR (D : D7) : ℝ := D.host.rdE ^ 7

def PP {D : D7} (L : SizeData₂ D) (C e : ℝ) : ℝ := C * ((D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L) ^ e


def lrd (D : D7) : ℝ := Real.log D.host.rdE

def lc (D : D7) : ℝ := Real.log (Ideal.absNorm D.host.ccK : ℝ)

def PU (D : D7) (n : ℕ) : ℝ :=
  (D.R.f : ℝ) * n * (2 * lrd D + 2 * Real.log ((D.R.f : ℝ) * n) + 3)

def SizeRows {D : D7} (L : SizeData₂ D) : Prop :=
  D.R.m ^ 2 ≤ D.R.r ∧ (∀ i, Real.log (D.host.g i : ℝ) ≤ 9 * L.sc.L + 1) ∧ lc D ≤ L.sc.L

@[ext] structure ThetaWeight (D : D7) (j : Lift D.R) where
  plus : D.what₂.Tau → Fin (pSig j) → ℤ
  minus : D.what₂.Tau → Fin (qSig j) → ℤ
  plus_anti : ∀ τ, Antitone (plus τ)
  minus_anti : ∀ τ, Antitone (minus τ)
  n : ℕ

namespace ThetaWeight

variable {D : D7} {j : Lift D.R}

def add (G G' : ThetaWeight D j) : ThetaWeight D j where
  plus := G.plus + G'.plus
  minus := G.minus + G'.minus
  plus_anti τ := (G.plus_anti τ).add (G'.plus_anti τ)
  minus_anti τ := (G.minus_anti τ).add (G'.minus_anti τ)
  n := G.n + G'.n

def nsmul (N : ℕ) (G : ThetaWeight D j) : ThetaWeight D j where
  plus τ i := N * G.plus τ i
  minus τ i := N * G.minus τ i
  plus_anti τ _ _ h := mul_le_mul_of_nonneg_left (G.plus_anti τ h) (by positivity)
  minus_anti τ _ _ h := mul_le_mul_of_nonneg_left (G.minus_anti τ h) (by positivity)
  n := N * G.n

def DF (G : ThetaWeight D j) : ℤ := ∑ τ, ((∑ i, G.plus τ i) + ∑ i, G.minus τ i)

def size (G : ThetaWeight D j) : ℤ :=
  G.DF + ((D.R.f * max (rho j) 1 * D.R.r * G.n : ℕ) : ℤ) + 1

def plusLast (G : ThetaWeight D j) (τ : D.what₂.Tau) : ℤ :=
  G.plus τ ⟨pSig j - 1, Nat.sub_lt (pSig_pos j) one_pos⟩

def Dominant (G : ThetaWeight D j) : Prop := ∀ τ, (∀ i, 0 ≤ G.plus τ i) ∧ ∀ i, 0 ≤ G.minus τ i

def PlusLastPos (G : ThetaWeight D j) : Prop := ∀ τ, 1 ≤ G.plusLast τ

end ThetaWeight

def staircase (D : D7) (j : Lift D.R) : ThetaWeight D j where
  plus _ i := (pSig j : ℤ) - i.1
  minus _ i := (qSig j : ℤ) - i.1
  plus_anti _ a b h := by have : a.1 ≤ b.1 := h; simp only; omega
  minus_anti _ a b h := by have : a.1 ≤ b.1 := h; simp only; omega
  n := 2

example (D : D7) (j : Lift D.R) :
    (staircase D j).Dominant ∧ (staircase D j).PlusLastPos ∧ Even (staircase D j).n := by
  refine ⟨fun τ => ⟨fun i => ?_, fun i => ?_⟩, fun τ => ?_, by simp [staircase]⟩
  · have := i.2; simp only [staircase]; omega
  · have := i.2; simp only [staircase]; omega
  · have := pSig_pos j; simp only [ThetaWeight.plusLast, staircase]; omega

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

end
