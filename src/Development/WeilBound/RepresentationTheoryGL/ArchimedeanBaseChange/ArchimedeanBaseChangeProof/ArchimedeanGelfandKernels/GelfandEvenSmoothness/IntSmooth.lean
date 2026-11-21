import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Mult

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def EpowT (s : Bool) : ℕ → Fin n → Fin n → (Mat n → V) → (Mat n → V)
  | 0, a, b => fun f => if a = b then f else 0
  | m + 1, a, b => fun f => ∑ c, Eu s c a (EpowT s m c b f)

def gelT (s : Bool) (m : ℕ) (f : Mat n → V) : Mat n → V := ∑ a, EpowT s m a a f

def zAdj : List (Bool × ℕ) → (Mat n → V) → (Mat n → V)
  | [] => id
  | p :: w => fun h => zAdj w (((-1 : ℂ) ^ p.2) • gelT (!p.1) p.2 h)

end Ops

def kAdj (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Mat n → (E.V →L[ℂ] E.V) :=
  haveI := FiniteDimensional.complete ℂ E.V
  fun y => ContinuousLinearMap.adjoint (k y⁻¹)

def KReg {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (k : Mat n → (W →L[ℂ] W)) : Prop :=
  ContinuousOn k (GLs n) ∧ ∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0

def REq (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂

def Hyp : Prop := LgFacts ∧ Unimod ∧ RCalc ∧ WaveSpeed ∧ WaveEx ∧ KerUniq ∧ KerOne

def KerAgree : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k₁ k₂ : Mat n → (E.V →L[ℂ] E.V)),
  KReg k₁ → KReg k₂ → REq E k₁ → REq E k₂ → (∀ u, IsWave E u → Cpt (u 0) → act μ E k₁ (u 0) 1 = act μ E k₂ (u 0) 1) →
    ∀ y ∈ GLs n, k₁ y = k₂ y

def KerBasic : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (k : Mat n → (E.V →L[ℂ] E.V)),
  IsKer μ E w g k → KReg k ∧ REq E k ∧ KReg (kAdj E k) ∧ REq E (kAdj E k)

def IntSmooth : Prop := ∀ (n : ℕ) (H V : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V] (F : ℝ → H → Mat n → V) (g : ℝ → ℝ) (T : ℝ), IsBump g T →
  ContDiffOn ℝ ∞ (fun p : ℝ × H × Mat n => F p.1 p.2.1 p.2.2) (Set.univ ×ˢ (Set.univ ×ˢ GLs n)) →
    ContDiffOn ℝ ∞ (fun q : H × Mat n => ∫ t, (g t : ℂ) • F t q.1 q.2) (Set.univ ×ˢ GLs n)

def ZLin : Prop := RCalc → ∀ n : ℕ, (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × ℕ)) (f h : Mat n → V) (a b : ℂ),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) →
      ContDiffOn ℝ ∞ (zOp w f) (GLs n) ∧ ContDiffOn ℝ ∞ (Om f) (GLs n) ∧
      ∀ x ∈ GLs n, zOp w (fun y => a • f y + b • h y) x = a • zOp w f x + b • zOp w h x ∧
        Om (fun y => a • f y + b • h y) x = a • Om f x + b • Om h x) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × ℕ)) (f f' : Mat n → V), Set.EqOn f f' (GLs n) →
    ∀ x ∈ GLs n, zOp w f x = zOp w f' x ∧ Om f x = Om f' x) ∧
  ∀ (E : KMod n) (w : List (Bool × ℕ)), ∀ f ∈ CE E, zOp w f ∈ CE E ∧ Om f ∈ CE E

def AdjWave : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)),
  IsBump g T → IsKer μ E w g k → ∀ u, IsWave E u → Cpt (u 0) →
    ∀ x ∈ GLs n, act μ E (kAdj E k) (u 0) x = zAdj w (fun y => ∫ t, (g t : ℂ) • u t y) x

end PositivityTheory.RgBcC.Mult
