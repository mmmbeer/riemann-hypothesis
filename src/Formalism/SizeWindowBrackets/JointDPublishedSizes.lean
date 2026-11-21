import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.ProjectiveLineModels

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates

def HypBRam {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    {ιf : I → Type} [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u U HH δ Dstar sg η0 η1 e0 de bb x c : ℝ) : Prop :=
  LatGeom b' X' cc b X N B h v Y Y' Ball δ ∧
  LatNum b' X' cc b X N h s u HH ∧
  (∀ i, 0 < γ i) ∧
  (∀ i, Ball i = Bf i * Vr i) ∧
  (∀ i, (Vr i)ᴴ * Vr i = 1) ∧
  0 < Dstar ∧
  0 < sg ∧
  sg ≤ 1 / 20 ∧
  Dstar / sg ≤ RsG ιf ∧
  -1 ≤ η0 ∧
  η0 ≤ sg / 2 ∧
  η1 ≤ sg / 2 ∧
  0 ≤ e0 ∧
  0 ≤ de ∧
  3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg ∧
  ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf ∧
  InputSG Bf γ Dstar η0 η1 e0 ∧
  2 ≤ x ∧
  0 ≤ c ∧
  0 < bb ∧
  HH ≤ bb / sg ∧
  HH ≤ x ^ c * bb ∧
  u ≤ U ∧
  δ ≤ 1 / 7

def HypBPow {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    {ιf : I → Type} [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u U HH δ Dstar η0 η1 e0 de bb x c : ℝ) : Prop :=
  LatGeom b' X' cc b X N B h v Y Y' Ball δ ∧
  LatNum b' X' cc b X N h s u HH ∧
  (∀ i, 0 < γ i) ∧
  (∀ i, Ball i = Bf i * Vr i) ∧
  (∀ i, (Vr i)ᴴ * Vr i = 1) ∧
  0 < Dstar ∧
  x ^ (-c) ≤ 1 / 20 ∧
  Dstar * x ^ c ≤ RsG ιf ∧
  -1 ≤ η0 ∧
  η0 ≤ x ^ (-c) / 2 ∧
  η1 ≤ x ^ (-c) / 2 ∧
  0 ≤ e0 ∧
  0 ≤ de ∧
  3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-c) ∧
  ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf ∧
  InputSG Bf γ Dstar η0 η1 e0 ∧
  2 ≤ x ∧
  0 ≤ c ∧
  0 < bb ∧
  HH ≤ x ^ c * bb ∧
  u ≤ U ∧
  δ ≤ 1 / 7

def HypC {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    {ιf : I → Type} [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (muMaxM muM dr BE : I → ℝ) (Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c : ℝ) : Prop :=
  LatGeom b' X' cc b X N B h v Y Y' Ball δ ∧
  (∀ i, 0 < Fintype.card (ι i)) ∧
  WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h - muMinDef b' X' cc ≤ HH ∧
  0 ≤ HH ∧
  (∀ i, 0 ≤ dr i) ∧
  WeightedMeanLemmas.Slopes2ge (fun i => muMaxDef (b i) (X i) (N i)) (fun i => muDef (b i) (X i) (N i)) muMaxM muM dr BE
    Sg0 ∧
  (∀ i, muMaxM i ≤ A) ∧
  (∀ i, -A' ≤ muM i) ∧
  (∀ i j, |h i - h j| ≤ Vh) ∧
  (∀ i, 0 < γ i) ∧
  (∀ i, Ball i = Bf i * Vr i) ∧
  (∀ i, (Vr i)ᴴ * Vr i = 1) ∧
  0 < Dstar ∧
  0 < sg ∧
  sg ≤ 1 / 20 ∧
  Dstar / sg ≤ RsG ιf ∧
  -1 ≤ η0 ∧
  η0 ≤ sg / 2 ∧
  η1 ≤ sg / 2 ∧
  0 ≤ e0 ∧
  0 ≤ de ∧
  3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg ∧
  ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf ∧
  InputSG Bf γ Dstar η0 η1 e0 ∧
  2 ≤ x ∧
  0 ≤ c ∧
  0 < bb ∧
  HH ≤ bb / sg ∧
  HH ≤ x ^ c * bb ∧
  δ ≤ 1 / 7

def HypD {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    {ιf : I → Type} [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (σ τ : I → slopeLatticeData.FinPl K →₀ ℤ) (M N0 : ∀ i, Submodule (𝓞 K) (V i)) (β : I → slopeLatticeData.FinPl K → ℝ)
    (dr : I → ℝ) (Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c : ℝ) : Prop :=
  LatGeom b' X' cc b X N B h v Y Y' Ball δ ∧
  (∀ i, 0 < Fintype.card (ι i)) ∧
  WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h - muMinDef b' X' cc ≤ HH ∧
  0 ≤ HH ∧
  (∀ i, N i = slopeLatticeData.modLat (σ i) (N0 i)) ∧
  (∀ i, (M i).FG) ∧
  (∀ i, M i ≠ ⊥) ∧
  (∀ i, N0 i ≤ Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (τ i) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) (M i)) ∧
  (∀ i, rkK (N0 i) = rkK (M i)) ∧
  (∀ i (w : slopeLatticeData.FinPl K), ((slopeLatticeData.lenAt w (Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (τ i) : FractionalIdeal
    (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (M i)) (N0 i)).toNat : ℝ) = (rkK (M i) : ℝ) * β i w) ∧
  (∀ i, slopeLatticeData.sgSum (σ i) (τ i) = Sg0 - dr i) ∧
  (∀ i, 0 ≤ dr i) ∧
  (∀ i, muMaxDef (b i) (X i) (M i) ≤ A) ∧
  (∀ i, -A' ≤ muDef (b i) (X i) (M i)) ∧
  (∀ i j, |h i - h j| ≤ Vh) ∧
  (∀ i, 0 < γ i) ∧
  (∀ i, Ball i = Bf i * Vr i) ∧
  (∀ i, (Vr i)ᴴ * Vr i = 1) ∧
  0 < Dstar ∧
  0 < sg ∧
  sg ≤ 1 / 20 ∧
  Dstar / sg ≤ RsG ιf ∧
  -1 ≤ η0 ∧
  η0 ≤ sg / 2 ∧
  η1 ≤ sg / 2 ∧
  0 ≤ e0 ∧
  0 ≤ de ∧
  3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg ∧
  ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf ∧
  InputSG Bf γ Dstar η0 η1 e0 ∧
  2 ≤ x ∧
  0 ≤ c ∧
  0 < bb ∧
  HH ≤ bb / sg ∧
  HH ≤ x ^ c * bb ∧
  δ ≤ 1 / 7

def BRamGrouped : Prop :=
  JointBRam ↔
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u U HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    HypBRam b' X' cc b X N B h v Y Y' Ball γ Bf Vr s u U HH δ Dstar sg η0 η1 e0 de bb x c →
    s ≤ muDef b' X' cc + Real.log (Fintype.card I : ℝ) + 5 * (c + 1) * Real.log x * (U + bb) + 7 * bb

def BPowGrouped : Prop :=
  JointBPow ↔
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u U HH δ Dstar η0 η1 e0 de bb x c : ℝ),
    HypBPow b' X' cc b X N B h v Y Y' Ball γ Bf Vr s u U HH δ Dstar η0 η1 e0 de bb x c →
    s ≤ muDef b' X' cc + Real.log (Fintype.card I : ℝ) + 5 * (c + 1) * Real.log x * (U + bb) + 7 * bb

def CGrouped : Prop :=
  JointC ↔
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (muMaxM muM dr BE : I → ℝ) (Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    HypC b' X' cc b X N B h v Y Y' Ball γ Bf Vr muMaxM muM dr BE Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h ≤ muDef b' X' cc +
      Real.log (Fintype.card I : ℝ) + 5 * (c + 1) * Real.log x * (A + A' + Vh + WeightedMeanLemmas.wmean (fun i =>
      (Fintype.card (ι i) : ℝ)) (fun i => dr i + BE i) + bb) + 7 * bb

def DGrouped : Prop :=
  JointD ↔
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (σ τ : I → slopeLatticeData.FinPl K →₀ ℤ) (M N0 : ∀ i, Submodule (𝓞 K) (V i)) (β : I → slopeLatticeData.FinPl K → ℝ)
    (dr : I → ℝ) (Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c : ℝ),
    HypD b' X' cc b X N B h v Y Y' Ball γ Bf Vr σ τ M N0 β dr Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h ≤ muDef b' X' cc +
      Real.log (Fintype.card I : ℝ) + 5 * (c + 1) * Real.log x * (A + A' + Vh + WeightedMeanLemmas.wmean (fun i =>
      (Fintype.card (ι i) : ℝ)) (fun i => dr i + ∑ᶠ w : slopeLatticeData.FinPl K, 2 * slopeLatticeData.ell w * β i w) + bb) + 7 * bb

def HypPowToRam : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u U HH δ Dstar η0 η1 e0 de bb x c : ℝ),
    HypBPow b' X' cc b X N B h v Y Y' Ball γ Bf Vr s u U HH δ Dstar η0 η1 e0 de bb x c →
    HypBRam b' X' cc b X N B h v Y Y' Ball γ Bf Vr s u U HH δ Dstar (x ^ (-c)) η0 η1 e0 de bb x c

def FlatIff : Prop := TheoremFLat ↔ Formalism.HN.TheoremF

def JointDPublishedSizes : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (σ τ : I → slopeLatticeData.FinPl K →₀ ℤ) (M N0 : ∀ i, Submodule (𝓞 K) (V i)) (β : I → slopeLatticeData.FinPl K → ℝ)
    (dr : I → ℝ) (Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c k cU nT a L mB0 Loss : ℝ),
    HypD b' X' cc b X N B h v Y Y' Ball γ Bf Vr σ τ M N0 β dr Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c →
    A + A' + Vh + WeightedMeanLemmas.wmean (fun i => (Fintype.card (ι i) : ℝ))
      (fun i => dr i + ∑ᶠ w : slopeLatticeData.FinPl K, 2 * slopeLatticeData.ell w * β i w) ≤ cU * (nT * a * L + mB0 + Loss) →
    a = x * bb → 1 ≤ nT → 1 ≤ L → 0 ≤ mB0 → 0 ≤ Loss →
    Real.log (Fintype.card I : ℝ) ≤ k → k ≤ bb →
    WeightedMeanLemmas.sF (fun i => (Fintype.card (ι i) : ℝ)) (fun i => muDef (b i) (X i) (N i)) h
      ≤ muDef b' X' cc + (5 * (c + 1) * (cU + 1) + 2) * Real.log x * (nT * a * L + mB0 + Loss) + 7 * bb

def linePt (p : ℕ) : Option (ZMod p) × ZMod p → ZMod p → ZMod p × ZMod p
  | (some m, b), t => (t, m * t + b)
  | (none, b), t => (b, t)

def lineMat (p : ℕ) (i : Option (ZMod p) × ZMod p) : Matrix ((ZMod p × ZMod p) ⊕ Empty) (ZMod p) ℂ :=
  Matrix.of fun a t => if a = Sum.inl (linePt p i t) then 1 else 0

def stdLat (K n : Type) [Field K] [NumberField K] [Fintype n] : Submodule (𝓞 K) (n → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K n))

def lineMap (K : Type) [Field K] (p : ℕ) [NeZero p] (i : Option (ZMod p) × ZMod p) :
    (ZMod p → K) →ₗ[K] (ZMod p × ZMod p → K) :=
  Matrix.toLin (Pi.basisFun K (ZMod p)) (Pi.basisFun K (ZMod p × ZMod p))
    (Matrix.of fun q t => if q = linePt p i t then 1 else 0)

def inclMat (κ κ₁ : Type) [DecidableEq κ] [DecidableEq κ₁] : Matrix (κ ⊕ κ₁) κ ℂ :=
  Matrix.of fun a k => if a = Sum.inl k then 1 else 0

def ModelLinesAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 19 ≤ p → ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v : InfinitePlace K),
    ∃ (h : Option (ZMod p) × ZMod p → ℝ) (s u U HH bb : ℝ),
      HypBPow (κ₁ := Empty) (V := fun _ : Option (ZMod p) × ZMod p => ZMod p → K) (ι := fun _ => ZMod p)
        (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p))
        (fun _ => Pi.basisFun K (ZMod p)) (fun _ _ => 1) (fun _ => stdLat K (ZMod p)) (lineMap K p) h v
        (fun _ => 1) 1 (lineMat p) (fun _ => 1) (ιf := fun _ => ZMod p) (lineMat p) (fun _ => 1)
        s u U HH 0 ((p : ℝ) ^ 2) 0 0 0 0 bb ((p : ℝ) + 1) 1 ∧
      bb < HH ∧ ∀ i, lineMap K p i ≠ 0

def ModelLines : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v : InfinitePlace K),
    ∃ (h : Option (ZMod 19) × ZMod 19 → ℝ) (s u U HH bb : ℝ),
      HypBPow (κ₁ := Empty) (V := fun _ : Option (ZMod 19) × ZMod 19 => ZMod 19 → K) (ι := fun _ => ZMod 19)
        (Pi.basisFun K (ZMod 19 × ZMod 19)) (fun _ => 1) (stdLat K (ZMod 19 × ZMod 19))
        (fun _ => Pi.basisFun K (ZMod 19)) (fun _ _ => 1) (fun _ => stdLat K (ZMod 19)) (lineMap K 19) h v
        (fun _ => 1) 1 (lineMat 19) (fun _ => 1) (ιf := fun _ => ZMod 19) (lineMat 19) (fun _ => 1)
        s u U HH 0 361 0 0 0 0 bb 20 1 ∧
      bb < HH ∧ ∀ i, lineMap K 19 i ≠ 0

def ExistsModelLines : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v : InfinitePlace K),
    ∃ (h : Option (ZMod 19) × ZMod 19 → ℝ) (s u HH bb k cU nT a L mB0 Loss : ℝ),
      HypBRam (κ₁ := Empty) (V := fun _ : Option (ZMod 19) × ZMod 19 => ZMod 19 → K) (ι := fun _ => ZMod 19)
        (Pi.basisFun K (ZMod 19 × ZMod 19)) (fun _ => 1) (stdLat K (ZMod 19 × ZMod 19))
        (fun _ => Pi.basisFun K (ZMod 19)) (fun _ _ => 1) (fun _ => stdLat K (ZMod 19)) (lineMap K 19) h v
        (fun _ => 1) 1 (lineMat 19) (fun _ => 1) (ιf := fun _ => ZMod 19) (lineMat 19) (fun _ => 1)
        s u (cU * (nT * a * L + mB0 + Loss)) HH 0 361 (1 / 20) 0 0 0 0 bb 20 1 ∧
      a = 20 * bb ∧ 1 ≤ nT ∧ 1 ≤ L ∧ 0 ≤ mB0 ∧ 0 ≤ Loss ∧
      Real.log (Fintype.card (Option (ZMod 19) × ZMod 19) : ℝ) ≤ k ∧ k ≤ bb

end Formalism.LFunctionChainParameters.ProjectiveLineModels
