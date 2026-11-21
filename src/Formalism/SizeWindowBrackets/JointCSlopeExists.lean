import Formalism.SizeWindowBrackets.CutFailsForRSubmodule
import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic

open Module NumberField
open scoped Pointwise

noncomputable section

namespace Formalism.LFunctionChainParameters.LJC

open Formalism.HN Formalism.LFunctionChainParameters.slopeLatticeData Formalism.LFunctionChainParameters.DiagonalSublatticeLength

section Str

variable {K : Type} [Field K] [NumberField K]

def rlocToK (w : FinPl K) : Rloc w →+* K :=
  haveI := w.2.isPrime
  IsLocalization.lift (M := w.1.primeCompl) (S := Rloc w) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ fun h0 => y.2 ?_
    have : (y : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0)
    rw [this]; exact Ideal.zero_mem _)

@[reducible] def rlocAlgebra (w : FinPl K) : Algebra (Rloc w) K := (rlocToK w).toAlgebra

@[reducible] def rlocModule (w : FinPl K) (V : Type) [AddCommGroup V] [Module K V] : Module (Rloc w) V :=
  Module.compHom V (rlocToK w)

end Str

section Defs

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

def SmithLoc (w : FinPl K) [Module (Rloc w) V] (ϖ : 𝓞 K) (M N : Submodule (𝓞 K) V) {d : ℕ}
    (e : Fin d → ℕ) : Prop :=
  ∃ c : Basis (Fin d) (Rloc w) (Submodule.span (Rloc w) (M : Set V)),
    Submodule.span (Rloc w) (N : Set V) =
      Submodule.span (Rloc w) (Set.range fun i => ϖ ^ e i • (c i : V))

def SmithAt (w : FinPl K) (ϖ : 𝓞 K) (M N : Submodule (𝓞 K) V) {d : ℕ} (e : Fin d → ℕ) : Prop :=
  letI := rlocModule w V
  SmithLoc w ϖ M N e

def idl (τ : FinPl K →₀ ℤ) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Formalism.HermitianLatticesTheory.idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) L

def cutG [IsScalarTower (𝓞 K) K V] (τ : FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V)
    (V' : Submodule K V) : Submodule (𝓞 K) V :=
  N ⊓ idl τ M ⊓ V'.restrictScalars (𝓞 K)

def posSum {d : ℕ} (e : Fin d → ℕ) (t : ℤ) : ℕ := ∑ i, ((e i : ℤ) - t).toNat

end Defs

def JointCSlopeExists : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (σ τ : FinPl K →₀ ℤ), (∀ w, 0 ≤ τ w) → ∀ (M N : Submodule (𝓞 K) V), M.FG →
      Submodule.span K (M : Set V) = ⊤ → N ≤ M → Submodule.span K (N : Set V) = ⊤ →
    ∀ V' : Submodule K V, V' ≠ ⊥ →
    ∃ (ϖ : FinPl K → 𝓞 K) (e : FinPl K → Fin (finrank K V) → ℕ),
      (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) ∧ (∀ w, SmithAt w (ϖ w) M N (e w)) ∧
      (∀ w, lenAt w M N = ((∑ i, e w i : ℕ) : ℕ∞)) ∧
      (Function.support fun w : FinPl K => posSum (e w) (τ w)).Finite ∧
      muMaxDef b X (modLat σ (cutG τ M N V')) ≤ muMaxDef b X (latV M V') + sgSum σ τ ∧
      muDef b X (latV M V') + sgSum σ τ
          - ∑ᶠ w : FinPl K, 2 * ell w * ((posSum (e w) (τ w) : ℝ) / (finrank K V' : ℝ)) ≤
        muDef b X (modLat σ (cutG τ M N V'))

section Real

variable {ι κ : Type*} [DecidableEq ι]

def HypLowC (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ 0 < dM ∧ 0 ≤ de ∧ de < 1 ∧ du = (1 - de) * dM ∧ WT ⊆ W ∧
  (∀ w ∈ WT, tau w = 0) ∧ (∀ w ∈ W, 0 ≤ io w) ∧
  (∀ w ∈ W \ WT, len w ≤ du * tau w + dM * io w) ∧
  ∑ w ∈ WT, 2 * l w * len w / du ≤ PT ∧
  ∑ w ∈ W, 2 * l w * (UnitWeightPartition.sgw J gain F E w - sg' w) ≤ Rd ∧
  muN = muMu + UnitWeightPartition.Sg W l sg' tau - UnitWeightPartition.BeSum W l du len tau

end Real

end Formalism.LFunctionChainParameters.LJC
