import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PBrDiv

open Module NumberField Matrix IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6.Triv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)

section DefsD'
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsD'

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

def rT (f T : ℕ) : ℕ := (T - 2) ^ f

def r1T (f T : ℕ) : ℕ := (T - 1) ^ f - (T - 2) ^ f

def Jm (r r1 : ℕ) : Matrix (Fin (r + r1)) (Fin r) ℂ := (1 : Matrix (Fin (r + r1)) (Fin (r + r1)) ℂ).submatrix id (Fin.castAdd r1)

def Jm1 (r r1 : ℕ) : Matrix (Fin (r + r1)) (Fin r1) ℂ := (1 : Matrix (Fin (r + r1)) (Fin (r + r1)) ℂ).submatrix id (Fin.natAdd r)

def jL (r r1 : ℕ) : (Fin r → K) →ₗ[K] (Fin (r + r1) → K) where
  toFun x := Fin.append x 0
  map_add' x y := by
    ext a; refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> simp [Fin.append_left, Fin.append_right]
  map_smul' c x := by
    ext a; refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> simp [Fin.append_left, Fin.append_right]

def trivC (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ) : FamC (Fin Mw) m where
  K := K
  Wd := Fin (rT f T) → K
  Dall := rT f T + r1T f T
  D := rT f T
  D1 := r1T f T
  V := fun _ => Fin (rT f T) → K
  r := fun _ => rT f T
  Vf := fun _ => Fin (rT f T + r1T f T) → K
  d := fun _ => rT f T + r1T f T
  b' := Pi.basisFun K _
  X' := fun _ => 1
  cc := stdLat K _
  b := fun _ => Pi.basisFun K _
  X := fun _ _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1
  M := fun _ => stdLat K _
  N0 := fun _ => Formalism.HermitianLatticesTheory.idealSmul
    ((slopeLatticeData.idealPow (tau0 K 2 0) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K _)
  bf := fun _ => Pi.basisFun K _
  Xf := fun _ _ => 1
  Mf := fun _ => stdLat K _
  j := fun _ => jL K (rT f T) (r1T f T)
  σ := fun _ => tau0 K 2 0
  τ := tau0 K 2 0
  B := fun _ => LinearMap.id
  v := v
  Y := fun _ => 1
  Y' := 1
  Pf := fun _ => 1
  Vr := fun _ => Jm (rT f T) (r1T f T)
  ga := fun _ => 1
  c := fun _ => 1
  Vrow := 1
  U := fun _ => 1
  J := Jm (rT f T) (r1T f T)
  J1 := Jm1 (rT f T) (r1T f T)
  S := lm_S K Q
  gain := fun j w => gn j (prBelow w)
  Fj := fun j w => bump K m gE w - gn j (prBelow w)
  Ej := fun _ _ w => bump K m gE w
  iop := fun _ => 0
  T := fun _ => T
  h := fun _ => max (htMap (Pi.basisFun K (Fin (rT f T)))
    (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (Pi.basisFun K (Fin (rT f T))) (fun _ => 1)
    LinearMap.id) hb
  lam := fun _ => 0
  Dstar := ((rT f T + r1T f T : ℕ) : ℝ)
  η0 := 0
  η1 := 0
  e0 := 0

def trivR (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ) :
    Rows (trivC K v m f T Mw hb gE Q gn).toFam where
  D := rT f T
  XE := fun _ => 1
  R := stdLat K _
  ψ := ((Pi.basisFun K (Fin (rT f T))).dualBasis.equivFun : Module.Dual K (Fin (rT f T) → K) ≃ₗ[K] (Fin (rT f T) → K)).toLinearMap

theorem int_mul {a c : K} (ha : a ∈ Set.range (algebraMap (𝓞 K) K)) (hc : c ∈ Set.range (algebraMap (𝓞 K) K)) :
    a * c ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨c', rfl⟩ := hc
  exact ⟨a' * c', by simp⟩

section T
variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ)

end T

section SlopeTestRemainingChoices
variable (r r1 : ℕ)

def piL : (Fin (r + r1) → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x := fun i => x (Fin.castAdd r1 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SlopeTestRemainingChoices

section P
variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ)

end P

def Xlev (T : ℕ) (k : ℝ) : ℝ := ((T : ℝ) ^ k - 1) ^ (1 / k)

section Gen
variable (v0 : InfinitePlace K)
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
  (D : ArithData H) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (T : H → ℕ)
  (Mw : ℕ) (gE : ℝ)

def ObjT (k Sc : ℝ) (btH : H → ℝ) (bN : H → Fin m → Fin (PhiSet (H := H)).card → ℝ) :
    SizeCountLevelObjects H (fun _ => Fin Mw) m TT where
  X := fun u0 _ => Xlev (T u0) k
  dst := fun u0 _ => ((rT (PhiSet (H := H)).card (T u0) + r1T (PhiSet (H := H)).card (T u0) : ℕ) : ℝ)
    / ((T u0 : ℝ) ^ k - 1) ^ (PhiSet (H := H)).card
  bN := bN
  Gam := 1
  Sc := Sc
  LZ := 0
  aM := 0
  Wt := fun _ => 0
  bt := fun t => btH t
  VV := fun _ _ => ∅

theorem sum_top (φ : H → ℝ) : ∑ t ∈ TT.map (topPhi H), φ t.1.2 = ∑ t ∈ TT, φ t := by
  rw [Finset.sum_map]; rfl

end Gen

section Gen2
variable (v0 : InfinitePlace K)
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
  (D : ArithData H) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (T : H → ℕ)
  (Mw : ℕ) (gE : ℝ)

end Gen2

end Formalism.LFunctionChainParameters.LChain6.Triv

namespace Formalism.LFunctionChainParameters.LChain6

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer

end Formalism.LFunctionChainParameters.LChain6
