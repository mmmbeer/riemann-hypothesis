import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec eulerFac seg)
open Formalism.UG (qV IsUnifV dosetInd)

namespace GlobalTheory.CompanionTheory.Ipf.Val

section Local

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev Cv : Type := v.adicCompletion K

def absV (x : Cv v) : ℝ := (WithZeroMulInt.toNNReal (NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ)

def IsPar (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))) : Prop :=
  ∀ k, k ∈ J ↔ k ∈ KGL v (r + c) ∧ ∀ i j, Valued.v (bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)) i j) < 1

def IsTame (δ : (Cv v)ˣ →* ℂˣ) : Prop :=
  (∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1) ∧ ∀ x : (Cv v)ˣ, Valued.v ((x : Cv v) - 1) < 1 → δ x = 1

def IsRam (δ : (Cv v)ˣ →* ℂˣ) : Prop := ∃ x : (Cv v)ˣ, Valued.v (x : Cv v) = 1 ∧ δ x ≠ 1

def lamD {r c : ℕ} (δ : (Cv v)ˣ →* ℂˣ) (k : GL (Fin (r + c)) (Cv v)) : ℂ :=
  chi0 δ (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v))).det

def blk (r : ℕ) {c : ℕ} (m : GL (Fin c) (Cv v)) : GL (Fin (r + c)) (Cv v) := pEl (1 : GL (Fin r) (Cv v)) 0 m

def IsDiag {c : ℕ} (ϖ : Cv v) (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)) : Prop := m.1 = Matrix.diagonal fun i => ϖ ^ d i

def len {c : ℕ} (d : Fin c → ℤ) : ℕ := ∑ i, (d i).natAbs

def IsBlockDoubleCosetFunction {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) (m : GL (Fin c) (Cv v))
    (h : GL (Fin (r + c)) (Cv v) → ℂ) : Prop :=
  (∀ k₁ ∈ J, ∀ k₂ ∈ J, h (k₁ * blk v r m * k₂) = (lamD v δ k₁ * lamD v δ (blk v r m) * lamD v δ k₂)⁻¹) ∧
    ∀ g, g ∉ DoubleCoset.doubleCoset (blk v r m) (J : Set _) J → h g = 0

def IsSphEig {c : ℕ} (B : Multiset ℂˣ) (m : GL (Fin c) (Cv v)) (lam : ℂ) : Prop :=
  ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module ℂ V₀) (ρ₀ : Representation ℂ (GL (Fin c) (Cv v)) V₀) (x₀ : V₀),
    IsSatVecGL v ρ₀ x₀ B ∧ heckeVec ρ₀ (KGL v c) (dosetInd ℂ (KGL v c) m) x₀ = lam • x₀

def IsBlockVector {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ) : Prop :=
  B.card = c ∧ (∀ k ∈ J, ρ k x = lamD v δ k • x) ∧
    ∀ ϖ, IsUnifV K v ϖ → ∀ (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)), IsDiag v ϖ d m → ∀ lam, IsSphEig v B m lam →
      ∀ h, IsBlockDoubleCosetFunction v J δ m h → heckeVec ρ J h x = ((qV K v : ℂ) ^ ((r : ℂ) / 2 * len d) * lam) • x

def phiB (δ : (Cv v)ˣ →* ℂˣ) (r d c : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) : ℂ :=
  open Classical in
  if (∀ i j, Valued.v (x i j) ≤ 1) ∧ Valued.v (bAA x).det = 1 ∧ ∀ i j, Valued.v (bDA x i j) < 1 then chi0 δ (bAA x).det else 0

def linAct {a b : ℕ} (δS δT : (Cv v)ˣ →* ℂˣ) (g : GL (Fin a) (Cv v)) (h : GL (Fin b) (Cv v))
    (Φ : Matrix (Fin b) (Fin a) (Cv v) → ℂ) : Matrix (Fin b) (Fin a) (Cv v) → ℂ :=
  fun y => (((δT (Matrix.GeneralLinearGroup.det g))⁻¹ * δS (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
    ((absV v g.1.det ^ ((b : ℝ) / 2) * absV v h.1.det ^ (-(a : ℝ) / 2) : ℝ) : ℂ) * Φ ((h⁻¹).1 * y * g.1)

end Local

def BlockDoubleCosetFunctionsExist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ),
    (∃ J, IsPar v r c J) ∧ ∀ J, IsPar v r c J → ∀ δ, IsTame v δ → ∀ m, ∃ h, IsBlockDoubleCosetFunction v J δ m h

def SphMatchAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c t : ℕ) (ϖ : Cv v), IsUnifV K v ϖ →
    ∀ m' : GL (Fin (c + t)) (Cv v), ∃ (I : Finset (Fin c → ℤ)) (a : (Fin c → ℤ) → ℂ) (m : (Fin c → ℤ) → GL (Fin c) (Cv v)),
      (∀ e, IsDiag v ϖ e (m e)) ∧
      (∀ y, (∑ᶠ z : GL (Fin (c + t)) (Cv v) ⧸ KGL v (c + t), dosetInd ℂ (KGL v (c + t)) m' z.out *
          linAct v 1 1 (1 : GL (Fin c) (Cv v)) z.out (Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1) y) =
        ∑ e ∈ I, a e * ∑ᶠ z : GL (Fin c) (Cv v) ⧸ KGL v c, dosetInd ℂ (KGL v c) (m e) z.out *
          linAct v 1 1 z.out (1 : GL (Fin (c + t)) (Cv v)) (Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1) y) ∧
      ∀ (B : Multiset ℂˣ) (lam : (Fin c → ℤ) → ℂ), (∀ e, IsSphEig v B (m e)⁻¹ (lam e)) →
        IsSphEig v (B + seg v 1 t) m' (∑ e ∈ I, a e * lam e)

def BlockUnramifiedTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))),
    IsPar v r c J → ∀ δ ν : (Cv v)ˣ →* ℂˣ, IsTame v δ → IsTame v ν → ¬ IsRam v ν → ∀ z : ℂˣ,
    (∀ ϖ : (Cv v)ˣ, IsUnifV K v (ϖ : Cv v) → ν ϖ = z) →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ),
      IsBlockVector v J δ ρ x B → IsBlockVector v J (δ * ν) ρ x (B.map (z⁻¹ * ·))

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FinZeta (projV embV Kv Gv)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsIdemOf IsProjAt rdA grpCo frCo)
open GlobalTheory.CompanionTheory.Ipf.Loc (FPl)

variable {D : D7}

end Adelic

end GlobalTheory.CompanionTheory.Ipf.Val

end
