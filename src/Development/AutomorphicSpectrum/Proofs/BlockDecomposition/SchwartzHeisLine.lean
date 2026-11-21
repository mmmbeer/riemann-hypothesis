import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralsAgreeOf

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc Model Rep Base Geo Chars RealMaps FinMaps pure PolMatch IsMatched Decay OneConst Coinv IsConst)
open GlobalTheory.WeilM (SB schA)

variable {D : D7}

structure PairSit (ε : Bool) {M X : HSp D} (θ : InfFam D) (A : Fr M) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) {Y : Spc D.host.F D.host.E M.rank} {Z : Spc D.host.F D.host.E d}
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X) : Prop where

  fam : IsInfFam θ

  base : Bs.IsGood D.sp.cm.sig

  good : Mo.IsGood Bs.ψ

  weilD : Mo.IsWeil Bs.ψ χ₁ χ₂ om

  weil : IsWeil Bs.ψ ε M X χ₁ χ₂ ω

  dict : IsDict (ε := ε) e Bs.ψ ω Mo om c hY hZ

  herm : ∃ r s, Y.IsHerm D.sp.cm.sig Bs r s

  skew : ∃ r s, Z.IsSkew D.sp.cm.sig Bs r s

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Y.θ w = (if ε then (1 : ℂ) else -1) • A.cart τ ∧
    Z.θ w = (reindex e e (B.cart τ)).map conj

structure Sit {W W₁ X : HSp D} (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank) : Prop where

  fam : IsInfFam θ

  tri : IsTriple W W₁ X α β

  hν : IsHaarFD W ν 𝓕

  hν₁ : IsHaarFD W₁ ν₁ 𝓕₁

  weilA : IsWeil Bs.ψ true W X β (β / α) ωA

  weilB : IsWeil Bs.ψ false W₁ X α (α / β) ωB

  read : IsReading Bs.ψ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ Bs Γ Xc

  dictA : IsDict (ε := true) e Bs.ψ ωA Γ.M om 1 read.JW read.JX

  dictB : IsDict (ε := false) e Bs.ψ ωB Γ.M' om' (-1) read.JW₁ read.JX

  matched : IsMatched Bs Γ Xc om om' R Rf

  decay : Decay Bs Γ om om'

  const : OneConst Bs Γ Xc om om' R Rf

  coinv : Coinv Bs Γ Xc om om' Rf

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO GlobalTheory.CompanionTheory.AgreeO.Sys
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (evI realAd At tens Rest IsStd SInf)
open GlobalTheory.WeilM (schr)
open scoped SchwartzMap LineDeriv

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  simp [evI, realAd]

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  simp [linForm, map_sum, LinearMap.sum_apply]

open scoped Classical in

theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add, map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]

end GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
end
