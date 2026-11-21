import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.GlobalTheory.GL3.PUnitBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFourSq
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Formalism.FrobeniusOrbits Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def LinkStdOK : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.StdOK

def LinkVecB : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → NonzeroThetaVectorFamily D (tor0 D cc δ) (B.eNat χ)

def LinkThB : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ →
      ThetaNormIndependent D (tor0 D cc δ) (B.eNat χ) ∧ th22U D (tor0 D cc δ) (B.eNat χ)

def LinkExistsBase : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∃ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

theorem vector_bound_link : LinkVecB :=
  fun D cc hcc δ hδ B => vector_link_holds D cc hcc δ hδ B (SO.stdOK B hcc hδ)



def LinkPeriodPair : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → ∀ δ : ℂ, δ ≠ 0 →
    ∃ L : PeriodPair, L.lattice.toAddSubgroup = lamOf D cc δ

def BasePointExists : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 →
    ∃ t : ℂ, Formalism.L2.Ker.Cd.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t

def IsoExists (D : Car) : Prop :=
  ∃ (γ₀ : IsoK D) (gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
    ∀ x : Fin 4 → D.host.E, gC (fun w => embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)

def IsoPExists (D : Car) : Prop :=
  ∀ p : ℕ, p.Prime → SplitK D p → ∃ γ : IsoK D, γ.AtP p

def LinkBase : Prop :=
  ∀ D : Car, IsoExists D → IsoPExists D → BaseExists D





theorem ext_exists {K E : Type} [Field K] [Field E] [Algebra K E] {I : Type} [Fintype I] [DecidableEq I]
    (g : (Fin 4 → E) ≃ₗ[K] (I → K)) (φ : K →+* ℂ) (em : (Fin 4 → E) →+ (I → ℂ))
    (hem : ∀ (k : K) (y : Fin 4 → E), em (k • y) = φ k • em y)
    (hspan : Submodule.span ℂ (Set.range em) = ⊤) :
    ∃ G : (I → ℂ) ≃ₗ[ℂ] (I → ℂ), ∀ x, G (em x) = fun w => φ (g x w) := by
  have repr : ∀ x, x = ∑ v, (g x v) • g.symm (Pi.single v 1) := by
    intro x
    apply g.injective
    rw [map_sum]
    simp_rw [map_smul, LinearEquiv.apply_symm_apply]
    funext w
    simp [Finset.sum_apply, Pi.single_apply]
  let hC : (I → ℂ) →ₗ[ℂ] (I → ℂ) :=
    { toFun := fun c => ∑ v, c v • em (g.symm (Pi.single v 1))
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.smul_sum, mul_smul] }
  have key : ∀ x, hC (fun w => φ (g x w)) = em x := by
    intro x
    conv_rhs => rw [repr x]
    rw [map_sum]
    simp_rw [hem]
    rfl
  have hsurj : Function.Surjective hC := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, key x⟩
  have hinj : Function.Injective hC := LinearMap.injective_iff_surjective.2 hsurj
  refine ⟨(LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
  rw [← key x]
  exact LinearEquiv.symm_apply_apply (LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩) _

def LinkIsoExt : Prop := ∀ D : Car, Nonempty (IsoK D) → IsoExists D


def DiscrNe (D : Car) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → discr (lamOf D cc 1) ≠ 0

def IsometryExtensionLink : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D → Nonempty (IsoK D) → IsoPExists D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C


end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.G0

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Formalism.FrobeniusOrbits Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem rat_mem (t : ℚ) : (t : D.host.E) ∈ D.host.K := by
  rw [← eq_ratCast (algebraMap ℚ D.host.E) t]; exact D.host.K.algebraMap_mem t

theorem conj_b : D.host.conj (D.host.sqd) = -D.host.sqd := by
  apply D.host.φ₀.injective
  rw [CU.emb_conj, map_neg, CS.embedding_sqrt_neg_d, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem conj_mem (k : D.host.K) : D.host.conj (k : D.host.E) ∈ D.host.K := by
  obtain ⟨p, q, e⟩ := CS.K_repr D _ k.2
  rw [e, map_add, map_mul, map_ratCast, map_ratCast, conj_b]
  exact add_mem (rat_mem D p) (mul_mem (rat_mem D q) (neg_mem (FL.bE_mem D)))

def cK : D.host.K →+* D.host.K where
  toFun k := ⟨D.host.conj (k : D.host.E), conj_mem D k⟩
  map_one' := Subtype.ext (by show D.host.conj ((1 : D.host.K) : D.host.E) = _; simp)
  map_mul' x y := Subtype.ext (by
    show D.host.conj ((x * y : D.host.K) : D.host.E) = D.host.conj x * D.host.conj y
    rw [IntermediateField.coe_mul, map_mul])
  map_zero' := Subtype.ext (by show D.host.conj ((0 : D.host.K) : D.host.E) = _; simp)
  map_add' x y := Subtype.ext (by
    show D.host.conj ((x + y : D.host.K) : D.host.E) = D.host.conj x + D.host.conj y
    rw [IntermediateField.coe_add, map_add])

def hK (x y : D.host.E) : D.host.K := Algebra.trace D.host.K D.host.E (x * D.host.conj y)

theorem tau_nonempty : Nonempty D.what₂.Tau := by
  rw [← Fintype.card_pos_iff, FL.card_tau]; positivity

theorem herm : FS.Herm4 (cK D) (hK D) where
  add_left x x' y := by simp only [hK, add_mul, map_add]
  smul_left k x y := by simp only [hK, smul_mul_assoc, map_smul, smul_eq_mul]
  symm x y := by
    apply Subtype.ext
    apply D.host.φ₀.injective
    show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (y * D.host.conj x) : D.host.K) : D.host.E)
      = D.host.φ₀ (D.host.conj ((Algebra.trace D.host.K D.host.E (x * D.host.conj y) : D.host.K) : D.host.E))
    rw [CU.emb_conj, ← FL.sum_tau_trace, ← FL.sum_tau_trace, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, map_mul, map_mul, CU.emb_conj, CU.emb_conj, Complex.conj_conj, mul_comm]
  pos x hx := by
    have hφ : D.host.φ₀ ((hK D x x : D.host.K) : D.host.E)
        = ((∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) : ℝ) : ℂ) := by
      show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (x * D.host.conj x) : D.host.K) : D.host.E) = _
      rw [← FL.sum_tau_trace]
      push_cast
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, CU.emb_conj, Complex.mul_conj]
    have hpos : 0 < ∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) := by
      haveI := tau_nonempty D
      exact Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ((map_ne_zero _).2 hx)) Finset.univ_nonempty
    obtain ⟨p, q, e⟩ := CS.K_repr D _ (hK D x x).2
    have hs := IO.sqrt_d_pos D
    rw [e, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d] at hφ
    have him := congrArg Complex.im hφ
    have hre := congrArg Complex.re hφ
    simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re] at him hre
    have hq : (q : ℝ) = 0 := by
      have : (q : ℝ) * Real.sqrt D.host.d = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hs.ne'
    have hq' : q = 0 := by exact_mod_cast hq
    have hp : (0 : ℝ) < (p : ℝ) := by rw [hq] at hre; linarith
    have hp' : 0 < p := by exact_mod_cast hp
    have hKp : hK D x x = ((p : ℚ) : D.host.K) := by
      apply Subtype.ext
      rw [e, hq']
      show _ = algebraMap D.host.K D.host.E ((p : ℚ) : D.host.K)
      rw [map_ratCast]; simp
    obtain ⟨a, b, c, d, h4⟩ := FS.rat_four_sq p hp'.le
    refine ⟨by rw [hKp]; exact Rat.cast_ne_zero.2 hp'.ne', (a : D.host.K), (b : D.host.K), (c : D.host.K), (d : D.host.K),
      map_ratCast _ a, map_ratCast _ b, map_ratCast _ c, map_ratCast _ d, ?_⟩
    rw [hKp, h4]; push_cast; ring

theorem card_eq : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  letI := FL.algKC D
  rw [← AlgHom.card D.host.K D.host.E ℂ]
  exact Fintype.card_of_bijective (FL.embA_bij D)

theorem iso0 : Nonempty (IsoK D) := by
  obtain ⟨g, hg⟩ := (herm D).iso (n := D.what₂.Tau) (card_eq D)
  refine ⟨⟨g, fun x y => ?_⟩⟩
  have h := hg x y
  have h2 : (∑ a, Algebra.trace D.host.K D.host.E (x a * D.host.conj (y a))) = ∑ w, g x w * cK D (g y w) := h.symm
  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul]
  rfl

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.G0

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def LinkIso0 : Prop := ∀ D : Car, Nonempty (IsoK D)

def LinkBaseP : Prop := ∀ D : Car, IsoPExists D → BaseExists D

def LinkTrivialLevelIsometry : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D → IsoPExists D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C




end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.GP

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Formalism.FrobeniusOrbits Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

def OO : Subring D.host.K := (algebraMap (𝓞 D.host.K) D.host.K).range

def LL : AddSubgroup D.host.E := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup

theorem memO_iff (t : D.host.K) : t ∈ OO D ↔ IsIntegral ℤ t :=
  ⟨by rintro ⟨y, rfl⟩; exact y.isIntegral_coe, fun h => ⟨⟨t, h⟩, rfl⟩⟩

theorem psi_cK (t : D.host.K) : AR.psi D (G0.cK D t) = starRingEnd ℂ (AR.psi D t) :=
  CU.emb_conj D D.host.φ₀ (t : D.host.E)

theorem int_mul_mem {z x : D.host.E} (hz : IsIntegral ℤ z) (hx : x ∈ LL D) : z * x ∈ LL D := by
  have h2 : ((⟨z, hz⟩ : 𝓞 D.host.E) • x) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
    Submodule.smul_mem _ _ hx
  have e : ((⟨z, hz⟩ : 𝓞 D.host.E) • x) = z * x := by rw [Algebra.smul_def]; rfl
  rw [e] at h2
  exact h2

theorem hK_rat (x : D.host.E) : ∃ p : ℚ, 0 ≤ p ∧ G0.hK D x x = ((p : ℚ) : D.host.K) := by
  have hφ : D.host.φ₀ ((G0.hK D x x : D.host.K) : D.host.E)
      = ((∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) : ℝ) : ℂ) := by
    show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (x * D.host.conj x) : D.host.K) : D.host.E) = _
    rw [← FL.sum_tau_trace]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, CU.emb_conj, Complex.mul_conj]
  have hpos : 0 ≤ ∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) :=
    Finset.sum_nonneg fun τ _ => Complex.normSq_nonneg _
  obtain ⟨p, q, e⟩ := CS.K_repr D _ (G0.hK D x x).2
  have hs := IO.sqrt_d_pos D
  rw [e, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d] at hφ
  have him := congrArg Complex.im hφ
  have hre := congrArg Complex.re hφ
  simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re] at him hre
  have hq : (q : ℝ) = 0 := by
    have : (q : ℝ) * Real.sqrt D.host.d = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hs.ne'
  have hq' : q = 0 := by exact_mod_cast hq
  have hp : (0 : ℝ) ≤ (p : ℝ) := by rw [hq] at hre; linarith
  refine ⟨p, by exact_mod_cast hp, ?_⟩
  apply Subtype.ext
  rw [e, hq']
  show _ = algebraMap D.host.K D.host.E ((p : ℚ) : D.host.K)
  rw [map_ratCast]; simp

theorem hK_nat (x : D.host.E) (hx : x ∈ LL D) : ∃ n : ℕ, G0.hK D x x = (n : D.host.K) := by
  obtain ⟨p, hp, e⟩ := hK_rat D x
  have hint : IsIntegral ℤ (G0.hK D x x) := TI.trace_conj_integral D x x hx hx
  rw [e] at hint
  have h2 : IsIntegral ℤ ((p : ℚ) : ℂ) := by
    have := hint.map (AR.psi D).toIntAlgHom
    simpa using this
  obtain ⟨n, hn⟩ := AR.int_of_rat p h2
  have hn0 : 0 ≤ n := by rw [hn] at hp; exact_mod_cast hp
  refine ⟨n.toNat, ?_⟩
  rw [e, hn]
  have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
  conv_lhs => rw [← this]
  push_cast; rfl

theorem crit (p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ D.host.d) (t : D.host.K) (ht : t ∈ OO D)
    (h1 : ∃ k : ℤ, t + G0.cK D t = (p : D.host.K) * k)
    (h2 : ∃ k : ℤ, ((AR.om D : 𝓞 D.host.K) : D.host.K) * t + G0.cK D (((AR.om D : 𝓞 D.host.K) : D.host.K) * t)
      = (p : D.host.K) * k) : ∃ t' ∈ OO D, t = (p : D.host.K) * t' := by
  obtain ⟨o, rfl⟩ := ht
  obtain ⟨x, y, -, hxy⟩ := AR.okc_of D o
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  have hψ : AR.psi D (algebraMap (𝓞 D.host.K) D.host.K o) = ((x : ℂ) + (y : ℂ) * AR.be D) / 2 := hxy
  have hω : AR.psi D ((AR.om D : 𝓞 D.host.K) : D.host.K) = (1 + AR.be D) / 2 := AR.ph_om D
  have hb2 := AR.be_sq D
  have hbc := AR.conj_be D
  have e1 : (x : ℂ) = (p : ℂ) * k := by
    have := congrArg (AR.psi D) hk
    rw [map_add, psi_cK, hψ] at this
    simp only [map_mul, map_div₀, map_add, hbc, map_intCast, map_natCast, map_ofNat] at this
    linear_combination this
  have e2 : (x : ℂ) - (D.host.d : ℂ) * y = 2 * (p : ℂ) * k' := by
    have := congrArg (AR.psi D) hk'
    rw [map_add, psi_cK, map_mul, hψ, hω] at this
    simp only [map_mul, map_div₀, map_add, hbc, map_intCast, map_natCast, map_ofNat, map_one] at this
    linear_combination 2 * this - (y : ℂ) * hb2
  have e1' : x = (p : ℤ) * k := by exact_mod_cast e1
  have e2' : x - (D.host.d : ℤ) * y = 2 * (p : ℤ) * k' := by exact_mod_cast e2
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hdy : (p : ℤ) ∣ (D.host.d : ℤ) * y := ⟨k - 2 * k', by linarith⟩
  obtain ⟨y', hy'⟩ : (p : ℤ) ∣ y := by
    rcases hpp.dvd_or_dvd hdy with h | h
    · exact absurd (Int.natCast_dvd_natCast.1 h) hpd
    · exact h
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e3 : k - (D.host.d : ℤ) * y' = 2 * k' := by
    apply mul_left_cancel₀ hp0
    rw [hy'] at e2'
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℤ, (D.host.d : ℤ) = 2 * e + 1 := ⟨(D.host.d : ℤ) / 2, by have := D.host.hyp.2.2.2.1; omega⟩
  refine ⟨((k' + e * y' : ℤ) : D.host.K) + ((y' : ℤ) : D.host.K) * ((AR.om D : 𝓞 D.host.K) : D.host.K),
    (OO D).add_mem (intCast_mem _ _) ((OO D).mul_mem (intCast_mem _ _) ⟨AR.om D, rfl⟩), ?_⟩
  apply (AR.psi D).injective
  rw [hψ, map_mul, map_add, map_mul, hω, map_natCast, map_intCast, map_intCast]
  have hkC : (k : ℂ) = (y' : ℂ) + 2 * ((k' + e * y' : ℤ) : ℂ) := by
    have : k = y' + 2 * (k' + e * y') := by rw [he] at e3; linarith
    exact_mod_cast this
  have hyC : (y : ℂ) = (p : ℂ) * y' := by exact_mod_cast hy'
  rw [e1, hyC, hkC]
  ring

theorem plat (p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ D.host.d) : FS.PLat (G0.cK D) (G0.hK D) (OO D) (LL D) p where
  herm := G0.herm D
  prime := hp
  cO t ht := (memO_iff D _).2 (((memO_iff D t).1 ht).map (G0.cK D).toIntAlgHom)
  smul o ho x hx := by
    obtain ⟨o', rfl⟩ := ho
    rw [Algebra.smul_def]
    exact int_mul_mem D (FL.intK D o') hx
  int x hx y hy := (memO_iff D _).2 (TI.trace_conj_integral D x y hx hy)
  unim x h :=
    (D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 x).2 (fun y hy => h y hy)
  full x := by
    obtain ⟨m, hm, h⟩ := SO.exists_nat_mul D.host.E {x}
    refine ⟨m, hm, ?_⟩
    rw [Algebra.smul_def, map_natCast]
    exact SO.int_mem_inverse_half_different (h x (Finset.mem_singleton_self x))
  nat := hK_nat D
  crit := ⟨_, ⟨AR.om D, rfl⟩, fun t ht h1 h2 => crit D p hp hpd t ht h1 h2⟩


theorem isoP (p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ D.host.d) : ∃ γ : IsoK D, γ.AtP p := by
  obtain ⟨g, hg, s, hcop, h1, h2⟩ := (plat D p hp hpd).iso (ι := D.what₂.Tau) (G0.card_eq D)
  refine ⟨⟨g, fun x y => ?_⟩, fun x hx => ⟨s, hcop, fun w => h1 x hx w⟩, fun v hv => ⟨s, hcop, fun a => ?_⟩⟩
  · have h3 : (∑ a, Algebra.trace D.host.K D.host.E (x a * D.host.conj (y a))) = ∑ w, g x w * G0.cK D (g y w) :=
      (hg x y).symm
    rw [h3, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul]
    rfl
  · have := h2 v hv a
    rw [Algebra.smul_def, map_natCast] at this
    exact this

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.GP

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def LinkIsoP : Prop := ∀ D : Car, IsoPExists D

def LinkBaseEx : Prop := ∀ D : Car, BaseExists D

def LinkSplitPrimeIsometry : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C




end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem discrNe (D : Car) : DiscrNe D := by
  intro cc hcc
  obtain ⟨L, hL0⟩ := Formalism.L2.Ker.Cd.periodExists D cc 1 hcc one_ne_zero
  have hL : ∀ w : ℂ, w ∈ lamOf D cc 1 ↔ w ∈ L.lattice := fun w => by rw [← hL0]; rfl
  have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 2 (by norm_num)
  have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 3 (by norm_num)
  have := Formalism.L2.Th1.F.discNeZero L
  unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
  rw [h4, h6]
  simpa [PeriodPair.g₂, PeriodPair.g₃] using this

def LinkDeltaNe : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0

def LinkBaseRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → Nonempty (Base D cc δ)

def LinkQInt : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.QIntAll

def LinkEqBase : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → ∀ N N' L L', admitted D N N' L L' →
      (B.eNat χ N N' L L' = fun z => χ (detId D (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ)) *
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N')) (La D (tor0 D cc δ) L L')
          (B.eNat χ N N' L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N')) z) ∧
      (B.eNat χ N N' L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') = fun z => χ (detId D (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) *
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N'))
          (La D (tor0 D cc δ) L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N'))
          (B.eNat χ N N' (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N')) z) ∧
      B.eNat χ N N' (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') = B.thZero N N'

def LinkPart : Prop :=
  ∀ D : Car, AdmittedStatements D → ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    (∃ χ, IsChi D χ) ∧ ∀ χ, IsChi D χ → ∃ e : FamE D,
      NonzeroThetaVectorFamily D (tor0 D cc δ) e ∧ ThetaNormIndependent D (tor0 D cc δ) e ∧ th22U D (tor0 D cc δ) e

def LinkThetaFamily : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

def LinkThetaFamily' : Prop :=
  LinkPer → ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    KroneckerLimit → Uniformization → CMTransitive D → DedekindFactor D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

theorem delta_nonzero_link : LinkDeltaNe := by
  intro D cc hcc δ hδ e
  apply discrNe D cc hcc.1
  rw [← (show δ ^ 12 = discr (lamOf D cc 1) from hδ), e]
  norm_num


theorem rational_integrality_link : LinkQInt := by
  intro D cc hcc δ hδ B N N' L L' hA x hx
  obtain ⟨a, b, hab, e⟩ := hermitian_form_integral_values D cc hcc δ hδ (delta_nonzero_link D cc hcc δ hδ) N N' L L' hA x hx x hx
  have hs := IO.sqrt_d_pos D
  have hreal : (Hf D (tor0 D cc δ) x x).im = 0 := by
    have h1 := IO.Hf_herm (tor0 D cc δ) x x
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    linarith
  have hb : b = 0 := by
    rw [e] at hreal
    simp at hreal
    exact hreal
  subst hb
  obtain ⟨j, hj⟩ := hab
  refine ⟨j, ?_⟩
  show Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = (j : ℝ)
  rw [e]
  have ha : (a : ℝ) = 2 * j := by
    have : a = 2 * j := by linarith
    exact_mod_cast this
  simp only [Int.cast_zero, zero_mul, add_zero, Complex.ofReal_re]
  rw [ha]
  field_simp





end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end
