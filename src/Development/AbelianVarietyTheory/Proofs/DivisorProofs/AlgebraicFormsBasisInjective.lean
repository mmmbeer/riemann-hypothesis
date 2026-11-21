import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocLenEqZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LidxFinite
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistChoiceExample
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalZeroIffRationalSubspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GoodLiftPhase
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations

section
open NumberField

namespace GlobalTheory.DualFinitelyGenerated

variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}

theorem hform_single_apply (H : Matrix (Fin d) (Fin d) K) (i : Fin d) (x : Fin d → K) :
    Formalism.DivisionValues.hform H (Pi.single i 1) x = (H.mulVec x) i := by
  simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem dual_fg (H : Matrix (Fin d) (Fin d) K) (hH : H.det ≠ 0)
    (T : Submodule (𝓞 K) (Fin d → K)) (hT : Submodule.IsLattice K T) :
    (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) T).FG := by
  obtain ⟨s, hs⟩ := hT.fg
  let φ : (Fin d → K) →ₗ[𝓞 K] (s → K) :=
    (LinearMap.pi fun t : s => Formalism.DivisionValues.hform H t.1).restrictScalars (𝓞 K)
  let ψ : (s → 𝓞 K) →ₗ[𝓞 K] (s → K) :=
    LinearMap.pi fun t : s => (Algebra.linearMap (𝓞 K) K).comp (LinearMap.proj t)
  have hspan : Submodule.span K (s : Set (Fin d → K)) = ⊤ := by
    have := hT.span_eq_top
    rw [← hs, Submodule.span_span_of_tower] at this
    exact this
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h0 : ∀ t ∈ s, Formalism.DivisionValues.hform H t x = 0 := fun t ht => congrFun hx ⟨t, ht⟩
    have hle : Submodule.span K (s : Set (Fin d → K)) ≤ LinearMap.ker ((Formalism.DivisionValues.hform H).flip x) := by
      rw [Submodule.span_le]
      intro t ht
      simpa using h0 t ht
    rw [hspan] at hle
    have hv : H.mulVec x = 0 := by
      funext i
      rw [← hform_single_apply]
      have := hle (Submodule.mem_top (x := Pi.single i 1))
      simpa using this
    simpa using Matrix.eq_zero_of_mulVec_eq_zero hH hv
  have hψ : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have hle : (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) T).map φ ≤ LinearMap.range ψ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
    have hr : ∀ t : s, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = Formalism.DivisionValues.hform H t.1 x := by
      intro t
      have := hx t.1 (hs ▸ Submodule.subset_span t.2)
      rw [Submodule.mem_one] at this
      exact this
    choose r hr using hr
    refine ⟨r, ?_⟩
    funext t
    simp [ψ, φ, hr t]
  haveI : IsNoetherian (𝓞 K) (LinearMap.range ψ) := isNoetherian_of_fg_of_noetherian _ hψ
  exact Submodule.fg_of_fg_map_injective φ hinj (Submodule.FG.of_le_of_isNoetherian hle)

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : StarRing K] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) K), Matrix.det H ≠ (0 : K) →
    ∀ (T : Submodule (NumberField.RingOfIntegers K) (Fin d → K)), Submodule.IsLattice K T →
      Submodule.FG (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) T) :=
  fun H hH T hT => dual_fg H hH T hT

end GlobalTheory.DualFinitelyGenerated
end

section
open NumberField

namespace GlobalTheory.SimplifiedNormIdentities

theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (B : Submodule (𝓞 K) V) :
    ∀ x ∈ Submodule.span K (↑B : Set V), ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ B := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have h1 : (s * t) • y = t • (s • y) := by rw [mul_comm, mul_smul]
    have h2 : (s * t) • z = s • (t • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact B.add_mem (B.smul_mem t hsy) (B.smul_mem s htz)
  | smul c y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * s, mul_ne_zero hd0 hs, ?_⟩
    have key : (d * s) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) • y) = a • (s • y) := by
      rw [← algebraMap_smul K (d * s), ← algebraMap_smul K a, ← algebraMap_smul K s,
        smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact B.smul_mem a hsy

end GlobalTheory.SimplifiedNormIdentities
end

section
namespace GlobalTheory.UniformScalarBound

theorem uniform_scalar {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]
    (A B : Submodule R V) (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) :
    ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf0 hfB using fun x (hx : x ∈ S) => h x (Submodule.subset_span hx)
  refine ⟨∏ g ∈ S, f g, Finset.prod_ne_zero_iff.mpr (fun g hg => hf0 g hg), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase S f hy, mul_comm, mul_smul]
    exact B.smul_mem _ (hfB y hy)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact B.smul_mem a hx

theorem main : ∀ {R V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : AddCommGroup V]
    [inst_3 : Module R V] (A B : Submodule R V), Submodule.FG A →
    (∀ x ∈ A, ∃ (s : R), s ≠ (0 : R) ∧ s • x ∈ B) →
    ∃ (s : R), s ≠ (0 : R) ∧ ∀ x ∈ A, s • x ∈ B :=
  fun A B hA h => uniform_scalar A B hA h

end GlobalTheory.UniformScalarBound
end

section
open NumberField

namespace GlobalTheory.StarIntegralityLemmas

theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (r : 𝓞 K) :
    ∃ r' : 𝓞 K, (r' : K) = star (r : K) := by
  have hi : IsIntegral ℤ (star (r : K)) := by
    have := (RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom
    simpa [starRingEnd_apply] using this
  exact ⟨⟨star (r : K), (mem_integralClosure_iff ℤ K).mpr hi⟩, rfl⟩

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : StarRing K] {d : ℕ}
    (h : (Fin d → K) →ₗ⋆[K] (Fin d → K) →ₗ[K] K)
    (T : Submodule (NumberField.RingOfIntegers K) (Fin d → K)), Submodule.FG T →
    ∀ (x : Fin d → K), ∃ (s : NumberField.RingOfIntegers K),
      s ≠ (0 : NumberField.RingOfIntegers K) ∧ s • x ∈ Formalism.HermitianLatticesTheory.dual h T := by
  intro K _ _ _ d h T hT x
  classical
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.image fun v => h v x)
  refine ⟨(b : 𝓞 K), nonZeroDivisors.coe_ne_zero b, ?_⟩
  have key : ∀ y : Fin d → K, h y ((b : 𝓞 K) • x) = algebraMap (𝓞 K) K (b : 𝓞 K) * h y x := by
    intro y
    rw [← algebraMap_smul K (b : 𝓞 K) x, map_smul, smul_eq_mul]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨c, hc⟩ := hb (h v x) (Finset.mem_image_of_mem _ hv)
    rw [key, Submodule.mem_one]
    refine ⟨c, ?_⟩
    rw [hc, Algebra.smul_def]
  | zero => simp
  | add u w _ _ hu hw =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hu hw
  | smul r u _ hu =>
    obtain ⟨r', hr'⟩ := star_int r
    rw [← algebraMap_smul K r u, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hu
    rw [Submodule.mem_one]
    refine ⟨r' * c, ?_⟩
    rw [map_mul, hc]
    simp [hr']

end GlobalTheory.StarIntegralityLemmas
end

section
noncomputable section

open Module NumberField IsDedekindDomain
open scoped InnerProductSpace

namespace GlobalTheory.TwistPlacesObj

open GlobalTheory.QPosCompare

section Lin

variable {K X E W : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {σ : K →+* ℂ} {j : X →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)

theorem lin_injective (hj : IsForm j) {n : ℕ} (f : (Fin n → K) →ₗ[K] X) (hf : Function.Injective f)
    (hZ : ∀ y, j (f y) ∈ LinearMap.range (LinearMap.adjoint θ)) :
    Function.Injective (Formalism.IndefR.Cx.lin fun k => θ (j (f (Pi.single k 1)))) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have h1 : LinearIndependent K fun k : Fin n => f (Pi.single k 1) := by
    have := (Pi.basisFun K (Fin n)).linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
    simpa [Function.comp_def] using this
  have h2 := hj.linInd h1
  set u : E := ∑ k, c k • j (f (Pi.single k 1)) with hu
  have h3 : u ∈ LinearMap.ker θ := by
    rw [Formalism.IndefR.Cx.lin_apply] at hc
    rw [LinearMap.mem_ker, hu, map_sum]
    simpa only [map_smul] using hc
  have h4 : u ∈ (LinearMap.ker θ)ᗮ := by
    rw [LinearMap.orthogonal_ker]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hZ _)
  have h5 : u = 0 := inner_self_eq_zero.1 (h4 u h3)
  funext k
  exact Fintype.linearIndependent_iff.1 h2 c h5 k

variable {G : Type} [Group G] [Fintype G] (r : Representation K G X) (ρ : G → W →ₗ[ℂ] W)

end Lin

section Block

open Formalism.DivisionValues Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)
  {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {σ : K →+* ℂ} {j : B.S.Forms →ₛₗ[σ] E} (θ : E →ₗ[ℂ] W)
  (ρ : G → W →ₗ[ℂ] W)

theorem toF_mem (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z :=
  (B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y)

end Block

section Content

open Formalism.BasicNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree.DepthCond GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample

end Content

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isForm_tw {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ σ' : K →+* ℂ} (s : Bool) (h : ∀ a, σ' a = cj s (σ a)) {j : X →ₛₗ[σ] E} (hj : IsForm j) :
    IsForm (E := Tw s E) (Tw.semi s h j) := by
  obtain ⟨⟨n, b, h1, h2⟩, h3⟩ := hj
  refine ⟨⟨n, b, (Tw.linInd (E := E) s h1 :), ?_⟩, fun x y => ?_⟩
  · have e : Set.range (Tw.semi s h j) = Tw.mk s '' Set.range j := by rw [← Set.range_comp]; rfl
    rw [e, tw_span, h2]
    rfl
  · obtain ⟨a, ha⟩ := h3 x y
    exact ⟨a, (congrArg (cj s) ha).trans (h a).symm⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

variable {R F}

open GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample

end Real

end GlobalTheory.TwistPlacesObj

end
end
