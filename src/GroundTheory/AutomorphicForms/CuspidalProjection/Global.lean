import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.CuspidalProjection.Unfold
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

section
open MeasureTheory Set Function Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalProjection

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} (v : HeightOneSpectrum (𝓞 K))

theorem continuous_finiteAdeleSingleAdd :
    Continuous (GroundTheory.Global.finiteAdeleSingleAdd (K := K) v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 {v}ᶜ := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact Set.finite_singleton v
  let g : v.adicCompletion K → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (𝓟 {v}ᶜ) := fun x =>
    ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x,
      Filter.eventually_principal.2 fun w hw => by
        rw [Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.1 hw)]
        exact zero_mem _⟩
  have hs : Continuous fun x : v.adicCompletion K =>
      Pi.single (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x :=
    continuous_single v
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.2 hs
  have heq : (GroundTheory.Global.finiteAdeleSingleAdd (K := K) v : v.adicCompletion K → _) =
      RestrictedProduct.inclusion _ _ hle ∘ g := by
    funext x
    rfl
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

def adeleSingle : v.adicCompletion K →+ 𝔸[K] :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (GroundTheory.Global.finiteAdeleSingleAdd v)


def evAt : 𝔸[K] →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) v).comp
    (RingHom.snd _ _)

theorem evAt_apply (x : 𝔸[K]) : evAt v x = x.2 v := rfl


def compAt : AdelicGLn.AdelicGL K n →* GL (Fin n) (v.adicCompletion K) :=
  (RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) => GL (Fin n) (w.adicCompletion K)) v).comp
    ((MonoidHom.snd _ _).comp (AdelicGLn.restrictedProductEquiv K n).toMonoidHom)

theorem compAt_apply (g : AdelicGLn.AdelicGL K n) (a b : Fin n) :
    (compAt v g : GL (Fin n) (v.adicCompletion K)) a b = ((g : AdelicGLn.AdelicMatrix K n) a b).2 v :=
  AdelicGLn.restrictedProductEquiv_apply_snd K n g v a b

theorem continuous_compAt : Continuous (compAt (K := K) (n := n) v) :=
  (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

variable (n r) in

def unipAt (y : UPos n r → v.adicCompletion K) : normOneGL K n :=
  unipOne K n r fun p => adeleSingle v (y p)

theorem unipAt_add (y y' : UPos n r → v.adicCompletion K) :
    unipAt n r v (y + y') = unipAt n r v y * unipAt n r v y' := by
  rw [unipAt, unipAt, unipAt, ← unipOne_add]
  congr 1
  funext p
  simp [map_add]



def unipCoord (g : normOneGL K n) : UPos n r → v.adicCompletion K := fun p =>
  (compAt v (g : AdelicGLn.AdelicGL K n) : GL (Fin n) (v.adicCompletion K)) p.1.1 p.1.2

theorem continuous_unipCoord : Continuous (unipCoord (K := K) (n := n) (r := r) v) := by
  refine continuous_pi fun p => ?_
  have h : Continuous fun g : GL (Fin n) (v.adicCompletion K) =>
      (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) p.1.1 p.1.2 :=
    Units.continuous_val.matrix_elem p.1.1 p.1.2
  exact h.comp ((continuous_compAt v).comp continuous_subtype_val)



end CuspidalProjection

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalProjection

open Reduction AutomorphicForm CuspidalSpectrum RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]


theorem constantTermL2_unipotent_mul (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (r : ℕ)
    (Y : UPos n r → 𝔸[K]) (z : normOneGL K n) :
    constantTermL2 μ r φ (unipOne K n r Y * z) = constantTermL2 μ r φ z := by
  simp only [constantTermL2, ctFun]
  have h : ∀ X, unipOne K n r X * (unipOne K n r Y * z) = unipOne K n r (X + Y) * z := by
    intro X
    rw [unipOne_add, mul_assoc]
  simp_rw [h]
  refine setIntegral_add_right_of_periodic isAddFundamentalDomain_unipFundamentalDomain
    (h := fun X => (φ : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ (unipOne K n r X * z))) (fun ξ hξ s => ?_) Y
  show (φ : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ (unipOne K n r (ξ + s) * z)) = φ (mk Γ₁ (unipOne K n r s * z))
  rw [unipOne_add, mul_assoc, mk_mul_of_mem (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]


variable (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
  [BorelSpace (v.adicCompletion K)]

def IsCuspidalAt (ν : ∀ r : ℕ, Measure (UPos n r → v.adicCompletion K)) (f : normOneGL K n → ℂ) :
    Prop :=
  ∀ r : ℕ, 0 < r → r < n → ∀ g₁ g₂ : normOneGL K n,
    ∫ y, f (g₁ * unipAt n r v y * g₂) ∂ν r = 0

variable {μ v}


omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem unipAt_neg (r : ℕ) (y : UPos n r → v.adicCompletion K) :
    unipAt n r v (-y) = (unipAt n r v y)⁻¹ := by
  have h0 : unipAt n r v (0 : UPos n r → v.adicCompletion K) = 1 := by
    rw [unipAt]
    simp only [Pi.zero_apply, map_zero]
    exact unipOne_zero r
  rw [eq_inv_iff_mul_eq_one, ← unipAt_add, neg_add_cancel, h0]

def ccStar (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    CompactlySupportedContinuousMap (normOneGL K n) ℂ where
  toFun g := conj (f g⁻¹)
  continuous_toFun := Complex.continuous_conj.comp (f.continuous.comp continuous_inv)
  hasCompactSupport' :=
    (f.hasCompactSupport.comp_isClosedEmbedding (Homeomorph.inv (normOneGL K n)).isClosedEmbedding).comp_left
      (map_zero _)

@[simp] theorem ccStar_apply (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (g : normOneGL K n) : ccStar f g = conj (f g⁻¹) := rfl


variable (μ) in

theorem ccToL1_ccStar [μ.IsInvInvariant] (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    UnitaryRep.ccToL1 μ (ccStar f) = UnitaryRep.involution μ (UnitaryRep.ccToL1 μ f) := by
  have h1 : (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) =ᵐ[μ] f :=
    MemLp.coeFn_toLp _
  have h1' : (fun g => (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) g⁻¹) =ᵐ[μ] fun g => f g⁻¹ :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq_comp h1
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (μ := μ) ((ccStar f).continuous.memLp_of_hasCompactSupport
    (ccStar f).hasCompactSupport), UnitaryRep.coeFn_involution μ (UnitaryRep.ccToL1 μ f), h1']
    with g ha hb hc
  rw [hb, hc]
  exact ha




end CuspidalProjection

end

end GroundTheory.Automorphic
end
