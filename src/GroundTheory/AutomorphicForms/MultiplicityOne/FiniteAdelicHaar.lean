import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar
import GroundTheory.AutomorphicForms.WhittakerLocal
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Filter Set

open scoped RestrictedProduct

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def localChar (v : HeightOneSpectrum (𝓞 K)) : AddChar (v.adicCompletion K) ℂ where
  toFun x := (GroundTheory.Global.localAdelicChar K v x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [AddChar.map_add_eq_mul]

theorem sigma_mem_integralGL {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} {g : GL (Fin n) F} (hg : g ∈ GLnLocal.integralGL F n) :
    sigma g ∈ GLnLocal.integralGL F n := by
  rw [GLnLocal.mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [sigma_apply]; exact hg.1 _ _
  · rw [← sigma_inv, sigma_apply]; exact hg.2 _ _

variable (n : ℕ)

abbrev FinRes : Type _ := Πʳ v : HeightOneSpectrum (𝓞 K),
  [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n]

theorem sigma_mapsTo_integralGL : ∀ᶠ v in cofinite, MapsTo
    (sigma : GL (Fin n) ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K) → _)
    (GLnLocal.integralGL ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n :
      Set (GL (Fin n) ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K)))
    (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
  Eventually.of_forall fun _ _ hg => sigma_mem_integralGL hg

def sigmaResFun : FinRes K n → FinRes K n :=
  RestrictedProduct.mapAlong _ _ id tendsto_id
    (fun v => (sigma : GL (Fin n) ((id v : HeightOneSpectrum (𝓞 K)).adicCompletion K) → _))
    (sigma_mapsTo_integralGL K n)

theorem continuous_sigmaResFun : Continuous (sigmaResFun K n) :=
  RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _ (sigma_mapsTo_integralGL K n)
    fun _ => continuous_sigma

def sigmaRes : FinRes K n ≃ₜ FinRes K n where
  toFun := sigmaResFun K n
  invFun := sigmaResFun K n
  left_inv _ := RestrictedProduct.ext _ _ fun _ => sigma_sigma _
  right_inv _ := RestrictedProduct.ext _ _ fun _ => sigma_sigma _
  continuous_toFun := continuous_sigmaResFun K n
  continuous_invFun := continuous_sigmaResFun K n

@[simp] theorem sigmaRes_apply (x : FinRes K n) (v : HeightOneSpectrum (𝓞 K)) :
    sigmaRes K n x v = sigma (x v) := rfl

def unipotentF : Subgroup (AdelicGLn.FiniteAdelicGL K n) where
  carrier := {g | ∀ v, AdelicGLn.finiteRestrictedEquiv K n g v ∈
    Iwasawa.unipotent (v.adicCompletion K) n}
  mul_mem' {g h} hg hh v := by
    show AdelicGLn.finiteRestrictedEquiv K n (g * h) v ∈ _
    rw [map_mul, RestrictedProduct.mul_apply]
    exact (Iwasawa.unipotent _ n).mul_mem (hg v) (hh v)
  one_mem' v := by
    show AdelicGLn.finiteRestrictedEquiv K n 1 v ∈ _
    rw [map_one, RestrictedProduct.one_apply]
    exact (Iwasawa.unipotent _ n).one_mem
  inv_mem' {g} hg v := by
    show AdelicGLn.finiteRestrictedEquiv K n g⁻¹ v ∈ _
    rw [map_inv, RestrictedProduct.inv_apply]
    exact (Iwasawa.unipotent _ n).inv_mem (hg v)

variable [DecidableEq (HeightOneSpectrum (𝓞 K))]

end

end Whittaker

end GroundTheory.Automorphic
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Filter Set

open scoped RestrictedProduct

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

def pullL {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    locallyConstantCompactSupport Y ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport X ℂ ℂ where
  toFun φ := ⟨(φ : Y → ℂ) ∘ e, mem_locallyConstantCompactSupport.2
    ⟨φ.2.1.comp_continuous e.continuous, φ.2.2.comp_homeomorph e⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_pullL {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (φ : locallyConstantCompactSupport Y ℂ ℂ) :
    ((pullL e φ : locallyConstantCompactSupport X ℂ ℂ) : X → ℂ) = (φ : Y → ℂ) ∘ e := rfl

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

end

end Whittaker

end GroundTheory.Automorphic
end

section
open MeasureTheory Measure Topology Filter Set IsDedekindDomain NumberField

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

theorem isMulRightInvariant_finite (μ : Measure (AdelicGLn.FiniteAdelicGL K n)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.FiniteAdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨fun g => ?_⟩
    rw [Subsingleton.elim g 1]
    simp only [mul_one]
    exact Measure.map_id
  let _ : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _
  have : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  set P := μi.prod μ
  set e := AdelicGLn.prodEquiv K n
  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar
  have hν := GJGlobal.isMulRightInvariant_haar ν hn
  have he : Measurable e := e.continuous.measurable
  have : (ν.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map ν e.toMulEquiv e.continuous e.symm.continuous
  have hν' : ∀ p, (ν.map e).map (· * p) = ν.map e := by
    intro p
    have hcomp : (· * p) ∘ e = e ∘ (· * e.symm p) := by
      funext x
      simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
    rw [Measure.map_map (measurable_mul_const p) he, hcomp,
      ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]

  set c := haarScalarFactor (ν.map e) P
  have hc : ν.map e = c • P := isMulLeftInvariant_eq_smul (ν.map e) P
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    have hne := isOpen_univ.measure_ne_zero (ν.map e) univ_nonempty
    rw [hc] at hne
    exact hne rfl
  have hP : ∀ p, P.map (· * p) = P := by
    intro p
    have h1 : P = c⁻¹ • ν.map e := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1, Measure.map_smul, hν']
  refine ⟨fun g => ?_⟩
  have hprod : P.map (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = μi.prod (μ.map (· * g)) := by
    have hf : (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = Prod.map id (· * g) := by
      funext p
      exact Prod.ext (mul_one p.1) rfl
    rw [hf, ← Measure.map_prod_map μi μ measurable_id (measurable_mul_const g), Measure.map_id]
  rw [hP] at hprod
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds (1 : AdelicGLn.InfiniteAdelicGL K n)
  have hA0 : μi A ≠ 0 := (measure_pos_of_mem_nhds μi hA).ne'
  have hAt : μi A ≠ ⊤ := hAc.measure_lt_top.ne
  refine Measure.ext fun B hB => ?_
  have h1 := congrArg (fun m : Measure _ => m (A ×ˢ B)) hprod
  simp only [P, Measure.prod_prod] at h1
  exact ((ENNReal.mul_right_inj hA0 hAt).1 h1).symm

end

end Whittaker

end GroundTheory.Automorphic
end
