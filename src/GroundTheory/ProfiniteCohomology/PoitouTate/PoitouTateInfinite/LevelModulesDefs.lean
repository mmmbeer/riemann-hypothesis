import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Descent
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.ArithmeticGeometry.SelmerPairing.Unramified
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

noncomputable section

universe u

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S T U : Set (HeightOneSpectrum (𝓞 K))}

def gsAutExtend (S : Set (HeightOneSpectrum (𝓞 K))) (σ : galUnramifiedOutside K Ω S) : Gal(Ω/K) :=
  (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside K Ω S) Ω σ).choose

theorem gsAutExtend_apply (σ : galUnramifiedOutside K Ω S) (y : maxUnramifiedOutside K Ω S) :
    gsAutExtend S σ (y : Ω) = ((σ y : maxUnramifiedOutside K Ω S) : Ω) := by
  have h := (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside K Ω S) Ω σ).choose_spec
  conv_rhs => rw [← h]
  exact (AlgEquiv.restrictNormal_commutes (gsAutExtend S σ) (maxUnramifiedOutside K Ω S) y).symm

def gsResFun (T : Set (HeightOneSpectrum (𝓞 K))) (σ : galUnramifiedOutside K Ω S) :
    galUnramifiedOutside K Ω T :=
  AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω T) (gsAutExtend S σ)

theorem gsResFun_apply (h : T ⊆ S) (σ : galUnramifiedOutside K Ω S) (x : maxUnramifiedOutside K Ω T) :
    ((gsResFun T σ x : maxUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maxUnramifiedOutside_mono h x.2⟩ : maxUnramifiedOutside K Ω S) : Ω) := by
  rw [gsResFun, AlgEquiv.restrictNormalHom_apply]
  exact gsAutExtend_apply σ ⟨x, maxUnramifiedOutside_mono h x.2⟩

def gsRes (h : T ⊆ S) : galUnramifiedOutside K Ω S →* galUnramifiedOutside K Ω T where
  toFun := gsResFun T
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    rw [gsResFun_apply h, AlgEquiv.one_apply, AlgEquiv.one_apply]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    have e : (⟨((gsResFun T τ x : maxUnramifiedOutside K Ω T) : Ω),
        maxUnramifiedOutside_mono h (gsResFun T τ x).2⟩ : maxUnramifiedOutside K Ω S) =
        τ ⟨x, maxUnramifiedOutside_mono h x.2⟩ :=
      Subtype.val_injective (gsResFun_apply h τ x)
    rw [AlgEquiv.mul_apply (gsResFun T σ), gsResFun_apply h (σ * τ) x,
      gsResFun_apply h σ (gsResFun T τ x), e, AlgEquiv.mul_apply]

theorem gsRes_apply (h : T ⊆ S) (σ : galUnramifiedOutside K Ω S) (x : maxUnramifiedOutside K Ω T) :
    ((gsRes h σ x : maxUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maxUnramifiedOutside_mono h x.2⟩ : maxUnramifiedOutside K Ω S) : Ω) :=
  gsResFun_apply h σ x

theorem gsRes_restrictNormalHom (h : T ⊆ S) (σ : Gal(Ω/K)) :
    gsRes h (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) σ) =
      AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω T) σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [gsRes_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]

theorem gsRes_surjective (h : T ⊆ S) : Function.Surjective (gsRes (Ω := Ω) h) := fun τ =>
  ⟨AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) (gsAutExtend T τ), by
    rw [gsRes_restrictNormalHom]
    exact (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside K Ω T) Ω τ).choose_spec⟩



theorem continuous_gsRes (h : T ⊆ S) : Continuous (gsRes (Ω := Ω) h) := by
  have hq : Topology.IsQuotientMap
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnramifiedOutside K Ω S)) :=
    (InfiniteGalois.restrictNormalHom_continuous _).isClosedMap.isQuotientMap
      (InfiniteGalois.restrictNormalHom_continuous _) (AlgEquiv.restrictNormalHom_surjective Ω)
  rw [hq.continuous_iff]
  have e : ⇑(gsRes h) ∘ ⇑(AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnramifiedOutside K Ω S)) =
      ⇑(AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnramifiedOutside K Ω T)) :=
    funext (gsRes_restrictNormalHom h)
  rw [e]
  exact InfiniteGalois.restrictNormalHom_continuous _

def gsResCont (h : T ⊆ S) : galUnramifiedOutside K Ω S →ₜ* galUnramifiedOutside K Ω T :=
  ⟨gsRes h, continuous_gsRes h⟩

@[simp]
theorem gsResCont_apply (h : T ⊆ S) (σ : galUnramifiedOutside K Ω S) : gsResCont h σ = gsRes h σ :=
  rfl

section Local

variable {Kv Ωv : Type u} [Field Kv] [Field Ωv] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv]
  [IsScalarTower K Kv Ωv]

end Local

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Finite

variable {S : Set (HeightOneSpectrum (𝓞 K.1))}

def finitePlaceUnder (E : IntermediateField K.1 ℚ̄) [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 K.1) where
  asIdeal := w.asIdeal.under (𝓞 K.1)
  isPrime := Ideal.IsPrime.under (𝓞 K.1) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot




end Finite

section Unramified

open GroundTheory.LocalField

variable (T : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

theorem inertiaGroup_le_ker_decompHomS (hv : v ∉ T) :
    inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) ≤
      (decompHomS (v.adicCompletion K.1) T ι).ker := by
  intro g hg
  refine MonoidHom.mem_ker.2 (decompHomS_eq_one_of_unramifiedDegree_eq_one T ι hv g ?_)
  rw [← MonoidHom.mem_ker, ker_unramifiedDegree]
  exact hg

def decompHomSUnram (hv : v ∉ T) :
    Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
        inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) →ₜ*
      galUnramifiedOutside K.1 ℚ̄ T :=
  ⟨QuotientGroup.lift _ (decompHomS (v.adicCompletion K.1) T ι) (inertiaGroup_le_ker_decompHomS T ι hv),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      (continuous_decompHomS (Kv := v.adicCompletion K.1) T ι)⟩


variable (v) in

theorem exists_isZHatGenerator_inertia_adicCompletion :
    ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
        inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)),
      IsZHatGenerator σ :=
  GroundTheory.Arith.Selmer.exists_isZHatGenerator_inertia _ _

end Unramified

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

theorem isOpen_ker_ρ {k G : Type*} [CommRing k] [Group G] [TopologicalSpace G] (A : Rep k G) [IsDiscreteRep A]
    [Finite A] : IsOpen ((A.ρ.ker : Subgroup G) : Set G) := by
  have e : ((A.ρ.ker : Subgroup G) : Set G) = ⋂ a : A, (stabilizer A.ρ a : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    constructor
    · intro h a
      change A.ρ g a = a
      rw [h, Module.End.one_apply]
    · intro h
      exact LinearMap.ext fun a => h a
  rw [e]
  exact isOpen_iInter_of_finite fun a => isOpen_stabilizer A a




variable {T : Set (HeightOneSpectrum (𝓞 K.1))} (h : T ⊆ S)

theorem gsResCont_surjective : Function.Surjective (gsResCont (Ω := ℚ̄) h) := fun τ => by
  obtain ⟨σ, hσ⟩ := gsRes_surjective (Ω := ℚ̄) h τ
  exact ⟨σ, by rw [gsResCont_apply]; exact hσ⟩

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
  (hM : ∀ g, gsResCont (Ω := ℚ̄) h g = 1 → M.ρ g = 1)

abbrev levelModule : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ T) :=
  descendRep (gsResCont (Ω := ℚ̄) h) (gsResCont_surjective h) M hM

theorem isQuotientMap_gsResCont : Topology.IsQuotientMap (gsResCont (Ω := ℚ̄) h) :=
  (gsResCont (Ω := ℚ̄) h).continuous.isClosedMap.isQuotientMap (gsResCont (Ω := ℚ̄) h).continuous
    (gsResCont_surjective h)

instance isDiscreteRep_levelModule [IsDiscreteRep M] : IsDiscreteRep (levelModule h M hM) :=
  isDiscreteRep_descendRep _ (gsResCont_surjective h) M hM (isQuotientMap_gsResCont h)

end

end GroundTheory.ProfCoh
end
