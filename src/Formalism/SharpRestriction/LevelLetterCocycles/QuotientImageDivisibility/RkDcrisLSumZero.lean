import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump

section
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

section Ops

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem rk_mem_Dcris {x : V ⊗[Qp] B} : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem rk_mem_DcrisL (τ : K₀ →ₐ[Qp] LL) {x : V ⊗[Qp] B} :
    x ∈ DcrisL PD ρ τ ↔ x ∈ Dcris PD ρ ∧
      ∀ c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ c • x := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem rk_act_mulVB (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => simp [actVB, mulVB, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rk_mulVB_Dcris (c : K₀) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x ∈ Dcris PD ρ := by
  rw [rk_mem_Dcris] at hx ⊢
  intro g
  rw [rk_act_mulVB, hx g]

theorem rk_ιV_mul (c : K₀) (y : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c y) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul w b =>
    simp only [ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply, map_mul,
      AlgHom.commutes]
    rw [← IsScalarTower.algebraMap_apply K₀ K BdR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rk_mulVdR_FilV (c : K) (a : ℤ) {y : V ⊗[Qp] BdR} (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w f =>
    refine ⟨w ⊗ₜ[Qp] (⟨algebraMap K BdR c * (f : BdR), ?_⟩ : ↥((PD.Fil a).restrictScalars Qp)), ?_⟩
    · rw [← Algebra.smul_def]
      exact (PD.Fil a).smul_mem c f.2
    · simp [mulVdR, AlgebraTensorModule.map_tmul]
  | add y z hy hz =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hy hz

theorem rk_mulVB_FilCris (c : K₀) (a : ℤ) {x : V ⊗[Qp] B} (hx : x ∈ FilCris PD ρ a) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x ∈ FilCris PD ρ a := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
  refine Submodule.mem_inf.2 ⟨rk_mulVB_Dcris PD ρ c h1, ?_⟩
  rw [Submodule.mem_comap] at h2 ⊢
  rw [rk_ιV_mul]
  exact rk_mulVdR_FilV PD _ a h2

theorem rk_mapVB_mulVB {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') (c : K₀) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB LL f (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V') (LL := LL) c (Formalism.MainNotions.RamifiedCoefficientChains.mapVB LL f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => simp [Formalism.MainNotions.RamifiedCoefficientChains.mapVB, mulVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rk_ιV_inj : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

end Ops

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

open Formalism.BasicNotions

section Dec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private lemma mem_DcrisL_iff' (T : LocLat G Qp LL O) (σ : K₀ →ₐ[Qp] LL) (x : T.V ⊗[Qp] B) :
    x ∈ DcrisL PD T.ρ σ ↔ x ∈ Dcris PD T.ρ ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x = σ c • x := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private lemma mem_DdRE_iff' (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (y : T.V ⊗[Qp] BdR) :
    y ∈ DdRE PD T.ρ τ ↔ y ∈ DdR PD T.ρ ∧
      ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) c y = τ c • y := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private lemma iotaV_injective (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ x, ιV PD (LL := LL) (V := T.V) x =
      LinearMap.lTensor T.V (PD.ι.toLinearMap.restrictScalars Qp) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => first | rfl | simp [ιV]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (by exact PD.ι_inj) hxy

private lemma iotaV_mulVB_comm (T : LocLat G Qp LL O) (c : K₀) (x : T.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x) =
      mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := T.V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ιV, mulVB, mulVdR, ← IsScalarTower.algebraMap_apply]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]

theorem rk_lift (hK : Function.Bijective (algebraMap K₀ K)) (σ : K₀ →ₐ[Qp] LL) :
    ∃ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = σ := by
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  refine ⟨σ.comp (e.symm : K →ₐ[Qp] K₀), ?_⟩
  ext x
  have hx : (IsScalarTower.toAlgHom Qp K₀ K) x = e x := rfl
  simp only [AlgHom.comp_apply, hx, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]

variable [NeZero n] (W : LocWach PD LL O v n)

include W in
theorem rk_DcrisL_map (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (τ : K →ₐ[Qp] LL) :
    (DcrisL PD T.ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map (ιV PD (LL := LL) (V := T.V)) =
      DdRE PD T.ρ τ := by
  have hD := (hQ hK T.V T.ρ hT).1
  ext y
  rw [Submodule.mem_map, mem_DdRE_iff']
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_DcrisL_iff'] at hx
    refine ⟨?_, fun c => ?_⟩
    · rw [← hD]; exact Submodule.mem_map_of_mem hx.1
    · obtain ⟨c₀, rfl⟩ := hK.2 c
      rw [← iotaV_mulVB_comm, hx.2 c₀, map_smul]
      first | rfl | simp
  · rintro ⟨hyD, hyc⟩
    rw [← hD, Submodule.mem_map] at hyD
    obtain ⟨x, hxD, rfl⟩ := hyD
    refine ⟨x, (mem_DcrisL_iff' T _ x).mpr ⟨hxD, fun c₀ => ?_⟩, rfl⟩
    apply iotaV_injective (PD := PD) T
    rw [iotaV_mulVB_comm, hyc, map_smul]
    first | rfl | simp

include W in
theorem rk_finrank_DcrisL (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (σ : K₀ →ₐ[Qp] LL) :
    finrank LL ↥(DcrisL PD T.ρ σ) = finrank LL T.V := by
  obtain ⟨τ, hτ⟩ := rk_lift hK σ
  rw [← hτ]
  have hmap := rk_DcrisL_map W hK hQ T hT τ
  have hE := (hQ hK T.V T.ρ hT).2 τ
  rw [← hE.2.1, ← hmap]
  exact (Submodule.equivMapOfInjective _ (iotaV_injective (PD := PD) T) _).finrank_eq

end Dec

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
