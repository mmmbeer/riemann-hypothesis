import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G]

abbrev underlyingRep (X : TopRep.{u} k G) : Rep.{u} k G :=
  Rep.of X.ρ.toRepresentation

@[simp]
theorem underlyingRep_ρ_apply (X : TopRep.{u} k G) (g : G) (x : X) :
    (underlyingRep X).ρ g x = X.ρ g x :=
  rfl

section Discrete

variable [DiscreteTopology k]

def discreteTopRep (A : Rep.{u} k G) : TopRep.{u} k G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  haveI : ContinuousSMul k A := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalAddGroup A := ⟨⟩
  TopRep.of (X := A) <| ContRepresentation.ofMonoidHom
    { toFun g := { toLinearMap := A.ρ g, cont := continuous_of_discreteTopology }
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }

instance (A : Rep.{u} k G) : DiscreteTopology (discreteTopRep A) :=
  ⟨rfl⟩

variable [TopologicalSpace G]

instance (A : Rep.{u} k G) [IsDiscreteRep A] : IsDiscreteRep (underlyingRep (discreteTopRep A)) :=
  ‹IsDiscreteRep A›

end Discrete

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory TopRep ContRepresentation

universe u v w

section Cons

variable {G : Type v} [TopologicalSpace G]

def finConsHomeomorph (m : ℕ) : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by simp
  right_inv x := by simp
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (m + 1) => G) continuous_fst continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk (continuous_pi fun _ => continuous_apply _)

@[simp]
theorem finConsHomeomorph_symm_apply (m : ℕ) (x : Fin (m + 1) → G) :
    (finConsHomeomorph m).symm x = (x 0, Fin.tail x) :=
  rfl

end Cons

variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

def nestedHomeomorph (X : TopRep.{u} k G) : (m : ℕ) → resolutionX X m ≃ₜ C(Fin m → G, X)
  | 0 => Homeomorph.continuousMapOfUnique
  | m + 1 => ((Homeomorph.refl G).arrowCongr (nestedHomeomorph X m)).trans
      (Homeomorph.curry.symm.trans ((finConsHomeomorph m).arrowCongr (Homeomorph.refl X)))

variable (X : TopRep.{u} k G)

@[simp]
theorem nestedHomeomorph_zero_apply (v : resolutionX X 0) (x : Fin 0 → G) :
    nestedHomeomorph X 0 v x = v :=
  rfl

theorem nestedHomeomorph_succ_apply (m : ℕ) (f : resolutionX X (m + 1))
    (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) f x =
      nestedHomeomorph X m ((f : C(G, resolutionX X m)) (x 0)) (Fin.tail x) :=
  rfl

theorem nestedHomeomorph_add (m : ℕ) (a b : resolutionX X m) :
    nestedHomeomorph X m (a + b) = nestedHomeomorph X m a + nestedHomeomorph X m b := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((a + b : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x) +
          nestedHomeomorph X m ((b : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.add_apply, ih]
    rfl

theorem nestedHomeomorph_smul (m : ℕ) (r : k) (a : resolutionX X m) :
    nestedHomeomorph X m (r • a) = r • nestedHomeomorph X m a := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((r • a : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = r • nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.smul_apply, ih]
    rfl

def nestedLinearEquiv (m : ℕ) : resolutionX X m ≃ₗ[k] C(Fin m → G, X) where
  toFun := nestedHomeomorph X m
  invFun := (nestedHomeomorph X m).symm
  map_add' := nestedHomeomorph_add X m
  map_smul' := nestedHomeomorph_smul X m
  left_inv := (nestedHomeomorph X m).symm_apply_apply
  right_inv := (nestedHomeomorph X m).apply_symm_apply

@[simp]
theorem nestedLinearEquiv_apply (m : ℕ) (a : resolutionX X m) :
    nestedLinearEquiv X m a = nestedHomeomorph X m a :=
  rfl

theorem nestedHomeomorph_ρ_apply (m : ℕ) (g : G) (a : resolutionX X m) (x : Fin m → G) :
    nestedHomeomorph X m ((resolutionX X m).ρ g a) x =
      X.ρ g (nestedHomeomorph X m a fun i => g⁻¹ * x i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nestedHomeomorph_succ_apply, nestedHomeomorph_succ_apply]
    exact ih _ _

theorem nestedHomeomorph_d_apply (m : ℕ) (a : resolutionX X m) (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) ((d X m).hom a) x =
      ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) • nestedHomeomorph X m a (fun j => x (i.succAbove j)) := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul]
    rfl
  | succ m ih =>
    have h1 : ((d X (m + 1)).hom a : C(G, resolutionX X (m + 1))) (x 0) =
        a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0)) := by
      rw [hom_d_succ]
      rfl
    rw [nestedHomeomorph_succ_apply, h1,
      show nestedHomeomorph X (m + 1) (a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0))) =
        nestedHomeomorph X (m + 1) a -
          nestedHomeomorph X (m + 1) ((d X m).hom ((a : C(G, resolutionX X m)) (x 0))) from
        map_sub (nestedLinearEquiv X (m + 1)) _ _,
      ContinuousMap.sub_apply, ih, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [nestedHomeomorph_succ_apply X m a, Fin.succ_succAbove_zero]
    congr 1
    funext j
    simp only [Fin.tail, Fin.succ_succAbove_succ]
end ProfCoh
end GroundTheory
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory TopRep ContRepresentation

universe u

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_partialProd (n : ℕ) :
    Continuous fun g : Fin n → G => Fin.partialProd g := by
  refine continuous_pi fun i => ?_
  induction i using Fin.induction with
  | zero => simpa using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

variable {k : Type u} [CommRing k]

theorem isLocallyConstant_ρ_apply {Y : Type*} [TopologicalSpace Y] (A : Rep.{u} k G)
    [IsDiscreteRep A] {p : Y → G} (hp : Continuous p) {ψ : Y → A} (hψ : IsLocallyConstant ψ) :
    IsLocallyConstant fun y => A.ρ (p y) (ψ y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have h1 : ∀ᶠ z in nhds y, ψ z = ψ y := hψ.eventually_eq y
  have h2 : ∀ᶠ z in nhds y, A.ρ (p z) (ψ y) = A.ρ (p y) (ψ y) :=
    hp.continuousAt.eventually ((isLocallyConstant_apply A (ψ y)).eventually_eq (p y))
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]

end General

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

section Invariant

variable (X : TopRep.{u} k G)

theorem nestedHomeomorph_mul_apply_of_mem_invariants {m : ℕ} {a : resolutionX X m}
    (ha : a ∈ (resolutionX X m).ρ.invariants) (g : G) (x : Fin m → G) :
    nestedHomeomorph X m a (fun i => g * x i) = X.ρ g (nestedHomeomorph X m a x) := by
  have h := nestedHomeomorph_ρ_apply X m g a (fun i => g * x i)
  rw [(mem_invariants a).1 ha g] at h
  simpa using h

end Invariant

variable (X : TopRep.{u} k G) [DiscreteTopology X] [IsDiscreteRep (underlyingRep X)]

def toInhomogeneous (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) :
    locallyConstantCochains (underlyingRep X) n :=
  ⟨fun g => nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g),
    (IsLocallyConstant.iff_continuous _).2
      ((nestedHomeomorph X (n + 1) σ.1).continuous.comp (continuous_partialProd n))⟩

omit [IsDiscreteRep (underlyingRep X)] in
theorem toInhomogeneous_apply (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) (g : Fin n → G) :
    (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g =
      nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g) :=
  rfl

def homogeneousFun (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (x : Fin (n + 1) → G) : X :=
  X.ρ (x 0) (φ fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)

omit [LocallyCompactSpace G] [DiscreteTopology X] in
theorem isLocallyConstant_homogeneousFun (n : ℕ) {φ : (Fin n → G) → underlyingRep X}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant (homogeneousFun X n φ) :=
  isLocallyConstant_ρ_apply (underlyingRep X) (continuous_apply 0)
    (hφ.comp_continuous (continuous_pi fun _ =>
      ((continuous_apply _).inv).mul (continuous_apply _)))

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [DiscreteTopology X]
  [IsDiscreteRep (underlyingRep X)] in
theorem homogeneousFun_mul (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (g : G)
    (x : Fin (n + 1) → G) :
    homogeneousFun X n φ (fun i => g * x i) = X.ρ g (homogeneousFun X n φ x) := by
  simp only [homogeneousFun, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
  rfl

def ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n) :
    (resolutionX X (n + 1)).ρ.invariants :=
  ⟨(nestedHomeomorph X (n + 1)).symm
      ⟨homogeneousFun X n φ.1, (isLocallyConstant_homogeneousFun X n φ.2).continuous⟩, by
    rw [mem_invariants]
    intro g
    apply (nestedHomeomorph X (n + 1)).injective
    ext x
    rw [nestedHomeomorph_ρ_apply, Homeomorph.apply_symm_apply]
    change X.ρ g (homogeneousFun X n φ.1 fun i => g⁻¹ * x i) = homogeneousFun X n φ.1 x
    rw [homogeneousFun_mul]
    change (X.ρ g * X.ρ g⁻¹) _ = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl⟩

omit [DiscreteTopology X] in
theorem nestedHomeomorph_ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n)
    (x : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 1) (ofInhomogeneous X n φ).1 x = homogeneousFun X n φ.1 x := by
  simp [ofInhomogeneous]

def homogeneousEquiv (n : ℕ) :
    locallyConstantCochains (underlyingRep X) n ≃ₗ[k] (resolutionX X (n + 1)).ρ.invariants :=
  LinearEquiv.symm
  { toFun := toInhomogeneous X n
    invFun := ofInhomogeneous X n
    map_add' σ τ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_add, Pi.add_apply]
      rw [nestedHomeomorph_add]
      rfl
    map_smul' r σ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [nestedHomeomorph_smul]
      rfl
    left_inv σ := by
      apply Subtype.ext
      apply (nestedHomeomorph X (n + 1)).injective
      ext x
      rw [nestedHomeomorph_ofInhomogeneous]
      change X.ρ (x 0) (nestedHomeomorph X (n + 1) σ.1
        (Fin.partialProd fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)) = _
      rw [← nestedHomeomorph_mul_apply_of_mem_invariants X σ.2]
      congr 1
      exact Fin.partialProd_left_inv x
    right_inv φ := by
      ext g
      rw [toInhomogeneous_apply, nestedHomeomorph_ofInhomogeneous]
      simp only [homogeneousFun, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
      rfl }

omit [IsDiscreteRep (underlyingRep X)] in

theorem nestedHomeomorph_d_partialProd (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants)
    (g : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 2) ((d X (n + 1)).hom σ.1) (Fin.partialProd g) =
      (inhomogeneousCochains.d (underlyingRep X) n).hom
        (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g := by
  rw [nestedHomeomorph_d_apply, Fin.sum_univ_succ, inhomogeneousCochains.d_hom_apply]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.partialProd_succ']
    exact nestedHomeomorph_mul_apply_of_mem_invariants X σ.2 _ _
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInhomogeneous_apply, Fin.partialProd_contractNth, Fin.val_succ]
    rfl

theorem homogeneousEquiv_symm_d (i : ℕ) (σ : (homogeneousCochains X).X i) :
    (homogeneousEquiv X (i + 1)).symm (((homogeneousCochains X).d i (i + 1)).hom σ) =
      (dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ) := by
  apply Subtype.ext
  funext g
  rw [dLocallyConstant_hom_apply]
  change nestedHomeomorph X (i + 2) (((homogeneousCochains X).d i (i + 1)).hom σ).1
    (Fin.partialProd g) = _
  rw [homogeneousCochains.d_apply]
  exact nestedHomeomorph_d_partialProd X i σ g

noncomputable def cochainsIsoHomogeneousCochains :
    cochainsComplex (underlyingRep X) ≅
      ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
        (homogeneousCochains X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (homogeneousEquiv X n).toModuleIso) (by
    rintro i j (rfl : i + 1 = j)
    rw [cochainsComplex_d]
    ext φ : 2
    obtain ⟨σ, rfl⟩ := (homogeneousEquiv X i).symm.surjective φ
    change ((homogeneousCochains X).d i (i + 1)).hom (homogeneousEquiv X i
      ((homogeneousEquiv X i).symm σ)) = homogeneousEquiv X (i + 1)
        ((dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ))
    rw [LinearEquiv.apply_symm_apply]
    exact (homogeneousEquiv X (i + 1)).symm_apply_eq.1 (homogeneousEquiv_symm_d X i σ))

noncomputable def cohomologyIsoContinuousCohomology (n : ℕ) :
    cohomology (underlyingRep X) n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology n X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cochainsIsoHomogeneousCochains X) ≪≫
    ((homogeneousCochains X).sc n).mapHomologyIso (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))

section Discrete

variable [DiscreteTopology k]

noncomputable def cohomologyIsoContinuousCohomologyDiscrete (A : Rep.{u} k G) [IsDiscreteRep A]
    (n : ℕ) :
    cohomology A n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology n (discreteTopRep A)) :=
  cohomologyIsoContinuousCohomology (discreteTopRep A) n

end Discrete

end GroundTheory.ProfCoh
end
