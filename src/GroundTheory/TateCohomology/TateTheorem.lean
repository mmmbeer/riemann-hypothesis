import Mathlib
import GroundTheory.TateCohomology.AugmentationSES
import GroundTheory.TateCohomology.CohTrivialBasic
import GroundTheory.TateCohomology.DeltaMap
import GroundTheory.TateCohomology.CohTrivial
import GroundTheory.TateCohomology.TateConnecting
import GroundTheory.TateCohomology.TateLow
import GroundTheory.TateCohomology.TateGroupIso
import GroundTheory.TateCohomology.TateZeroClass
import GroundTheory.TateCohomology.CoresRes

section
set_option maxSynthPendingDepth 1

open CategoryTheory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)

def pullbackSubmodule : Submodule k (S.X₂.V × Y.V) :=
  LinearMap.ker (S.g.hom.toLinearMap ∘ₗ LinearMap.fst k S.X₂.V Y.V -
    β.hom.toLinearMap ∘ₗ LinearMap.snd k S.X₂.V Y.V)

variable {S β} in
theorem mem_pullbackSubmodule {p : S.X₂.V × Y.V} :
    p ∈ pullbackSubmodule S β ↔ S.g.hom p.1 = β.hom p.2 := by
  simp [pullbackSubmodule, sub_eq_zero]

theorem pullbackSubmodule_le_comap (g : G) :
    pullbackSubmodule S β ≤ (pullbackSubmodule S β).comap ((S.X₂.ρ.prod Y.ρ) g) := by
  intro p hp
  rw [Submodule.mem_comap, mem_pullbackSubmodule]
  rw [mem_pullbackSubmodule] at hp
  simp [Rep.hom_comm_apply, hp]

noncomputable abbrev pullbackRep : Rep.{u} k G :=
  Rep.subrepresentation (Rep.of (S.X₂.ρ.prod Y.ρ)) (pullbackSubmodule S β)
    (pullbackSubmodule_le_comap S β)

noncomputable def pullbackFst : pullbackRep S β ⟶ S.X₂ :=
  Rep.ofHom ⟨LinearMap.fst k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

noncomputable def pullbackSnd : pullbackRep S β ⟶ Y :=
  Rep.ofHom ⟨LinearMap.snd k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

@[simp] theorem pullbackFst_apply (p : pullbackRep S β) : (pullbackFst S β).hom p = p.1.1 := rfl

@[simp] theorem pullbackSnd_apply (p : pullbackRep S β) : (pullbackSnd S β).hom p = p.1.2 := rfl

theorem g_apply_f_apply (x : S.X₁) : S.g.hom (S.f.hom x) = 0 := by
  change (S.f ≫ S.g).hom x = 0
  rw [S.zero]
  rfl

noncomputable def pullbackιLinear : S.X₁.V →ₗ[k] pullbackSubmodule S β :=
  LinearMap.codRestrict (pullbackSubmodule S β)
    (LinearMap.prod S.f.hom.toLinearMap 0) fun x => by
      rw [mem_pullbackSubmodule]
      simp [g_apply_f_apply]

noncomputable def pullbackι : S.X₁ ⟶ pullbackRep S β :=
  Rep.ofHom ⟨pullbackιLinear S β, fun g => by
    refine LinearMap.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
    · simp [pullbackιLinear, Rep.hom_comm_apply]
    · simp [pullbackιLinear]⟩

@[simp] theorem pullbackι_apply_fst (x : S.X₁) : ((pullbackι S β).hom x).1.1 = S.f.hom x := rfl

@[simp] theorem pullbackι_apply_snd (x : S.X₁) : ((pullbackι S β).hom x).1.2 = 0 := rfl

theorem pullbackι_pullbackSnd : pullbackι S β ≫ pullbackSnd S β = 0 := by
  ext x
  rfl

noncomputable def pullbackSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (pullbackι S β) (pullbackSnd S β) (pullbackι_pullbackSnd S β)

@[simp] theorem pullbackSES_X₁ : (pullbackSES S β).X₁ = S.X₁ := rfl
@[simp] theorem pullbackSES_X₂ : (pullbackSES S β).X₂ = pullbackRep S β := rfl
@[simp] theorem pullbackSES_X₃ : (pullbackSES S β).X₃ = Y := rfl
@[simp] theorem pullbackSES_f : (pullbackSES S β).f = pullbackι S β := rfl
@[simp] theorem pullbackSES_g : (pullbackSES S β).g = pullbackSnd S β := rfl

variable {S} in

theorem pullbackSES_shortExact (hS : S.ShortExact) : (pullbackSES S β).ShortExact := by
  have hex := function_exact_of_shortExact hS
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  refine shortExact_of_linear ?_ ?_ ?_
  · intro a b hab
    exact hinj (congrArg (fun p : pullbackRep S β => p.1.1) hab)
  · intro y
    obtain ⟨x, hx⟩ := hsurj (β.hom y)
    exact ⟨⟨(x, y), mem_pullbackSubmodule.2 hx⟩, rfl⟩
  · intro p hp
    have hp2 : p.1.2 = 0 := hp
    have hg : S.g.hom p.1.1 = 0 := by
      rw [(mem_pullbackSubmodule.1 p.2), hp2, map_zero]
    obtain ⟨x, hx⟩ := (hex p.1.1).1 hg
    refine ⟨x, Subtype.ext (Prod.ext hx hp2.symm)⟩

noncomputable def pullbackSESHom : pullbackSES S β ⟶ S where
  τ₁ := 𝟙 S.X₁
  τ₂ := pullbackFst S β
  τ₃ := β
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2

@[simp] theorem pullbackSESHom_τ₁ : (pullbackSESHom S β).τ₁ = 𝟙 S.X₁ := rfl
@[simp] theorem pullbackSESHom_τ₂ : (pullbackSESHom S β).τ₂ = pullbackFst S β := rfl
@[simp] theorem pullbackSESHom_τ₃ : (pullbackSESHom S β).τ₃ = β := rfl

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

open CategoryTheory groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

variable (k G : Type u) [CommRing k] [Group G]

noncomputable def augHom : Rep.leftRegular k G ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨augmentation k G, fun g => LinearMap.ext fun x => by
    change augmentation k G ((Rep.leftRegular k G).ρ g x) = augmentation k G x
    exact augmentation_ρ g x⟩

@[simp] theorem augHom_apply (x : Rep.leftRegular k G) :
    (augHom k G).hom x = augmentation k G x := rfl

theorem augIdealι_augHom : augIdealι k G ≫ augHom k G = 0 := by
  ext x
  exact LinearMap.mem_ker.1 x.2

noncomputable def augTrivSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (augIdealι k G) (augHom k G) (augIdealι_augHom k G)

@[simp] theorem augTrivSES_X₁ : (augTrivSES k G).X₁ = augIdeal k G := rfl
@[simp] theorem augTrivSES_X₂ : (augTrivSES k G).X₂ = Rep.leftRegular k G := rfl
@[simp] theorem augTrivSES_X₃ : (augTrivSES k G).X₃ = Rep.trivial k G k := rfl

theorem augTrivSES_shortExact : (augTrivSES k G).ShortExact := by
  refine shortExact_of_linear (fun a b h => Subtype.ext h)
    (fun r => ⟨MonoidAlgebra.single (1 : G) (show k from r), ?_⟩)
    (fun y hy => ⟨⟨y, LinearMap.mem_ker.2 hy⟩, rfl⟩)
  exact augmentation_single (k := k) (1 : G) (show k from r)

theorem cohTrivial_leftRegular [Fintype G] : CohTrivial (Rep.leftRegular k G) := by
  refine cohTrivial_of_sum_eq _ coeffOneProj fun m => ?_
  induction m using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | single h c =>
    rw [Fintype.sum_eq_single h]
    · simp [coeffOneProj_apply]
    · intro g hg
      have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
      simp [coeffOneProj_apply, this]

variable {k G}

noncomputable def augIdealSubOne (g : G) : augIdeal k G :=
  ⟨MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1, by
    rw [LinearMap.mem_ker, map_sub, augmentation_single, augmentation_single, sub_self]⟩

@[simp] theorem augIdealSubOne_val (g : G) :
    ((augIdealSubOne g : augIdeal k G) : MonoidAlgebra k G) =
      MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1 := rfl

section Cocycle

variable {A : Rep.{u} k G}

noncomputable def cocycleLinear (f : cocycles₁ A) : MonoidAlgebra k G →ₗ[k] A.V :=
  Finsupp.linearCombination k (fun g => f g) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem cocycleLinear_single (f : cocycles₁ A) (g : G) (r : k) :
    cocycleLinear f (MonoidAlgebra.single g r) = r • f g := by
  simp [cocycleLinear]

theorem cocycleLinear_ρ (f : cocycles₁ A) (s : G) (x : MonoidAlgebra k G) :
    cocycleLinear f ((Rep.leftRegular k G).ρ s x) =
      A.ρ s (cocycleLinear f x) + augmentation k G x • f s := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_smul]; abel
  | single g r =>
    have hf : f (s * g) = A.ρ s (f g) + f s := (mem_cocycles₁_iff _).1 f.2 s g
    rw [Representation.ofMulAction_single, smul_eq_mul, cocycleLinear_single, cocycleLinear_single,
      augmentation_single, map_smul, hf, smul_add]

noncomputable def cocycleHom (f : cocycles₁ A) : augIdeal k G ⟶ A :=
  Rep.ofHom ⟨cocycleLinear f ∘ₗ (LinearMap.ker (augmentation k G)).subtype, fun s =>
    LinearMap.ext fun x => by
      have hx : augmentation k G x.1 = 0 := LinearMap.mem_ker.1 x.2
      change cocycleLinear f ((Rep.leftRegular k G).ρ s x.1) = A.ρ s (cocycleLinear f x.1)
      rw [cocycleLinear_ρ, hx, zero_smul, add_zero]⟩

theorem cocycleHom_apply (f : cocycles₁ A) (x : augIdeal k G) :
    (cocycleHom f).hom x = cocycleLinear f x.1 := rfl

theorem cocycleHom_augIdealSubOne (f : cocycles₁ A) (g : G) :
    (cocycleHom f).hom (augIdealSubOne g) = f g := by
  rw [cocycleHom_apply, augIdealSubOne_val, map_sub, cocycleLinear_single, cocycleLinear_single,
    cocycles₁_map_one, smul_zero, sub_zero, one_smul]

end Cocycle

section Restrict

variable (k) {H : Type u} [Group H] (φ : H →* G)

noncomputable def augCocycle : cocycles₁ (Rep.res φ (augIdeal k G)) :=
  ⟨fun h => augIdealSubOne (φ h), (mem_cocycles₁_iff _).2 fun a b => by
    apply Subtype.ext
    change MonoidAlgebra.single (φ (a * b)) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ a) (MonoidAlgebra.single (φ b) 1 - MonoidAlgebra.single 1 1) +
        (MonoidAlgebra.single (φ a) 1 - MonoidAlgebra.single 1 1)
    rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, smul_eq_mul,
      smul_eq_mul, mul_one, map_mul]
    abel⟩

@[simp] theorem augCocycle_apply (h : H) : augCocycle k φ h = augIdealSubOne (φ h) := rfl

theorem augTrivSES_res_shortExact : ((augTrivSES k G).map (resFunctor φ)).ShortExact :=
  (shortExact_res φ).2 (augTrivSES_shortExact k G)

def oneInvariant : (Rep.res φ (Rep.trivial k G k)).ρ.invariants :=
  ⟨(1 : k), fun _ => rfl⟩

theorem δ₀_augTrivSES_res :
    δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ)) =
      H1π _ (augCocycle k φ) := by
  have hx : ((augTrivSES k G).map (resFunctor φ)).f.hom ∘ (fun h => augIdealSubOne (φ h)) =
      d₀₁ ((augTrivSES k G).map (resFunctor φ)).X₂ (MonoidAlgebra.single (1 : G) (1 : k)) := by
    funext h
    change MonoidAlgebra.single (φ h) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ h) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  exact δ₀_apply (augTrivSES_res_shortExact k φ) (oneInvariant k φ)
    (MonoidAlgebra.single (1 : G) (1 : k)) (by exact augmentation_single (k := k) (1 : G) (1 : k)) _ hx

end Restrict

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

open CategoryTheory Limits groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

section Construction

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)

theorem isZero_groupCohomology_coind_two : IsZero (groupCohomology (coindSES.obj M).X₂ 2) :=
  ((tateAcyclic_coindSES_X₂ M) 2).of_iso (tateIsoH _ 2 2 rfl).symm

theorem exists_cocycle_δ_eq : ∃ f : cocycles₁ (coindSES.obj M).X₃,
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ f) = u := by
  have : Epi (δ (coindSES_shortExact M) 1 2 rfl) :=
    epi_δ_of_isZero (coindSES_shortExact M) 1 (isZero_groupCohomology_coind_two M)
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective _).1 this u
  obtain ⟨f, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π _)).1 inferInstance v
  exact ⟨f, hv⟩

noncomputable def splittingCocycle : cocycles₁ (coindSES.obj M).X₃ :=
  (exists_cocycle_δ_eq M u).choose

theorem δ_splittingCocycle :
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ (splittingCocycle M u)) = u :=
  (exists_cocycle_δ_eq M u).choose_spec

noncomputable def splittingSES : ShortComplex (Rep.{u} k G) :=
  pullbackSES (coindSES.obj M) (cocycleHom (splittingCocycle M u))

theorem splittingSES_shortExact : (splittingSES M u).ShortExact :=
  pullbackSES_shortExact _ (coindSES_shortExact M)

noncomputable abbrev splittingModule : Rep.{u} k G := (splittingSES M u).X₂

omit [Fintype G] in

theorem map_H1π_augCocycle {H : Type u} [Group H] (φ : H →* G) {A : Rep.{u} k G}
    (f : cocycles₁ A) :
    map (A := res φ (augIdeal k G)) (B := res φ A) (MonoidHom.id H)
      ((resFunctor φ).map (cocycleHom f)) 1 (H1π _ (augCocycle k φ)) =
    map φ (𝟙 (res φ A)) 1 (H1π A f) := by
  rw [H1π_comp_map_apply, H1π_comp_map_apply]
  congr 1
  apply cocycles₁_ext
  intro h
  exact cocycleHom_augIdealSubOne f (φ h)

noncomputable def splittingSESResHom {H : Type u} [Group H] (φ : H →* G) :
    (splittingSES M u).map (resFunctor φ) ⟶ (coindSES.obj M).map (resFunctor φ) where
  τ₁ := 𝟙 _
  τ₂ := (resFunctor φ).map (pullbackFst _ (cocycleHom (splittingCocycle M u)))
  τ₃ := (resFunctor φ).map (cocycleHom (splittingCocycle M u))
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2

theorem δ_splittingSES_res_δ₀ {H : Type u} [Group H] (φ : H →* G) :
    δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
      (δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ))) =
    map φ (𝟙 (res φ M)) 2 u := by
  rw [δ₀_augTrivSES_res]
  have hN := groupCohomology.δ_naturality ((shortExact_res φ).2 (splittingSES_shortExact M u))
    ((shortExact_res φ).2 (coindSES_shortExact M)) (splittingSESResHom M u φ) 1 2 rfl
  have e : (map (MonoidHom.id H) (𝟙 (res φ M)) 2).hom
      (δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
        (H1π (res φ (augIdeal k G)) (augCocycle k φ))) =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map (A := res φ (augIdeal k G)) (B := res φ (coindSES.obj M).X₃) (MonoidHom.id H)
          ((resFunctor φ).map (cocycleHom (splittingCocycle M u))) 1).hom
          (H1π _ (augCocycle k φ))) :=
    congr(($hN).hom (H1π _ (augCocycle k φ)))
  have hid : ∀ y, (map (A := res φ M) (B := res φ M) (MonoidHom.id H) (𝟙 (res φ M)) 2).hom y =
      y := fun y => by
    rw [groupCohomology.map_id]
    rfl
  have hR := congr(($(δ_comp_map_res φ (coindSES_shortExact M) 1 2 rfl)).hom
    (H1π _ (splittingCocycle M u)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hR
  have hR' : (map φ (𝟙 (res φ M)) 2).hom u =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map φ (𝟙 (res φ (coindSES.obj M).X₃)) 1).hom (H1π _ (splittingCocycle M u))) := by
    conv_lhs => rw [← δ_splittingCocycle M u]
    exact hR
  refine (hid _).symm.trans (e.trans ?_)
  rw [map_H1π_augCocycle φ (splittingCocycle M u)]
  exact hR'.symm

end Construction

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

open CategoryTheory Limits groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

section LES

variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)

theorem eq_zero_of_isZero {A : ModuleCat.{u} k} (h : IsZero A) (x : A) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero h).elim x 0

theorem isZero_of_forall_eq_zero {A : ModuleCat.{u} k} (h : ∀ x : A, x = 0) : IsZero A :=
  ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩

include hX in

theorem δ_map_g_apply (i j : ℕ) (hij : i + 1 = j) (x : groupCohomology X.X₂ i) :
    δ hX i j hij (map (MonoidHom.id H) X.g i x) = 0 := by
  have h := congr(($((map_cochainsFunctor_shortExact hX).comp_δ i j hij)).hom x)
  exact h

include hX in

theorem map_f_δ_apply (i j : ℕ) (hij : i + 1 = j) (z : groupCohomology X.X₃ i) :
    map (MonoidHom.id H) X.f j (δ hX i j hij z) = 0 := by
  have h := congr(($((map_cochainsFunctor_shortExact hX).δ_comp i j hij)).hom z)
  exact h

include hX in

theorem exists_map_f_eq (n : ℕ) (x : groupCohomology X.X₂ n)
    (hx : map (MonoidHom.id H) X.g n x = 0) : ∃ w, map (MonoidHom.id H) X.f n w = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (mapShortComplex₂_exact hX n) x hx

include hX in

theorem isZero_X₂_of_injective_δ (n : ℕ) (h₁ : IsZero (groupCohomology X.X₁ n))
    (hδ : Function.Injective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ n) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  have h1 : map (MonoidHom.id H) X.g n x = 0 :=
    hδ (by rw [δ_map_g_apply hX n (n + 1) rfl, map_zero])
  obtain ⟨w, hw⟩ := exists_map_f_eq hX n x h1
  rw [← hw, eq_zero_of_isZero h₁ w, map_zero]

include hX in

theorem isZero_X₂_succ_of_surjective_δ (n : ℕ) (h₃ : IsZero (groupCohomology X.X₃ (n + 1)))
    (hδ : Function.Surjective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ (n + 1)) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨w, hw⟩ := exists_map_f_eq hX (n + 1) x (eq_zero_of_isZero h₃ _)
  obtain ⟨z, rfl⟩ := hδ w
  rw [← hw, map_f_δ_apply hX n (n + 1) rfl z]

end LES

section TrivialInt

theorem isZero_H1_trivial_int {H : Type} [Group H] [Finite H] :
    IsZero (groupCohomology (Rep.trivial ℤ H ℤ) 1) := by
  have : Subsingleton (Additive H →+ ℤ) := ⟨fun f g => AddMonoidHom.ext fun x => by
    have key : ∀ φ : Additive H →+ ℤ, φ x = 0 := fun φ => by
      have h : addOrderOf x • φ x = 0 := by rw [← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
      exact (smul_eq_zero.1 h).resolve_left (addOrderOf_pos x).ne'
    rw [key f, key g]⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (H1IsoOfIsTrivial _)

end TrivialInt

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]

theorem tateAcyclic_res_leftRegular : TateAcyclic (res S.subtype (Rep.leftRegular ℤ G)) :=
  cohTrivial_leftRegular ℤ G S

theorem isZero_groupCohomology_res_leftRegular (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (res S.subtype (Rep.leftRegular ℤ G)) n) :=
  ((tateAcyclic_res_leftRegular S) n).of_iso (tateIsoH _ n n rfl).symm

noncomputable def augClass : groupCohomology (res S.subtype (augIdeal ℤ G)) 1 :=
  δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl ((H0Iso _).inv (oneInvariant ℤ S.subtype))

theorem exists_eq_zsmul_augClass (y : groupCohomology (res S.subtype (augIdeal ℤ G)) 1) :
    ∃ m : ℤ, y = m • augClass S := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 0
      (isZero_groupCohomology_res_leftRegular S 1)
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep y
  let c : ℤ := show ℤ from ((H0Iso _).hom w).1
  refine ⟨c, ?_⟩
  have hw : w = (H0Iso _).inv (c • oneInvariant ℤ S.subtype) := by
    have : ((H0Iso _).hom w) = c • oneInvariant ℤ S.subtype := by
      apply Subtype.ext
      change _ = c * 1
      rw [mul_one]
    rw [← this]
    exact ((Iso.hom_inv_id_apply (H0Iso _) w)).symm
  conv_lhs => rw [hw]
  rw [map_zsmul]
  exact map_zsmul _ c _

noncomputable def subgroupNormElt : MonoidAlgebra ℤ G :=
  ∑ t : S, MonoidAlgebra.single (t : G) (1 : ℤ)

omit [Fintype G] in

theorem ρ_subgroupNormElt (s : S) :
    (Rep.leftRegular ℤ G).ρ (s : G) (subgroupNormElt S) = subgroupNormElt S := by
  simp only [subgroupNormElt, map_sum, Representation.ofMulAction_single, smul_eq_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft s) _ _ (fun t => rfl)

omit [Fintype G] in

theorem augmentation_subgroupNormElt :
    augmentation ℤ G (subgroupNormElt S) = (Fintype.card S : ℤ) := by
  rw [subgroupNormElt, map_sum,
    Finset.sum_congr rfl (fun (x : S) _ => augmentation_single (k := ℤ) (x : G) (1 : ℤ))]
  simp

theorem card_smul_augClass : (Fintype.card S : ℤ) • augClass S = 0 := by
  let z : (res S.subtype (Rep.trivial ℤ G ℤ)).ρ.invariants := ⟨(Fintype.card S : ℤ), fun _ => rfl⟩
  have hx : ((augTrivSES ℤ G).map (resFunctor S.subtype)).f.hom ∘
      (0 : S → res S.subtype (augIdeal ℤ G)) =
      d₀₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₂ (subgroupNormElt S) := by
    funext s
    change (augIdealι ℤ G).hom 0 =
      (Rep.leftRegular ℤ G).ρ (s : G) (subgroupNormElt S) - subgroupNormElt S
    rw [map_zero, ρ_subgroupNormElt, sub_self]
  have hδ := δ₀_apply (augTrivSES_res_shortExact ℤ S.subtype) z (subgroupNormElt S)
    (by exact augmentation_subgroupNormElt S) _ hx
  have hz : z = (Fintype.card S : ℤ) • oneInvariant ℤ S.subtype := by
    apply Subtype.ext
    change _ = (Fintype.card S : ℤ) * 1
    rw [mul_one]
  have h0 : H1π ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₁
      ⟨0, mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ = 0 := by
    have : (⟨0, mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ :
        cocycles₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₁) = 0 := rfl
    rw [this, map_zero]
  have e1 : (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv z =
      (Fintype.card S : ℤ) • (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv
        (oneInvariant ℤ S.subtype) :=
    (congrArg (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv hz).trans
      (map_zsmul _ _ _)
  exact (map_zsmul _ _ _).symm.trans ((congrArg _ e1.symm).trans (hδ.trans h0))

noncomputable abbrev resClass : groupCohomology (res S.subtype M) 2 :=
  map S.subtype (𝟙 (res S.subtype M)) 2 u

noncomputable abbrev splitδ :
    groupCohomology (res S.subtype (augIdeal ℤ G)) 1 ⟶ groupCohomology (res S.subtype M) 2 :=
  δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 2 rfl

omit [Fintype S] in

theorem splitδ_augClass : splitδ M u S (augClass S) = resClass M u S :=
  δ_splittingSES_res_δ₀ M u S.subtype

theorem splitδ_injective (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    Function.Injective (splitδ M u S) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨m, rfl⟩ := exists_eq_zsmul_augClass S y
  rw [map_zsmul, splitδ_augClass] at hy
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.2 hy
  rw [h2, Nat.card_eq_fintype_card] at hd
  obtain ⟨t, rfl⟩ := hd
  rw [mul_comm, mul_zsmul, card_smul_augClass, zsmul_zero]

omit [Fintype S] in

theorem splitδ_surjective
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    Function.Surjective (splitδ M u S) := by
  intro y
  obtain ⟨m, rfl⟩ := h3 y
  exact ⟨m • augClass S, by rw [map_zsmul, splitδ_augClass]⟩

theorem isZero_groupCohomology_res_augIdeal_two :
    IsZero (groupCohomology (res S.subtype (augIdeal ℤ G)) 2) := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 1 2 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 1
      (isZero_groupCohomology_res_leftRegular S 2)
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep x
  have hz : IsZero (groupCohomology (res S.subtype (Rep.trivial ℤ G ℤ)) 1) :=
    isZero_H1_trivial_int (H := S)
  exact (congrArg _ (eq_zero_of_isZero hz z)).trans (map_zero _)

theorem isZero_groupCohomology_res_splittingModule_one
    (h1 : IsZero (groupCohomology (res S.subtype M) 1))
    (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    IsZero (groupCohomology (res S.subtype (splittingModule M u)) 1) :=
  isZero_X₂_of_injective_δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 h1
    (splitδ_injective M u S h2)

theorem isZero_groupCohomology_res_splittingModule_two
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    IsZero (groupCohomology (res S.subtype (splittingModule M u)) 2) :=
  isZero_X₂_succ_of_surjective_δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1
    (isZero_groupCohomology_res_augIdeal_two S) (splitδ_surjective M u S h3)

omit [Fintype S] in

theorem cohTrivial_splittingModule
    (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
    (h2 : ∀ S : Subgroup G, addOrderOf (map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
      ∃ m : ℤ, y = m • map S.subtype (𝟙 (res S.subtype M)) 2 u) :
    CohTrivial (splittingModule M u) := by
  refine cohTrivial_of_forall_subgroup _ 1 fun T _ => ⟨?_, ?_⟩
  · exact (isZero_groupCohomology_res_splittingModule_one M u T (h1 T) (h2 T)).of_iso
      (tateIsoH _ 1 1 rfl)
  · exact (isZero_groupCohomology_res_splittingModule_two M u T (h3 T)).of_iso
      (tateIsoH _ (1 + 1) 2 (by norm_num))

end Tate

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}
  (hX : X.ShortExact)

theorem tateIsoH_δ_zero_apply (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) (c : (tateComplex X.X₃).cycles 0)
    (hc : ((tateComplex X.X₃).iCycles 0).hom c = (cochainsIso₀ X.X₃).inv.hom z) :
    (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom
      ((TateCohomology.δ hX 0).hom (((tateComplex X.X₃).homologyπ 0).hom c)) =
      H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  have hxc : x ∈ cocycles₁ X.X₁ := mem_cocycles₁_of_comp_eq_d₀₁ hX hx
  let x₁ : (tateComplex X.X₁).X (0 + 1) := (cochainsIso₁ X.X₁).inv.hom x
  let x₂ : (tateComplex X.X₂).X 0 := (cochainsIso₀ X.X₂).inv.hom y
  have hd : ((tateComplex X.X₁).d (0 + 1) (0 + 1 + 1)).hom x₁ = 0 := by
    have e := congr(($(eq_d₁₂_comp_inv X.X₁)).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    have h0 : d₁₂ X.X₁ x = 0 := LinearMap.mem_ker.1 hxc
    rw [h0, map_zero] at e
    exact e
  have hx₂ : ((tateComplex.map X.g).f 0).hom x₂ = ((tateComplex X.X₃).iCycles 0).hom c := by
    rw [hc]
    funext v
    exact hy
  have hx₁ : ((tateComplex.map X.f).f (0 + 1)).hom x₁ = ((tateComplex X.X₂).d 0 (0 + 1)).hom x₂ := by
    have e := congr(($(eq_d₀₁_comp_inv X.X₂)).hom y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    refine Eq.trans ?_ e.symm
    funext v
    exact congrFun hx (v 0)
  have h1 := tδ_apply hX 0 (((tateComplex X.X₃).iCycles 0).hom c)
    (tate_d_iCycles_int _ 0 c) x₂ hx₂ x₁ hx₁ hd
  rw [tateCyclesMk_iCycles] at h1
  have h2 := tateIsoH_homologyπ X.X₁ 1 (tateCyclesMk X.X₁ (0 + 1) x₁ hd)
  refine (congrArg (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom h1).trans (h2.trans ?_)
  have h3 := cocyclesMk₁_eq X.X₁ ⟨x, hxc⟩
  refine Eq.trans ?_ (congrArg (π X.X₁ 1).hom h3)
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans ((iCycles_tateCyclesMk _ _ _ _).trans (iCocycles_mk _ _).symm)

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

omit [Fintype G] in

theorem tate_natTrans_eq_of_eq_zero {U V : Type u} [Group U] [Group V] [Fintype U] [Fintype V]
    (E : Rep.{u} k G ⥤ Rep.{u} k U) (E' : Rep.{u} k G ⥤ Rep.{u} k V)
    [E.PreservesZeroMorphisms] [E'.PreservesZeroMorphisms]
    (hE : ∀ {X : ShortComplex (Rep.{u} k G)}, X.ShortExact → (X.map E).ShortExact)
    (hE' : ∀ {X : ShortComplex (Rep.{u} k G)}, X.ShortExact → (X.map E').ShortExact)
    (hEc : ∀ A : Rep.{u} k G, TateAcyclic (E.obj (coindSES.obj A).X₂))
    (hEi : ∀ A : Rep.{u} k G, TateAcyclic (E'.obj (indSES.obj A).X₂))
    (α β : ∀ n : ℤ, E ⋙ tateCohomologyFunctor n ⟶ E' ⋙ tateCohomologyFunctor n)
    (hα : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
      TateCohomology.δ (hE hX) n ≫ (α (n + 1)).app X.X₁ =
        (α n).app X.X₃ ≫ TateCohomology.δ (hE' hX) n)
    (hβ : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
      TateCohomology.δ (hE hX) n ≫ (β (n + 1)).app X.X₁ =
        (β n).app X.X₃ ≫ TateCohomology.δ (hE' hX) n)
    (h0 : α 0 = β 0) (n : ℤ) : α n = β n := by
  have up : ∀ m : ℤ, α m = β m → α (m + 1) = β (m + 1) := by
    intro m hm
    refine NatTrans.ext (funext fun A => ?_)
    have hX := coindSES_shortExact A
    have : IsIso (TateCohomology.δ (hE hX) m) :=
      isIso_δ_of_tateAcyclic (hE hX) (hEc A) m
    refine (cancel_epi (TateCohomology.δ (hE hX) m)).1 ?_
    exact (hα hX m).trans ((congrArg (fun t => t.app _ ≫ _) hm).trans (hβ hX m).symm)
  have down : ∀ m : ℤ, α (m + 1) = β (m + 1) → α m = β m := by
    intro m hm
    refine NatTrans.ext (funext fun A => ?_)
    have hX := indSES_shortExact A
    have : IsIso (TateCohomology.δ (hE' hX) m) :=
      isIso_δ_of_tateAcyclic (hE' hX) (hEi A) m
    refine (cancel_mono (TateCohomology.δ (hE' hX) m)).1 ?_
    exact (hα hX m).symm.trans ((congrArg (fun t => _ ≫ t.app _) hm).trans (hβ hX m))
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact up _ ih
  | pred i ih => exact down _ (by rwa [sub_add_cancel])

theorem tateAcyclic_res_coindSES_X₂ (U : Subgroup G) [Fintype U] (A : Rep.{u} k G) :
    TateAcyclic ((resFunctor U.subtype).obj (coindSES.obj A).X₂) :=
  cohTrivial_coind_bot _ U

theorem tateAcyclic_res_indSES_X₂ (U : Subgroup G) [Fintype U] (A : Rep.{u} k G) :
    TateAcyclic ((resFunctor U.subtype).obj (indSES.obj A).X₂) :=
  cohTrivial_ind_bot _ U

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology groupHomology

universe u

variable {k H K : Type u} [CommRing k] [Group H] [Group K]

section Complex

variable (e : H ≃* K)

noncomputable def transportChainsMor (B : Rep.{u} k K) :
    B ⟶ res (e.symm : K →* H) (res (e : H →* K) B) :=
  Rep.ofHom ⟨LinearMap.id, fun x => by
    ext b
    simp⟩

@[simp]
lemma transportChainsMor_hom_apply (B : Rep.{u} k K) (b : B) :
    (transportChainsMor e B).hom b = b := rfl

variable [Fintype H] [Fintype K]

lemma transport_comm_zero (B : Rep.{u} k K) :
    (chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0 ≫
        (tateComplexConnectData (res (e : H →* K) B)).d₀ =
      (tateComplexConnectData B).d₀ ≫ (cochainsMap (e : H →* K) (𝟙 _)).f 0 := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun v b => ?_)
  refine funext fun w => ?_
  have e1 : ((tateComplexConnectData B).d₀).hom (Finsupp.single v b) = fun _ => B.ρ.norm b := by
    simp [Rep.tateNorm_eq]
    rfl
  have e2 : ((tateComplexConnectData (res (e : H →* K) B)).d₀).hom
      (((chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0).hom (Finsupp.single v b)) =
      fun _ => (res (e : H →* K) B).ρ.norm b := by
    rw [chainsMap_f_single]
    simp [Rep.tateNorm_eq]
    rfl
  change ((tateComplexConnectData (res (e : H →* K) B)).d₀).hom
      (((chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0).hom (Finsupp.single v b)) w =
    ((cochainsMap (e : H →* K) (𝟙 _)).f 0).hom
      (((tateComplexConnectData B).d₀).hom (Finsupp.single v b)) w
  rw [e1, e2, norm_res_of_bijective (e : H →* K) e.bijective]
  rfl

noncomputable def tateTransportComplex (B : Rep.{u} k K) :
    tateComplex B ⟶ tateComplex (res (e : H →* K) B) :=
  CochainComplex.ConnectData.map _ _ (chainsMap (e.symm : K →* H) (transportChainsMor e B))
    (cochainsMap (e : H →* K) (𝟙 _)) (transport_comm_zero e B)

lemma tateTransportComplex_naturality {B B' : Rep.{u} k K} (φ : B ⟶ B') :
    tateTransportComplex e B ≫ tateComplex.map ((resFunctor (e : H →* K)).map φ) =
      tateComplex.map φ ≫ tateTransportComplex e B' := by
  ext (m | m) : 1
  · rfl
  · change (chainsMap (e.symm : K →* H) (transportChainsMor e B) ≫ chainsMap (MonoidHom.id H)
      ((resFunctor (e : H →* K)).map φ)).f m = (chainsMap (MonoidHom.id K) φ ≫
        chainsMap (e.symm : K →* H) (transportChainsMor e B')).f m
    rw [← chainsMap_comp, ← chainsMap_comp]
    congr 1

@[simps]
noncomputable def tateTransportComplexNatTrans :
    tateComplexFunctor k K ⟶ resFunctor (e : H →* K) ⋙ tateComplexFunctor k H where
  app := tateTransportComplex e
  naturality _ _ φ := (tateTransportComplex_naturality e φ).symm

end Complex

section Cohomology

variable [Fintype H] [Fintype K] (e : H ≃* K)

noncomputable def tateTransport (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := K) n ⟶
      resFunctor (e : H →* K) ⋙ tateCohomologyFunctor (R := k) (G := H) n :=
  Functor.whiskerRight (tateTransportComplexNatTrans e) (HomologicalComplex.homologyFunctor _ _ n)


@[simps]
noncomputable def tateTransportShortComplex (X : ShortComplex (Rep.{u} k K)) :
    X.map (tateComplexFunctor k K) ⟶
      (X.map (resFunctor (e : H →* K))).map (tateComplexFunctor k H) where
  τ₁ := tateTransportComplex e X.X₁
  τ₂ := tateTransportComplex e X.X₂
  τ₃ := tateTransportComplex e X.X₃
  comm₁₂ := tateTransportComplex_naturality e X.f
  comm₂₃ := tateTransportComplex_naturality e X.g

omit [Fintype H] [Fintype K] in

lemma shortExact_map_resFunctor_equiv {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact) :
    (X.map (resFunctor (e : H →* K))).ShortExact :=
  (Rep.shortExact_res (e : H →* K)).2 hX

theorem tateTransport_δ {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateTransport e (n + 1)).app X.X₁ =
      (tateTransport e n).app X.X₃ ≫
        TateCohomology.δ (shortExact_map_resFunctor_equiv e hX) n :=
  HomologicalComplex.HomologySequence.δ_naturality (tateTransportShortComplex e X)
    (TateCohomology.map_tateComplexFunctor_shortExact hX)
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_map_resFunctor_equiv e hX))
    n (n + 1) rfl

omit [Fintype H] [Fintype K] in

def invariantsTransport {B : Rep.{u} k K} (x : B.ρ.invariants) :
    (res (e : H →* K) B).ρ.invariants :=
  ⟨x, fun h => x.2 (e h)⟩

omit [Fintype H] [Fintype K] in
@[simp]
lemma coe_invariantsTransport {B : Rep.{u} k K} (x : B.ρ.invariants) :
    (invariantsTransport e x : B) = x := rfl


end Cohomology

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

section Invariants

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

def invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) : (res f A).ρ.invariants :=
  ⟨x, fun h => x.2 (f h)⟩

@[simp]
lemma coe_invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) :
    (invariantsRes f x : A) = x := rfl

variable (S : Subgroup G) {A : Rep.{u} k G}

lemma ρ_mul_of_mem (y : (res S.subtype A).ρ.invariants) (g : G) {s : G} (hs : s ∈ S) :
    A.ρ (g * s) (y : A) = A.ρ g y := by
  rw [map_mul, Module.End.mul_apply]
  exact congrArg (A.ρ g) (y.2 ⟨s, hs⟩)

def cosetSMul (y : (res S.subtype A).ρ.invariants) (q : G ⧸ S) : A :=
  Quotient.liftOn' q (fun g => A.ρ g y) fun g g' h => by
    rw [QuotientGroup.leftRel_apply] at h
    rw [← ρ_mul_of_mem S y g h, mul_inv_cancel_left]

@[simp]
lemma cosetSMul_mk (y : (res S.subtype A).ρ.invariants) (g : G) :
    cosetSMul S y (g : G ⧸ S) = A.ρ g y := rfl

lemma cosetSMul_smul (y : (res S.subtype A).ρ.invariants) (h : G) (q : G ⧸ S) :
    cosetSMul S y (h • q) = A.ρ h (cosetSMul S y q) := by
  induction q using QuotientGroup.induction_on with | H g =>
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, cosetSMul_mk, cosetSMul_mk, map_mul,
    Module.End.mul_apply]

variable [Fintype G]

open scoped Classical in

noncomputable def transferSum (y : (res S.subtype A).ρ.invariants) : A :=
  ∑ q : G ⧸ S, cosetSMul S y q

lemma transferSum_mem_invariants (y : (res S.subtype A).ρ.invariants) :
    transferSum S y ∈ A.ρ.invariants := fun h => by
  classical
  simp only [transferSum, map_sum]
  rw [show (∑ q : G ⧸ S, A.ρ h (cosetSMul S y q)) = ∑ q : G ⧸ S, cosetSMul S y (h • q) from
    Finset.sum_congr rfl fun q _ => (cosetSMul_smul S y h q).symm]
  exact Fintype.sum_equiv (MulAction.toPerm h) _ _ fun _ => rfl

noncomputable def transferInv (y : (res S.subtype A).ρ.invariants) : A.ρ.invariants :=
  ⟨transferSum S y, transferSum_mem_invariants S y⟩

@[simp]
lemma coe_transferInv (y : (res S.subtype A).ρ.invariants) :
    (transferInv S y : A) = transferSum S y := rfl

end Invariants

section Shapiro

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

def coindConst (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (coind S.subtype B).ρ.invariants :=
  ⟨⟨fun _ => y, (Representation.mem_coindV _ _ _).2 fun s _ => (y.2 s).symm⟩,
    fun _ => rfl⟩

@[simp]
lemma coindConst_apply (B : Rep.{u} k S) (y : B.ρ.invariants) (g : G) :
    ((coindConst S B y : coind S.subtype B) : G → B) g = y := rfl

variable [Fintype G] [Fintype S]





end Shapiro

section ResCores

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]


omit [Fintype S] in

lemma counit_indCoindIso_inv_coindConst [DecidableRel (QuotientGroup.rightRel S)]
    (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((Rep.indResAdjunction.{u} k S.subtype).counit.app A).hom
      ((indCoindIso (res S.subtype A)).inv.hom (coindConst S (res S.subtype A) y)) =
      transferSum S y := by
  classical
  change ((Rep.indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (coindConst S (res S.subtype A) y)) = _
  rw [coindToInd_apply, map_sum, transferSum]
  refine (Finset.sum_congr (by convert rfl) fun x _ => ?_ : _ = ∑ x : Quotient (QuotientGroup.rightRel S),
    cosetSMul S y (QuotientGroup.quotientRightRelEquivQuotientLeftRel S x)).trans (Equiv.sum_comp _ _)
  induction x using Quotient.inductionOn with
  | h g =>
    rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
    rfl


end ResCores

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Delta

lemma tate_whiskerRight_δ {H : Type u} [Group H] [Fintype H] {F F' : Rep.{u} k G ⥤ Rep.{u} k H}
    [F.PreservesZeroMorphisms] [F'.PreservesZeroMorphisms] (σ : F ⟶ F')
    {X : ShortComplex (Rep.{u} k G)} (hX : (X.map F).ShortExact) (hX' : (X.map F').ShortExact)
    (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateCohomologyFunctor (n + 1)).map (σ.app X.X₁) =
      (tateCohomologyFunctor n).map (σ.app X.X₃) ≫ TateCohomology.δ hX' n :=
  TateCohomology.δ_naturality hX hX' (X.mapNatTrans σ) n

lemma sq_comp {C : Type*} [Category C] {a₁ a₂ a₃ b₁ b₂ b₃ : C} {δ₁ : a₁ ⟶ b₁} {δ₂ : a₂ ⟶ b₂}
    {δ₃ : a₃ ⟶ b₃} {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} {g : b₂ ⟶ b₃} {g' : a₂ ⟶ a₃}
    (h₁ : δ₁ ≫ f = f' ≫ δ₂) (h₂ : δ₂ ≫ g = g' ≫ δ₃) : δ₁ ≫ (f ≫ g) = (f' ≫ g') ≫ δ₃ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

lemma sq_sum {C : Type*} [Category C] [Preadditive C] {a₁ a₂ b₁ b₂ : C} {δ₁ : a₁ ⟶ b₁}
    {δ₂ : a₂ ⟶ b₂} {ι : Type*} (s : Finset ι) {f : ι → (b₁ ⟶ b₂)} {f' : ι → (a₁ ⟶ a₂)}
    (h : ∀ i ∈ s, δ₁ ≫ f i = f' i ≫ δ₂) : δ₁ ≫ ∑ i ∈ s, f i = (∑ i ∈ s, f' i) ≫ δ₂ := by
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  exact Finset.sum_congr rfl h

lemma sq_nsmul {C : Type*} [Category C] [Preadditive C] {a₁ a₂ b₁ b₂ : C} {δ₁ : a₁ ⟶ b₁}
    {δ₂ : a₂ ⟶ b₂} (m : ℕ) {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} (h : δ₁ ≫ f = f' ≫ δ₂) :
    δ₁ ≫ (m • f) = (m • f') ≫ δ₂ := by
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, h]

variable [Fintype G]

def IsTateDelta {U V : Subgroup G} [Fintype U] [Fintype V]
    (α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n) : Prop :=
  ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
    TateCohomology.δ (shortExact_map_resFunctor U hX) n ≫ (α (n + 1)).app X.X₁ =
      (α n).app X.X₃ ≫ TateCohomology.δ (shortExact_map_resFunctor V hX) n

namespace IsTateDelta

variable {U V W : Subgroup G} [Fintype U] [Fintype V] [Fintype W]

theorem ext {α β : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) (h0 : α 0 = β 0) : α = β :=
  funext (tate_natTrans_eq_of_eq_zero (resFunctor U.subtype) (resFunctor V.subtype)
    (shortExact_map_resFunctor U) (shortExact_map_resFunctor V)
    (tateAcyclic_res_coindSES_X₂ U) (tateAcyclic_res_indSES_X₂ V) α β hα hβ h0)

omit [Fintype G] in

theorem id : IsTateDelta (fun n => 𝟙 (resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n)) :=
  fun _ _ => (Category.comp_id _).trans (Category.id_comp _).symm

omit [Fintype G] in

theorem comp {α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    {β : ∀ n : ℤ, resFunctor V.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor W.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) : IsTateDelta (fun n => α n ≫ β n) := by
  intro X hX n
  exact sq_comp (hα hX n) (hβ hX n)

omit [Fintype G] in

theorem sum {ι : Type*} (s : Finset ι)
    {α : ι → ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : ∀ i ∈ s, IsTateDelta (α i)) : IsTateDelta (fun n => ∑ i ∈ s, α i n) := by
  intro X hX n
  rw [NatTrans.app_sum, NatTrans.app_sum]
  exact sq_sum s fun i hi => hα i hi hX n

omit [Fintype G] in

theorem nsmul (m : ℕ)
    {α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) : IsTateDelta (fun n => m • α n) := by
  intro X hX n
  rw [NatTrans.app_nsmul, NatTrans.app_nsmul]
  exact sq_nsmul m (hα hX n)


end IsTateDelta

end Delta

section LE

variable {U W : Subgroup G} (h : W ≤ U)

@[simps]
def resLENatTrans :
    resFunctor U.subtype ⋙ resFunctor (W.subgroupOf U).subtype ⋙
        resFunctor ((Subgroup.subgroupOfEquivOfLe h).symm : W →* W.subgroupOf U) ⟶
      resFunctor (k := k) W.subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl

@[simps]
def coresLENatTrans :
    resFunctor W.subtype ⋙ resFunctor (Subgroup.subgroupOfEquivOfLe h : W.subgroupOf U →* W) ⟶
      resFunctor (k := k) U.subtype ⋙ resFunctor (W.subgroupOf U).subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl

variable [Fintype U] [Fintype W]

@[instance_reducible]
noncomputable def fintypeSubgroupOf : Fintype (W.subgroupOf U) :=
  Fintype.ofEquiv W (Subgroup.subgroupOfEquivOfLe h).symm.toEquiv

noncomputable def tateResLE (n : ℤ) :
    resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor W.subtype ⋙ tateCohomologyFunctor n :=
  letI := fintypeSubgroupOf h
  Functor.whiskerLeft (resFunctor U.subtype) (tateRes (W.subgroupOf U) n) ≫
    Functor.whiskerLeft (resFunctor U.subtype ⋙ resFunctor (W.subgroupOf U).subtype)
      (tateTransport (Subgroup.subgroupOfEquivOfLe h).symm n) ≫
    Functor.whiskerRight (resLENatTrans h) (tateCohomologyFunctor n)

noncomputable def tateCoresLE (n : ℤ) :
    resFunctor W.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor U.subtype ⋙ tateCohomologyFunctor n :=
  letI := fintypeSubgroupOf h
  Functor.whiskerLeft (resFunctor W.subtype) (tateTransport (Subgroup.subgroupOfEquivOfLe h) n) ≫
    Functor.whiskerRight (coresLENatTrans h) (tateCohomologyFunctor n) ≫
    Functor.whiskerLeft (resFunctor U.subtype) (tateCores (W.subgroupOf U) n)



omit [Fintype U] [Fintype W] in

def invariantsLE {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (res W.subtype A).ρ.invariants :=
  ⟨y, fun w => y.2 ⟨w, h w.2⟩⟩

omit [Fintype U] [Fintype W] in
@[simp]
lemma coe_invariantsLE {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (invariantsLE h y : A) = y := rfl


omit [Fintype U] [Fintype W] in
variable (U) in

def invariantsSubgroupOf {A : Rep.{u} k G} (y : (res W.subtype A).ρ.invariants) :
    (res (W.subgroupOf U).subtype (res U.subtype A)).ρ.invariants :=
  ⟨y, fun w => y.2 ⟨(w : U), w.2⟩⟩


end LE

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

open CategoryTheory Limits Rep

namespace GroundTheory.GroupCoh

section Basics

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

omit [Fintype G] in

noncomputable def tateOneClass : tateCohomology (Rep.trivial ℤ S ℤ) 0 :=
  ((tateCohomologyZeroIso ℤ S).app (Rep.trivial ℤ S ℤ)).inv.hom
    (Submodule.Quotient.mk ⟨(1 : ℤ), fun _ => rfl⟩)

end Basics

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
  (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup G,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

include h1 h2 h3

noncomputable def tateTheoremIsoTop (n : ℤ) :
    tateCohomology (Rep.trivial ℤ G ℤ) n ≅ tateCohomology M (n + 2) :=
  @asIso _ _ _ _ (TateCohomology.δ (augTrivSES_shortExact ℤ G) n)
      (isIso_δ_of_tateAcyclic (augTrivSES_shortExact ℤ G) (tateAcyclic_leftRegular (k := ℤ)) n) ≪≫
    @asIso _ _ _ _ (TateCohomology.δ (splittingSES_shortExact M u) (n + 1))
      (isIso_δ_of_tateAcyclic (splittingSES_shortExact M u)
        (cohTrivial_splittingModule M u h1 h2 h3).tateAcyclic (n + 1)) ≪≫
    eqToIso (congrArg (tateCohomology M) (by ring))

variable (S : Subgroup G) [Fintype S]

noncomputable def tateTheoremIso (n : ℤ) :
    tateCohomology (Rep.trivial ℤ S ℤ) n ≅ tateCohomology (res S.subtype M) (n + 2) :=
  @asIso _ _ _ _ (TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) n)
      (isIso_δ_of_tateAcyclic (augTrivSES_res_shortExact ℤ S.subtype)
        (tateAcyclic_res_leftRegular S) n) ≪≫
    @asIso _ _ _ _ (TateCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (n + 1))
      (isIso_δ_of_tateAcyclic ((shortExact_res S.subtype).2 (splittingSES_shortExact M u))
        (cohTrivial_splittingModule M u h1 h2 h3 S) (n + 1)) ≪≫
    eqToIso (congrArg (tateCohomology (res S.subtype M)) (by ring))

theorem tateTheoremIso_zero_apply :
    (tateIsoH (res S.subtype M) (0 + 2) 2 (by norm_num)).hom.hom
      ((tateTheoremIso M u h1 h2 h3 S 0).hom.hom (tateOneClass S)) =
      groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u := by
  obtain ⟨c, hc⟩ := exists_tateComplex_cycles_zero (Rep.trivial ℤ S ℤ) ⟨(1 : ℤ), fun _ => rfl⟩
  have hcls : tateOneClass S = ((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c :=
    tateCohomologyZeroIso_inv_mk _ c _ hc.symm
  have hx : ((augTrivSES ℤ G).map (resFunctor S.subtype)).f.hom ∘
      (fun s : S => augIdealSubOne (k := ℤ) (s : G)) =
      groupCohomology.d₀₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₂
        (MonoidAlgebra.single (1 : G) (1 : ℤ)) := by
    funext h
    change MonoidAlgebra.single (h : G) (1 : ℤ) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular ℤ G).ρ (h : G) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  have ha := tateIsoH_δ_zero_apply (augTrivSES_res_shortExact ℤ S.subtype)
    (oneInvariant ℤ S.subtype) (MonoidAlgebra.single (1 : G) (1 : ℤ))
    (by exact augmentation_single (k := ℤ) (1 : G) (1 : ℤ)) _ hx c hc
  have hcoc : (⟨fun s : S => augIdealSubOne (k := ℤ) (s : G),
      groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ :
        groupCohomology.cocycles₁ (res S.subtype (augIdeal ℤ G))) = augCocycle ℤ S.subtype := rfl
  have hs : (tateIsoH ((splittingSES M u).map (resFunctor S.subtype)).X₁ ((1 : ℕ) + 1) (1 + 1)
      (Nat.cast_succ 1).symm).hom.hom
      ((tδ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (1 : ℕ) ((1 : ℕ) + 1)
        rfl).hom ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
          (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c))) =
      (groupCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 (1 + 1)
        rfl).hom ((tateIsoH ((splittingSES M u).map (resFunctor S.subtype)).X₃ (1 : ℕ) 1
          rfl).hom.hom ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
            (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c))) :=
    congr(($(tδ_comp_tateIsoH ((shortExact_res S.subtype).2
      (splittingSES_shortExact M u)) 1)).hom
        ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
          (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c)))
  have key := δ_splittingSES_res_δ₀ M u S.subtype
  rw [δ₀_augTrivSES_res] at key
  rw [hcls]
  refine hs.trans ?_
  refine Eq.trans ?_ key
  exact congrArg (groupCohomology.δ ((shortExact_res S.subtype).2
    (splittingSES_shortExact M u)) 1 2 rfl).hom (ha.trans (congrArg _ hcoc))

end Tate

end GroundTheory.GroupCoh
end
