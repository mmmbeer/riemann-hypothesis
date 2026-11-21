import Mathlib

section
namespace CompanionTheory.LimBd.URep

open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology

structure UnitaryRep (G : Type*) [Group G] [TopologicalSpace G] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where

  toHom : G →* unitary (H →L[ℂ] H)

  continuous_orbit' : ∀ v : H, Continuous fun g => (toHom g : H →L[ℂ] H) v

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

@[coe] noncomputable def op (π : UnitaryRep G H) (g : G) : H →L[ℂ] H := (π.toHom g : H →L[ℂ] H)

noncomputable instance : CoeFun (UnitaryRep G H) (fun _ => G → H →L[ℂ] H) := ⟨op⟩

variable (π : UnitaryRep G H)

lemma continuous_orbit (v : H) : Continuous fun g => π g v := π.continuous_orbit' v

@[simp] lemma map_one : π 1 = 1 := by
  show ((π.toHom 1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1
  simp

@[simp] lemma map_mul (g h : G) : π (g * h) = π g * π h := by
  show ((π.toHom (g * h) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
    (π.toHom g : H →L[ℂ] H) * (π.toHom h : H →L[ℂ] H)
  simp

lemma map_mul_apply (g h : G) (v : H) : π (g * h) v = π g (π h v) := by
  rw [map_mul]; rfl

@[simp] lemma map_one_apply (v : H) : π 1 v = v := by rw [map_one]; rfl

@[simp] lemma norm_map (g : G) (v : H) : ‖π g v‖ = ‖v‖ := Unitary.norm_map _ v

@[simp] lemma inner_map_map (g : G) (v w : H) : ⟪π g v, π g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  Unitary.inner_map_map _ v w

lemma mem_unitary (g : G) : π g ∈ unitary (H →L[ℂ] H) := (π.toHom g).2

@[simp] lemma star_map (g : G) : star (π g) = π g⁻¹ := by
  show star ((π.toHom g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
    ((π.toHom g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  rw [MonoidHom.map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]

@[simp] lemma adjoint_map (g : G) : adjoint (π g) = π g⁻¹ := by
  rw [← star_eq_adjoint, star_map]

@[simp] lemma map_inv_apply_map (g : G) (v : H) : π g⁻¹ (π g v) = v := by
  rw [← map_mul_apply, inv_mul_cancel, map_one_apply]

@[simp] lemma map_apply_map_inv (g : G) (v : H) : π g (π g⁻¹ v) = v := by
  rw [← map_mul_apply, mul_inv_cancel, map_one_apply]

lemma inner_map_left (g : G) (v w : H) : ⟪π g v, w⟫_ℂ = ⟪v, π g⁻¹ w⟫_ℂ := by
  rw [← adjoint_map, adjoint_inner_right]

lemma inner_map_right (g : G) (v w : H) : ⟪v, π g w⟫_ℂ = ⟪π g⁻¹ v, w⟫_ℂ := by
  rw [← adjoint_map, adjoint_inner_left]

lemma norm_map_le (g : G) : ‖π g‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v => by simp

lemma map_injective (g : G) : Function.Injective (π g) := fun v w h => by
  have := congrArg (π g⁻¹) h
  rwa [map_inv_apply_map, map_inv_apply_map] at this

noncomputable def ofLinearIsometryEquiv (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (hρ : ∀ v, Continuous fun g => ρ g v) : UnitaryRep G H where
  toHom := (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := H)).symm.toMonoidHom.comp ρ
  continuous_orbit' v := by simpa using hρ v

@[simp] lemma ofLinearIsometryEquiv_apply (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (hρ : ∀ v, Continuous fun g => ρ g v) (g : G) (v : H) :
    ofLinearIsometryEquiv ρ hρ g v = ρ g v := rfl

theorem continuous_of_continuousAt_one [IsTopologicalGroup G] (ρ : G →* unitary (H →L[ℂ] H))
    (hρ : ∀ v : H, ContinuousAt (fun g => (ρ g : H →L[ℂ] H) v) 1) (v : H) :
    Continuous fun g => (ρ g : H →L[ℂ] H) v := by
  rw [continuous_iff_continuousAt]
  intro h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ g, ‖(ρ g : H →L[ℂ] H) v - (ρ h : H →L[ℂ] H) v‖ =
      ‖(ρ (h⁻¹ * g) : H →L[ℂ] H) v - v‖ := by
    intro g
    have e : ρ g = ρ h * ρ (h⁻¹ * g) := by rw [← MonoidHom.map_mul, mul_inv_cancel_left]
    have : (ρ g : H →L[ℂ] H) v - (ρ h : H →L[ℂ] H) v =
        (ρ h : H →L[ℂ] H) ((ρ (h⁻¹ * g) : H →L[ℂ] H) v - v) := by
      rw [map_sub, e]
      rfl
    rw [this, Unitary.norm_map]
  simp_rw [key]
  have ht : Tendsto (fun g => h⁻¹ * g) (𝓝 h) (𝓝 1) := by
    have := (continuous_const_mul h⁻¹).tendsto h
    rwa [inv_mul_cancel] at this
  have h1 := Filter.Tendsto.comp (hρ v) ht
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1
  simpa [Function.comp_def] using h1

def IsInvariant (V : Submodule ℂ H) : Prop := ∀ (g : G) (v : H), v ∈ V → π g v ∈ V

variable {π}



theorem IsInvariant.orthogonal {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant Vᗮ := by
  intro g v hv w hw
  rw [inner_map_right]
  exact hv _ (hV _ _ hw)

theorem IsInvariant.topologicalClosure {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant V.topologicalClosure := by
  intro g v hv
  have hsub : Set.MapsTo (π g) (V : Set H) (V.topologicalClosure : Set H) :=
    fun x hx => V.le_topologicalClosure (hV g x hx)
  have hv' : v ∈ closure (V : Set H) := by
    rwa [← Submodule.topologicalClosure_coe]
  have := hsub.closure (π g).continuous hv'
  rwa [V.isClosed_topologicalClosure.closure_eq] at this

theorem isInvariant_iff_commute_starProjection (V : Submodule ℂ H) [V.HasOrthogonalProjection] :
    π.IsInvariant V ↔ ∀ g, Commute (π g) V.starProjection := by
  constructor
  · intro hV g
    ext v
    have hdec : v = V.starProjection v + (v - V.starProjection v) := by abel
    have hq : v - V.starProjection v ∈ Vᗮ := V.sub_starProjection_mem_orthogonal v
    have hp : V.starProjection v ∈ V := V.starProjection_apply_mem v
    have e1 : V.starProjection (π g v) = π g (V.starProjection v) := by
      conv_lhs => rw [hdec, map_add, map_add,
        Submodule.starProjection_eq_self_iff.mpr (hV g _ hp),
        (V.starProjection_apply_eq_zero_iff).mpr (hV.orthogonal g _ hq), add_zero]
    exact e1.symm
  · intro h g v hv
    rw [← Submodule.starProjection_eq_self_iff] at hv ⊢
    have : π g (V.starProjection v) = V.starProjection (π g v) :=
      congrArg (fun T : H →L[ℂ] H => T v) (h g)
    rw [← this, hv]

variable (π) in

def intertwiners (σ : UnitaryRep G K) : Submodule ℂ (H →L[ℂ] K) where
  carrier := {T | ∀ (g : G) (v : H), T (π g v) = σ g (T v)}
  add_mem' {S T} hS hT g v := by simp [hS g v, hT g v]
  zero_mem' g v := by simp
  smul_mem' c T hT g v := by simp [hT g v]

variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}

lemma mem_intertwiners {T : H →L[ℂ] K} :
    T ∈ π.intertwiners σ ↔ ∀ (g : G) (v : H), T (π g v) = σ g (T v) := Iff.rfl



lemma comp_mem_intertwiners {S : K →L[ℂ] L} {T : H →L[ℂ] K} (hS : S ∈ σ.intertwiners τ)
    (hT : T ∈ π.intertwiners σ) : S ∘L T ∈ π.intertwiners τ := fun g v => by
  simp [hT g v, hS g (T v)]


theorem adjoint_mem_intertwiners {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    adjoint T ∈ σ.intertwiners π := by
  intro g w
  apply ext_inner_left ℂ
  intro v
  rw [adjoint_inner_right, inner_map_right π, adjoint_inner_right, hT, inner_map_left σ, inv_inv]

lemma star_mem_intertwiners {T : H →L[ℂ] H} (hT : T ∈ π.intertwiners π) :
    star T ∈ π.intertwiners π := by
  rw [star_eq_adjoint]; exact adjoint_mem_intertwiners hT

lemma commute_of_mem_intertwiners {T : H →L[ℂ] H} (hT : T ∈ π.intertwiners π) (g : G) :
    Commute T (π g) := by
  ext v; exact hT g v

lemma mem_intertwiners_self_iff {T : H →L[ℂ] H} :
    T ∈ π.intertwiners π ↔ ∀ g, Commute T (π g) := by
  refine ⟨commute_of_mem_intertwiners, fun h g v => ?_⟩
  exact congrArg (fun S : H →L[ℂ] H => S v) (h g)

lemma isInvariant_range {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    σ.IsInvariant (LinearMap.range (T : H →ₗ[ℂ] K)) := by
  rintro g _ ⟨v, rfl⟩
  exact ⟨π g v, hT g v⟩

variable (π σ) in

structure Equiv where

  toLinearIsometryEquiv : H ≃ₗᵢ[ℂ] K

  map_apply' : ∀ (g : G) (v : H), toLinearIsometryEquiv (π g v) = σ g (toLinearIsometryEquiv v)

variable (π σ) in

def IsEquivalent : Prop := Nonempty (π.Equiv σ)

namespace Equiv

def refl (π : UnitaryRep G H) : π.Equiv π := ⟨LinearIsometryEquiv.refl ℂ H, fun _ _ => rfl⟩

def symm (e : π.Equiv σ) : σ.Equiv π where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.symm
  map_apply' g w := by
    apply e.toLinearIsometryEquiv.injective
    rw [LinearIsometryEquiv.apply_symm_apply, e.map_apply', LinearIsometryEquiv.apply_symm_apply]

def trans (e : π.Equiv σ) (f : σ.Equiv τ) : π.Equiv τ where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.trans f.toLinearIsometryEquiv
  map_apply' g v := by simp [e.map_apply', f.map_apply']

lemma mem_intertwiners (e : π.Equiv σ) :
    (e.toLinearIsometryEquiv : H →L[ℂ] K) ∈ π.intertwiners σ := e.map_apply'

end Equiv

lemma IsEquivalent.refl (π : UnitaryRep G H) : π.IsEquivalent π := ⟨Equiv.refl π⟩

lemma IsEquivalent.symm (h : π.IsEquivalent σ) : σ.IsEquivalent π := ⟨h.some.symm⟩

lemma IsEquivalent.trans (h : π.IsEquivalent σ) (h' : σ.IsEquivalent τ) : π.IsEquivalent τ :=
  ⟨h.some.trans h'.some⟩

variable (π) in

def IsIrreducible : Prop :=
  Nontrivial H ∧ ∀ V : Submodule ℂ H, IsClosed (V : Set H) → π.IsInvariant V → V = ⊥ ∨ V = ⊤

theorem IsIrreducible.of_equiv (hπ : π.IsIrreducible) (e : π.Equiv σ) : σ.IsIrreducible := by
  obtain ⟨hnt, hπ⟩ := hπ
  refine ⟨e.toLinearIsometryEquiv.toEquiv.nontrivial_congr.mp hnt, fun W hW hWinv => ?_⟩
  let E : H →L[ℂ] K := e.toLinearIsometryEquiv
  have hcl : IsClosed ((W.comap (E : H →ₗ[ℂ] K) : Submodule ℂ H) : Set H) :=
    hW.preimage E.continuous
  have hinv : π.IsInvariant (W.comap (E : H →ₗ[ℂ] K)) := by
    intro g v hv
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe] at hv ⊢
    rw [show E (π g v) = σ g (E v) from e.map_apply' g v]
    exact hWinv g _ hv
  have hsurj : Function.Surjective E := e.toLinearIsometryEquiv.surjective
  rcases hπ _ hcl hinv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := hsurj w
    have : v ∈ W.comap (E : H →ₗ[ℂ] K) := hw
    rw [h, Submodule.mem_bot] at this
    simp [this]
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hsurj w
    have : v ∈ W.comap (E : H →ₗ[ℂ] K) := by rw [h]; exact Submodule.mem_top
    exact this

theorem IsEquivalent.isIrreducible_iff (h : π.IsEquivalent σ) :
    π.IsIrreducible ↔ σ.IsIrreducible :=
  ⟨fun hπ => hπ.of_equiv h.some, fun hσ => hσ.of_equiv h.some.symm⟩

section restrict

variable (π) (V : Submodule ℂ H) [CompleteSpace V] (hV : π.IsInvariant V)

noncomputable def restrictAux (g : G) : V ≃ₗᵢ[ℂ] V where
  toFun v := ⟨π g v, hV g v v.2⟩
  invFun v := ⟨π g⁻¹ v, hV _ v v.2⟩
  map_add' v w := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)
  left_inv v := Subtype.ext (by simp)
  right_inv v := Subtype.ext (by simp)
  norm_map' v := by simp [Submodule.coe_norm]

noncomputable def restrict : UnitaryRep G V :=
  ofLinearIsometryEquiv
    { toFun := restrictAux π V hV
      map_one' := by ext v; simp [restrictAux]
      map_mul' := fun g h =>
        LinearIsometryEquiv.ext fun v => Subtype.ext (map_mul_apply π g h v) }
    (fun v => (π.continuous_orbit v).subtype_mk _)

@[simp] lemma coe_restrict_apply (g : G) (v : V) :
    ((π.restrict V hV g v : V) : H) = π g v := rfl

end restrict

end UnitaryRep

end CompanionTheory.LimBd.URep
end

section
namespace CompanionTheory.LimBd.URep

namespace UnitaryRep

open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}

omit [CompleteSpace H] in

lemma nontrivial_endomorphisms [Nontrivial H] : Nontrivial (H →L[ℂ] H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  exact ⟨⟨1, 0, fun h => hv (by simpa using congrArg (fun T : H →L[ℂ] H => T v) h)⟩⟩

theorem IsIrreducible.spectrum_subsingleton (hπ : π.IsIrreducible) {A : H →L[ℂ] H}
    (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) : (spectrum ℝ A).Subsingleton := by
  have := hπ.1
  have := nontrivial_endomorphisms (H := H)
  intro a ha b hb
  by_contra hab
  wlog hlt : a < b generalizing a b
  · exact this hb ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
  set c := (a + b) / 2 with hc
  have hcb : c < b := by rw [hc]; linarith
  have hac : a < c := by rw [hc]; linarith
  let f : ℝ → ℝ := fun x => max (x - c) 0
  let g : ℝ → ℝ := fun x => max (c - x) 0
  have hfc : Continuous f := by fun_prop
  have hgc : Continuous g := by fun_prop
  have hgf : (fun x => g x * f x) = (0 : ℝ → ℝ) := by
    funext x
    rcases le_total x c with h | h
    · simp [f, max_eq_right (sub_nonpos.mpr h)]
    · simp [g, max_eq_right (sub_nonpos.mpr h)]
  have hQP : cfc g A * cfc f A = 0 := by
    rw [← cfc_mul g f A hgc.continuousOn hfc.continuousOn, hgf, cfc_zero]
  have hne : ∀ (φ : ℝ → ℝ), Continuous φ → ∀ x ∈ spectrum ℝ A, φ x ≠ 0 → cfc φ A ≠ 0 := by
    intro φ hφ x hx hφx h
    have hs : spectrum ℝ (cfc φ A) = φ '' spectrum ℝ A := cfc_map_spectrum φ A hsa hφ.continuousOn
    have hmem : φ x ∈ spectrum ℝ (cfc φ A) := hs ▸ ⟨x, hx, rfl⟩
    rw [h, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
    exact hφx hmem
  have hP0 : cfc f A ≠ 0 := hne f hfc b hb (by
    simp only [f]; rw [max_eq_left (by linarith)]; linarith)
  have hQ0 : cfc g A ≠ 0 := hne g hgc a ha (by
    simp only [g]; rw [max_eq_left (by linarith)]; linarith)
  have hPmem : cfc f A ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun h => (commute_of_mem_intertwiners hA h).cfc_real f
  set V := (LinearMap.range ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H)).topologicalClosure with hV
  have hinv : π.IsInvariant V := (isInvariant_range hPmem).topologicalClosure
  rcases hπ.2 V (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
  · apply hP0
    ext v
    have : cfc f A v ∈ V := Submodule.le_topologicalClosure _ ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    simpa using this
  · apply hQ0
    have hle : LinearMap.range ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
        LinearMap.ker ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rintro _ ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      have := congrArg (fun T : H →L[ℂ] H => T v) hQP
      simpa using this
    have hcl := Submodule.topologicalClosure_minimal _ hle (cfc g A).isClosed_ker
    rw [← hV, htop] at hcl
    ext v
    have : v ∈ LinearMap.ker ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H) := hcl Submodule.mem_top
    simpa using this

theorem IsIrreducible.exists_eq_algebraMap_of_isSelfAdjoint (hπ : π.IsIrreducible)
    {A : H →L[ℂ] H} (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have := hπ.1
  have := nontrivial_endomorphisms (H := H)
  have hne : (spectrum ℝ A).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty A hsa
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_⟩
  have hsub := hπ.spectrum_subsingleton hA hsa
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A hsa).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hsub hx hc
    _ = algebraMap ℝ _ c := cfc_const c A hsa

theorem IsIrreducible.exists_eq_smul_one (hπ : π.IsIrreducible) {T : H →L[ℂ] H}
    (hT : T ∈ π.intertwiners π) : ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  have hstar := star_mem_intertwiners hT
  have hre : (ℜ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [realPart_apply_coe]
    exact Submodule.smul_of_tower_mem _ _ (add_mem hT hstar)
  have him : (ℑ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [imaginaryPart_apply_coe]
    exact Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _ (sub_mem hT hstar))
  obtain ⟨a, ha⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint hre (ℜ T).2
  obtain ⟨b, hb⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint him (ℑ T).2
  refine ⟨a + I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]

theorem isIrreducible_iff :
    π.IsIrreducible ↔
      Nontrivial H ∧ ∀ T ∈ π.intertwiners π, ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  refine ⟨fun hπ => ⟨hπ.1, fun T hT => hπ.exists_eq_smul_one hT⟩, fun ⟨hnt, h⟩ => ⟨hnt, ?_⟩⟩
  intro V hcl hinv
  have : CompleteSpace V := hcl.completeSpace_coe
  have hP : V.starProjection ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun g => ((isInvariant_iff_commute_starProjection V).mp hinv g).symm
  obtain ⟨c, hc⟩ := h _ hP
  have hPv : ∀ v, V.starProjection v = c • v := fun v => by simp [hc]
  by_cases hc0 : c = 0
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot, ← Submodule.starProjection_eq_self_iff.mpr hv, hPv, hc0, zero_smul]
  · right
    rw [eq_top_iff]
    intro v _
    have hmem : V.starProjection v ∈ V := V.starProjection_apply_mem v
    rw [hPv] at hmem
    simpa [hc0] using V.smul_mem c⁻¹ hmem

theorem IsIrreducible.isEquivalent_of_mem_intertwiners (hπ : π.IsIrreducible)
    (hσ : σ.IsIrreducible) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) (hT0 : T ≠ 0) :
    π.IsEquivalent σ := by
  obtain ⟨c, hc⟩ := hπ.exists_eq_smul_one
    (comp_mem_intertwiners (adjoint_mem_intertwiners hT) hT)
  obtain ⟨d, hd⟩ := hσ.exists_eq_smul_one
    (comp_mem_intertwiners hT (adjoint_mem_intertwiners hT))
  have key : ∀ v, (‖T v‖ : ℂ) ^ 2 = c * (‖v‖ : ℂ) ^ 2 := by
    intro v
    have h1 : ⟪v, (adjoint T ∘L T) v⟫_ℂ = ⟪T v, T v⟫_ℂ := by
      rw [comp_apply, adjoint_inner_right]
    rw [hc] at h1
    simp only [smul_apply, one_apply_eq_self, inner_smul_right] at h1
    have e1 : ⟪v, v⟫_ℂ = (‖v‖ : ℂ) ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; rfl
    have e2 : ⟪T v, T v⟫_ℂ = (‖T v‖ : ℂ) ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; rfl
    rw [e1, e2] at h1
    exact h1.symm
  obtain ⟨v₀, hv₀⟩ : ∃ v, T v ≠ 0 := by
    by_contra h
    push Not at h
    exact hT0 (ContinuousLinearMap.ext h)
  have hv₀' : v₀ ≠ 0 := fun h => hv₀ (by rw [h, map_zero])
  set r : ℝ := ‖T v₀‖ / ‖v₀‖ with hr
  have hrpos : 0 < r := div_pos (norm_pos_iff.mpr hv₀) (norm_pos_iff.mpr hv₀')
  have hcr : c = ((r ^ 2 : ℝ) : ℂ) := by
    have h := key v₀
    have hn : (‖v₀‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (norm_pos_iff.mpr hv₀').ne')
    rw [hr, div_pow]
    push_cast
    exact eq_div_of_mul_eq hn h.symm
  have hnorm : ∀ v, ‖T v‖ = r * ‖v‖ := by
    intro v
    have h := key v
    rw [hcr] at h
    have h' : ‖T v‖ ^ 2 = (r * ‖v‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hrpos.le (norm_nonneg _)) two_ne_zero).mp h'
  have hc0 : c ≠ 0 := by rw [hcr]; exact_mod_cast (pow_pos hrpos 2).ne'
  have hcd : c = d := by
    have e1 : T ∘L (adjoint T ∘L T) = c • T := by rw [hc]; ext v; simp
    have e2 : (T ∘L adjoint T) ∘L T = d • T := by rw [hd]; ext v; simp
    have e3 : (c - d) • T = 0 := by rw [sub_smul, ← e1, ← e2]; simp [comp_assoc]
    rcases smul_eq_zero.mp e3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hT0
  have hsurjT : Function.Surjective T := by
    intro w
    refine ⟨c⁻¹ • adjoint T w, ?_⟩
    have : (T ∘L adjoint T) w = d • w := by rw [hd]; simp
    rw [map_smul, show T (adjoint T w) = d • w from this, smul_smul, ← hcd, inv_mul_cancel₀ hc0,
      one_smul]
  let U : H →L[ℂ] K := ((r⁻¹ : ℝ) : ℂ) • T
  have hU : ∀ v, ‖U v‖ = ‖v‖ := by
    intro v
    simp only [U, smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, hnorm v,
      abs_of_pos (inv_pos.mpr hrpos)]
    rw [← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul]
  let Ui : H →ₗᵢ[ℂ] K := { toLinearMap := (U : H →ₗ[ℂ] K), norm_map' := hU }
  have hsurj : Function.Surjective Ui := by
    intro w
    obtain ⟨v, rfl⟩ := hsurjT w
    refine ⟨(r : ℂ) • v, ?_⟩
    show U ((r : ℂ) • v) = T v
    simp only [U, smul_apply, map_smul, smul_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hrpos.ne', Complex.ofReal_one, one_smul]
  refine ⟨⟨LinearIsometryEquiv.ofSurjective Ui hsurj, fun g v => ?_⟩⟩
  show U (π g v) = σ g (U v)
  exact (Submodule.smul_mem _ _ hT) g v

theorem IsIrreducible.eq_zero_of_not_isEquivalent (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hne : ¬ π.IsEquivalent σ) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) : T = 0 := by
  by_contra h
  exact hne (hπ.isEquivalent_of_mem_intertwiners hσ hT h)

end UnitaryRep

end CompanionTheory.LimBd.URep
end
