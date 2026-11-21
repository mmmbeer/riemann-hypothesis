import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtAdjoinIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
import Lemmata.GeneralBFactSecondForm.Imports

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace WittTransvections

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def transv (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (ξ : K) : V →ₗ[K] V :=
  LinearMap.id - ξ • (h u).smulRight u

theorem transv_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (ξ : K) (v : V) :
    transv h u ξ v = v - (ξ * h u v) • u := by
  simp [transv, LinearMap.smulRight_apply, smul_smul]

theorem transv_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ η : K}
    (hξ : ξ + η = ξ * η * h u u) : transv h u η ∘ₗ transv h u ξ = LinearMap.id := by
  ext v
  rw [LinearMap.comp_apply, transv_apply, transv_apply, LinearMap.id_apply]
  have e1 : h u (v - (ξ * h u v) • u) = h u v - ξ * h u v * h u u := by
    rw [map_sub, map_smul, smul_eq_mul, mul_assoc]
  rw [e1, sub_sub, ← add_smul]
  have hc : ξ * h u v + η * (h u v - ξ * h u v * h u u) = 0 := by linear_combination (h u v) * hξ
  rw [hc, zero_smul, sub_zero]

def transvEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (transv h u ξ) (transv h u (star ξ))
    (transv_comp h u (by rw [add_comm, mul_comm (star ξ)]; exact hξ)) (transv_comp h u hξ)

theorem transvEquiv_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v : V) :
    transvEquiv h u hξ v = v - (ξ * h u v) • u := transv_apply h u ξ v

theorem transvEquiv_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v w : V) :
    h (transvEquiv h u hξ v) (transvEquiv h u hξ w) = h v w := by
  rw [transvEquiv_apply, transvEquiv_apply]
  have h1 : star (h u v) = h v u := by rw [← starRingEnd_apply]; exact hs.eq u v
  simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    map_mul, starRingEnd_apply, star_mul', h1]
  linear_combination (-(h v u * h u w)) * hξ

end WittTransvections

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_isom_map_of_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : IsTotPosDef h) {x y : V} (hx : x ≠ 0) (hxy : h x x = h y y) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, g x = y := by
  by_cases hxy' : x = y
  · exact ⟨1, Subgroup.one_mem _, by rw [hxy']; rfl⟩
  have hu0 : x - y ≠ 0 := sub_ne_zero.2 hxy'
  have hsym : ∀ a b, starRingEnd K (h a b) = h b a := fun a b => hs.eq a b
  have hnz : ∀ v : V, v ≠ 0 → h v v ≠ 0 := by
    intro v hv h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd v hv φ
    rw [h0, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have huu : h (x - y) (x - y) = starRingEnd K (h (x - y) x) + h (x - y) x := by
    rw [hsym]
    simp only [map_sub, LinearMap.sub_apply]
    rw [← hxy]
    ring
  have hux : h (x - y) x ≠ 0 := by
    intro h0
    apply hnz _ hu0
    rw [huu, h0, map_zero, add_zero]
  have hξ : (h (x - y) x)⁻¹ + star (h (x - y) x)⁻¹ =
      (h (x - y) x)⁻¹ * star (h (x - y) x)⁻¹ * h (x - y) (x - y) := by
    have hs' : star (h (x - y) x) ≠ 0 := by
      intro h0; exact hux (by simpa using congrArg star h0)
    have hs'' : starRingEnd K (h (x - y) x) ≠ 0 := by rwa [starRingEnd_apply]
    rw [huu, ← starRingEnd_apply, map_inv₀]
    field_simp
    try ring
  refine ⟨WittTransvections.transvEquiv h (x - y) hξ, fun v w => WittTransvections.transvEquiv_isom hs _ hξ v w, ?_⟩
  rw [WittTransvections.transvEquiv_apply, inv_mul_cancel₀ hux, one_smul, sub_sub_cancel]


end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace SplitBAux

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem h_x₀_decomp (S : VecSplit h h') (c : K) (a : V') :
    h S.x₀ (c • S.x₀ + S.ι a) = c * h S.x₀ S.x₀ := by
  exact S.h_x₀_comb c a

theorem exists_of_orth (S : VecSplit h h') {v : V} (hv : h S.x₀ v = 0) : ∃ a, S.ι a = v := by
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [S.h_x₀_comb] at hv
  have hc : c = 0 := (mul_eq_zero.mp hv).resolve_right S.hx₀
  exact ⟨a, by rw [hc, zero_smul, zero_add]⟩

theorem orth' (hs : h.IsSymm) (S : VecSplit h h') (a : V') : h (S.ι a) S.x₀ = 0 := by
  exact S.orth' hs a

theorem h_decomp (hs : h.IsSymm) (S : VecSplit h h') (c d : K) (a b : V') :
    h (c • S.x₀ + S.ι a) (d • S.x₀ + S.ι b) = star c * d * h S.x₀ S.x₀ + h' a b := by
  simp [S.orth, S.orth' hs, S.isom, mul_assoc, starRingEnd_apply]

def liftι {W : Type} [AddCommGroup W] [Module K W] (S : VecSplit h h') (f : W →ₗ[K] V)
    (hf : ∀ w, ∃ b, S.ι b = f w) : W →ₗ[K] V' where
  toFun a := (hf a).choose
  map_add' a b := S.inj (by
    rw [map_add S.ι, (hf a).choose_spec, (hf b).choose_spec, (hf (a + b)).choose_spec, map_add f])
  map_smul' c a := S.inj (by
    simp only [RingHom.id_apply]
    rw [map_smul S.ι, (hf a).choose_spec, (hf (c • a)).choose_spec, map_smul f])

theorem liftι_spec {W : Type} [AddCommGroup W] [Module K W] (S : VecSplit h h') (f : W →ₗ[K] V)
    (hf : ∀ w, ∃ b, S.ι b = f w) (w : W) : S.ι (liftι S f hf w) = f w := (hf w).choose_spec

def projX (S : VecSplit h h') : V →ₗ[K] V :=
  ((h S.x₀ S.x₀)⁻¹ • h S.x₀).smulRight S.x₀

theorem projX_apply (S : VecSplit h h') (c : K) (a : V') :
    projX S (c • S.x₀ + S.ι a) = c • S.x₀ := by
  unfold projX
  rw [LinearMap.smulRight_apply, LinearMap.smul_apply, S.h_x₀_comb, smul_eq_mul]
  congr 1
  rw [inv_mul_eq_iff_eq_mul₀ S.hx₀]
  exact mul_comm _ _

def coordA (S : VecSplit h h') : V →ₗ[K] V' :=
  liftι S (LinearMap.id - projX S) (by
    intro v; obtain ⟨c, b, rfl⟩ := S.cover v
    exact ⟨b, by simp [projX_apply]⟩)

theorem coordA_apply (S : VecSplit h h') (c : K) (a : V') : coordA S (c • S.x₀ + S.ι a) = a := by
  apply S.inj
  unfold coordA
  rw [liftι_spec, LinearMap.sub_apply, LinearMap.id_apply, projX_apply, add_sub_cancel_left]

theorem linearMap_ext (S : VecSplit h h') {f g : V →ₗ[K] V} (h0 : f S.x₀ = g S.x₀)
    (h1 : ∀ a, f (S.ι a) = g (S.ι a)) : f = g := by
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [map_add, map_add, map_smul, map_smul, h0, h1]

theorem autL_iff {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {k : W →ₗ⋆[K] W →ₗ[K] K} {M : Submodule (𝓞 K) W} {g : W ≃ₗ[K] W} :
    g ∈ Formalism.ThetaLiftIndependence.autL k M ↔ g ∈ Formalism.HermitianLatticesTheory.isom k ∧ Formalism.HermitianLatticesTheory.gmap g M = M := Iff.rfl

theorem isom_apply {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (x y : V) : h (g x) (g y) = h x y := hg x y

theorem symm_mem_isom {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) : g.symm ∈ Formalism.HermitianLatticesTheory.isom h := by
  exact inv_mem hg

theorem mem_gmap_iff {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (e : W ≃ₗ[K] W) (M : Submodule (𝓞 K) W) (v : W) :
    v ∈ Formalism.HermitianLatticesTheory.gmap e M ↔ e.symm v ∈ M := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hv
    exact ⟨e.symm v, hv, by simp⟩

theorem mem_adjoin_iff (S : VecSplit h h') (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ S.adjoin L' ↔ (∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c) ∧ a ∈ L' := by
  rw [S.comb_mem_adjoin_iff, Submodule.mem_one]

theorem maps_of_fix (S : VecSplit h h') {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : ∃ b, S.ι b = (g.toLinearMap ∘ₗ S.ι) a := by
  apply exists_of_orth S
  show h S.x₀ (g (S.ι a)) = 0
  rw [← hx, isom_apply hg, S.orth]

theorem symm_fix {g : V ≃ₗ[K] V} {x : V} (hx : g x = x) : g.symm x = x := by
  exact g.symm_apply_eq.mpr hx.symm

def res (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hx : g S.x₀ = S.x₀) :
    V' ≃ₗ[K] V' :=
  LinearEquiv.ofLinearMap (liftι S _ (maps_of_fix S hg hx))
    (liftι S _ (maps_of_fix S (symm_mem_isom hg) (symm_fix hx)))
    (by ext a; apply S.inj; simp [liftι_spec])
    (by ext a; apply S.inj; simp [liftι_spec])

theorem res_spec (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : S.ι (res S g hg hx a) = g (S.ι a) := by
  exact liftι_spec S _ _ a

theorem res_symm_spec (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : S.ι ((res S g hg hx).symm a) = g.symm (S.ι a) := by
  exact liftι_spec S _ _ a

theorem res_mem_isom (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) : res S g hg hx ∈ Formalism.HermitianLatticesTheory.isom h' := by
  show ∀ x y, h' (res S g hg hx x) (res S g hg hx y) = h' x y
  intro x y
  rw [← S.isom, res_spec, res_spec, isom_apply hg, S.isom]

theorem gmap_res (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) {L₁ L₂ : Submodule (𝓞 K) V} (hL : Formalism.HermitianLatticesTheory.gmap g L₁ = L₂) :
    Formalism.HermitianLatticesTheory.gmap (res S g hg hx) (S.cut L₁) = S.cut L₂ := by
  ext a
  rw [mem_gmap_iff, S.mem_cut_iff, S.mem_cut_iff, res_symm_spec, ← hL, mem_gmap_iff]

def extFun (S : VecSplit h h') (f : V' →ₗ[K] V') : V →ₗ[K] V :=
  projX S + S.ι ∘ₗ f ∘ₗ coordA S

theorem extFun_apply (S : VecSplit h h') (f : V' →ₗ[K] V') (c : K) (a : V') :
    extFun S f (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (f a) := by
  unfold extFun
  rw [LinearMap.add_apply, projX_apply, LinearMap.comp_apply, LinearMap.comp_apply, coordA_apply]

theorem eq_decomp_x₀ (S : VecSplit h h') : S.x₀ = (1 : K) • S.x₀ + S.ι 0 := by
  simp

theorem eq_decomp_ι (S : VecSplit h h') (a : V') : S.ι a = (0 : K) • S.x₀ + S.ι a := by
  simp

def extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (extFun S g'.toLinearMap) (extFun S g'.symm.toLinearMap)
    (linearMap_ext S (by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [eq_decomp_x₀ S, extFun_apply, extFun_apply]; simp)
      (fun a => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        rw [eq_decomp_ι S, extFun_apply, extFun_apply]; simp))
    (linearMap_ext S (by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [eq_decomp_x₀ S, extFun_apply, extFun_apply]; simp)
      (fun a => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        rw [eq_decomp_ι S, extFun_apply, extFun_apply]; simp))

theorem extOf_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (c : K) (a : V') :
    extOf S g' (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (g' a) := extFun_apply S g'.toLinearMap c a

theorem extOf_symm_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (c : K) (a : V') :
    (extOf S g').symm (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (g'.symm a) := extFun_apply S g'.symm.toLinearMap c a

theorem extOf_x₀ (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : extOf S g' S.x₀ = S.x₀ := by
  rw [eq_decomp_x₀ S, extOf_apply]
  simp

theorem extOf_ι (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (a : V') :
    extOf S g' (S.ι a) = S.ι (g' a) := by
  rw [eq_decomp_ι S a, extOf_apply]
  simp

theorem extOf_mem_isom (hs : h.IsSymm) (S : VecSplit h h') {g' : V' ≃ₗ[K] V'}
    (hg : g' ∈ Formalism.HermitianLatticesTheory.isom h') : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := by
  have hg' : ∀ x y, h' (g' x) (g' y) = h' x y := hg
  show ∀ x y, h (extOf S g' x) (extOf S g' y) = h x y
  intro x y
  obtain ⟨c, a, rfl⟩ := S.cover x
  obtain ⟨d, b, rfl⟩ := S.cover y
  rw [extOf_apply, extOf_apply, h_decomp hs, h_decomp hs, hg']

theorem gmap_extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') {C₁ C₂ : Submodule (𝓞 K) V'}
    (hC : Formalism.HermitianLatticesTheory.gmap g' C₁ = C₂) :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (S.adjoin C₁) = S.adjoin C₂ := by
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [mem_gmap_iff, extOf_symm_apply, SplitBAux.mem_adjoin_iff, SplitBAux.mem_adjoin_iff, ← hC,
    mem_gmap_iff]

end SplitBAux

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open SplitBAux in
theorem VecSplit.card_stab (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : S.adjoin (S.cut L) = L) :
    Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g S.x₀ = S.x₀} =
      Nat.card (Formalism.ThetaLiftIndependence.autL h' (S.cut L)) := by
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨res S g.1 (autL_iff.mp g.2.1).1 g.2.2,
        autL_iff.mpr ⟨res_mem_isom S _ _ _, gmap_res S _ _ _ (autL_iff.mp g.2.1).2⟩⟩
      invFun := fun g' => ⟨extOf S g'.1,
        autL_iff.mpr ⟨extOf_mem_isom hs S (autL_iff.mp g'.2).1, by
          have := gmap_extOf S g'.1 (autL_iff.mp g'.2).2
          rwa [hL] at this⟩, extOf_x₀ S _⟩
      left_inv := fun g => Subtype.ext (LinearEquiv.toLinearMap_injective
        (linearMap_ext S (by simp [extOf_x₀, g.2.2]) (fun a => by simp [extOf_ι, res_spec])))
      right_inv := fun g' => Subtype.ext (LinearEquiv.ext fun a => S.inj (by
        simp [res_spec, extOf_ι])) }

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbitRepresentatives

theorem exists_orbit_reps {G X : Type*} [Group G] [MulAction G X] (A : Set X) (hfin : A.Finite)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let r := MulAction.orbitRel G X
  let f : X → X := fun x => (@Quotient.mk _ r x).out
  have hf1 : ∀ x, ∃ g : G, g • x = f x := fun x => MulAction.orbitRel_apply.mp (@Quotient.mk_out _ r x)
  have hf2 : ∀ x y (g : G), g • y = x → f x = f y := fun x y g hg =>
    congrArg Quotient.out (@Quotient.sound _ r x y (MulAction.orbitRel_apply.mpr ⟨g, hg⟩))
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨g, hg⟩ := hf1 x
    rw [← hg]
    exact hA g x (hfin.mem_toFinset.mp hx)
  · intro x hx
    obtain ⟨g, hg⟩ := hf1 x
    refine ⟨f x, ⟨Finset.mem_image_of_mem f (hfin.mem_toFinset.mpr hx), g⁻¹, ?_⟩, ?_⟩
    · rw [← hg, inv_smul_smul]
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨k, hk⟩ := hf1 z
      exact (hf2 x z (g' * k) (by rw [mul_smul, hk, hg'])).symm

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem card_stabilizer_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : V) :
    Nat.card (MulAction.stabilizer (autSub h L) t) =
      Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem gmap_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    Formalism.HermitianLatticesTheory.gmap g L ∈ Formalism.HermitianLatticesTheory.genus h I := by
  obtain ⟨hLat, hG⟩ := hL
  have hiso : ∀ x y, h (g x) (g y) = h x y := hg
  show Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)
  refine ⟨?_, ?_⟩
  · constructor
    · unfold Formalism.HermitianLatticesTheory.gmap
      exact hLat.fg.map _
    · unfold Formalism.HermitianLatticesTheory.gmap
      rw [Submodule.map_coe]
      show Submodule.span K (⇑(g : V →ₗ[K] V) '' L) = ⊤
      rw [Submodule.span_image, hLat.span_eq_top, Submodule.map_top,
        LinearMap.range_eq_top.mpr g.surjective]
  · unfold Formalism.HermitianLatticesTheory.SameGenus
    intro p hp
    obtain ⟨g', hg', he⟩ := hG p hp
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]

theorem integral_of_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  obtain ⟨-, -, hi⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  exact ((hi I L (isLattice_of_ortho hI).fg hL.1.fg hL.2).2).mp (isIntegralLat_of_ortho hI)

theorem exists_reps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    ∃ T : Finset V, (∀ t ∈ T, t ∈ L ∧ h t t = 1) ∧
      (∀ x, x ∈ L → h x x = 1 → ∃ t ∈ T, ∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t = x) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, (∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t₁ = t₂) → t₁ = t₂) ∧
      (repCount h L 1 : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h L) : ℕ) : ℝ) =
        ∑ t ∈ T, ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ := by
  classical
  unfold Formalism.HermitianLattices.Ext.L3.repCount
  have hfin := finite_repSet_of_ortho hK hs hI hL 1
  haveI : Finite (autSub h L) := by
    have := (finite_autL_of_ortho hK hs hI hL).to_subtype
    exact this
  haveI : Finite ({x : V | x ∈ L ∧ h x x = 1} : Set V) := hfin.to_subtype
  have hA : ∀ g : autSub h L, ∀ x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V),
      g • x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V) := by
    rintro ⟨g, hgI, hgL⟩ x ⟨hxL, hxx⟩
    have hgI' : ∀ x y, h (g x) (g y) = h x y := hgI
    refine ⟨?_, ?_⟩
    · show g x ∈ L
      rw [← hgL]
      unfold Formalism.HermitianLatticesTheory.gmap
      exact Submodule.mem_map_of_mem hxL
    · show h (g x) (g x) = 1
      rw [hgI' x x, hxx]
  obtain ⟨T, hTA, hT⟩ := exists_orbit_reps (G := autSub h L) _ hfin hA
  refine ⟨T, hTA, ?_, ?_, ?_⟩
  · intro x hxL hxx
    obtain ⟨t, ⟨htT, g, hg⟩, -⟩ := hT x ⟨hxL, hxx⟩
    exact ⟨t, htT, g.1, g.2, hg⟩
  · rintro t₁ h₁ t₂ h₂ ⟨a, ha, hat⟩
    obtain ⟨t, -, huniq⟩ := hT t₂ (hTA t₂ h₂)
    have e1 := huniq t₁ ⟨h₁, ⟨a, ha⟩, hat⟩
    have e2 := huniq t₂ ⟨h₂, 1, one_smul _ _⟩
    rw [e1, e2]
  · have key := sum_inv_card_stab (G := autSub h L) _ hA T hTA hT
    have e : ∀ t ∈ T, ((Nat.card (MulAction.stabilizer (autSub h L) t) : ℕ) : ℝ)⁻¹ =
        ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ :=
      fun t _ => by rw [card_stabilizer_autSub]
    rw [← Finset.sum_congr rfl e]
    exact key

end OrbitRepresentatives

end Formalism.HermitianLattices.Ext.L3
end
end

section
open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbSum

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem exists_reps_of_cover (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (C : Set X)
    (hC : C.Finite) (hCA : ∀ c ∈ C, c ∈ A) (hcov : ∀ x ∈ A, ∃ c ∈ C, ∃ g : G, g • c = x) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x => by
    have h1 : Quotient.mk (MulAction.orbitRel G X) (rep x) = Quotient.mk _ x := Quotient.out_eq _
    have h2 : rep x ∈ MulAction.orbit G x := Quotient.exact h1
    exact MulAction.mem_orbit_iff.1 h2
  have hrepA : ∀ x ∈ A, rep x ∈ A := fun x hx => by
    obtain ⟨g, hg⟩ := hrep x
    rw [← hg]
    exact hA g x hx
  have hrep_eq : ∀ x y : X, ∀ g : G, g • y = x → rep y = rep x := fun x y g hg => by
    show (Quotient.mk (MulAction.orbitRel G X) y).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    apply Quotient.sound
    show y ∈ MulAction.orbit G x
    rw [MulAction.mem_orbit_iff]
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  refine ⟨hC.toFinset.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
    exact hrepA c (hCA c (hC.mem_toFinset.1 hc))
  · intro x hx
    obtain ⟨c, hc, g, hg⟩ := hcov x hx
    obtain ⟨g', hg'⟩ := hrep c
    refine ⟨rep c, ⟨Finset.mem_image.2 ⟨c, hC.mem_toFinset.2 hc, rfl⟩, ⟨g * g'⁻¹, ?_⟩⟩, ?_⟩
    · rw [← hg', mul_smul, inv_smul_smul, hg]
    · rintro t ⟨ht, h, hh⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨g'', hg''⟩ := hrep c'
      have e1 : rep c' = rep x := (hrep_eq (rep c') c' g'' hg'').trans (hrep_eq x (rep c') h hh)
      have e2 : rep c = rep x := hrep_eq x c g hg
      rw [e1, e2]

theorem card_stab_smul (g : G) (x : X) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_stab_sub (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : X) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G (π x)) x) =
      Nat.card (MulAction.stabilizer G x) := Nat.card_congr
  { toFun := fun h => ⟨h.1.1, h.2⟩
    invFun := fun g => ⟨⟨g.1, by
      show g.1 • π x = π x
      rw [← hπ]
      exact congrArg π g.2⟩, g.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem sum_orbits_on (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (B : Set Y)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (hAB : ∀ x ∈ A, π x ∈ B)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ t ∈ sX, t ∈ A) (hsY : ∀ u ∈ sY, u ∈ B)
    (hX : ∀ x ∈ A, ∃! t : X, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ B, ∃! t : Y, t ∈ sY ∧ ∃ g : G, g • t = y)
    (hfinY : ∀ y ∈ B, (MulAction.stabilizer G y : Set G).Finite) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ =
      ∑ u ∈ sY, (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) /
        (Nat.card (MulAction.stabilizer G u) : ℝ) := by
  classical
  have key : ∀ t : X, ∃ (u : Y) (g : G), t ∈ A → (u ∈ sY ∧ g • u = π t) := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨u, ⟨hu, g, hg⟩, -⟩ := hY (π t) (hAB t ht)
      exact ⟨u, g, fun _ => ⟨hu, hg⟩⟩
    · exact ⟨π t, 1, fun h => absurd h ht⟩
  choose U γ hU using key
  have hπ' : ∀ t ∈ A, π ((γ t)⁻¹ • t) = U t := by
    intro t ht
    rw [hπ, ← (hU t ht).2, inv_smul_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := sX) (t := sY) (g := U)
    (fun t ht => (hU t (hsX t ht)).1)]
  refine Finset.sum_congr rfl fun u hu => ?_
  set T : Finset X := (sX.filter (fun t => U t = u)).image (fun t => (γ t)⁻¹ • t) with hTdef
  have hinj : Set.InjOn (fun t => (γ t)⁻¹ • t) (sX.filter (fun t => U t = u) : Set X) := by
    intro t₁ h₁ t₂ h₂ e
    have h₁' := (Finset.mem_filter.mp h₁).1
    have h₂' := (Finset.mem_filter.mp h₂).1
    exact (hX _ (hA (γ t₁)⁻¹ t₁ (hsX t₁ h₁'))).unique ⟨h₁', _, rfl⟩ ⟨h₂', _, e.symm⟩
  have hstab : ∀ g : MulAction.stabilizer G u, ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      g • x ∈ {x : X | x ∈ A ∧ π x = u} := by
    rintro ⟨g, hg⟩ x ⟨hx1, hx2⟩
    refine ⟨hA g x hx1, ?_⟩
    change π (g • x) = u
    rw [hπ, hx2]
    exact MulAction.mem_stabilizer_iff.mp hg
  have hTA : ∀ t ∈ T, t ∈ {x : X | x ∈ A ∧ π x = u} := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h₁, rfl⟩ := Finset.mem_filter.mp h₀
    exact ⟨hA _ _ (hsX t₀ h₁), hπ' t₀ (hsX t₀ h₁)⟩
  have hT : ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      ∃! t, t ∈ T ∧ ∃ g : MulAction.stabilizer G u, g • t = x := by
    rintro x ⟨hx1, hx2⟩
    obtain ⟨t, ⟨ht, g, hg⟩, huniq⟩ := hX x hx1
    have htA := hsX t ht
    have e1 : (g * γ t) • U t = u := by
      rw [mul_smul, (hU t htA).2, ← hπ, hg, hx2]
    have hUt : U t = u :=
      (hY u (hsY u hu)).unique ⟨(hU t htA).1, _, e1⟩ ⟨hu, 1, one_smul _ _⟩
    refine ⟨(γ t)⁻¹ • t, ⟨Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hUt⟩, rfl⟩,
      ⟨g * γ t, MulAction.mem_stabilizer_iff.mpr (by rw [← hUt] at e1 ⊢; exact e1)⟩, ?_⟩, ?_⟩
    · change (g * γ t) • (γ t)⁻¹ • t = x
      rw [mul_smul, smul_inv_smul, hg]
    · rintro t' ⟨ht', ⟨g', hg'm⟩, hg'⟩
      obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht'
      have h₀' := (Finset.mem_filter.mp h₀).1
      have : t₀ = t := huniq t₀ ⟨h₀', g' * (γ t₀)⁻¹, by rw [mul_smul]; exact hg'⟩
      rw [this]
  have hfinG : Finite (MulAction.stabilizer G u) := (hfinY u (hsY u hu)).to_subtype
  have hfinA : Finite ↥{x : X | x ∈ A ∧ π x = u} := by
    apply Set.Finite.to_subtype
    refine ((T : Set X).toFinite.biUnion
      (fun t _ => Set.finite_range (fun g : MulAction.stabilizer G u => g • t))).subset ?_
    intro x hx
    obtain ⟨t, ⟨ht, g, hg⟩, -⟩ := hT x hx
    exact Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨g, hg⟩
  have main := sum_inv_card_stab (G := MulAction.stabilizer G u) {x : X | x ∈ A ∧ π x = u}
    hstab T hTA hT
  have e0 : (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) =
      (Nat.card ↥{x : X | x ∈ A ∧ π x = u} : ℝ) := rfl
  rw [e0, main, hTdef, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨ht1, rfl⟩ := Finset.mem_filter.mp ht
  have := card_stab_sub π hπ ((γ t)⁻¹ • t)
  rw [hπ' t (hsX t ht1)] at this
  rw [this, card_stab_smul]

end OrbSum

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

section One

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hp := hd x hx
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hp σ.toRingHom)
      ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩
  rw [← hre] at hpos
  have : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    simp
  rw [this] at hpos
  exact_mod_cast hpos

theorem exists_smul_mem {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (v : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • v ∈ Λ := by
  first | exact Bl.general_b_fact_second_form.goal1 .. | (apply Bl.general_b_fact_second_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_form.goal1 <;> assumption)

scoped instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem smul_pair (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, g.1 p.2) := rfl

def stabLatEquiv (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) Λ ≃ Formalism.ThetaLiftIndependence.autL h Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pairs (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (n : K) :
    Set (Submodule (𝓞 K) V × V) :=
  {p | p.1 ∈ Formalism.HermitianLatticesTheory.genus h L ∧ p.2 ∈ p.1 ∧ h p.2 p.2 = n}

theorem apply_mem_gmap (g : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Λ) :
    g x ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
  exact hx

theorem pairs_stable (hs : h.IsSymm) (L : Submodule (𝓞 K) V) (n : K) (g : Formalism.HermitianLatticesTheory.isom h)
    (p : Submodule (𝓞 K) V × V) (hp : p ∈ pairs h L n) : g • p ∈ pairs h L n :=
  ⟨OrbitRepresentatives.gmap_mem_genus hs hp.1 g.2, apply_mem_gmap g.1 hp.2.1, (g.2 p.2 p.2).trans hp.2.2⟩

def perpO (h : V →ₗ⋆[K] V →ₗ[K] K) (x : V) : Submodule (𝓞 K) V :=
  (LinearMap.ker (h x)).restrictScalars (𝓞 K)

theorem mem_perpO (x v : V) : v ∈ perpO h x ↔ h x v = 0 := Iff.rfl

def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Submodule (𝓞 K) V × V) : Submodule (𝓞 K) V × V :=
  (p.1 ⊓ perpO h p.2, p.2)

theorem proj_smul (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    proj h (g • p) = g • proj h p := by
  refine Prod.ext ?_ rfl
  ext v
  change v ∈ Formalism.HermitianLatticesTheory.gmap g.1 p.1 ⊓ perpO h (g.1 p.2) ↔
    v ∈ Formalism.HermitianLatticesTheory.gmap g.1 (p.1 ⊓ perpO h p.2)
  rw [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.mem_inf,
    mem_perpO, mem_perpO]
  have : h (g.1 p.2) v = h p.2 (g.1.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply g.1 v]
    exact g.2 _ _
  rw [this]

end One

section Two

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open SplitBAux

theorem isLattice_cut (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsLattice K Λ) : Submodule.IsLattice K (S.cut Λ) := by
  refine ⟨?_, ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    have hle : (S.cut Λ).map (S.ι.restrictScalars (𝓞 K)) ≤ Λ := Submodule.map_comap_le _ _
    exact Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj
      (Submodule.FG.of_le_of_isNoetherian hle)
  · rw [eq_top_iff]
    intro a _
    obtain ⟨r, hr, hra⟩ := exists_smul_mem hΛ (S.ι a)
    have h1 : r • a ∈ S.cut Λ := by
      rw [VecSplit.mem_cut_iff, ← algebraMap_smul K r a, map_smul, algebraMap_smul]
      exact hra
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by
      simpa using hr
    have e : a = (algebraMap (𝓞 K) K r)⁻¹ • (r • a) := by
      rw [← algebraMap_smul K r a, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

def emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Λ'.map (S.ι.restrictScalars (𝓞 K))

theorem cut_emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : S.cut (emb S Λ') = Λ' :=
  Submodule.comap_map_eq_of_injective (f := S.ι.restrictScalars (𝓞 K)) S.inj Λ'

theorem emb_injective (S : VecSplit h h') : Function.Injective (emb S) := fun A B e => by
  rw [← cut_emb S A, e, cut_emb]

theorem inf_perpO (S : VecSplit h h') (Λ : Submodule (𝓞 K) V) :
    Λ ⊓ perpO h S.x₀ = emb S (S.cut Λ) := by
  ext v
  constructor
  · rintro ⟨hv, hv0⟩
    obtain ⟨a, rfl⟩ := exists_of_orth S hv0
    exact Submodule.mem_map.mpr ⟨a, hv, rfl⟩
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨ha, S.orth a⟩

theorem gmap_extOf_emb (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (C : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (emb S C) = emb S (Formalism.HermitianLatticesTheory.gmap g' C) := by
  unfold Formalism.HermitianLatticesTheory.gmap emb
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext a
  exact extOf_ι S g' a

theorem cut_gmap_extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (Λ : Submodule (𝓞 K) V) :
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap g' (S.cut Λ) := by
  ext a
  rw [VecSplit.mem_cut_iff, mem_gmap_iff, mem_gmap_iff, VecSplit.mem_cut_iff, eq_decomp_ι S a,
    extOf_symm_apply, ← eq_decomp_ι]

theorem stab_pair_iff (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') (g : Formalism.HermitianLatticesTheory.isom h) :
    g ∈ MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ↔
      Formalism.HermitianLatticesTheory.gmap g.1 (emb S Λ') = emb S Λ' ∧ g.1 S.x₀ = S.x₀ := by
  rw [MulAction.mem_stabilizer_iff, smul_pair, Prod.ext_iff]

def stabPairEquiv (hs : h.IsSymm) (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ≃
      Formalism.ThetaLiftIndependence.autL h' Λ' where
  toFun a := ⟨res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2,
    res_mem_isom S _ _ _, by
      have := gmap_res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2
        ((stab_pair_iff S Λ' a.1).mp a.2).1
      rwa [cut_emb] at this⟩
  invFun b := ⟨⟨extOf S b.1, extOf_mem_isom hs S b.2.1⟩, (stab_pair_iff S Λ' _).mpr
    ⟨by rw [gmap_extOf_emb, b.2.2], extOf_x₀ S _⟩⟩
  left_inv a := Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
    (linearMap_ext S (by simp [extOf_x₀, ((stab_pair_iff S Λ' a.1).mp a.2).2])
      (fun v => by simp [extOf_ι, res_spec]))))
  right_inv b := Subtype.ext (LinearEquiv.ext fun v => S.inj (by simp [res_spec, extOf_ι]))

end Two

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
end
end
