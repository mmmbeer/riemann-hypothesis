import Formalism.LocalToGlobal.Columns.TiedMvA
import Formalism.LocalToGlobal.Columns.TiedUpDn
import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT
import Formalism.LocalToGlobal.Columns.HermOwed

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hxm_hform_mulVec {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J g : Matrix (Fin n) (Fin n) R)
    (h : cT σ g * J * g = J) (x y : Fin n → R) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have key : ∀ (J' : Matrix (Fin n) (Fin n) R) (a b : Fin n → R), hform σ J' a b = (fun i => σ (a i)) ⬝ᵥ (J' *ᵥ b) := by
    intro J' a b
    unfold hform dotProduct mulVec dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  have hs : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    unfold mulVec dotProduct
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
  rw [key, key, hs, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ g * J * g) *ᵥ y) = _
  rw [h]

variable {D : ColRec}

def hxG (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨((CF.crdN D i hi).trans (glEquiv γ.1)).trans (CF.crdN D i hi).symm, by
    intro x y
    rw [hx_hform i hi, hx_hform i hi x y]
    show hform _ _ (CF.crdN D i hi ((CF.crdN D i hi).symm (γ.1.1 *ᵥ CF.crdN D i hi x)))
      (CF.crdN D i hi ((CF.crdN D i hi).symm (γ.1.1 *ᵥ CF.crdN D i hi y))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hxm_hform_mulVec _ _ _ γ.2 _ _⟩

theorem hxG_crd (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) (x : (D.sp.X i).V) :
    CF.crdN D i hi ((hxG i hi γ).1 x) = γ.1.1 *ᵥ CF.crdN D i hi x :=
  (CF.crdN D i hi).apply_symm_apply _

abbrev hxMap (i : ℕ) (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  M.map ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

theorem hxm_map_inj {i : ℕ} (hi : i ≤ D.R.m) {M M' : Submodule (𝓞 D.host.E) (D.sp.X i).V} (h : hxMap i hi M = hxMap i hi M') :
    M = M' := by
  ext x
  rw [← hx_mem_map hi M x, ← hx_mem_map hi M' x]
  show _ ∈ hxMap i hi M ↔ _ ∈ hxMap i hi M'
  rw [h]

theorem hxm_map_gmap (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    hxMap i hi (gmap (hxG i hi γ).1 M) = Formalism.L2.Forms.mulLat γ.1.1 (hxMap i hi M) := by
  unfold hxMap gmap Formalism.L2.Forms.mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact hxG_crd i hi γ x

theorem hxm_map_locP (i : ℕ) (hi : i ≤ D.R.m) (p : Ideal (𝓞 D.host.E)) [p.IsPrime] (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    hxMap i hi (localization₂ p M) = localization₂ p (hxMap i hi M) := by
  ext t
  constructor
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    refine ⟨s, hs, ⟨s • x, hx, ?_⟩⟩
    exact ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)).map_smul s x
  · rintro ⟨s, hs, ⟨x, hx, e⟩⟩
    refine ⟨(CF.crdN D i hi).symm t, ⟨s, hs, ?_⟩, (CF.crdN D i hi).apply_symm_apply t⟩
    have e2 : s • (CF.crdN D i hi).symm t = x := by
      apply (CF.crdN D i hi).injective
      have e3 := ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
        (𝓞 D.host.E)).map_smul s ((CF.crdN D i hi).symm t)
      refine Eq.trans e3 ?_
      show s • CF.crdN D i hi ((CF.crdN D i hi).symm t) = _
      rw [LinearEquiv.apply_symm_apply]
      exact e.symm
    rw [e2]
    exact hx

theorem hxm_crd_frame (i : ℕ) (hi : i ≤ D.R.m) (b : Fin (D.sp.X i).rank) :
    CF.crdN D i hi ((D.sp.X i).frame b) = Pi.single (finCongr (CF.rankN D i hi) b) (1 : D.host.E) := by
  funext j
  show (D.sp.X i).frame.equivFun ((D.sp.X i).frame b) ((finCongr (CF.rankN D i hi)).symm j) = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩

theorem hxG_toGLb (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) :
    Formalism.L2.Herm.toGLb (D.sp.X i).frame (hxG i hi γ).1 = Formalism.L2.Forms.reGL (CF.rankN D i hi).symm _ γ.1 := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  show LinearMap.toMatrixAlgEquiv (D.sp.X i).frame (((hxG i hi γ).1 : (D.sp.X i).V ≃ₗ[D.host.E] (D.sp.X i).V) :
    (D.sp.X i).V →ₗ[D.host.E] (D.sp.X i).V) a b = γ.1.1 (finCongr (CF.rankN D i hi) a) (finCongr (CF.rankN D i hi) b)
  rw [LinearMap.toMatrixAlgEquiv_apply]
  have h1 : (D.sp.X i).frame.repr ((hxG i hi γ).1 ((D.sp.X i).frame b)) a =
      CF.crdN D i hi ((hxG i hi γ).1 ((D.sp.X i).frame b)) (finCongr (CF.rankN D i hi) a) := by
    show _ = (D.sp.X i).frame.equivFun _ ((finCongr (CF.rankN D i hi)).symm (finCongr (CF.rankN D i hi) a))
    rw [Equiv.symm_apply_apply]
    rfl
  refine Eq.trans h1 ?_
  rw [hxG_crd, hxm_crd_frame, Matrix.mulVec_single_one]
  rfl

theorem hxG_toGLb0 (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D 0 (Nat.zero_le _))) :
    Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (hxG 0 (Nat.zero_le _) γ).1 =
      Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ γ.1 := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  show LinearMap.toMatrixAlgEquiv ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0))
    (((hxG 0 (Nat.zero_le _) γ).1 : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V) a b =
      γ.1.1 (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) a) (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) b)
  rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindex_apply, Basis.repr_reindex_apply]
  have h1 : ∀ x : (D.sp.X 0).V, (D.sp.X 0).frame.repr x ((finCongr D.sp.rank0).symm a) =
      CF.crdN D 0 (Nat.zero_le _) x (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) a) := fun x => rfl
  refine Eq.trans (h1 _) (Eq.trans (congrFun (hxG_crd 0 (Nat.zero_le _) γ ((D.sp.X 0).frame ((finCongr D.sp.rank0).symm b)))
    (finCongr (Formalism.L2.Forms.rank_eq_first_level D.R) a)) ?_)
  rw [hxm_crd_frame, Matrix.mulVec_single_one]
  rfl

theorem localization_map_eq_of_transport {i : ℕ} (hi : i ≤ D.R.m) (p : Ideal (𝓞 D.host.E)) [p.IsPrime]
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) {M M' : Submodule (𝓞 D.host.E) (D.sp.X i).V}
    (h : localization₂ p (Formalism.L2.Forms.mulLat γ.1.1 (hxMap i hi M)) = localization₂ p (hxMap i hi M')) :
    localization₂ p (gmap (hxG i hi γ).1 M) = localization₂ p M' := by
  apply hxm_map_inj hi
  rw [hxm_map_locP, hxm_map_locP, hxm_map_gmap]
  exact h

theorem hxm_sameOff {i : ℕ} (hi : i ≤ D.R.m) (p : Ideal (𝓞 D.host.E))
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) {M M' : Submodule (𝓞 D.host.E) (D.sp.X i).V}
    (h : SameOffC p (Formalism.L2.Forms.mulLat γ.1.1 (hxMap i hi M)) (hxMap i hi M')) :
    Formalism.L2.Herm.SameOff (S := D.sp.X i) p (gmap (hxG i hi γ).1 M) M' := fun q hq h1 h2 => by
  have := hq.isPrime
  exact localization_map_eq_of_transport hi q γ (h q hq h1 h2)

theorem hxm_map_sup_span {i : ℕ} (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (t : D.host.E) (y : (D.sp.X i).V) :
    hxMap i hi (M ⊔ Submodule.span (𝓞 D.host.E) {t • y}) =
      hxMap i hi M ⊔ Submodule.span (𝓞 D.host.E) {t • CF.crdN D i hi y} := by
  unfold hxMap
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  congr 3
  exact map_smul (CF.crdN D i hi) t y

theorem hxm_nat_smul {i : ℕ} (hi : i ≤ D.R.m) (T : ℕ) (x : (D.sp.X i).V) :
    CF.crdN D i hi ((T : D.host.E) • x) = ((T : ℕ) : 𝓞 D.host.E) • CF.crdN D i hi x := by
  rw [map_smul, Algebra.smul_def', map_natCast]
  rfl

theorem hxm_Ld (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    hxMap i hi (CH.Ld D u i c) = CF.Ld D u i hi c := (hx_Ld_eq u i hi c).symm

variable {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

set_option maxHeartbeats 4000000 in

theorem hxm_up (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c))
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) (p : (D.fm u).lv i v c)
    (h : SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c p))) (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.Ld D u i hi ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (hxLd i hi c y).1}) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c p)))
        (hz : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ z.1) ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c p))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))) :
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).up i v c p))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (CH.Ld D u i ((D.fm u).up i v c p))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).up i v c p))
        (hz : ((D.mem u).A.T : D.host.E) • (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).up i v c p))
        (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨hxm_sameOff hi _ γ h1, localization_map_eq_of_transport hi _ γ ?_, localization_map_eq_of_transport hi _ γ ?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · rw [hxm_Ld]; exact h2
  · rw [hxm_map_sup_span, hxm_Ld, hxm_Ld]; exact h3
  · have e : CF.crdN D i hi (((D.mem u).A.T : D.host.E) • (hxG i hi γ).1 z.1) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (hxLd i hi _ z).1) := by
      rw [hxm_nat_smul, hxG_crd]; rfl
    have hz' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (hxLd i hi _ z).1) ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h4 (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h5 v' hv' (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm

set_option maxHeartbeats 4000000 in

theorem hxm_dn (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c))
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (h : SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).dn i v c g))) (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat γ.1.1 (CF.Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.clsCrd D u i hi c) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Lk A i hi v c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = g ((P i hi).prk v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))) :
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (CH.Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (D.clsLat u i c) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Lk D u (A.Pv v) i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = g (hxPrk A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hxm_sameOff hi _ γ h1, localization_map_eq_of_transport hi _ γ ?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · rw [hxm_Ld]; exact h2
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Lk A i hi v c := by
      rw [← e]; exact (hx_mem_Lk A i hi v c _).2 hz
    rw [hxPr_eq A P i hi, hxPrk_eq A P i hi, h3 (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h4 v' hv' (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm

set_option maxHeartbeats 4000000 in

theorem hxm_dil (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i)
    (γ : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (h : Formalism.L2.Forms.mulLat γ.1.1 (CF.clsCrd D u i hi ((D.fm u).dil i v a c)) = CF.clsCrd D u i hi c ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : γ.1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))) :
    Formalism.HermitianLatticesTheory.gmap (hxG i hi γ).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (hxG i hi γ).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hxm_map_inj hi ?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · rw [hxm_map_gmap]; exact h1
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h2 (hxLd i hi _ z) hz']
    congr 3
    exact Subtype.ext e.symm
  · have e : CF.crdN D i hi ((hxG i hi γ).1 z.1) = γ.1.1 *ᵥ (hxLd i hi _ z).1 := hxG_crd i hi γ z.1
    have hz' : γ.1.1 *ᵥ (hxLd i hi _ z).1 ∈ CF.Ld D u i hi c := by
      rw [← e]; exact (hx_mem_Ld u i hi c _).2 hz
    rw [hxPr_eq A P i hi, hxPr_eq A P i hi, h3 v' hv' (hxLd i hi _ z) hz']
    congr 2
    exact Subtype.ext e.symm

variable {A P} (M : AtTMovesC A P)

open Classical in

def AtTMovesC.upS (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c)) : CH.GX D i :=
  if hi : i ≤ D.R.m then hxG i hi (M.upG i hi v c (hxLd i hi c y)) else 1

open Classical in

def AtTMovesC.dnS (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) : CH.GX D i :=
  if hi : i ≤ D.R.m then hxG i hi (M.dnG i hi v c g) else 1

open Classical in

def AtTMovesC.dilS (i : ℕ) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) : CH.GX D i :=
  if hi : i ≤ D.R.m then hxG i hi (M.dilG i hi v a c) else 1

theorem AtTMovesC.upS_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c)) :
    M.upS i v c y = hxG i hi (M.upG i hi v c (hxLd i hi c y)) := dif_pos hi

theorem AtTMovesC.dnS_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) : M.dnS i v c g = hxG i hi (M.dnG i hi v c g) := dif_pos hi

theorem AtTMovesC.dilS_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) :
    M.dilS i v a c = hxG i hi (M.dilG i hi v a c) := dif_pos hi

set_option maxHeartbeats 4000000 in

def AtTMovesC.toMoves : AtTMoves A P where
  upG := M.upS
  up_tie := fun i hi v c y hy => by
    have hy' : (D.fm u).fv i v c ((P i hi).pr v c (hxLd i hi c y)) = 1 := by
      rw [← hxPr_eq A P i hi]; exact hy
    have h := M.up_tie i hi v c (hxLd i hi c y) hy'
    rw [← hxPr_eq A P i hi v c y] at h
    rw [M.upS_eq i hi]
    exact hxm_up A P i hi v c y _ _ h
  dnG := M.dnS
  dn_tie := fun i hi v c g hg => by
    rw [M.dnS_eq i hi]
    exact hxm_dn A P i hi v c g _ (M.dn_tie i hi v c g hg)
  dilG := M.dilS
  dil_tie := fun i hi v a c => by
    rw [M.dilS_eq i hi]
    exact hxm_dil A P i hi v a c _ (M.dil_tie i hi v a c)

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem tam_locP_L_off {d : Deco E n ST SG} (hd : d.Ok) (Q : HeightOneSpectrum (𝓞 E)) (hQ : Q ∉ ST) :
    localization₂ Q.asIdeal d.L = localization₂ Q.asIdeal d.N := by
  classical
  have hex : ∀ P : ST, ∃ a ∈ P.1.asIdeal, a ∉ Q.asIdeal := fun P =>
    exists_mem_notMem (P := P.1) (Q := Q) fun e => hQ (e ▸ P.2)
  choose a ha ha' using hex
  refine le_antisymm (localizationAt_mono Q hd.L_le_N) (localization_le_of_smul_mem (a := ∏ P : ST, a P) ?_ fun x hx =>
    hd.smul_N_mem_L (fun P => Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ P)) (ha P)) hx)
  intro h
  obtain ⟨P, -, hP⟩ := (Ideal.IsPrime.prod_mem_iff (hp := Q.isPrime)).1 h
  exact ha' P hP

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem tam_locP_L_same {v : HeightOneSpectrum (𝓞 F)} {d d₁ : Deco E n ST SG} (hd : d.Ok) (hd₁ : d₁.Ok)
    (h : Deco.SameOff ST SG v d d₁) (Q : HeightOneSpectrum (𝓞 E)) (hQ : ¬ IsOver v Q) :
    localization₂ Q.asIdeal d.L = localization₂ Q.asIdeal d₁.L := by
  by_cases hS : Q ∈ ST
  · ext x
    rw [hd.mem_locP_L ⟨Q, hS⟩, hd₁.mem_locP_L ⟨Q, hS⟩, h.f ⟨Q, hS⟩ hQ]
    show x ∈ localization₂ Q.asIdeal d.N ∧ _ ↔ x ∈ localization₂ Q.asIdeal d₁.N ∧ _
    rw [h.N Q hQ]
  · rw [tam_locP_L_off hd Q hS, tam_locP_L_off hd₁ Q hS, h.N Q hQ]

omit [StarRing E] in
theorem localizationAt_congr (I : Ideal (𝓞 E)) [I.IsPrime] {A B : Submodule (𝓞 E) (Fin n → E)} (e : A = B) : localization₂ I A = localization₂ I B := by
  rw [e]

theorem SameOffC.congr_right {I : Ideal (𝓞 E)} {A B B' : Submodule (𝓞 E) (Fin n → E)} (h : SameOffC I A B) (e : B' = B) :
    SameOffC I A B' := e ▸ h

theorem tam_sameOffC (hc : Formalism.BasicNotions.CMData F E) {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} (hov : IsOver v P)
    {A B : Submodule (𝓞 E) (Fin n → E)} (h : ∀ Q : HeightOneSpectrum (𝓞 E), ¬ IsOver v Q → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B)
    (I : Ideal (𝓞 E)) (hI : I = P.asIdeal) : SameOffC I A B := by
  subst hI
  intro q hq h1 h2
  have hb : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField E)
  refine h ⟨q, hq.isPrime, hb⟩ fun hQ => ?_
  rcases rll_over_cases hc hov hQ with e | e
  · exact h1 (congrArg HeightOneSpectrum.asIdeal e)
  · exact h2 ((congrArg HeightOneSpectrum.asIdeal e).trans (conjIdeal_asIdeal P).symm)

end Lat

section Move

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

omit [NeZero n] in

theorem tam_ufGL_mem (g : UF E n) : ufGL E n g ∈ URat hc n := by
  obtain ⟨γ, rfl⟩ := (ratHom_bijective hc n).2 g
  rw [tud_ufGL_ratHom]
  exact γ.2

omit [NeZero n] in
theorem tam_ratHom (g : UF E n) : ratHom hc n ⟨ufGL E n g, tam_ufGL_mem hc n g⟩ = g := by
  obtain ⟨γ, rfl⟩ := (ratHom_bijective hc n).2 g
  congr 1
  exact Subtype.ext (tud_ufGL_ratHom hc n γ)

include hc in

theorem tam_lat_move (g₀ : UF E n × H) (d' d₁ : DecoSet E n ST SG) (hg₀ : g₀ • d' = d₁) :
    Formalism.L2.Forms.mulLat ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.L = d₁.1.L ∧
      Formalism.L2.Forms.mulLat ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh = d₁.1.Lsh ∧
      ∀ (P : ST) y, d'.1.f P y = d₁.1.f P (((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) := by
  subst hg₀
  have hap : ∀ y, ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y = ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) y := by
    intro y
    have h1 := rlc_ratHom_apply hc n ⟨ufGL E n g₀.1, tam_ufGL_mem hc n g₀.1⟩ y
    rw [tam_ratHom] at h1
    exact h1.symm
  have hm : ∀ L : Submodule (𝓞 E) (Sp E n), Formalism.L2.Forms.mulLat ((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) L =
      gmap ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) L := by
    intro L
    unfold Formalism.L2.Forms.mulLat gmap
    congr 1
    apply LinearMap.ext
    intro y
    exact hap y
  refine ⟨by rw [hm, rlc_smul_val, Deco.L_act], by rw [hm, rlc_smul_val, Deco.Lsh_act _ g₀.1.2], fun P y => ?_⟩
  show d'.1.f P y = d'.1.f P (((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n).symm (((ufGL E n g₀.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y))
  rw [hap, LinearEquiv.symm_apply_apply]

theorem tam_move (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) (v : HeightOneSpectrum (𝓞 F)) (d d₁ d' : DecoSet E n ST SG)
    (h : Deco.SameOff ST SG v d.1 d₁.1) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d₁) :
    Formalism.L2.Herm.AdStep hc.sig (1 : Matrix (Fin n) (Fin n) E) (levU hc n ST SG H)
      (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
      (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (ufGL E n g₀.1) v := by
  obtain ⟨γ, η, κ, hγ, -, hη, e⟩ := updn_move hc n ST SG H hS c₀ v d d₁ d' h g₀ hg₀
  rw [← hγ, tud_ufGL_ratHom]
  exact ⟨κ.1, κ.2, η.1, η.2, hη, e⟩

theorem tam_sameOff_dia (d : DecoSet E n ST SG) (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) {v : HeightOneSpectrum (𝓞 F)}
    (hov : IsOver v P.1) : Deco.SameOff ST SG v d.1 (d.dia1 P a).1 := by
  classical
  refine ⟨fun _ _ => rfl, fun Q hQ => ?_, fun _ _ => rfl⟩
  funext x
  show d.1.f Q x = ((Pi.mulSingle P a : DiaG E ST) Q).1 * d.1.f Q x
  rw [Pi.mulSingle_eq_of_ne (fun e => hQ (by rw [e]; exact hov)), Units.val_one, one_mul]

end Move

section Moved

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG : Finset (Pl E)}

include hc in

theorem tam_upL {v : HeightOneSpectrum (𝓞 F)} (d : DecoSet E n ST SG) (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {a : 𝓞 E} (ha : SepElt ST a) (x : d.lv P) (hx : d.fv P x = 1) :
    Deco.SameOff ST SG v d.1 (d.upL P q x).1 ∧
      localization₂ P.1.asIdeal (d.upL P q x).1.L = localization₂ P.1.asIdeal d.1.Lsh ∧
      (∀ {w : Sp E n} {t : 𝓞 E}, t ∉ P.1.asIdeal → w ∈ d.1.Lsh → modP.rep x - t • w ∈ P.1.asIdeal • d.1.N →
        localization₂ P.1.asIdeal (d.upL P q x).1.Lsh =
          localization₂ P.1.asIdeal (d.1.Lsh ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • w})) ∧
      (∀ y ∈ (d.upL P q x).1.Lsh, (d.upL P q x).1.f P y = d.1.f P (q • y)) ∧
      ∀ P' : ST, P' ≠ P → (d.upL P q x).1.f P' = d.1.f P' := by
  have hfr := tud_f_rep n ST SG d P hx
  have hd₁ : (d.upL P q x).1 = d.1.up P q (modP.rep x) := d.up_val P hP hq hq2 (modP.rep_mem x) hfr
  have hSO := tud_sameOff_up hc d P hP hq hq2 hov (modP.rep_mem x) hfr
  refine ⟨hSO, ?_, ?_, ?_, ?_⟩
  · rw [tud_locP_L ha, DecoSet.locP_LshKer_up hP hq hq2 ha (d.upL_mem P hP hq hq2 hx) P]
  · intro w t ht hw hrw
    rw [(d.upL P q x).2.locP_Lsh ha P, show (d.upL P q x).1.N = upN P.1.asIdeal d.1.N (modP.rep x) from
      congrArg Deco.N hd₁, localizationAt_upN d.2.lat d.2.uni P.1 hP.ne (modP.rep_mem x)]
    exact localizationAt_upA hq hq2 d.2.N_le_Lsh (by rw [← d.2.locP_Lsh ha P]; exact le_locP _ _) hw ht hrw
  · intro y hy
    have hy2 := (d.upL P q x).2.Lsh_le_at ha P hy
    rw [hd₁, Deco.up_f, if_pos]
    rw [hd₁] at hy2
    exact hy2
  · intro P' hP'
    rw [hd₁]
    exact Deco.up_f_ne d.1 P q _ hP'

include hc in

theorem tam_dnL {v : HeightOneSpectrum (𝓞 F)} (d : DecoSet E n ST SG) (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P)
    {a : 𝓞 E} (ha : SepElt ST a) (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (d.lk P)) (hg : g ≠ 0) :
    Deco.SameOff ST SG v d.1 (d.dnL P g).1 ∧
      localization₂ P.1.asIdeal (d.dnL P g).1.Lsh = localization₂ P.1.asIdeal d.1.L ∧
      (∀ y, (d.dnL P g).1.f P y = modP.ext P.1 (d.1.kerAt P) g y) ∧
      ∀ P' : ST, P' ≠ P → (d.dnL P g).1.f P' = d.1.f P' := by
  classical
  have hd₁ := d.dnL_val P hP hg
  refine ⟨tud_sameOff_dn hc d P hP hg hov, ?_, fun y => ?_, fun P' hP' => ?_⟩
  · rw [(d.dnL P g).2.locP_Lsh ha P, show (d.dnL P g).1.N = d.1.dnN P from congrArg Deco.N hd₁,
      (d.2.dnN_spec P hP.ne).2.2.2, ← d.2.locP_LshKer_self ha P, tud_locP_L ha]
  · rw [hd₁]
    show Function.update d.1.f P _ P _ = _
    rw [Function.update_self]
  · rw [hd₁]
    show Function.update d.1.f P _ P' = _
    rw [Function.update_of_ne hP']

omit [NeZero n] in

theorem tam_diaL (d : DecoSet E n ST SG) (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    (d.dia1 P a).1.L = d.1.L ∧ (∀ y, (d.dia1 P a).1.f P y = a.1 * d.1.f P y) ∧
      ∀ P' : ST, P' ≠ P → (d.dia1 P a).1.f P' = d.1.f P' := by
  classical
  refine ⟨Deco.L_dia _ _, fun y => ?_, fun P' hP' => ?_⟩
  · show ((Pi.mulSingle P a : DiaG E ST) P).1 * d.1.f P y = _
    rw [Pi.mulSingle_eq_same]
  · funext y
    show ((Pi.mulSingle P a : DiaG E ST) P').1 * d.1.f P' y = _
    rw [Pi.mulSingle_eq_of_ne hP', Units.val_one, one_mul]

end Moved

section Crd

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) {σ₀ : X.K →+* ℂ} {n : ℕ} {cls : Type}
  {L : cls → Submodule (𝓞 X.E) (Fin n → X.E)}

def tamG (Q : StepCrd Pr σ₀ n L) (g : UF X.E n) : UJ (hc.sig : X.E →+* X.E) Q.J :=
  ⟨ufGL X.E n g, by rw [Q.hJ]; exact tam_ufGL_mem hc n g⟩

end Crd

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (i : ℕ)

abbrev tamDil (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (c : StCl W Λ u i) : StCl W Λ u i :=
  dilD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) P a c

abbrev tamMv (d₁ : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) : UF X.E (R.N i) := ((stepGSD W Λ u i).outSec.mv d₁).1

variable (Q : StepCrd Pr σ₀ (R.N i) fun c : StCl W Λ u i => (tudR W Λ u i c).1.L)

theorem tam_lat (d₁ : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) :
    Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i d₁)).1.1 (Q.lat (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁)) = d₁.1.L ∧
      Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i d₁)).1.1
        (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁))) = d₁.1.Lsh ∧
      ∀ (P : Pr.vT u) y, (tudR W Λ u i (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁)).1.f P y =
        d₁.1.f P ((tamG hc Q (tamMv W Λ u i d₁)).1.1 *ᵥ y) := by
  have hLd := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q (clsD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) d₁)
  rw [hLd, Q.hlat]
  exact tam_lat_move hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp ((stepGSD W Λ u i).outSec.mv d₁) _ d₁ ((stepGSD W Λ u i).outSec.mv_smul d₁)

include hX in
set_option maxHeartbeats 1000000 in

theorem tam_up (P : Pr.vT u) (c : StCl W Λ u i) (z : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z) = 1) :
    SameOffC (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
        (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
          (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))) (Q.lat c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
                  (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
                  (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1
                  (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) ⊔
          Submodule.span (𝓞 X.E) {((Pr.T u : ℕ) : X.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))))
        (hx : ((Pr.T u : ℕ) : 𝓞 X.E) • ((tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
          (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 *ᵥ x.1) ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudUp W Λ hc hPr σ₀ u i Q P c z)).fv P
            (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tudUp W Λ hc hPr σ₀ u i Q P c z) x) =
          (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c ⟨_, hx⟩)) ∧
      ∀ P' : Pr.vT u, P' ≠ P → ∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudUp W Λ hc hPr σ₀ u i Q P c z))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
          (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudUp W Λ hc hPr σ₀ u i Q P c z)).fv P'
            (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' (tudUp W Λ hc hPr σ₀ u i Q P c z) x) =
          (tudR W Λ u i c).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' c ⟨_, hx⟩) := by
  classical
  have ha := sepElt_of_ok hPr u
  have hP := moveHyp_of_ok hPr u P
  obtain ⟨hq, hq2⟩ := T_unif hX hPr u P
  have hLd := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q c
  have hLd' := tie_Ld_eq hc σ₀ u (tudR W Λ u i) Q (tudUp W Λ hc hPr σ₀ u i Q P c z)
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q
  have hrz := tud_rep_pr hc hPr σ₀ u (tudR W Λ u i) Q P c z
  have hzL : z.1 ∈ (tudR W Λ u i c).1.Lsh := hLd ▸ z.2
  obtain ⟨hL, hLs, hf⟩ := tam_lat W Λ hc σ₀ u i Q ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E)
    (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z))
  obtain ⟨h1, h2, h3, h4, h5⟩ := tam_upL hc (tudR W Λ u i c) P (tieEV_over hc hX hPr u P) hP hq hq2 ha _ hz
  have h3' := h3 (tud_unit hPr u P) hzL hrz
  rw [map_natCast] at h3'
  have hlat : Q.lat c = (tudR W Λ u i c).1.L := congrFun Q.hlat c
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact (tam_sameOffC hc (tieEV_over hc hX hPr u P)
      (fun Q' hQ' => (tam_locP_L_same (tudR W Λ u i c).2 (Subtype.property _) h1 Q' hQ').symm) _ Ideal.mk_ker).congr_right hlat
  · simp only [Ideal.mk_ker]
    rw [hL]
    exact h2.trans (localizationAt_congr _ hLd.symm)
  · simp only [Ideal.mk_ker]
    rw [hLs]
    exact h3'.trans (localizationAt_congr _ (congrArg (· ⊔ Submodule.span (𝓞 X.E) {((Pr.T u : ℕ) : X.E)⁻¹ • z.1}) hLd.symm))
  · intro x hx
    rw [hfv, hfv, hf]
    exact h4 _ (hLs ▸ Submodule.mem_map_of_mem x.2)
  · intro P' hP' x hx
    rw [hfv, hfv, hf, h5 P' hP']

include hX in
set_option maxHeartbeats 1000000 in

theorem tam_dn (P : Pr.vT u) (c : StCl W Λ u i) (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) ((tudR W Λ u i c).lk P)) (hg : g ≠ 0) :
    SameOffC (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
        (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1 (Q.lat (tudDn W Λ u i P c g))) (Q.lat c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal))
                (Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1
                  (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) (Q.lat c) ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1 *ᵥ x.1 ∈
          Q.lat c ⊔ RingHom.ker (Ideal.Quotient.mk P.1.asIdeal) • dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudDn W Λ u i P c g)).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tudDn W Λ u i P c g) x) =
          g (tiePrk hc hPr σ₀ u (tudR W Λ u i) Q P c (RingHom.ker (Ideal.Quotient.mk P.1.asIdeal)) Ideal.mk_ker ⟨_, hx⟩)) ∧
      ∀ P' : Pr.vT u, P' ≠ P → ∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tudDn W Λ u i P c g))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dnL P g))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tudDn W Λ u i P c g)).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' (tudDn W Λ u i P c g) x) =
          (tudR W Λ u i c).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' c ⟨_, hx⟩) := by
  classical
  have ha := sepElt_of_ok hPr u
  have hP := moveHyp_of_ok hPr u P
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q
  have hprk := tud_prk hc hPr σ₀ u (tudR W Λ u i) Q P c _ Ideal.mk_ker g
  obtain ⟨hL, hLs, hf⟩ := tam_lat W Λ hc σ₀ u i Q ((tudR W Λ u i c).dnL P g)
  obtain ⟨h1, h2, h3, h5⟩ := tam_dnL hc (tudR W Λ u i c) P (tieEV_over hc hX hPr u P) hP ha g hg
  have hlat : Q.lat c = (tudR W Λ u i c).1.L := congrFun Q.hlat c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact (tam_sameOffC hc (tieEV_over hc hX hPr u P)
      (fun Q' hQ' => (tam_locP_L_same (tudR W Λ u i c).2 (Subtype.property _) h1 Q' hQ').symm) _ Ideal.mk_ker).congr_right hlat
  · simp only [Ideal.mk_ker]
    rw [hLs]
    exact h2.trans (localizationAt_congr _ hlat.symm)
  · intro x hx
    rw [hfv, hprk, hf]
    exact h3 _
  · intro P' hP' x hx
    rw [hfv, hfv, hf, h5 P' hP']

theorem tam_dil (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (c : StCl W Λ u i) :
    Formalism.L2.Forms.mulLat (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dia1 P a))).1.1 (Q.lat (tamDil W Λ u i P a c)) = Q.lat c ∧
      (∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tamDil W Λ u i P a c))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dia1 P a))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tamDil W Λ u i P a c)).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P (tamDil W Λ u i P a c) x) =
          a.1 * (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c ⟨_, hx⟩)) ∧
      ∀ P' : Pr.vT u, P' ≠ P → ∀ (x : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat (tamDil W Λ u i P a c))))
        (hx : (tamG hc Q (tamMv W Λ u i ((tudR W Λ u i c).dia1 P a))).1.1 *ᵥ x.1 ∈ dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)),
        (tudR W Λ u i (tamDil W Λ u i P a c)).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' (tamDil W Λ u i P a c) x) =
          (tudR W Λ u i c).fv P' (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P' c ⟨_, hx⟩) := by
  have hfv := tie_fv hc hPr σ₀ u (tudR W Λ u i) Q
  obtain ⟨hL, -, hf⟩ := tam_lat W Λ hc σ₀ u i Q ((tudR W Λ u i c).dia1 P a)
  obtain ⟨h1, h2, h3⟩ := tam_diaL (tudR W Λ u i c) P a
  have hlat : Q.lat c = (tudR W Λ u i c).1.L := congrFun Q.hlat c
  refine ⟨?_, ?_, ?_⟩
  · exact hL.trans (h1.trans hlat.symm)
  · intro x hx
    rw [hfv, hfv]
    exact (hf P x.1).trans (h2 _)
  · intro P' hP' x hx
    rw [hfv, hfv]
    exact (hf P' x.1).trans (congrFun (h3 P' hP') _)

include hX in

theorem tam_so_up (P : Pr.vT u) (c : StCl W Λ u i) (z : ↥(dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : (tudR W Λ u i c).fv P (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z) = 1) :
    Deco.SameOff (Pr.vT u) Pr.vGs (tieEV hc hX hPr u P).1 (tudR W Λ u i c).1
      ((tudR W Λ u i c).upL P (Pr.T u : 𝓞 X.E) (tiePr hc hPr σ₀ u (tudR W Λ u i) Q P c z)).1 :=
  (tam_upL hc (tudR W Λ u i c) P (tieEV_over hc hX hPr u P) (moveHyp_of_ok hPr u P) (T_unif hX hPr u P).1 (T_unif hX hPr u P).2
    (sepElt_of_ok hPr u) _ hz).1

omit Q in
include hX in

theorem tam_so_dn (P : Pr.vT u) (c : StCl W Λ u i) (g : Module.Dual (𝓞 X.E ⧸ P.1.asIdeal) ((tudR W Λ u i c).lk P)) (hg : g ≠ 0) :
    Deco.SameOff (Pr.vT u) Pr.vGs (tieEV hc hX hPr u P).1 (tudR W Λ u i c).1 ((tudR W Λ u i c).dnL P g).1 :=
  tud_sameOff_dn hc (tudR W Λ u i c) P (moveHyp_of_ok hPr u P) hg (tieEV_over hc hX hPr u P)

end Gen

section Ad

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem tam_ad (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (v : HeightOneSpectrum (𝓞 X.F))
    (c c' : DecoCl n (Pr.vT u) Pr.vGs Λ.grp) (d₁ : DecoSet X.E n (Pr.vT u) Pr.vGs)
    (h : Deco.SameOff (Pr.vT u) Pr.vGs v (s c).1 d₁.1) (g₀ : UF X.E n × Λ.grp) (hg₀ : g₀ • s c' = d₁) :
    Formalism.L2.Herm.AdStep hc.sig H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.U
      ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c).1 ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c').1
      (Formalism.L2.Forms.reGL H.hn.symm _ (ufGL X.E n g₀.1)) v := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  rw [Formalism.L2.Forms.reGL_rfl]
  exact tam_move hc _ (Pr.vT u) Pr.vGs Λ.grp hS c₀ v (s c) d₁ (s c') h g₀ hg₀

end Ad

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Any

variable {D : ColRec} {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} (H : CH.HermCols D) (M : AtTMovesC A P)

theorem hxm_adI_up (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).up i v c ((P i hm).pr v c (hxLd i hm c y))))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.upG i hm v c (hxLd i hm c y)).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).up i v c (hxPr A P i v c y)) (M.toMoves.upG i v c y) v := by
  rw [hxPr_eq A P i hm]
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.upS i v c y).1) _
  rw [M.upS_eq i hm, hxG_toGLb]
  exact h

theorem hxm_adI_dn (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).dn i v c g))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.dnG i hm v c g).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).dn i v c g) (M.toMoves.dnG i v c g) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.dnS i v c g).1) _
  rw [M.dnS_eq i hm, hxG_toGLb]
  exact h

theorem hxm_adI_dil (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i)
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).dil i v a c))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.dilG i hm v a c).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).dil i v a c) (M.toMoves.dilG i v a c) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.dilS i v a c).1) _
  rw [M.dilS_eq i hm, hxG_toGLb]
  exact h

theorem adjacency_level_zero_up (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (y : ↥(CH.Ld D u 0 c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c)
      ((H.lev0 u).y ((D.fm u).up 0 v c ((P 0 (Nat.zero_le _)).pr v c (hxLd 0 (Nat.zero_le _) c y))))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.upG 0 (Nat.zero_le _) v c (hxLd 0 (Nat.zero_le _) c y)).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).up 0 v c (hxPr A P 0 v c y)) (M.toMoves.upG 0 v c y) v := by
  rw [hxPr_eq A P 0 (Nat.zero_le _)]
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.upS 0 v c y).1) _
  rw [M.upS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

theorem adjacency_level_zero_down (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y ((D.fm u).dn 0 v c g))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.dnG 0 (Nat.zero_le _) v c g).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).dn 0 v c g) (M.toMoves.dnG 0 v c g) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.dnS 0 v c g).1) _
  rw [M.dnS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

theorem adjacency_level_zero_dilation (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls 0)
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y ((D.fm u).dil 0 v a c))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.dilG 0 (Nat.zero_le _) v a c).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).dil 0 v a c) (M.toMoves.dilG 0 v a c) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.dilS 0 v a c).1) _
  rw [M.dilS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

end Any

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)

set_option maxHeartbeats 4000000 in

def atTMovesC (u : d.what₂.Word) : AtTMovesC (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) where
  upG := fun i hi v c y => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i
    ((d.repr u i c).upL v (d.Pr.T u : 𝓞 d.X.E) (tiePr d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c y)))
  up_tie := fun i hi v c y hy => tam_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v c y hy
  dnG := fun i hi v c g => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i ((d.repr u i c).dnL v g))
  dn_tie := fun i hi v c g hg => tam_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v c g hg
  dilG := fun i hi v x c => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i ((d.repr u i c).dia1 v x))
  dil_tie := fun i hi v x c => tam_dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v x c

def atTMoves (u : d.what₂.Word) : AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) :=
  (atTMovesC a hS hH u).toMoves

end Rec

section AdRec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

theorem th_adI (u : d.what₂.Word) (i : ℕ) (hm : i ≤ d.R.m) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u i)
    (d₁ : DecoSet d.X.E (d.R.N i) (d.Pr.vT u) d.Pr.vGs)
    (h : Deco.SameOff (d.Pr.vT u) d.Pr.vGs (tieEV d.sp.cm d.hX d.hPr u v).1 (d.repr u i c).1 d₁.1) :
    Formalism.L2.Herm.AdStep d.sp.cm.sig (d.sp.X i).gram (hermPack hS hP hK u i hm).lev.U ((hermPack hS hP hK u i hm).cls.y c).1
      ((hermPack hS hP hK u i hm).cls.y (clsD (colVal (Pr := d.Pr) d.W u i (d.Pr.vT u) d.Pr.vGs) (d.lev i) d₁)).1
      (Formalism.L2.Forms.reGL (d.sp.X_rank i hm).symm _ (ufGL d.X.E (d.R.N i) (tamMv (Pr := d.Pr) d.W d.lev u i d₁)))
      (tieEV d.sp.cm d.hX d.hPr u v).1 :=
  tam_ad d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hm) _ c _ d₁ h
    ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.mv d₁) ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.mv_smul d₁)

theorem adjacency_level_zero_tied (u : d.what₂.Word) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u 0)
    (d₁ : DecoSet d.X.E (d.R.N 0) (d.Pr.vT u) d.Pr.vGs)
    (h : Deco.SameOff (d.Pr.vT u) d.Pr.vGs (tieEV d.sp.cm d.hX d.hPr u v).1 (d.repr u 0 c).1 d₁.1) :
    Formalism.L2.Herm.AdStep d.sp.cm.sig d.sp.gram0 (hermPack0 hS hP hK u).lev.U ((hermPack0 hS hP hK u).cls.y c).1
      ((hermPack0 hS hP hK u).cls.y (clsD (colVal (Pr := d.Pr) d.W u 0 (d.Pr.vT u) d.Pr.vGs) (d.lev 0) d₁)).1
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level d.R).symm _ (ufGL d.X.E (d.R.N 0) (tamMv (Pr := d.Pr) d.W d.lev u 0 d₁)))
      (tieEV d.sp.cm d.hX d.hPr u v).1 :=
  tam_ad d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) _ c _ d₁ h
    ((stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.mv d₁) ((stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.mv_smul d₁)

set_option maxHeartbeats 4000000 in

theorem adTied (O : AtTOwed a hS hH) (hO : O.moves = atTMoves a hS hH) :
    CH.AdTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  obtain ⟨disc, moves, xp⟩ := O
  obtain rfl : moves = atTMoves a hS hH := hO
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v c y hy
    have hy' := hy
    rw [show (hermAtT a hS hH ⟨disc, atTMoves a hS hH, xp⟩ u).pr 0 v c y = _ from
      hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) 0 (Nat.zero_le _) v c y] at hy'
    exact adjacency_level_zero_up (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v c y
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_so_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u 0 (stepCrd a hS hH u 0 (Nat.zero_le _)) v c _ hy'))
  · intro u i h1 hm v c y hy
    have hy' := hy
    rw [show (hermAtT a hS hH ⟨disc, atTMoves a hS hH, xp⟩ u).pr i v c y = _ from
      hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) i hm v c y] at hy'
    exact hxm_adI_up (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v c y
      (th_adI hS hP hK u i hm v c _ (tam_so_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hm) v c _ hy'))
  · intro u v c g hg
    exact adjacency_level_zero_down (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v c g
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_so_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr u 0 v c g hg))
  · intro u i h1 hm v c g hg
    exact hxm_adI_dn (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v c g
      (th_adI hS hP hK u i hm v c _ (tam_so_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr u i v c g hg))
  · intro u v x c
    exact adjacency_level_zero_dilation (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v x c
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_sameOff_dia (d.R.N 0) (d.Pr.vT u) d.Pr.vGs (d.repr u 0 c) v x (tieEV_over d.sp.cm d.hX d.hPr u v)))
  · intro u i h1 hm v x c
    exact hxm_adI_dil (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v x c
      (th_adI hS hP hK u i hm v c _ (tam_sameOff_dia (d.R.N i) (d.Pr.vT u) d.Pr.vGs (d.repr u i c) v x (tieEV_over d.sp.cm d.hX d.hPr u v)))

end AdRec

end Formalism.L2.Col
end
end
