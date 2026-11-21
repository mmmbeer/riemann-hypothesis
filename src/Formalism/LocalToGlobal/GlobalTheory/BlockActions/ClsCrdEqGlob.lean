import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.InJSymRestrict
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfDegree
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LatSOfMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ChiFinM (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U,
    (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)

def SelfDualP (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem gramP_det_unit (D : D7) : IsUnit (gramP D).det := by
  let _ := D.host.cmStar
  unfold gramP
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.G.gram_det_unit D.sp.cm D.sp.X'

theorem isLat_dlP (D : D7) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)) (hM : Comp.IsLat M) :
    Comp.IsLat (Comp.dl (sigD D) (gramP D) M) := by
  have hL : Submodule.IsLattice D.host.E M := ⟨Module.Finite.iff_fg.1 hM.1, hM.2⟩
  obtain ⟨d, hd, hle⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramP D) (gramP_det_unit D) M hL
  exact ⟨Module.Finite.iff_fg.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hd hle),
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramP D) M hL⟩

variable {D : D7} {u : D.what₂.Word}

theorem levelLattice_dual_eq_self (K : ClsPTied (D := D) u) : Comp.dl (sigD D) (gramP D) K.lev.Lb = K.lev.Lb := by
  have hS : dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) K.lev.Lb = (K.lev.Lb : Set _) := by
    ext y
    constructor
    · intro hy
      have h := K.lev.Lb_dual y hy
      simpa using h
    · intro hy
      exact K.lev.Lb_int y hy
  unfold Comp.dl
  rw [hS, Submodule.span_eq]

theorem classLattice_eq_globalLattice (K : ClsPTied (D := D) u) (c : (D.fm u).clsP) :
    K.lat c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
  ext x
  constructor
  · intro hx
    exact (K.y_lat c _).1 (latS_of_mem _ x hx)
  · intro hx
    exact latLocGlob _ _ _ (K.lat c) (K.lat_fin c) x ((K.y_lat c _).2 hx)

theorem selfDualP_of_formsTiedSym {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    SelfDualP Tf := by
  intro c
  have hLb : Comp.IsLat Tf.clsP.lev.Lb := ⟨Tf.clsP.lev.Lb_fin, Tf.clsP.lev.Lb_span⟩
  have h1 : Comp.dl (sigD D) (gramP D) (Tf.clsP.lat c) = Tf.clsP.lat c := by
    rw [classLattice_eq_globalLattice, ← Comp.glob_dl (sigD D) (gramP D) (isLat_dlP D) hLb _ (Tf.clsP.y c).2, levelLattice_dual_eq_self]
  rw [← Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_span_dualSet]
  exact congrArg (fun M : Submodule _ _ => (M : Set (Fin (D.R.N D.R.m - 1) → D.host.E))) h1

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms

theorem bij_of_inj_back {A B : Type} [Finite A] (f : A → B) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    Function.Bijective f := by
  haveI : Finite B := Finite.of_injective g hg
  exact hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective g hg)

theorem stabiliser_bijective_of_injection
    (h : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      ∀ c, ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g) :
    StabiliserMapBijective := by
  intro D u Ch chOf Tf c
  obtain ⟨g, hg⟩ := h D u Ch chOf Tf c
  exact bij_of_inj_back _ ((D.fm u).stabMap_inj c) g hg

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in
theorem stab_restrict (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range)
    (δ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D))
    (hδ : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ.1.1 ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1)) :
    δ ∈ (Tf.clsP.stabI c).range := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  rw [Km.stabI_range] at hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ
  rw [Tf.clsP.stabI_range]
  have hdet : IsUnit ((Tf.clsP.y c).1.1).det := (Matrix.isUnit_iff_isUnit_det _).mp (Tf.clsP.y c).1.isUnit
  obtain ⟨g, hg, hu⟩ := til_ext Tf (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1
  set Gc : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := ((Matrix.isUnit_iff_isUnit_det g).mpr (hu hdet)).unit with hGcdef
  have hGcv : Gc.1 = g := IsUnit.unit_spec _
  have hGc : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1 Gc.1 := by rw [hGcv]; exact hg
  have e1 := Tf.tilAd.til_ad c Gc hGc
  have hGc1 : Gc = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1 * (Km.y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c).1)⁻¹ := eq_mul_inv_of_mul_eq e1.symm
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = (Km.y ((D.fm u).til c)).1 * κ * ((Km.y ((D.fm u).til c)).1)⁻¹ := by
    rw [← hκe]; rfl
  set Γ : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.til.ga c).1 * γ.1 * ((Tf.til.ga c)⁻¹).1) with hΓ
  have hGK : Gc⁻¹ * Γ * Gc ∈ Km.lev.U := by
    have e : Gc⁻¹ * Γ * Gc = (Tf.tilAd.ka c).1 * κ * ((Tf.tilAd.ka c).1)⁻¹ := by
      rw [hΓ, map_mul, map_mul, hbc, hGc1]
      have hi : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.til.ga c)⁻¹).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1)⁻¹ := by
        rw [← map_inv]; rfl
      rw [hi]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Tf.tilAd.ka c).2 hκ) (Subgroup.inv_mem _ (Tf.tilAd.ka c).2)
  have hinv : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.clsP.y c).1.1)⁻¹ (Gc⁻¹).1 :=
    isExt_inv hGc (Units.inv_mul Gc) (Matrix.mul_nonsing_inv _ hdet)
  have hΓ1 : (Γ.1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
      ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [hΓ]; rfl
  have hΓE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (δ.1.1.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) Γ.1 := by
    rw [hΓ1]; exact isExt_map hδ
  set K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
    ((Tf.clsP.y c).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 * (Tf.clsP.y c).1 with hK
  have hKE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 (Gc⁻¹ * Γ * Gc).1 := by
    have e : K.1 = ((Tf.clsP.y c).1.1)⁻¹ * δ.1.1.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 := by
      rw [hK, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]; rfl
    rw [e, Units.val_mul, Units.val_mul]
    exact isExt_mul (isExt_mul hinv hΓE) hGc
  have hKU := lev_mem Tf K _ hKE hGK
  refine Subgroup.mem_map.mpr ⟨K, hKU, ?_⟩
  show (Tf.clsP.y c).1 * K * ((Tf.clsP.y c).1)⁻¹ = _
  rw [hK]
  group

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def StabFix (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *ᵥ Tf.til.z0 = Tf.til.z0

theorem span_with_orthogonal_vector (Tf : FormsTiedSym D u Ch chOf) :
    ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • Tf.til.z0 := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have ha0 : a ≠ 0 := by
    intro h0
    have hzz := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, h0, zero_smul] at hzz
    apply hT0; rw [← hzz]; simp [hform]
  intro y
  obtain ⟨x, s, hy⟩ := span_iXc_zc D y
  exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩

theorem ext_of_fix (Tf : FormsTiedSym D u Ch chOf) (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)
    (hΓ : cT (sigD D : D.host.E →+* D.host.E) Γ * gramN D D.R.m le_rfl * Γ = gramN D D.R.m le_rfl)
    (hfix : Γ *ᵥ Tf.til.z0 = Tf.til.z0) :
    ∃ δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ ∧
      ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  have hC := crdFacts_of Tf
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hγ : ∀ x y, hform σ J (Γ *ᵥ x) (Γ *ᵥ y) = hform σ J x y := fun x y => hform_UJ σ J Γ hΓ x y
  obtain ⟨δ, hδ, hδi⟩ := fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth (span_with_orthogonal_vector Tf)
    (by rw [hzz]; exact hT0) Γ hγ hfix
  refine ⟨δ, ⟨?_, ?_⟩, hδi⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    show Γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)
    have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
    rw [hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]
  · have : (fun a => (RingHom.id D.host.E) (z0 a)) = z0 := rfl
    rw [this]; exact hfix

theorem ext_unique (Tf : FormsTiedSym D u Ch chOf) {δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E}
    {Γ1 Γ2 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E}
    (h1 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ1) (h2 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ2) : Γ1 = Γ2 := by
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  have hz : (fun a => (RingHom.id D.host.E) (Tf.til.z0 a)) = Tf.til.z0 := rfl
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  rw [hm] at a1 a2
  rw [hz] at b1 b2
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  simp only [Matrix.toLin'_apply]
  obtain ⟨x, s, rfl⟩ := span_with_orthogonal_vector Tf y
  have hx : iXc D x = iXm D *ᵥ x := by simp only [iXm, LinearMap.toMatrix'_mulVec]
  rw [hx, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, b1, b2, mulVec_mulVec, mulVec_mulVec, a1, a2]

set_option maxHeartbeats 4000000 in

theorem stab_back (Tf : FormsTiedSym D u Ch chOf) (hF : StabFix Tf) (c : (D.fm u).clsP) :
    ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  have key : ∀ s : (D.mem u).C.stab D.R.m ((D.fm u).til c), ∃ (s' : (D.fm u).stabilizer₂ c)
      (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ
        ((Tf.til.ga c).1.1 * (Km.stabI ((D.fm u).til c) s).1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      (Tf.clsP.stabI c s').1.1 = δ := by
    intro s
    set γ := Km.stabI ((D.fm u).til c) s with hγ
    have hU : cT (sigD D : D.host.E →+* D.host.E) ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *
        gramN D D.R.m le_rfl * ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) = gramN D D.R.m le_rfl := by
      have h0 := (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).2
      have e : (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 =
          (Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1 := by
        simp only [Subgroup.coe_mul, Units.val_mul]
      have h1 : cT (sigD D : D.host.E →+* D.host.E) (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 *
          gramN D D.R.m le_rfl * (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 = gramN D D.R.m le_rfl := h0
      rwa [e] at h1
    obtain ⟨δ, hδE, hδi⟩ := ext_of_fix Tf _ hU (hF c γ ⟨s, rfl⟩)
    have hΓu : IsUnit ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).det := by
      rw [← Units.val_mul, ← Units.val_mul]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
    have hδu := isUnit_of_extE Tf δ _ hΓu hδE
    set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef
    have hΔv : Δ.1 = δ := IsUnit.unit_spec _
    have hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) := by
      show cT _ Δ.1 * gramP D * Δ.1 = gramP D
      rw [hΔv]; exact unitary_of_hform _ _ _ hδi
    obtain ⟨s', hs'⟩ := stab_restrict Tf c γ ⟨s, rfl⟩ ⟨Δ, hΔ⟩ (by rw [show (⟨Δ, hΔ⟩ : UJ _ _).1.1 = δ from hΔv]; exact hδE)
    exact ⟨s', δ, hδE, by rw [hs']; exact hΔv⟩
  choose g δf hδE hδv using key
  refine ⟨g, fun s1 s2 h12 => ?_⟩
  have hδ12 : δf s1 = δf s2 := by rw [← hδv s1, ← hδv s2, h12]
  have hΓ := ext_unique Tf (hδE s1) (hδ12 ▸ hδE s2)
  apply Km.stabI_inj ((D.fm u).til c)
  apply Subtype.ext
  apply Units.ext
  have hi : ((Tf.til.ga c)⁻¹).1.1 * (Tf.til.ga c).1.1 = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have := congrArg (fun M => ((Tf.til.ga c)⁻¹).1.1 * M * (Tf.til.ga c).1.1) hΓ
  simp only [← Matrix.mul_assoc, hi, Matrix.one_mul] at this
  simp only [Matrix.mul_assoc, hi, Matrix.mul_one] at this
  exact this

theorem stabiliser_bijective_of_fixed
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      StabFix Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_injection (fun D u Ch chOf Tf c => stab_back Tf (hF D u Ch chOf Tf) c)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions NumberField

theorem T_sub_one_ge (D : D7) (u : D.what₂.Word) :
    D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 ≤ (D.mem u).A.T - 1 := by
  set M : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 with hM
  obtain ⟨π, -, hπ, hπ1⟩ := D.T_norm u
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp hπ1
  set cj : D.host.E →+* D.host.E := (D.host.conj : D.host.E →+* D.host.E) with hcj
  let αb : 𝓞 D.host.E := ⟨cj (α : D.host.E), (α.2).map cj.toIntAlgHom⟩
  let b : 𝓞 D.host.E := α + αb + (M : 𝓞 D.host.E) * α * αb
  have hαE : (π : D.host.E) = 1 + (M : D.host.E) * (α : D.host.E) := by
    have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hα
    simp only [map_mul, map_sub, map_one, map_natCast, RingOfIntegers.coe_eq_algebraMap] at this ⊢
    rw [← hM] at this
    linear_combination -this
  have hcπ : cj (π : D.host.E) = 1 + (M : D.host.E) * cj (α : D.host.E) := by
    rw [hαE, map_add, map_mul, map_one, map_natCast]
  have hT : ((D.mem u).A.T : D.host.E) - 1 = (M : D.host.E) * (b : D.host.E) := by
    have hπ' : (π : D.host.E) * cj (π : D.host.E) = ((D.mem u).A.T : D.host.E) := hπ
    rw [← hπ', hcπ, hαE]
    simp only [b, αb, map_add, map_mul, map_natCast, RingOfIntegers.coe_eq_algebraMap]
    show _ = (M : D.host.E) * ((α : D.host.E) + cj (α : D.host.E) + (M : D.host.E) * (α : D.host.E) * cj (α : D.host.E))
    ring
  have hMpos : 0 < M := by
    have hq : 0 < D.host.q := by have := D.host.qd_big.1; omega
    have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
    have hg0 := (D.host.g_prime 0).pos
    have hg1 := (D.host.g_prime 1).pos
    have hn : 0 < D.host.QS := D.host.QS_pos
    rw [hM]; positivity
  have hME : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  set r : ℚ := (((D.mem u).A.T : ℚ) - 1) / (M : ℚ) with hr
  have hbr : (b : D.host.E) = algebraMap ℚ D.host.E r := by
    rw [hr, map_div₀, map_sub, map_natCast, map_one, map_natCast, hT]
    field_simp
  have hint : IsIntegral ℤ r := by
    have h1 : IsIntegral ℤ (algebraMap ℚ D.host.E r) := hbr ▸ RingOfIntegers.isIntegral_coe b
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ D.host.E) (algebraMap ℚ D.host.E).injective).mp h1
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hTq : ((D.mem u).A.T : ℚ) - 1 = (M : ℚ) * (z : ℚ) := by
    have : (z : ℚ) = r := hz
    rw [this, hr]; field_simp
  have hT2 := (D.mem u).A.T_prime.two_le
  have hTz : ((D.mem u).A.T : ℤ) - 1 = (M : ℤ) * z := by exact_mod_cast hTq
  have hz1 : 1 ≤ z := by
    by_contra hc
    push Not at hc
    have : (M : ℤ) * z ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have : (M : ℤ) ≤ ((D.mem u).A.T : ℤ) - 1 := by nlinarith
  omega

theorem finrank_host_lt_T_sub_one (D : D7) (u : D.what₂.Word) : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1 := by
  have hf : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h := T_sub_one_ge D u
  have hq : 2 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hg0 := (D.host.g_prime 0).two_le
  have hg1 := (D.host.g_prime 1).two_le
  have hgg : 4 ≤ D.host.g 0 * D.host.g 1 := by nlinarith
  have hgg2 : 16 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := by nlinarith
  have hQ : 0 < D.host.QS := D.host.QS_pos
  have hN : 0 < D.host.QS * D.host.q * D.host.d := by positivity
  haveI : NeZero (D.host.QS * D.host.q * D.host.d) := ⟨hN.ne'⟩
  have hcard : Nat.card D.R.GG ≤ Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ :=
    Nat.card_le_card_of_surjective _ D.host.der.art_surj
  have hGG : Nat.card D.R.GG = 4 * D.R.ord := D.R.natCard_GG
  have hphi : Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ ≤ D.host.QS * D.host.q * D.host.d := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  have key : D.host.QS * D.host.q * D.host.d < D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
    nlinarith
  omega

theorem class_injective_of_self_dual
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramP D) (Tf.clsP.lat c) =
        (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))) :
    ClassMapInjective :=
  classMapInjective_of_finrank_lt hSD (fun D u _ _ _ => finrank_host_lt_T_sub_one D u)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def StabLF (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) ∧
    (∀ x ∈ Ld D u D.R.m le_rfl ((D.fm u).til c), γ.1.1 *ᵥ x ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)) ∧
    ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
      (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
      (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)

set_option maxHeartbeats 4000000 in

theorem stabFix_of (Tf : FormsTiedSym D u Ch chOf)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hLF : StabLF Tf) : StabFix Tf := by
  have hC := crdFacts_of Tf
  have hdeg := finrank_host_lt_T_sub_one D u
  obtain ⟨v⟩ := vT_nonempty D u
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  intro c γ hγ
  obtain ⟨hL, hLd, hf⟩ := hLF c γ hγ
  set g1 := (Tf.til.ga c).1.1 with hg1
  set gi := ((Tf.til.ga c)⁻¹).1.1 with hgi
  set gs := γ.1.1 with hgs
  have hgi1 : gi * g1 = 1 := by simp [hgi, hg1]
  have hg1i : g1 * gi = 1 := by simp [hgi, hg1]
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hUgi : cT σ gi * J * gi = J := ((Tf.til.ga c)⁻¹).2
  have hUgs : cT σ gs * J * gs = J := γ.2
  have hγf : ∀ x y, hform σ J ((g1 * gs * gi) *ᵥ x) ((g1 * gs * gi) *ᵥ y) = hform σ J x y := fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ga_herm Tf c, hform_UJ σ J gs hUgs,
      hform_UJ σ J gi hUgi]
  have hlat : mulLat (g1 * gs * gi) ((Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}) =
      (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
    rw [← Tf.til.til_lat c, mulLat_mulLat, Matrix.mul_assoc, hgi1, Matrix.mul_one, ← mulLat_mulLat, hL]
  have hres : ∀ y : Fin (D.R.N D.R.m) → D.host.E,
      (∀ w ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0},
        hform σ J w y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) →
      ∀ r r' : 𝓞 D.host.E, (r : D.host.E) = hform σ J z0 y → (r' : D.host.E) = hform σ J z0 ((g1 * gs * gi) *ᵥ y) →
        r - r' ∈ Tf.atT.Pv v := by
    intro y hy r r' hr hr'
    have hxy : g1 *ᵥ (gi *ᵥ y) = y := by rw [mulVec_mulVec, hg1i, one_mulVec]
    have hxa : gi *ᵥ y ∈ Ld D u D.R.m le_rfl ((D.fm u).til c) := by
      apply Submodule.subset_span
      intro l hl
      have hl' : g1 *ᵥ l ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
        rw [← Tf.til.til_lat c]; exact Submodule.mem_map.2 ⟨l, hl, rfl⟩
      have := hy _ hl'
      rw [← hxy, ga_herm Tf c] at this
      exact this
    have hxb := hLd _ hxa
    have e1 := Tf.til.til_fv v c ⟨gi *ᵥ y, hxa⟩ r (by rw [hr]; show _ = hform σ J z0 (g1 *ᵥ (gi *ᵥ y)); rw [hxy])
    have e2 := Tf.til.til_fv v c ⟨gs *ᵥ (gi *ᵥ y), hxb⟩ r' (by
      rw [hr']; show _ = hform σ J z0 (g1 *ᵥ (gs *ᵥ (gi *ᵥ y))); rw [mulVec_mulVec, mulVec_mulVec])
    rw [hf v ⟨gi *ᵥ y, hxa⟩ hxb, e1] at e2
    show Tf.atT.res v (r - r') = 0
    rw [map_sub, e2, sub_self]
  exact fix_orthogonal_vector σ hC.conj J (gramP D) hC.defN (iXc D) z0 hC.iso horth (span_with_orthogonal_vector Tf) _ hTp hdeg hzz
    (Tf.clsP.lat c) (Tf.clsP.lat c)
    ⟨fun y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c) := fun x hx => hy x hx
      rw [hSD c] at this; exact this,
     fun x hx y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c) := by rw [hSD c]; exact hy
      exact this x hx⟩
    (g1 * gs * gi) hγf hlat (Tf.atT.Pv v) inferInstance (T_mem_Pv Tf v) hres

theorem stabiliser_bijective_of_finite
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hLF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      StabLF Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_fixed (fun D u Ch chOf Tf => stabFix_of Tf (hSD D u Ch chOf Tf) (hLF D u Ch chOf Tf))

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem mulLat_one {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  unfold mulLat
  convert Submodule.map_id L
  ext x i
  simp

theorem dualL_stable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (γ γi : Matrix (Fin n) (Fin n) E) (hγi : γi * γ = 1) (hγ' : γ * γi = 1)
    (hU : cT σ γ * J * γ = J) (hL : mulLat γ L = L) :
    ∀ y ∈ dualL σ J L, γ *ᵥ y ∈ dualL σ J L := by
  have hLi : mulLat γi L = L := by
    conv_lhs => rw [← hL]
    rw [mulLat_mulLat, hγi, mulLat_one]
  have hset : ∀ y ∈ dualSet σ J L, γ *ᵥ y ∈ dualSet σ J L := by
    intro y hy x hx
    have hxi : γi *ᵥ x ∈ L := by
      rw [← hLi]; exact Submodule.mem_map_of_mem hx
    have e : x = γ *ᵥ (γi *ᵥ x) := by rw [mulVec_mulVec, hγ', one_mulVec]
    rw [e, hform_UJ σ J γ hU]
    exact hy _ hxi
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (hset z hz)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have e : γ *ᵥ (r • a) = r • (γ *ᵥ a) := by
      rw [← algebraMap_smul E r a, mulVec_smul, algebraMap_smul]
    rw [e]; exact Submodule.smul_mem _ r ha

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem stabLF_of (Tf : FormsTiedSym D u Ch chOf)
    (h : ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
      γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
      mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) ∧
      ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
        (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
          (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)) :
    StabLF Tf := by
  intro c γ hγ
  obtain ⟨hL, hf⟩ := h c γ hγ
  refine ⟨hL, ?_, hf⟩
  have h1 : (γ.1⁻¹ : GL _ _).1 * γ.1.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : γ.1.1 * (γ.1⁻¹ : GL _ _).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact dualL_stable _ _ _ γ.1.1 _ h1 h2 γ.2 hL

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_tensInt (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    prV (E := E) v s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · apply Subring.subset_closure
      left
      refine ⟨y, ?_⟩
      simp [prV, evalV, Algebra.TensorProduct.map_tmul]
    · apply Subring.subset_closure
      right
      refine ⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, y.2 v⟩, ?_⟩
      simp [prV, evalV, Algebra.TensorProduct.map_tmul]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem latS_prV (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hx : x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    (fun i => prV (E := E) v (x i)) ∈
      latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (fun i => prV (E := E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by
      funext i; simp
    rw [e]; exact add_mem ha hb
  | smul s a _ ha =>
    have e : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v s, prV_tensInt v s.1 s.2⟩ : ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) •
          (fun i => prV (E := E) v (a i)) := by
      funext i; simp [Subring.smul_def]
    rw [e]; exact Submodule.smul_mem _ _ ha

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem clsCrd_fin (u : D.what₂.Word) (c : (D.mem u).C.cls D.R.m) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u D.R.m le_rfl c) := by
  letI := D.host.cmStar
  rw [Module.Finite.iff_fg]
  exact (D.clsLat_lat u D.R.m c).fg.map _

set_option maxHeartbeats 4000000 in

theorem stab_lat_le (Tf : FormsTiedSym D u Ch chOf) (hLG : LatLocGlob) (hAL : AdLocLat) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range) :
    mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) ≤ clsCrd D u D.R.m le_rfl ((D.fm u).til c) := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  rw [Km.stabI_range] at hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ
  set Y := (Km.y ((D.fm u).til c)).1 with hY
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = Y * κ * Y⁻¹ := by rw [← hκe]; rfl
  rintro _ ⟨x, hx, rfl⟩
  show γ.1.1 *ᵥ x ∈ _
  apply hLG D.host.F D.host.E _ _ (clsCrd_fin u _)
  have hX := latS_of_mem (F := D.host.F) _ x hx
  have hZ := (Km.y_lat _ _).1 hX
  set Z := (Y⁻¹).1 *ᵥ (fun i => inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) with hZdef
  have hκZ : κ.1 *ᵥ Z ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Km.lev.Lb := by
    apply hAL D.host.F D.host.E _ _ Km.lev.Lb_fin
    intro v
    have hv := Km.lev.Uloc_lev v (((Km.lev.U_eq κ).1 hκ).2 v)
    have hst := (Subgroup.mem_inf.mp hv).2
    have e : (fun i => prV (E := D.host.E) v ((κ.1 *ᵥ Z) i)) =
        (bc (prV (E := D.host.E) v) κ).1 *ᵥ (fun i => prV (E := D.host.E) v (Z i)) := by
      funext i; exact RingHom.map_mulVec _ _ _ i
    rw [e]
    exact (hst _).1 (latS_prV v _ Z hZ)
  have hw : Y.1 *ᵥ (κ.1 *ᵥ Z) ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := by
    apply (Km.y_lat _ _).2
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    exact hκZ
  have e2 : Y.1 *ᵥ (κ.1 *ᵥ Z) = fun i => inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((γ.1.1 *ᵥ x) i) := by
    rw [hZdef, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← hbc]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  rw [← e2]
  exact hw

theorem stab_lat (Tf : FormsTiedSym D u Ch chOf) (hLG : LatLocGlob) (hAL : AdLocLat) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range) :
    mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) := by
  apply le_antisymm (stab_lat_le Tf hLG hAL c γ hγ)
  have h2 := stab_lat_le Tf hLG hAL c γ⁻¹ (Subgroup.inv_mem _ hγ)
  have e : γ.1.1 * (γ⁻¹).1.1 = 1 := by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  calc clsCrd D u D.R.m le_rfl ((D.fm u).til c) = mulLat (γ.1.1 * (γ⁻¹).1.1) (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := by
        rw [e, mulLat_one]
    _ = mulLat γ.1.1 (mulLat (γ⁻¹).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c))) := by rw [mulLat_mulLat]
    _ ≤ mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := Submodule.map_mono h2

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

section Decomp

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

def TQ {m : ℕ} (b : Fin m → 𝓞 E) (s : E ⊗[F] R) : Prop :=
  ∃ r : Fin m → R, (∀ j, r j ∈ S₂) ∧ s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j

variable {R S₂}

theorem tq_zero {m : ℕ} (b : Fin m → 𝓞 E) : TQ (F := F) R S₂ b 0 :=
  ⟨0, fun _ => S₂.zero_mem, by simp⟩

theorem tq_add {m : ℕ} (b : Fin m → 𝓞 E) {x y : E ⊗[F] R} (hx : TQ R S₂ b x) (hy : TQ R S₂ b y) :
    TQ R S₂ b (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  exact ⟨r + r', fun j => S₂.add_mem (hr j) (hr' j), by
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem tq_neg {m : ℕ} (b : Fin m → 𝓞 E) {x : E ⊗[F] R} (hx : TQ R S₂ b x) : TQ R S₂ b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨-r, fun j => S₂.neg_mem (hr j), by simp [TensorProduct.tmul_neg]⟩

theorem tq_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] R)
    (h : ∀ i ∈ s, TQ R S₂ b (f i)) : TQ R S₂ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (TQ R S₂ b) (fun _ _ hx hy => tq_add b hx hy) (tq_zero b) h

theorem tq_tmul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (e : 𝓞 E) {y : R} (hy : y ∈ S₂) : TQ R S₂ b (algebraMap (𝓞 E) E e ⊗ₜ[F] y) := by
  have he : e ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 he
  refine ⟨fun j => c j • y, fun j => zsmul_mem hy (c j), ?_⟩
  rw [← hc, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  exact TensorProduct.smul_tmul _ _ _

theorem tq_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : E ⊗[F] R} (hx : TQ R S₂ b x) (hy : TQ R S₂ b y) : TQ R S₂ b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine tq_sum b _ _ fun j _ => tq_sum b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact tq_tmul b hb _ (S₂.mul_mem (hr j) (hr' k))

theorem tq_decomp {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) S₂) : TQ R S₂ b s := by
  unfold tensInt at hs
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, ⟨e, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact tq_tmul b hb e S₂.one_mem
    · have h1 := tq_tmul (F := F) b hb (1 : 𝓞 E) hy
      simpa using h1
  | zero => exact tq_zero b
  | one =>
    have h1 := tq_tmul (F := F) b hb (1 : 𝓞 E) (S₂.one_mem)
    simpa [Algebra.TensorProduct.one_def] using h1
  | add x y _ _ hx hy => exact tq_add b hx hy
  | neg x _ hx => exact tq_neg b hx
  | mul x y _ _ hx hy => exact tq_mul b hb hx hy

theorem tensInt_tmul_mem (e : 𝓞 E) {y : R} (hy : y ∈ S₂) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] y ∈ tensInt (F := F) R (intOE E) S₂ := by
  have h1 : algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : R) ∈ tensInt (F := F) R (intOE E) S₂ :=
    Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩)
  have h2 : (1 : E) ⊗ₜ[F] y ∈ tensInt (F := F) R (intOE E) S₂ :=
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have h3 := Subring.mul_mem _ h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3

theorem inclE_mem_tensInt (e : 𝓞 E) :
    inclE (F := F) R (algebraMap (𝓞 E) E e) ∈ tensInt (F := F) R (intOE E) S₂ :=
  tensInt_tmul_mem e S₂.one_mem

end Decomp

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

section Lat

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
variable (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem latS_decomp {m k : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (g : Fin k → (Fin n → E))
    (hg : Submodule.span (𝓞 E) (Set.range g) = Λ) (y : Fin n → E ⊗[F] R)
    (hy : y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ) :
    ∃ r : Fin k → Fin m → R, (∀ i j, r i j ∈ S₂) ∧ ∀ l, y l =
      ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r i j) * inclE (F := F) R (g i l) := by
  set S := tensInt (F := F) R (intOE E) S₂
  set G : Fin k → (Fin n → E ⊗[F] R) := fun i l => inclE (F := F) R (g i l)
  have hle : latS (F := F) R S Λ ≤ Submodule.span S (Set.range G) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg] at hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
    have : (fun l => inclE (F := F) R ((∑ i, a i • g i) l)) =
        ∑ i, (⟨inclE (F := F) R (algebraMap (𝓞 E) E (a i)), inclE_mem_tensInt (F := F) (R := R) (S₂ := S₂) (a i)⟩ : S) • G i := by
      funext l
      rw [Finset.sum_apply, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
    show (fun l => inclE (F := F) R ((∑ i, a i • g i) l)) ∈ Submodule.span S (Set.range G)
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (hle hy)
  choose r hr hsr using fun i => tq_decomp (F := F) (R := R) (S₂ := S₂) b hb (s i).2
  refine ⟨r, hr, fun l => ?_⟩
  rw [← hs, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, hsr i, Finset.sum_mul]

end Lat

section Glue

variable {F : Type} [Field F] [NumberField F]

def glueInt (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨r, Filter.Eventually.of_forall hr⟩

theorem glueInt_apply (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    glueInt r hr v = r v := rfl

theorem glueInt_mem (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) : glueInt r hr ∈ intAd F := by
  first
  | exact fun v => hr v
  | (intro v; simpa [glueInt_apply] using hr v)
  | (simp only [intAd]; intro v; exact hr v)
  | simp [intAd, glueInt_apply, hr]
  | (unfold intAd; guard_target =ₛ True)

end Glue

theorem adelic_local_lattice : AdLocLat := by
  intro F E _ _ _ _ _ n Λ hΛ x hx
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (Module.Finite.iff_fg.1 hΛ)
  choose r hr hxr using fun v : HeightOneSpectrum (𝓞 F) =>
    latS_decomp (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring b hb Λ g hg _ (hx v)
  set Rg : Fin k → Fin m → FiniteAdeleRing (𝓞 F) F :=
    fun i j => glueInt (fun v => r v i j) (fun v => hr v i j) with hRg
  have hx' : x = fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) *
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l) := by
    funext l
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    rw [map_sub, sub_eq_zero]
    refine (hxr v l).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rfl
  have hgΛ : ∀ i, g i ∈ Λ := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  have hmem : ∀ i j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := fun i j =>
    tensInt_tmul_mem (b j) (glueInt_mem _ _)
  have hsum : (fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) *
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l)) =
      ∑ i, ∑ j, (⟨_, hmem i j⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
        (fun l => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l)) := by
    funext l
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
  rw [hx', hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hgΛ i, rfl⟩)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def DualLoc (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls D.R.m) (z : Fin (D.R.N D.R.m) → D.host.E), z ∈ Ld D u D.R.m le_rfl c →
    ((bc (prV (E := D.host.E) (Tf.atT.eV v).1) ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (z a)) ∈
      latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
          (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb))

def FvStab (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
      (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
      (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)

theorem stabLF_of_fv (Tf : FormsTiedSym D u Ch chOf) (hF : FvStab Tf) : StabLF Tf :=
  stabLF_of Tf (fun c γ hγ => ⟨stab_lat Tf latLocGlob adelic_local_lattice c γ hγ, hF c γ hγ⟩)

theorem stabiliser_bijective_self_dual
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      FvStab Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_finite hSD (fun D u Ch chOf Tf => stabLF_of_fv Tf (hF D u Ch chOf Tf))

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem isLat_dlN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) (hM : Comp.IsLat M) :
    Comp.IsLat (Comp.dl (sigD D) (gramN D i hi) M) := by
  have hL : Submodule.IsLattice D.host.E M := ⟨Module.Finite.iff_fg.1 hM.1, hM.2⟩
  obtain ⟨d, hd, hle⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) M hL
  exact ⟨Module.Finite.iff_fg.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hd hle),
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) M hL⟩

variable {D : D7} {u : D.what₂.Word}

theorem clsCrd_finite (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u i hi c) := by
  let _ := D.host.cmStar
  rw [Module.Finite.iff_fg]
  exact (D.clsLat_lat u i c).fg.map _

theorem clsCrd_eq_glob {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    clsCrd D u i hi c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
  ext x
  constructor
  · intro hx
    exact (K.y_lat c _).1 (latS_of_mem _ x hx)
  · intro hx
    exact latLocGlob _ _ _ _ (clsCrd_finite i hi c) x ((K.y_lat c _).2 hx)

theorem ld_eq_glob {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    Ld D u i hi c = Formalism.UG.CS.globLat (K.y c).1 (Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := by
  have hLb : Comp.IsLat K.lev.Lb := ⟨K.lev.Lb_fin, K.lev.Lb_span⟩
  show Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c) = _
  rw [clsCrd_eq_glob K c, Comp.glob_dl (sigD D) (gramN D i hi) (isLat_dlN D i hi) hLb _ (K.y c).2]

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem bc_val' {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL (Fin n) A) :
    ((bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map φ := rfl

theorem bc_incl_w (w : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin n) E) :
    bc (inclE (F := F) (w.adicCompletion F)) γ = bc (prV (E := E) w) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ) := by
  apply Units.ext
  rw [bc_val', bc_val', bc_val', Matrix.map_map, ← RingHom.coe_comp, Formalism.L2.G.Cmp.prV_incl]

theorem locDual (w : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ Formalism.UG.CS.globLat g Λ) :
    ((bc (prV (E := E) w) g)⁻¹ : GL (Fin n) (E ⊗[F] w.adicCompletion F)).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) Λ := by
  have h1 : ((g⁻¹ : GL (Fin n) _) : Matrix _ _ _) *ᵥ (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := hz
  have h2 := latS_prV w _ _ h1
  have e : ((bc (prV (E := E) w) g)⁻¹ : GL (Fin n) (E ⊗[F] w.adicCompletion F)).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (z a)) =
      fun j => prV (E := E) w ((((g⁻¹ : GL (Fin n) _) : Matrix _ _ _) *ᵥ
        (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a))) j) := by
    rw [← map_inv, bc_val']
    funext j
    rw [RingHom.map_mulVec]
    have hc : (⇑(prV (E := E) w) ∘ fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (z a) := by
      funext a
      exact RingHom.congr_fun (Formalism.L2.G.Cmp.prV_incl (E := E) w) (z a)
    rw [hc]
  rw [e]
  exact h2

theorem conj_step (w : HeightOneSpectrum (𝓞 F)) (Y κ : GL (Fin n) (E ⊗[F] w.adicCompletion F)) (γ : GL (Fin n) E)
    (h : bc (inclE (F := F) (w.adicCompletion F)) γ = Y * κ * Y⁻¹) (x : Fin n → E) :
    (Y⁻¹).val *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      κ.val *ᵥ ((Y⁻¹).val *ᵥ fun a => inclE (F := F) (w.adicCompletion F) (x a)) := by
  have em : (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      (bc (inclE (F := F) (w.adicCompletion F)) γ).val *ᵥ
        (fun a => inclE (F := F) (w.adicCompletion F) (x a)) := by
    funext a
    rw [bc_val']
    exact RingHom.map_mulVec _ _ _ a
  rw [em, h, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

theorem conj_stepA (w : HeightOneSpectrum (𝓞 F)) (Y κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ = Y * κ * Y⁻¹) (x : Fin n → E) :
    ((bc (prV (E := E) w) Y)⁻¹).val *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      (bc (prV (E := E) w) κ).val *ᵥ (((bc (prV (E := E) w) Y)⁻¹).val *ᵥ fun a => inclE (F := F) (w.adicCompletion F) (x a)) :=
  conj_step w _ _ γ (by rw [bc_incl_w, h, map_mul, map_mul, map_inv]) x

end Gen

theorem dualLoc_of {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (w : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c) :
    ((bc (prV (E := D.host.E) w) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (w.adicCompletion D.host.F) (z a)) ∈
      latS (F := D.host.F) (w.adicCompletion D.host.F) (intV D.host.E w)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  rw [ld_eq_glob K c] at hz
  exact locDual w (K.y c).1 _ z hz

end Formalism.L2.GlobalTheoryTheory.Br
end
end
