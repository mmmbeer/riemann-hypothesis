import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
noncomputable section

namespace GlobalTheory.HomFixMat

theorem appLE_res_pull {X Y Z : Scheme.{0}} (φ : Y ⟶ Z) (h : X ⟶ Y) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ φ ⁻¹ᵁ U) (e₂ : W ≤ h ⁻¹ᵁ V) (e₃ : W ≤ (h ≫ φ) ⁻¹ᵁ U) (u : Γ(Z, U)) :
    (h.appLE V W e₂).hom ((Y.presheaf.map (homOfLE e₁).op).hom ((φ.app U).hom u)) =
      (X.presheaf.map (homOfLE e₃).op).hom (((h ≫ φ).app U).hom u) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_comp_appLE]

theorem appLE_restrict {X Y : Scheme.{0}} (h : X ⟶ Y) (V V' : Y.Opens) (W W' : X.Opens) (eV : V' ≤ V)
    (eW : W' ≤ W) (e : W ≤ h ⁻¹ᵁ V) (e' : W' ≤ h ⁻¹ᵁ V') (x : Γ(Y, V)) :
    (X.presheaf.map (homOfLE eW).op).hom ((h.appLE V W e).hom x) =
      (h.appLE V' W' e').hom ((Y.presheaf.map (homOfLE eV).op).hom x) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem pullSec_exists : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ)
    (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι,
      s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q)
        (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  intro X Y Z L φ h a s
  refine ⟨⟨fun q => (h.appLE _ _ (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q), ?_⟩, fun q => rfl⟩
  intro (q : Fin 1 → L.ι) (q' : Fin 1 → L.ι)
  have e0 : LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q' ≤
      h ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q') :=
    fun x hx => ⟨GlobalTheory.HomFixMat.wchart_comp_le L h φ q hx.1, GlobalTheory.HomFixMat.wchart_comp_le L h φ q' hx.2⟩
  refine (appLE_restrict h _ _ _ _ inf_le_left inf_le_left _ e0 _).trans ?_
  refine (congrArg _ (s.compat q q')).trans ?_
  refine (map_mul _ _ _).trans ?_
  congr 1
  · have hg : ((powPull L (h ≫ φ) a).g q q') =
        Units.map (h.appLE _ _ e0).hom.toMonoidHom ((powPull L φ a).g q q') := by
      show (∏ k : Fin 1, _) = Units.map _ (∏ k : Fin 1, _)
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_zpow]
      congr 1
      ext
      exact (appLE_res_pull φ h (L.U (q 0) ⊓ L.U (q' 0))
        (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q')
        (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q') _ e0 _
        (L.g (q 0) (q' 0) : Γ(Z, L.U (q 0) ⊓ L.U (q' 0)))).symm
    rw [hg]
    rfl
  · exact (appLE_restrict h _ _ _ _ inf_le_right inf_le_right _ e0 _).symm

end GlobalTheory.HomFixMat
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ) (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι, s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q) (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  first | (exact @GlobalTheory.HomFixMat.pullSec_exists) | (exact GlobalTheory.HomFixMat.pullSec_exists) | (intros; apply GlobalTheory.HomFixMat.pullSec_exists  <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.QuotSec

variable {X : Scheme.{0}}

abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (s : Γ(X, U)) :
    rs h' (rs h s) = rs (h'.trans h) s := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem coe_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = rs h (u : Γ(X, U)) := rfl

theorem rs_coe_inv {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    rs h ((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (((res h u)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := by
  rw [← map_inv]; rfl

theorem res_g_self (L : LB X) (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i ⊓ L.U i) :
    res h (L.g i i) = 1 := by
  apply Units.ext
  rw [coe_res, ← rs_rs (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (h.trans inf_le_left), ← coe_res,
    hL.g_self]
  simp

def GenRel (P Q : LB X) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Prop :=
  ∀ p₁ q p₁' q', res (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q) (a p₁ q) =
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ P.U p₁') (P.g p₁ p₁') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ Q.U q ⊓ Q.U q') (Q.g q q'))⁻¹ *
      res (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁' ⊓ Q.U q') (a p₁' q')

theorem genRel_of_isGen (P Q : LB X) (α : LB.Gen (LB.div P Q)) (hα : α.IsGen) :
    GenRel P Q (fun p₁ q => α.s (p₁, q)) :=
  fun p₁ q p₁' q' => hα (p₁, q) (p₁', q')

theorem quot_compat (P Q : LB X) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) (ha : GenRel P Q a)
    (σ : LB.Sec P) (q : Q.ι) (p₁ p₁' : P.ι) :
    rs (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ Q.U q)
      ((((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁)) =
    rs (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁' ⊓ Q.U q)
      ((((a p₁' q)⁻¹ : Γ(X, P.U p₁' ⊓ Q.U q)ˣ) : Γ(X, P.U p₁' ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁' ⊓ Q.U q ≤ P.U p₁') (σ.f p₁')) := by
  have e := ha p₁ q p₁' q
  rw [res_g_self Q hQ q, inv_one, _root_.mul_one] at e
  have hσ := congrArg (rs (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ P.U p₁')) (σ.compat p₁ p₁')
  simp only [map_mul, rs_rs] at hσ ⊢
  rw [rs_coe_inv, rs_coe_inv, e, hσ, ← coe_res, mul_inv_rev, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem exists_quot_sec (P Q : LB X) (hP : P.IsLB) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ)
    (ha : GenRel P Q a) (σ : LB.Sec P) :
    ∃ s : LB.Sec Q, ∀ p₁ q, rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) =
      ((a p₁ q : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) (s.f q) := by
  have hcov : ∀ (V : X.Opens), V ≤ ⨆ p₁, P.U p₁ ⊓ V := fun V x hx => by
    have : x ∈ (⨆ p₁, P.U p₁ : X.Opens) := by rw [hP.cover]; trivial
    obtain ⟨p₁, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p₁, hp, hx⟩
  have hglue : ∀ q, ∃ t : Γ(X, Q.U q), ∀ p₁, rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) t =
      (((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) := fun q =>
    (X.sheaf.existsUnique_gluing' (fun p₁ => P.U p₁ ⊓ Q.U q) (Q.U q) (fun _ => homOfLE inf_le_right)
      (hcov (Q.U q)) _ (fun p₁ p₁' => quot_compat P Q hQ a ha σ q p₁ p₁')).exists
  choose t ht using hglue
  refine ⟨⟨t, fun q q' => ?_⟩, fun p₁ q => ?_⟩
  · refine X.sheaf.eq_of_locally_eq' (fun p₁ => P.U p₁ ⊓ (Q.U q ⊓ Q.U q')) (Q.U q ⊓ Q.U q')
      (fun _ => homOfLE inf_le_right) (hcov _) _ _ (fun p₁ => ?_)
    change rs _ (rs _ (t q)) = rs _ ((Q.g q q' : Γ(X, Q.U q ⊓ Q.U q')) * rs _ (t q'))
    simp only [map_mul, rs_rs]
    rw [      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q)
        (le_inf inf_le_left (inf_le_right.trans inf_le_left) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q),
      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q' ≤ Q.U q')
        (le_inf inf_le_left (inf_le_right.trans inf_le_right) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q'),
      ht, ht]
    have e := congrArg (fun u : Γ(X, (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q'))ˣ =>
      rs (le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right)) :
          P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q')) (u⁻¹ : Γ(X, _)ˣ)) (ha p₁ q p₁ q')
    rw [res_g_self P hP p₁, _root_.one_mul, mul_inv_rev, inv_inv] at e
    simp only [map_mul, rs_rs, rs_coe_inv, Units.val_mul, ← coe_res] at e ⊢
    simp only [map_inv, ReciprocityTheory.ChartRestriction.G.DVR.res_res'] at e ⊢
    rw [e]
    ring
  · rw [ht, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]

end GlobalTheory.QuotSec

namespace GlobalTheory.HomFixMat

theorem divSec_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  intro X Z₁ Z₂ L M f g a α hα hL hM σ
  obtain ⟨s, hs⟩ := GlobalTheory.QuotSec.exists_quot_sec (powPull M g a) (powPull L f a)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB M hM _ _) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _)
    (fun p₁ q => α.s (p₁, q)) (GlobalTheory.QuotSec.genRel_of_isGen _ _ α hα) σ
  exact ⟨s, fun p => hs p.1 p.2⟩

end GlobalTheory.HomFixMat
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_pullback_section_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  atlas_forward_decl GlobalTheory.HomFixMat.divSec_exists
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.PowIsoRe

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (e1 : W ≤ V) (e2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res e1 (res e2 x) = res (e1.trans e2) x := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem preimage_comp_le {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) : h ⁻¹ᵁ V ≤ (h ≫ φ) ⁻¹ᵁ W := by
  intro x hx
  exact e hx

theorem pullU_res_pullU {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) (u : Γ(Z, W)ˣ) :
    pullU h V (res e (pullU φ W u)) = res (preimage_comp_le h φ e) (pullU (h ≫ φ) W u) := by
  have key : φ.app W ≫ Y.presheaf.map (homOfLE e).op ≫ h.app V =
      (h ≫ φ).app W ≫ X.presheaf.map (homOfLE (preimage_comp_le h φ e)).op := by
    rw [Scheme.Hom.naturality, Scheme.Hom.comp_app]
    rfl
  ext1
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem res_pull_comp {X Y Z : Scheme.{0}} (h : X ⟶ Y) (m : Y ⟶ Z) {W : Z.Opens} {V1 : Y.Opens}
    {V2 V3 T : X.Opens} (u : Γ(Z, W)ˣ) (e1 : V1 ≤ m ⁻¹ᵁ W) (e2 : V2 ≤ h ⁻¹ᵁ V1) (e3 : T ≤ V2)
    (e4 : V3 ≤ (h ≫ m) ⁻¹ᵁ W) (e5 : T ≤ V3) :
    res e3 (res e2 (pullU h V1 (res e1 (pullU m W u)))) = res e5 (res e4 (pullU (h ≫ m) W u)) := by
  rw [pullU_res_pullU, res_res, res_res, res_res]

theorem res_res' {X : Scheme.{0}} {U V V' W : X.Opens} (x : Γ(X, U)ˣ) (e1 : W ≤ V) (e2 : V ≤ U)
    (e3 : W ≤ V') (e4 : V' ≤ U) : res e1 (res e2 x) = res e3 (res e4 x) := by
  rw [res_res, res_res]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem wchart_le_M {X Y Z : Scheme.{0}} (M : LB Z) (h : X ⟶ Y) (m : Y ⟶ Z) (j : Fin 1 → M.ι) :
    LB.wchart M (fun _ : Fin 1 => h ≫ m) j ≤
      LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => j 0) := by
  intro x hx
  have hx0 := Set.mem_iInter.1 hx 0
  refine Set.mem_iInter.2 fun _ => ?_
  refine Set.mem_iInter.2 fun _ => ?_
  simpa using hx0

theorem wchart_le_L {X Z : Scheme.{0}} (L : LB Z) (f : X ⟶ Z) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f) j ≤ LB.wchart L (fun _ : PUnit => f) (fun _ => j 0) := by
  intro x hx
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem exists_powIso {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂)
    (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  dsimp only [LB.Gen.IsGen, LB.div, LB.LinComb, LB.pull, powPull] at w hw ⊢
  have hle : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      LB.wchart M (fun _ : Fin 1 => h ≫ m) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤
        LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => p.1 0) ⊓
          LB.wchart L (fun _ : PUnit => f) (fun _ => p.2 0) := fun p =>
    inf_le_inf (wchart_le_M M h m p.1) (wchart_le_L L f p.2)
  dsimp only [LB.pull, LB.LinComb] at hle
  refine ⟨⟨fun p => (res (hle p) (w.s (fun _ _ => p.1 0, fun _ => p.2 0))) ^ k⟩, ?_⟩
  dsimp only
  intro p p'
  have e := congrArg (fun x => (res (inf_le_inf (hle p) (hle p')) x) ^ k)
    (hw (fun _ _ => p.1 0, fun _ => p.2 0) (fun _ _ => p'.1 0, fun _ => p'.2 0))
  simp only [map_mul, map_inv, map_pow, map_zpow, map_prod, res_res, pullU_res_pullU,
    Fin.prod_univ_one, Fintype.prod_unique, Fin.default_eq_zero, zpow_one, zpow_natCast, mul_pow, inv_pow] at e ⊢
  convert e using 5
  · exact (res_pull_comp h m (W := M.U (p.1 0) ⊓ M.U (p'.1 0))
      (V1 := LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p'.1 0))
      (M.g (p.1 0) (p'.1 0)) _ _ _ _ _).symm
  · rfl
  · exact res_res' (U := f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (p'.2 0))) (pullU f _ (L.g (p.2 0) (p'.2 0))) _ _ _ _

end GlobalTheory.PowIsoRe
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts : ∀ {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂) (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))), w.IsGen → ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  first | (exact @GlobalTheory.PowIsoRe.exists_powIso) | (exact GlobalTheory.PowIsoRe.exists_powIso) | (intros; apply GlobalTheory.PowIsoRe.exists_powIso  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section
namespace GlobalTheory.RigNorm
open Opposite TopologicalSpace

theorem glue_units {T : Scheme.{0}} {I : Type} (W : I → T.Opens) (hW : ∀ x : T, ∃ i, x ∈ W i)
    (u : ∀ i, Γ(T, W i)ˣ)
    (hu : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res (inf_le_right : W i ⊓ W j ≤ W j) (u j)) :
    ∃ v : Γ(T, ⊤)ˣ, ∀ i, res (le_top : W i ≤ ⊤) v = u i := by
  have hc : (⊤ : T.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := hW x
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  have glue : ∀ sf : ∀ i, Γ(T, W i), (∀ i j, (T.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (sf i) = (T.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (sf j)) →
      ∃ s : Γ(T, ⊤), ∀ i, (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom s = sf i := by
    intro sf hsf
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf W ⊤ (fun i => homOfLE le_top) hc sf hsf
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := glue (fun i => (u i).val) (fun i j => congrArg Units.val (hu i j))
  obtain ⟨s', hs'⟩ := glue (fun i => ((u i)⁻¹).val) (fun i j => by
    have := congrArg (fun x => (x⁻¹).val) (hu i j)
    simpa [res, map_inv] using this)
  have h1 : s * s' = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' T.sheaf W ⊤ (fun i => homOfLE le_top) hc
    intro i
    have := hs i; have := hs' i
    change (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom (s * s') = (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs i, hs' i, Units.mul_inv]
  refine ⟨⟨s, s', h1, by rw [mul_comm, h1]⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = (X.presheaf.map (homOfLE h).op).hom u.val := rfl

theorem val_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    (pullU f U u).val = (f.app U).hom u.val := rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (u : Γ(X, U)ˣ) :
    res h₁ (res h₂ u) = res (h₁.trans h₂) u := by
  apply Units.ext
  simp only [val_res]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem appLE_res {X Y : Scheme.{0}} (h : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (hU : U ≤ U') (x : Γ(Y, U')) :
    (h.appLE U V e).hom ((Y.presheaf.map (homOfLE hU).op).hom x) =
      (h.appLE U' V (e.trans fun _ hy => hU hy)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem res_appLE {X Y : Scheme.{0}} (h : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (hV : V' ≤ V) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE hV).op).hom ((h.appLE U V e).hom x) = (h.appLE U V' (hV.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_app {X Y Z : Scheme.{0}} (h : X ⟶ Y) (k : Y ⟶ Z) {U : Z.Opens} {W : X.Opens}
    (e : W ≤ h ⁻¹ᵁ (k ⁻¹ᵁ U)) (x : Γ(Z, U)) :
    (h.appLE (k ⁻¹ᵁ U) W e).hom ((k.app U).hom x) = ((h ≫ k).appLE U W (e.trans fun _ hy => hy)).hom x := by
  rw [Scheme.Hom.comp_appLE]; rfl

theorem appLE_congr' {X Y : Scheme.{0}} {h h' : X ⟶ Y} (H : h = h') {U : Y.Opens} {V : X.Opens}
    (e : V ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (h.appLE U V e).hom x = (h'.appLE U V (H ▸ e)).hom x := by
  subst H; rfl

theorem id_appLE' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U V e).hom x = (X.presheaf.map (homOfLE e).op).hom x := by
  rfl

theorem alg {R : Type*} [CommRing R] (Bp Bq Ap Aq ap aq cM cL : R) (k : ℕ) (hB : Bp = cM * Bq)
    (hA : Ap = cL * Aq) (ha : ap * cL ^ k = cM ^ k * aq) : Bp ^ k * (aq * Aq ^ k) = Bq ^ k * (ap * Ap ^ k) := by
  subst hB hA; linear_combination (-(Bq ^ k * Aq ^ k)) * ha

theorem mul_inv_mul_cancel_comm {G : Type*} [CommGroup G] (m l a l' : G) (h : l = l') : m * l⁻¹ * a * l' = m * a := by
  subst h; rw [mul_right_comm, inv_mul_cancel_right]

theorem map_map' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom x) =
      (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem pre_mono {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (h : U ≤ U') : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U' :=
  fun _ hx => h hx

theorem pre_inf {X Y : Scheme.{0}} (f : X ⟶ Y) (U U' : Y.Opens) : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ (U ⊓ U') :=
  fun _ hx => hx

theorem pull_inf_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : L.ι) :
    LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ φ ⁻¹ᵁ (L.U i ⊓ L.U j) :=
  fun _ hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩

theorem pow_inf_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) :=
  fun _ hy => ⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩

theorem pull_g_val {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : PUnit → L.ι) :
    ((L.pull φ).g i j).val = (Y.presheaf.map (homOfLE (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit,
      Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (L.pull φ).U i ⊓ (L.pull φ).U j ≤
        φ ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)))).op).hom
      ((φ.app _).hom (L.g (i PUnit.unit) (j PUnit.unit)).val) :=
by
  show (∏ m : PUnit, (res (le_inf (inf_le_left.trans (LB.wchart_le L _ i m)) (inf_le_right.trans (LB.wchart_le L _ j m)))
    (pullU φ (L.U (i m) ⊓ L.U (j m)) (L.g (i m) (j m)))) ^ (1 : ℤ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem powPull_g_val {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((powPull L φ (k : ℤ)).g i j).val = ((Y.presheaf.map (homOfLE (fun y hy => ⟨Set.mem_iInter.1 hy.1 0,
      Set.mem_iInter.1 hy.2 0⟩ : (powPull L φ (k : ℤ)).U i ⊓ (powPull L φ (k : ℤ)).U j ≤
        φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom ((φ.app _).hom (L.g (i 0) (j 0)).val)) ^ k :=
by
  show (∏ m : Fin 1, (res (le_inf (inf_le_left.trans (LB.wchart_le L _ i m)) (inf_le_right.trans (LB.wchart_le L _ j m)))
    (pullU φ (L.U (i m) ⊓ L.U (j m)) (L.g (i m) (j m)))) ^ (k : ℤ)).val = _
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

theorem pull_rel {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (e : LB.Gen (L.pull φ)) (he : e.IsGen)
    (s : ∀ i : L.ι, Γ(Y, LB.wchart L (fun _ : PUnit => φ) (fun _ => i))ˣ) (hs : s = fun i => e.s (fun _ => i))
    (i j : L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓
      LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ LB.wchart L (fun _ : PUnit => φ) (fun _ => i))).op).hom (s i).val =
    (Y.presheaf.map (homOfLE (pull_inf_le L φ i j)).op).hom ((φ.app _).hom (L.g i j).val) *
    (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓
      LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ LB.wchart L (fun _ : PUnit => φ) (fun _ => j))).op).hom (s j).val := by
  subst hs
  exact (congrArg Units.val (he (fun _ => i) (fun _ => j))).trans
    (congrArg (· * _) (pull_g_val L φ (fun _ => i) (fun _ => j)))

theorem div_rel {X Y₁ Y₂ : Scheme.{0}} (L : LB Y₁) (M : LB Y₂) (f : X ⟶ Y₁) (g : X ⟶ Y₂) (k : ℕ)
    (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))) (hα : α₀.IsGen)
    (s : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2)ˣ)
    (hs : s = fun p => α₀.s p) (p q : (Fin 1 → M.ι) × (Fin 1 → L.ι)) :
    (X.presheaf.map (homOfLE (inf_le_left : (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s p).val *
    ((X.presheaf.map (homOfLE ((inf_le_inf inf_le_right inf_le_right).trans (pow_inf_le L f p.2 q.2) :
      (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (q.2 0)))).op).hom ((f.app _).hom (L.g (p.2 0) (q.2 0)).val)) ^ k =
    ((X.presheaf.map (homOfLE ((inf_le_inf inf_le_left inf_le_left).trans (pow_inf_le M g p.1 q.1) :
      (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        g ⁻¹ᵁ (M.U (p.1 0) ⊓ M.U (q.1 0)))).op).hom ((g.app _).hom (M.g (p.1 0) (q.1 0)).val)) ^ k *
    (X.presheaf.map (homOfLE (inf_le_right : (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2)).op).hom (s q).val := by
  subst hs
  have hhL : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (powPull L f (k : ℤ)).U p.2 ⊓ (powPull L f (k : ℤ)).U q.2 :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hhM : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (powPull M g (k : ℤ)).U p.1 ⊓ (powPull M g (k : ℤ)).U q.1 :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h2 : res (inf_le_left : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (α₀.s p) *
        res hhL ((powPull L f (k : ℤ)).g p.2 q.2) =
      res hhM ((powPull M g (k : ℤ)).g p.1 q.1) *
        res (inf_le_right : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q) (α₀.s q) := by
    rw [hα p q]
    exact mul_inv_mul_cancel_comm _ _ _ _ rfl
  have eL := ((congrArg (X.presheaf.map (homOfLE hhL).op).hom (powPull_g_val L f k p.2 q.2)).trans
    (map_pow _ _ _)).trans (congrArg (· ^ k) (map_map' _ _ _))
  have eM := ((congrArg (X.presheaf.map (homOfLE hhM).op).hom (powPull_g_val M g k p.1 q.1)).trans
    (map_pow _ _ _)).trans (congrArg (· ^ k) (map_map' _ _ _))
  have h3 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul, val_res hhL, val_res hhM, eL, eM] at h3
  exact h3

theorem exists_rescaled_gen : ∀ {T X Z₀ Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (eL : Z₀ ⟶ Z₁) (eM : Z₀ ⟶ Z₂) (t : T ⟶ Z₀) (z : T ⟶ X) (π : X ⟶ T) (k : ℕ) (eA : LB.Gen (L.pull eL)) (eB : LB.Gen (M.pull eM)) (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → α₀.IsGen → z ≫ π = 𝟙 T → z ≫ f = t ≫ eL → z ≫ g = t ≫ eM → ∃ α : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen ∧ ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (z.appLE ((LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_left)).hom (α.s p).val * ((t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k = ((t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro T X Z₀ Z₁ Z₂ L M f g eL eM t z π k eA eB α₀ hL hM hA hB hα hzπ hzf hzg
  obtain ⟨sA, hsA⟩ : ∃ s : ∀ i : L.ι, Γ(Z₀, LB.wchart L (fun _ : PUnit => eL) (fun _ => i))ˣ, s = fun i => eA.s (fun _ => i) := ⟨_, rfl⟩
  obtain ⟨sB, hsB⟩ : ∃ s : ∀ i : M.ι, Γ(Z₀, LB.wchart M (fun _ : PUnit => eM) (fun _ => i))ˣ, s = fun i => eB.s (fun _ => i) := ⟨_, rfl⟩
  obtain ⟨sα, hsα⟩ : ∃ s : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), Γ(X, (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2))ˣ, s = fun p => α₀.s p :=
    ⟨_, rfl⟩
  let Wo : (Fin 1 → M.ι) × (Fin 1 → L.ι) → T.Opens := fun p =>
    z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)
  have hDU : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p = (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) := fun _ => rfl
  let a : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (z.appLE (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) (Wo p) ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU p).le))).hom.toMonoidHom (sα p)
  let A : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (Wo p) (inf_le_left.trans inf_le_right)).hom.toMonoidHom (sA (p.2 0))
  let B : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (Wo p) inf_le_right).hom.toMonoidHom (sB (p.1 0))
  let u : ∀ p, Γ(T, Wo p)ˣ := fun p => B p ^ k * (a p * A p ^ k)⁻¹
  have hcov : ∀ x : T, ∃ p, x ∈ Wo p := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show eL (t x) ∈ ⨆ i, L.U i by rw [hL.cover]; trivial)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (show eM (t x) ∈ ⨆ j, M.U j by rw [hM.cover]; trivial)
    have hf : f (z x) = eL (t x) := by rw [← Scheme.Hom.comp_apply, hzf, Scheme.Hom.comp_apply]
    have hg : g (z x) = eM (t x) := by rw [← Scheme.Hom.comp_apply, hzg, Scheme.Hom.comp_apply]
    refine ⟨(fun _ => j, fun _ => i), ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
    · exact Set.mem_iInter.2 fun _ => show g (z x) ∈ M.U j by rw [hg]; exact hj
    · exact Set.mem_iInter.2 fun _ => show f (z x) ∈ L.U i by rw [hf]; exact hi
    · exact Set.mem_iInter.2 fun _ => hi
    · exact Set.mem_iInter.2 fun _ => hj
  have hcomp : ∀ p q, res (inf_le_left : Wo p ⊓ Wo q ≤ Wo p) (u p) =
      res (inf_le_right : Wo p ⊓ Wo q ≤ Wo q) (u q) := by
    intro p q
    have eV : Wo p ⊓ Wo q ≤ z ⁻¹ᵁ ((LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓ (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2)) := (inf_le_inf ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU p).le))
      ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU q).le))).trans (pre_inf z _ _)
    have eVA : Wo p ⊓ Wo q ≤ t ⁻¹ᵁ (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ LB.wchart L (fun _ : PUnit => eL) (fun _ => q.2 0)) := (inf_le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right)).trans (pre_inf t _ _)
    have eVB : Wo p ⊓ Wo q ≤ t ⁻¹ᵁ (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit => eM) (fun _ => q.1 0)) := (inf_le_inf inf_le_right inf_le_right).trans (pre_inf t _ _)
    have ra := congrArg (z.appLE _ _ eV).hom (div_rel L M f g k α₀ hα sα hsα p q)
    have rA := congrArg (t.appLE _ _ eVA).hom (pull_rel L eL eA hA sA hsA (p.2 0) (q.2 0))
    have rB := congrArg (t.appLE _ _ eVB).hom (pull_rel M eM eB hB sB hsB (p.1 0) (q.1 0))
    simp only [map_mul, map_pow, appLE_res, appLE_app, appLE_congr' hzf, appLE_congr' hzg] at ra rA rB
    simp only [u, map_mul, map_pow, map_inv]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_res, a, A, B, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, res_appLE]
    exact alg _ _ _ _ _ _ _ _ k rB rA ra
  obtain ⟨v, hv⟩ := glue_units Wo hcov u hcomp
  refine ⟨⟨fun p => res (show (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ≤ π ⁻¹ᵁ ⊤ from fun _ _ => trivial) (pullU π ⊤ v) * α₀.s p⟩, ?_, ?_⟩
  · intro p q
    dsimp only
    simp only [map_mul, res_res, hα p q]
    exact mul_left_comm _ _ _
  · intro p
    have key : ((z ≫ π).appLE ⊤ (Wo p) (fun _ _ => trivial)).hom v.val = (u p).val := by
      have h1 := appLE_congr' hzπ (U := ⊤) (V := Wo p) (fun _ _ => trivial) v.val
      rw [id_appLE'] at h1
      exact h1.trans (congrArg Units.val (hv p))
    have hu := congrArg Units.val (inv_mul_cancel_right (B p ^ k) (a p * A p ^ k))
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hu
    dsimp only
    simp only [Units.val_mul, val_res, val_pullU, map_mul, appLE_res, appLE_app]
    rw [key, _root_.mul_assoc]
    subst hsA hsB hsα
    exact hu

end GlobalTheory.RigNorm
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator : ∀ {T X Z₀ Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (eL : Z₀ ⟶ Z₁) (eM : Z₀ ⟶ Z₂) (t : T ⟶ Z₀) (z : T ⟶ X) (π : X ⟶ T) (k : ℕ) (eA : LB.Gen (L.pull eL)) (eB : LB.Gen (M.pull eM)) (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → α₀.IsGen → z ≫ π = 𝟙 T → z ≫ f = t ≫ eL → z ≫ g = t ≫ eM → ∃ α : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen ∧ ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (z.appLE ((LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_left)).hom (α.s p).val * ((t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k = ((t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  first | (exact @GlobalTheory.RigNorm.exists_rescaled_gen) | (exact GlobalTheory.RigNorm.exists_rescaled_gen) | (intros; apply GlobalTheory.RigNorm.exists_rescaled_gen  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
noncomputable section

namespace GlobalTheory.HomFixMat.SpanPull

theorem appLE_appLE_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens)
    (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = ((f ≫ g).appLE U W e).hom x :=
  congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem id_appLE_self {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom x = x := by
  show (X.presheaf.map (𝟙 (Opposite.op U))).hom ((Scheme.Hom.app (𝟙 X) U).hom x) = x
  simp
  rfl

theorem appLE_appLE_eq {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (eh : W ≤ h ⁻¹ᵁ U)
    (x : Γ(Z, U)) : (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (h.appLE U W eh).hom x := by
  subst hfg
  exact appLE_appLE_apply f g U V W e₁ e₂ eh x

end GlobalTheory.HomFixMat.SpanPull

namespace GlobalTheory.HomFixMat

open GlobalTheory.HomFixMat.SpanPull in

theorem exists_coeff_of_isBCBasis : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left), IsPullback φA' A'.hom A.hom t → ∀ (ψA : A'.left ⟶ (topS Rg ⊗ A).left), ψA ≫ (snd (topS Rg) A).left = φA' → ∀ s : LB.Sec (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ)), ∃ c : Fin mA → Γ(Sp R, ⊤), ∀ q : Fin 1 → L.ι, s.f q = ∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (fun _ _ => trivial)).hom (c i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q) (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := by
  intro Rg _ A _ L k mA bA hB R _ t A' φA' hpb ψA hψ s
  let t' : Sp R ⟶ (topS Rg).left := t ≫ (Sp Rg).topIso.inv
  have hbt : (baseAt t').hom = t := by
    show (t ≫ (Sp Rg).topIso.inv) ≫ ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _) = t
    rw [Category.comp_id, ← Scheme.topIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have eH : ∀ _k : Fin 1, (homAt t' ▷ A).left ≫ (snd (topS Rg) A).left = (snd (baseAt t') A).left :=
    fun _ => by rw [← Over.comp_left, whiskerRight_snd]
  let b' : Fin mA → LB.Sec (LPow A L (k : ℤ) (baseAt t')) := fun i =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L _ _ _ (homAt t' ▷ A).left eH (bA i)
  have hb' : ∀ i, IsPullSec A L (k : ℤ) (homAt t' ▷ A) (whiskerRight_snd (homAt t') A) (bA i) (b' i) :=
    fun i j => rfl
  have hspan := (hB R t' b' hb').2
  have hY : IsPullback (snd (baseAt t') A).left (fst (baseAt t') A).left A.hom t := by
    rw [← hbt]
    exact (IsPullback.of_hasPullback _ _).flip
  let e := IsPullback.isoIsPullback _ _ hY hpb
  have e1 : e.hom ≫ φA' = (snd (baseAt t') A).left := IsPullback.isoIsPullback_hom_fst _ _ hY hpb
  have e2 : e.inv ≫ (snd (baseAt t') A).left = φA' := IsPullback.isoIsPullback_inv_fst _ _ hY hpb
  have e3 : e.inv ≫ (fst (baseAt t') A).left = A'.hom := IsPullback.isoIsPullback_inv_snd _ _ hY hpb
  have hTop : IsPullback (snd (topS Rg) A).left (fst (topS Rg) A).left A.hom (topS Rg).hom :=
    (IsPullback.of_hasPullback _ _).flip
  have e4 : e.inv ≫ (homAt t' ▷ A).left = ψA := by
    have hs : (e.inv ≫ (homAt t' ▷ A).left) ≫ (snd (topS Rg) A).left = ψA ≫ (snd (topS Rg) A).left := by
      rw [Category.assoc, eH 0, e2, hψ]
    refine hTop.hom_ext hs ?_
    haveI : Mono (topS Rg).hom := by dsimp [topS]; infer_instance
    rw [← cancel_mono (topS Rg).hom]
    simp only [Category.assoc, ← hTop.w]
    simp only [← Category.assoc]
    rw [hs]
  have eS : ∀ _k : Fin 1, e.hom ≫ (ψA ≫ (snd (topS Rg) A).left) = (snd (baseAt t') A).left :=
    fun _ => by rw [hψ, e1]
  let s'' : LB.Sec (LPow A L (k : ℤ) (baseAt t')) := ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L _ _ _ e.hom eS s
  have hmem : SecM.ofSec A s'' ∈ Submodule.span Γ((baseAt t').left, ⊤)
      (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t'))) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  refine ⟨c, fun q => ?_⟩
  have hq : s''.f q = (∑ i, liftHom A ((LPow A L (k : ℤ) (baseAt t')).U q) (c i) * (b' i).f q :
      Γ((baseAt t' ⊗ A).left, LB.wchart L (fun _ : Fin 1 => (snd (baseAt t') A).left) q)) := by
    have h0 := congrArg (fun x : SecM A L (k : ℤ) (baseAt t') =>
      (x : ∀ j, Γ((baseAt t' ⊗ A).left, (LPow A L (k : ℤ) (baseAt t')).U j)) q) hc
    rw [Submodule.coe_sum] at h0
    refine Eq.trans h0.symm ?_
    erw [Finset.sum_apply]
    rfl
  have hle : LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q ≤
      e.inv ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd (baseAt t') A).left) q :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.wchart_pull_le' L (fun _ : Fin 1 => (snd (baseAt t') A).left)
      (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) (fun _ => (k : ℤ)) e.inv (fun _ => by rw [e2, hψ]) q
  have h1 : (e.inv.appLE _ _ hle).hom (s''.f q) = s.f q := by
    refine (appLE_appLE_eq (f := e.inv) (g := e.hom) e.inv_hom_id
      (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q)
      (LB.wchart L (fun _ : Fin 1 => (snd (baseAt t') A).left) q)
      (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) _ hle (fun _ h => h) (s.f q)).trans ?_
    exact id_appLE_self _ _ _
  have h2 : ∀ r : Γ((baseAt t').left, ⊤),
      (e.inv.appLE _ _ hle).hom (liftHom A ((LPow A L (k : ℤ) (baseAt t')).U q) r) =
        (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q)
          (fun _ _ => trivial)).hom r := fun r =>
    appLE_appLE_eq (f := e.inv) (g := (fst (baseAt t') A).left) e3 ⊤ _ _ (fun _ _ => trivial) hle _ r
  have h3 : ∀ i, (e.inv.appLE _ _ hle).hom ((b' i).f q) =
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q)
        (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := fun i =>
    appLE_appLE_eq (f := e.inv) (g := (homAt t' ▷ A).left) e4 _ _ _ _ hle _ ((bA i).f q)
  rw [← h1, hq]
  erw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [map_mul, h2, h3]

end GlobalTheory.HomFixMat
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left), IsPullback φA' A'.hom A.hom t → ∀ (ψA : A'.left ⟶ (topS Rg ⊗ A).left), ψA ≫ (snd (topS Rg) A).left = φA' → ∀ s : LB.Sec (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ)), ∃ c : Fin mA → Γ(Sp R, ⊤), ∀ q : Fin 1 → L.ι, s.f q = ∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (fun _ _ => trivial)).hom (c i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q) (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (exact GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (intros; apply GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMatEx

theorem liftTop (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg)
    (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left) (hpb : IsPullback φA' A'.hom A.hom t) :
    ∃ ψ : A'.left ⟶ (topS Rg ⊗ A).left, ψ ≫ (snd (topS Rg) A).left = φA' := by
  let a0 : A'.left ⟶ (⊤ : (Sp Rg).Opens).toScheme :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι (A'.hom ≫ t) (by simp)
  let X : Over (Sp Rg) := Over.mk (A'.hom ≫ t)
  let a : X ⟶ topS Rg := Over.homMk a0 (by simp only [a0, X, topS, overRes, baseOver, Over.mk_hom, Category.comp_id]; exact IsOpenImmersion.lift_fac _ _ _)
  let b : X ⟶ A := Over.homMk φA' hpb.w
  refine ⟨(lift a b).left, ?_⟩
  rw [← Over.comp_left, lift_snd]
  rfl

theorem zero_comp (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (R : Type) [CommRing R]
    (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (h : IsGrpPullback A' A t φA') :
    zeroPt A' ≫ φA' = t ≫ eSec A := by
  let T : Over (Sp R) := 𝟙_ (Over (Sp R))
  let u : Over.mk (T.hom ≫ t) ⟶ A := Over.homMk ((1 : T ⟶ A').left ≫ φA') (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have hu1 : u = 1 := mul_eq_left.1 hu
  have e := congrArg (fun x => Over.Hom.left x) hu1
  simp only [u, Over.homMk_left] at e
  rw [Hom.one_def, Hom.one_def] at e
  simp at e
  exact e
end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMatEx

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V)
    (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (h.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMat
open GlobalTheory.HomFixMatEx

theorem exists_isMat : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M t A' B' φA' φB' Φ' → ∃ c, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' hT
  obtain ⟨_, _, hL, hM, heA, heB, _, _, _, hbA, _⟩ := hH
  obtain ⟨hpA, hpB, hΦ, hiso⟩ := hT
  obtain ⟨ψA, hψA⟩ := liftTop Rg A R t A' φA' hpA.1
  obtain ⟨ψB, hψB⟩ := liftTop Rg B R t B' φB' hpB.1
  obtain ⟨w, hw⟩ := hiso
  have eg : (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = Φ'.left ≫ φB' := by rw [Category.assoc, hψB]
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB), α₀.IsGen := by
    have := GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts L M φA' Φ'.left φB' k w hw
    show ∃ α₀ : LB.Gen (LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
      (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))), α₀.IsGen
    rw [eg, hψA]; exact this
  have hΦ0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
    haveI := hΦ
    exact congrArg Over.Hom.left (IsMonHom.one_hom (f := Φ'))
  have hz1 : zeroPt A' ≫ (ψA ≫ (snd (topS Rg) A).left) = t ≫ eSec A := by
    rw [hψA]; exact zero_comp Rg A R t A' φA' hpA
  have hz2 : zeroPt A' ≫ ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) = t ≫ eSec B := by
    rw [eg, ← Category.assoc, hΦ0]; exact zero_comp Rg B R t B' φB' hpB
  have hzπ : zeroPt A' ≫ A'.hom = 𝟙 (Sp R) := Over.w η[A']
  obtain ⟨α, hα, hrig⟩ := GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator (Z₀ := Sp Rg) L M (ψA ≫ (snd (topS Rg) A).left)
    ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (eSec A) (eSec B) t (zeroPt A') A'.hom k eA eB α₀
    hL hM heA heB hα₀ hzπ hz1 hz2
  have key : ∀ j : Fin mB, ∃ cj : Fin mA → Γ(Sp R, ⊤), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (cj i) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro j
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback M (snd (topS Rg) B).left (Φ'.left ≫ ψB) (k : ℤ) (bB j)
    obtain ⟨s, hs⟩ := GlobalTheory.T.power_pullback_section_exists L M (ψA ≫ (snd (topS Rg) A).left) ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)
      (k : ℤ) α hα hL hM σ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis Rg A L k mA bA hbA R t A' φA' hpA.1 ψA hψA s
    refine ⟨c, fun p => ?_⟩
    have e1 := hs p
    rw [hσ p.1, hc p.2, map_sum] at e1
    erw [res_appLE] at e1
    simp only [map_mul] at e1
    erw [e1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · exact res_appLE _ _ _ _
    · exact res_appLE _ _ _ _
  choose cj hcj using key
  exact ⟨fun i j => cj j i, ψA, ψB, α, hψA, hψB, hα, hrig, fun j p => hcj j p⟩

end GlobalTheory.HomFixMat
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_sections_product_base_change : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M t A' B' φA' φB' Φ' → ∃ c, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  first | (exact @GlobalTheory.HomFixMat.exists_isMat) | (exact GlobalTheory.HomFixMat.exists_isMat) | (intros; apply GlobalTheory.HomFixMat.exists_isMat <;> assumption)
end
