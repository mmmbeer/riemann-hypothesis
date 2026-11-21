import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BddAboveSubDegsOfJointlyMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCohSubDegEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.Points
open GlobalTheory.GradedPieces
open GlobalTheory.CechPic (cls)

namespace GlobalTheory.LocM

section Graded

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure IntChart (Z : Mdl Y i₀) : Type where

  U : Z.X.Opens

  aff : IsAffineOpen U

  w : Vecs Dw (Y Z.i).t Γ(Z.X, U)

  int : IntFrame Z aff w

theorem le_preimage_inf {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {U U' : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x ⁻¹ᵁ U') : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := fun _ hz => ⟨h hz, h' hz⟩

theorem valR_zero_fn {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) (U : X.Opens) : valR x U 0 = 0 := by
  unfold valR
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem spMap_valMap {X : Scheme.{0}} {R : Type} [CommRing R] {U : X.Opens} (hU : IsAffineOpen U) (x : Sp R ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : spMap (valMap x U h).hom ≫ hU.fromSpec = x := specMap_valMap_fromSpec hU x h

theorem le_preimage_of_eq {X : Scheme.{0}} {R : Type} [CommRing R] {U : X.Opens} {hU : IsAffineOpen U}
    {φ : Γ(X, U) →+* R} {x : Sp R ⟶ X} (hx : spMap φ ≫ hU.fromSpec = x) : ⊤ ≤ x ⁻¹ᵁ U := by
  subst hx
  exact le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)

open Classical in
variable (Dw) in

def oneAt (σ : E →+* ℂ) (n : ℕ) (σ' : E →+* ℂ) (a : Fin (Dw.mult σ')) : ℤ := if σ' = σ ∧ (a : ℕ) = n then 1 else 0

theorem oneAt_eq_zero {σ : E →+* ℂ} {n : ℕ} (h : Dw.mult σ ≤ n) : oneAt Dw σ n = 0 := by
  funext σ' a
  refine if_neg ?_
  rintro ⟨rfl, rfl⟩
  exact a.2.not_ge h

variable {Z : Mdl Y i₀}

theorem HasDR.exists_intChart (hZ : HasDR Z) (x : Z.X) : ∃ c : IntChart Z, x ∈ c.U :=
  have ⟨U, hU, w, hx, hw⟩ := hZ.2 x
  ⟨⟨U, hU, w, hw⟩, hx⟩

namespace IntChart

variable (c c' c'' : IntChart Z)

theorem aff_inf : IsAffineOpen (c.U ⊓ c'.U) := isAffineOpen_inf Z c.aff c'.aff

def vec {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    TanM (x ≫ Z.π) (Y Z.i).t.G :=
  tanOf (tan_bc c.int (valMap x _ h).hom (spMap_valMap c.aff x h) σ a)

theorem vec_eq {R : Type} [CommRing R] (φ : Γ(Z.X, c.U) →+* R) {x : Sp R ⟶ Z.X} (hx : spMap φ ≫ c.aff.fromSpec = x)
    (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : c.vec x h σ a = tanOf (tan_bc c.int φ hx σ a) := by
  subst hx
  have e : (valMap _ _ h).hom = φ := congrArg (fun f => f.hom) (valMap_specMap_fromSpec c.aff (CommRingCat.ofHom φ) h)
  exact tan_ext (by rw [vec, left_tanOf, left_tanOf, e])

theorem linearIndependent_vec {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) :
    LinearIndependent k (c.vec x h σ) := linInd_bc c.int _ (spMap_valMap c.aff x h) σ

theorem exists_tri (hZ : HasDR Z) (σ : E →+* ℂ) :
    ∃ m : Fin (Dw.mult σ) → Fin (Dw.mult σ) → Γ(Z.X, c.U ⊓ c'.U), (∀ a b, a < b → m a b = 0) ∧
      ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (a : Fin (Dw.mult σ)),
        c.vec x h σ a = ∑ b, valR x _ (m a b) • c'.vec x h' σ b := by
  obtain ⟨n, v, e, he, hv, hb⟩ := c'.int.1 σ
  have hV := c.aff_inf c'
  let ρ : Γ(Z.X, c.U) →+* Γ(Z.X, c.U ⊓ c'.U) := resG _ inf_le_left
  let ρ' : Γ(Z.X, c'.U) →+* Γ(Z.X, c.U ⊓ c'.U) := resG _ inf_le_right
  have hρ : spMap ρ ≫ c.aff.fromSpec = hV.fromSpec := c.aff.map_fromSpec hV _
  have hρ' : spMap ρ' ≫ c'.aff.fromSpec = hV.fromSpec := c'.aff.map_fromSpec hV _
  have hρ2 : spMap ρ' ≫ c'.aff.fromSpec ≫ Z.π = hV.fromSpec ≫ Z.π := by rw [← hρ', Category.assoc]
  choose q hq using fun a => (basis_map ρ' hρ2 hv hb _ (tan_bc c.int ρ hρ σ a)).exists
  have hx2 {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) :
      spMap (valMap x _ h').hom ≫ c'.aff.fromSpec ≫ Z.π = x ≫ Z.π := by
    rw [← Category.assoc, spMap_valMap]
  have key {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (a) :
      c.vec x h σ a = ∑ j, valR x _ (q a j) • tanOf (isTan_map _ (hx2 x h') (hv j)) := by
    have h3 : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U) := le_preimage_inf h h'
    have e1 : (valMap x _ h3).hom.comp ρ = (valMap x _ h).hom :=
      congrArg (fun f => f.hom) (res_valMap _ inf_le_left h3 h)
    have e2 : (valMap x _ h3).hom.comp ρ' = (valMap x _ h').hom :=
      congrArg (fun f => f.hom) (res_valMap _ inf_le_right h3 h')
    have hk := comb_map (valMap x _ h3).hom (x' := x ≫ Z.π)
      (by rw [← Category.assoc, spMap_valMap]) (hq a)
    simp only [Vecs.bc, dual_comp, e1, e2] at hk
    simp only [valR_eq x _ h3]
    exact (comb_iff (fun j => isTan_map _ (hx2 x h') (hv j)) _ (tan_bc c.int _ (spMap_valMap c.aff x h) σ a)).1 hk
  have ev {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (b) :
      tanOf (isTan_map _ (hx2 x h') (hv (e b))) = c'.vec x h' σ b :=
    tan_ext (by rw [vec, left_tanOf, left_tanOf, he b]; rfl)
  have zero (a j) (hj : ∀ b, e b = j → a < b) : q a j = 0 := fn_ext Z fun k _ x h3 ho => by
    have h := le_preimage_mono x inf_le_left h3
    have h' := le_preimage_mono x inf_le_right h3
    have p₁ := spMap_valMap c.aff x h
    have p₂ := spMap_valMap c'.aff x h'
    have f₁ := c.int.2 k (valMap x _ h).hom (by rw [p₁]; exact ho)
    have f₂ := c'.int.2 k (valMap x _ h').hom (by rw [p₂]; exact ho)
    rw [p₁] at f₁
    rw [p₂] at f₂
    obtain ⟨d, hd⟩ := exists_diag_of_flagAt Z hZ.1 f₁ f₂ σ
      (tan_bc c.int _ p₁ σ) (tan_bc c'.int _ p₂ σ) (linInd_bc c'.int _ p₂ σ)
    obtain ⟨cf, -, h0, hs⟩ := hd a
    have li := linInd_of_basis (fun j => isTan_map _ (hx2 x h') (hv j)) (basis_map _ (hx2 x h') hv hb)
    have e1 : ∑ b, cf b • tanOf (isTan_map _ (hx2 x h') (hv (e b))) =
        ∑ j, Function.extend e cf 0 j • tanOf (isTan_map _ (hx2 x h') (hv j)) :=
      Fintype.sum_of_injective e e.injective _ _
        (fun j hj => by rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply, zero_smul])
        (fun b => by rw [e.injective.extend_apply])
    simp only [ev] at e1
    rw [Fintype.linearIndependent_iffₛ.1 li _ _ ((key x h h' a).symm.trans (hs.trans e1)) j, valR_zero_fn]
    by_cases hj' : ∃ b, e b = j
    · obtain ⟨b, rfl⟩ := hj'
      rw [e.injective.extend_apply, h0 b (hj b rfl)]
    · rw [Function.extend_apply' _ _ _ hj', Pi.zero_apply]
  refine ⟨fun a b => q a (e b), fun a b hab => zero a _ fun b' hb' => by rwa [e.injective hb'], fun R _ x h h' a => ?_⟩
  rw [key x h h' a]
  refine (Fintype.sum_of_injective e e.injective _ _ (fun j hj => ?_) fun b => by rw [ev]).symm
  rw [zero a j fun b hb => (hj ⟨b, hb⟩).elim, valR_zero_fn, zero_smul]

variable (hZ : HasDR Z)

def chg (σ : E →+* ℂ) : Fin (Dw.mult σ) → Fin (Dw.mult σ) → Γ(Z.X, c.U ⊓ c'.U) := (c.exists_tri c' hZ σ).choose

theorem chg_eq_zero (σ : E →+* ℂ) {a b : Fin (Dw.mult σ)} (h : a < b) : c.chg c' hZ σ a b = 0 :=
  (c.exists_tri c' hZ σ).choose_spec.1 a b h

theorem vec_eq_sum {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : c.vec x h σ a = ∑ b, valR x _ (c.chg c' hZ σ a b) • c'.vec x h' σ b :=
  (c.exists_tri c' hZ σ).choose_spec.2 R x h h' a

theorem diag {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (σ : E →+* ℂ) :
    Diag (c'.vec x h' σ) (c.vec x h σ) fun a => valR x _ (c.chg c' hZ σ a a) := fun a =>
  ⟨_, rfl, fun b hb => by rw [c.chg_eq_zero c' hZ σ hb, valR_zero_fn],
    c.vec_eq_sum c' hZ x h h' σ a⟩

theorem valR_chg_self {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    valR x _ (c.chg c hZ σ a a) = 1 :=
  congrFun ((c.diag c hZ x h h σ).unique (c.linearIndependent_vec x h σ) (Diag.refl _)) a

theorem valR_chg_mul {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (h'' : ⊤ ≤ x ⁻¹ᵁ c''.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    valR x _ (c.chg c' hZ σ a a) * valR x _ (c'.chg c'' hZ σ a a) = valR x _ (c.chg c'' hZ σ a a) :=
  congrFun (((c'.diag c'' hZ x h' h'' σ).trans (c.diag c' hZ x h h' σ)).unique (c''.linearIndependent_vec x h'' σ)
    (c.diag c'' hZ x h h'' σ)) a

theorem isUnit_chg (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : IsUnit (c.chg c' hZ σ a a) := by
  refine IsUnit.of_mul_eq_one (resG _ (inf_comm c.U c'.U).le (c'.chg c hZ σ a a)) (fn_ext Z fun k _ x h _ => ?_)
  have hi := le_preimage_mono x inf_le_left h
  rw [valR_mul x _ h, valR_res x _ h, valR_one x _ h, c.valR_chg_mul c' c hZ x hi (le_preimage_mono x inf_le_right h) hi,
    c.valR_chg_self hZ x hi]

def tr (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : Γ(Z.X, c.U ⊓ c'.U)ˣ :=
  ∏ σ, ∏ a, (c.isUnit_chg c' hZ σ a).unit ^ e σ a

theorem tr_add (e e' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : c.tr c' hZ (e + e') = c.tr c' hZ e * c.tr c' hZ e' := by
  simp only [tr, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem tr_neg_oneAt (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    (c.tr c' hZ (-oneAt Dw σ a)).val = resG _ (inf_comm c.U c'.U).le (c'.chg c hZ σ a a) := by
  rw [tr, Finset.prod_eq_single σ (fun σ' _ h => by simp [oneAt, h]) (by simp),
    Finset.prod_eq_single a (fun a' _ h => by simp [oneAt, Fin.val_inj, h]) (by simp)]
  simp only [oneAt, Pi.neg_apply, and_self, if_true, zpow_neg, zpow_one]
  refine Units.inv_eq_of_mul_eq_one_right (fn_ext Z fun k _ x h _ => ?_)
  have hi := le_preimage_mono x inf_le_left h
  rw [valR_mul x _ h, valR_res x _ h, valR_one x _ h, IsUnit.unit_spec,
    c.valR_chg_mul c' c hZ x hi (le_preimage_mono x inf_le_right h) hi, c.valR_chg_self hZ x hi]

end IntChart

variable (hZ : HasDR Z) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ)

def grLB : LB Z.X := ⟨IntChart Z, IntChart.U, fun c c' => c.tr c' hZ e⟩

theorem valR_grLB {k : Type} [Field k] (x : Sp k ⟶ Z.X) (c c' : IntChart Z) {V : Z.X.Opens} (hV : V ≤ c.U ⊓ c'.U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : valR x V (res hV ((grLB hZ e).g c c')).val = ∏ σ, ∏ a, valR x _ (c.chg c' hZ σ a a) ^ e σ a :=
  (valR_res x hV h _).trans (valR_prod_zpow x (le_preimage_mono x hV h) _ e)

theorem isLB_grLB : (grLB hZ e).IsLB := by
  refine ⟨top_unique fun z _ => Opens.mem_iSup.2 (hZ.exists_intChart z), fun c => ?_, fun c c' c'' => ?_⟩
  · refine Units.ext (fn_ext Z fun k _ x h _ => (valR_grLB hZ e x c c _ h).trans ?_)
    simp only [c.valR_chg_self hZ x h, one_zpow, Finset.prod_const_one]
    exact (valR_one x _ h).symm
  · refine Units.ext (fn_ext Z fun k _ x h _ => (valR_mul x _ h _ _).trans ?_)
    refine (congrArg₂ (· * ·) (valR_grLB hZ e x c c' _ h) (valR_grLB hZ e x c' c'' _ h)).trans
      (.trans ?_ (valR_grLB hZ e x c c'' _ h).symm)
    simp only [← Finset.prod_mul_distrib, ← mul_zpow, c.valR_chg_mul c' c'' hZ x
      (le_preimage_mono x (inf_le_left.trans inf_le_left) h) (le_preimage_mono x (inf_le_left.trans inf_le_right) h)
      (le_preimage_mono x inf_le_right h)]

theorem diagAt_iff_chg (c c' : IntChart Z) {k : Type} [Field k] (φ : Γ(Z.X, c.U) →+* k) (φ' : Γ(Z.X, c'.U) →+* k)
    (hx : spMap φ ≫ c.aff.fromSpec = spMap φ' ≫ c'.aff.fromSpec) (σ : E →+* ℂ) (d : Fin (Dw.mult σ) → k) :
    DiagAt (Y Z.i).t (spMap φ ≫ c.aff.fromSpec ≫ Z.π) (c'.w.bc φ' σ) (c.w.bc φ σ) d ↔
      d = fun a => valR (spMap φ ≫ c.aff.fromSpec) _ (c.chg c' hZ σ a a) := by
  have h : ⊤ ≤ (spMap φ ≫ c.aff.fromSpec) ⁻¹ᵁ c.U := le_preimage_of_eq rfl
  have h' := le_preimage_of_eq hx.symm
  have hd := c.diag c' hZ _ h h' σ
  rw [funext (c.vec_eq φ rfl h σ), funext (c'.vec_eq φ' hx.symm h' σ)] at hd
  rw [← Category.assoc, diagAt_iff (tan_bc c'.int φ' hx.symm σ) (tan_bc c.int φ rfl σ)]
  exact ⟨fun h₁ => h₁.unique (linInd_bc c'.int φ' hx.symm σ) hd, fun h₁ => by rw [h₁]; exact hd⟩

theorem isGrLB_grLB : IsGrLB Z e (grLB hZ e) := by
  refine ⟨isLB_grLB hZ e, IntChart.aff, IntChart.w, IntChart.int, fun c c' k _ φ φ' d hx _ hd => ?_⟩
  refine (valR_prod_zpow _ (le_preimage_inf (le_preimage_of_eq rfl) (le_preimage_of_eq hx.symm)) _ e).trans (Finset.prod_congr rfl fun σ _ => ?_)
  rw [(diagAt_iff_chg hZ c c' φ φ' hx σ (d σ)).1 (hd σ)]
  rfl

variable {e} in

theorem IsGrLB.lbIso {L : LB Z.X} (h : IsGrLB Z e L) : LBIso L (grLB hZ e) := by
  obtain ⟨-, hU, w, hw, hg⟩ := h
  refine CechPic.iso_of_chart (isLB_grLB hZ e) ⟨fun i => ⟨_, hU i, w i, hw i⟩, fun _ => le_rfl, fun _ i j _ _ =>
    congrArg _ (Units.ext (fn_ext Z fun k _ x h ho => ?_))⟩
  have h₁ := spMap_valMap (hU i) x (le_preimage_mono x inf_le_left h)
  have h₂ := spMap_valMap (hU j) x (le_preimage_mono x inf_le_right h)
  have h₃ := hg i j k _ _ _ (h₁.trans h₂.symm) (by rw [h₁]; exact ho) fun σ =>
    (diagAt_iff_chg hZ ⟨_, hU i, w i, hw i⟩ ⟨_, hU j, w j, hw j⟩ _ _ (h₁.trans h₂.symm) σ _).2 rfl
  rw [h₁] at h₃
  exact h₃.trans (valR_prod_zpow x h (fun σ a => (IntChart.isUnit_chg ⟨_, hU i, w i, hw i⟩ ⟨_, hU j, w j, hw j⟩ hZ σ a).unit)
    e).symm

def grCls : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ CechPic.Pic Z.X :=
  AddMonoidHom.mk' (fun e => cls _ (isLB_grLB hZ e)) fun e e' => by
    have h := CechPic.isLB_tens (isLB_grLB hZ e) (isLB_grLB hZ e')
    refine (CechPic.cls_eq_iff _ h).2 (CechPic.iso_of_chart h ⟨fun c => (c, c), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' => ?_⟩)
    refine .trans ?_ (CechPic.gm_tens (grLB hZ e) (grLB hZ e') (𝟙 _) y (c, c) (c', c') ⟨hc, hc⟩ ⟨hc', hc'⟩).symm
    exact (congrArg _ (IntChart.tr_add c c' hZ e e')).trans (map_mul _ _ _)

variable {e} in

theorem IsGrLB.cls_eq {L : LB Z.X} (h : IsGrLB Z e L) : cls L h.1 = grCls hZ e :=
  (CechPic.cls_eq_iff _ _).2 (h.lbIso hZ)

end Graded

section Curves

structure Curve (k : Type) [Field k] (X : Scheme.{0}) : Type where

  n : ℕ

  I : (PSpace k n).IdealSheafData

  integral : IsIntegral I.subscheme

  dim : topologicalKrullDim I.subscheme = 1

  smooth : Smooth (I.subschemeι ≫ PSpace.str k n)

  f : I.subscheme ⟶ X

namespace Curve

variable {k : Type} [Field k] {X : Scheme.{0}} (c : Curve k X)

abbrev C : Scheme.{0} := c.I.subscheme

instance : IsIntegral c.C := c.integral

instance algebra : Algebra k Γ(c.C, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (c.I.subschemeι ≫ PSpace.str k c.n).appTop).hom.toAlgebra

theorem strHom_eq : strHom k c.C = c.I.subschemeι ≫ PSpace.str k c.n := GlobalTheory.strHom_eq fun _ => rfl

theorem isSmoothProjCurve : VB.IsSmoothProjCurve k c.C :=
  ⟨⟨c.integral, c.dim, c.n, _, inferInstance, c.strHom_eq.symm⟩, c.strHom_eq ▸ c.smooth⟩

theorem isProjCurve : VB.IsProjCurve k c.C := c.isSmoothProjCurve.toIsProjCurve

theorem exists_iso {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (h : VB.IsSmoothProjCurve k C) (f : C ⟶ X) :
    ∃ (c : Curve k X) (e : C ≅ c.C), e.hom ≫ c.f = f ∧ e.hom ≫ strHom k c.C = strHom k C := by
  obtain ⟨n, i, _, hi⟩ := h.isProjOver
  have hk : i.ker.subschemeι.ker = i.ker := Scheme.IdealSheafData.ker_subschemeι _
  have := IsClosedImmersion.isIso_lift _ _ hk
  let e := asIso (IsClosedImmersion.lift _ i hk.le)
  have he : e.hom ≫ i.ker.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  have hs : i.ker.subschemeι ≫ PSpace.str k n = e.inv ≫ strHom k C := by
    rw [Iso.eq_inv_comp, reassoc_of% he, hi]
  have := h.isIntegral
  have := h.smooth
  refine ⟨⟨n, i.ker, .of_isIso e.hom, ?_, hs ▸ inferInstance, e.inv ≫ f⟩, e, by simp, ?_⟩
  · exact (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans h.dim_eq
  · rw [strHom_eq]
    exact (congrArg (e.hom ≫ ·) hs).trans (by simp)

def degOf (L : LB X) : ℤ := VB.degLB k (L.pull c.f)

def degPic : CechPic.Pic X →+ ℤ := c.isProjCurve.degPic.comp (CechPic.pull c.f)

theorem degOf_eq {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C] (h : VB.IsProjCurve k C) (e : C ≅ c.C)
    (he : e.hom ≫ strHom k c.C = strHom k C) {L : LB X} (hL : L.IsLB) :
    c.degOf L = VB.degLB k (L.pull (e.hom ≫ c.f)) := by
  have h₁ := LB.isLB_pull hL c.f
  have h₂ := LB.isLB_pull h₁ e.hom
  have h₃ := LB.isLB_pull hL (e.hom ≫ c.f)
  rw [VB.degLB_congr h₃ h₂ ((CechPic.cls_eq_iff _ _).1 (CechPic.pull_comp e.hom c.f (cls L hL))), degOf,
    c.isProjCurve.degLB_eq_interNum h₁, h.degLB_eq_interNum h₂, ← interNumOn_id,
    ← interNumOn_comp_of_isIso k e.hom, Category.comp_id, interNumOn_eq_interNum_pull (fun r => by
      rw [algebraMap_eq_strHom, algebraMap_eq_strHom, ← he, Scheme.Hom.comp_appTop]; rfl) (isLB_vecOne h₁)]
  congr 1
  ext1 i
  fin_cases i
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra in
open ProjSpace ProjCoh in

theorem nonempty_of_point (x : Sp k ⟶ X) : Nonempty (Curve k X) :=
  (exists_iso (VB.isSmoothProjCurve_line k) (PSpace.str k 1 ≫ x)).nonempty

attribute [local instance] MvPolynomial.gradedAlgebra in
open ProjSpace ProjCoh in

theorem exists_degOf_On : ∃ c : Curve k (PSpace k 1), ∀ n : ℤ, c.degOf (ProjSpace.On k 1 n) = n := by
  obtain ⟨c, e, he, hs⟩ := exists_iso (VB.isSmoothProjCurve_line k) (𝟙 _)
  refine ⟨c, fun n => ?_⟩
  have hL := ProjSpace.On_isLB k 1 n
  rw [c.degOf_eq (VB.isSmoothProjCurve_line k).toIsProjCurve e hs hL, he]
  exact (VB.degLB_congr (LB.isLB_pull hL _) hL ((CechPic.cls_eq_iff (LB.isLB_pull hL _) hL).1
    (CechPic.pull_id (cls _ hL)))).trans (VB.degLB_On k n)

end Curve

end Curves

section OnModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {k : Type} [Field k] (c : Curve k Z.X)

namespace Curve

def t : SAB H c.C := (exists_sab (c.f ≫ Z.π) (Y Z.i).t).choose

def tMap : SABMap c.t (Y Z.i).t (c.f ≫ Z.π) := (exists_sab (c.f ≫ Z.π) (Y Z.i).t).choose_spec.some

abbrev lie : c.C.Modules := LieVB.Lie c.t.G

theorem exists_isVB_lie : ∃ g, VB.IsVB c.lie g :=
  have := c.t.semi
  (LieVB.exists_isVB_of_isSemiAbelian c.t.G).imp fun _ h => h.2

def eDeg : ℤ := -VB.deg k c.lie

def Pm : ℤ := sSup (VB.subDegs k c.lie)

theorem Pm_eq {P : ℤ} (h : VB.IsMaxSubDeg k c.lie P) : c.Pm = P := IsGreatest.csSup_eq h

variable (hZ : HasDR Z)

def degGr : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ ℤ := c.degPic.comp (grCls hZ)

theorem degGr_eq {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ} {L : LB Z.X} (h : IsGrLB Z e L) :
    c.degGr hZ e = VB.degLB k (L.pull c.f) := congrArg c.degPic (h.cls_eq hZ).symm

def degStep (σ : E →+* ℂ) (n : ℕ) : ℤ := c.degGr hZ (-oneAt Dw σ n)

theorem degStep_eq_zero {σ : E →+* ℂ} {n : ℕ} (h : Dw.mult σ ≤ n) : c.degStep hZ σ n = 0 := by
  rw [degStep, oneAt_eq_zero h, neg_zero, map_zero]

end Curve

end OnModel

section Place

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

theorem hasDR : HasDR ct.YY := ct.isYY.2.1

def Fbar (ct : At S κ p) : Type := haveI := Fact.mk ct.hp; AlgebraicClosure (ZMod p)

instance : Field ct.Fbar := haveI := Fact.mk ct.hp; inferInstanceAs (Field (AlgebraicClosure (ZMod p)))

instance : IsAlgClosed ct.Fbar := haveI := Fact.mk ct.hp; inferInstanceAs (IsAlgClosed (AlgebraicClosure (ZMod p)))

instance : CharP ct.Fbar p := haveI := Fact.mk ct.hp; inferInstanceAs (CharP (AlgebraicClosure (ZMod p)) p)

abbrev Crv : Type := Curve ct.Fbar ct.YY.X

abbrev CrvQ : Type := Curve (AlgebraicClosure κ.c.F) ct.YY.X

open Classical in

def indWt (τ : PsiT D) (i : ℕ) : PsiT D → ℕ → ℤ := fun τ' i' => if τ' = τ ∧ i' = i then 1 else 0

def degPiece {k : Type} [Field k] (c : Curve k ct.YY.X) (τ : PsiT D) (i : ℕ) : ℤ :=
  c.degGr ct.hasDR (-ct.expo (indWt τ i))

def degLie {k : Type} [Field k] (c : Curve k ct.YY.X) (τ : PsiT D) : Bool → ℤ
  | false => ∑ i ∈ Finset.Icc 1 j, ct.degPiece c τ i
  | true => -∑ i ∈ Finset.Icc (j + 1) N, ct.degPiece c τ i

def degWt {k : Type} [Field k] (c : Curve k ct.YY.X) (l : PsiT D → ℕ → ℝ) : ℝ :=
  -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (ct.degPiece c τ i : ℝ)

def nefQ (l : PsiT D → ℕ → ℝ) : Prop := ∀ c : ct.CrvQ, 0 ≤ ct.degWt c l

end At

def embOf (D : D7) (τ : PsiT D) : D.host.E →+* ℂ := DV.tauEmb D (D.eTau.symm τ)

theorem mult_embOf (S : Sig A N j) (τ : PsiT D) : S.Dw.mult (embOf D τ) = j := (if_pos (A.cm _)).trans S.p_eq

theorem mult_conj_embOf (S : Sig A N j) (τ : PsiT D) : S.Dw.mult (conjEmb (embOf D τ)) = N - j := by
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  refine (if_neg fun h => ?_).trans (by omega)
  have h₃ : starRingEnd ℂ A.H.rt0 = A.H.rt0 := (congrArg _ (A.cm (D.eTau.symm τ)).symm).trans h
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h₃
  have h₄ := A.H.sqrt_neg_disc_sq
  rw [hx] at h₄
  have h₅ : x ^ 2 = -(A.H.d : ℝ) := by exact_mod_cast h₄
  have h₆ : (0 : ℝ) < A.H.d := by exact_mod_cast A.H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem mult_le (S : Sig A N j) (σ : D.host.E →+* ℂ) : S.Dw.mult σ ≤ N := by
  have h₂ := S.rank_eq
  unfold Datum.mult
  split_ifs <;> omega

namespace At

variable (ct : At S κ p)

open Classical in

theorem expo_indWt_apply (τ : PsiT D) (i : ℕ) (σ : D.host.E →+* ℂ) (a : Fin (S.Dw.mult σ)) :
    ct.expo (indWt τ i) σ a = (if σ = embOf D τ ∧ (a : ℕ) + 1 = i then 1 else 0) -
      if σ = conjEmb (embOf D τ) ∧ N - a = i then 1 else 0 := by
  rw [expo, Finset.sum_eq_single (D.eTau.symm τ) (fun t _ h => by
    have : D.eTau t ≠ τ := fun e => h (D.eTau.eq_symm_apply.2 e)
    simp [indWt, this]) (by simp)]
  rw [sub_eq_add_neg]
  change (ite (σ = embOf D τ) _ _) + ite (σ = conjEmb (embOf D τ)) _ _ = _
  congr 1
  · by_cases h : σ = embOf D τ <;> simp only [h, indWt, Equiv.apply_symm_apply, true_and, false_and, if_true, if_false]
  · by_cases h : σ = conjEmb (embOf D τ) <;>
      simp only [h, indWt, Equiv.apply_symm_apply, true_and, false_and, if_true, if_false, neg_zero]

theorem expo_indWt (τ : PsiT D) {i : ℕ} (h₁ : 1 ≤ i) (h₂ : i ≤ N) :
    ct.expo (indWt τ i) = oneAt S.Dw (embOf D τ) (i - 1) - oneAt S.Dw (conjEmb (embOf D τ)) (N - i) := by
  funext σ a
  have e₁ : (a : ℕ) + 1 = i ↔ (a : ℕ) = i - 1 := by omega
  have e₂ : N - a = i ↔ (a : ℕ) = N - i := by omega
  classical
  rw [expo_indWt_apply]
  exact congrArg₂ (· - ·) (if_congr (and_congr_right' e₁) rfl rfl) (if_congr (and_congr_right' e₂) rfl rfl)


theorem expo_eq_sum (l : PsiT D → ℕ → ℤ) :
    ct.expo l = ∑ t : D.what₂.Tau, ∑ i ∈ Finset.Icc 1 N, l (D.eTau t) i • ct.expo (indWt (D.eTau t) i) := by
  funext σ a
  have := mult_le S σ
  have := a.2
  have m₁ : (a : ℕ) + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 (by omega)
  have m₂ : N - a ∈ Finset.Icc 1 N := Finset.mem_Icc.2 (by omega)
  have key (P : Prop) [Decidable P] (m : ℕ) (hm : m ∈ Finset.Icc 1 N) (f : ℕ → ℤ) [∀ x, Decidable (P ∧ m = x)] :
      (∑ x ∈ Finset.Icc 1 N, f x * if P ∧ m = x then 1 else 0) = if P then f m else 0 := by
    by_cases h : P <;> simp [h, hm]
  simp only [Finset.sum_apply, Pi.smul_apply, expo_indWt_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [expo, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  classical
  rw [key _ _ m₁, key _ _ m₂, embOf, Equiv.symm_apply_apply]
  split_ifs <;> simp [sub_eq_add_neg]

variable {k : Type} [Field k] (c : Curve k ct.YY.X) (τ : PsiT D) {i : ℕ}


theorem degPiece_of_le (h₁ : 1 ≤ i) (h₂ : i ≤ j) : ct.degPiece c τ i = c.degStep ct.hasDR (embOf D τ) (i - 1) := by
  have := mult_le S (embOf D τ)
  rw [mult_embOf] at this
  rw [degPiece, expo_indWt _ _ h₁ (by omega), oneAt_eq_zero (σ := conjEmb _) (by rw [mult_conj_embOf]; omega), sub_zero]
  rfl

theorem degPiece_of_lt (h₁ : j < i) (h₂ : i ≤ N) :
    ct.degPiece c τ i = -c.degStep ct.hasDR (conjEmb (embOf D τ)) (N - i) := by
  rw [degPiece, expo_indWt _ _ (by omega) h₂, oneAt_eq_zero (σ := embOf D τ) (by rw [mult_embOf]; omega), zero_sub,
    Curve.degStep, map_neg]

theorem sum_degPiece_head (h : i ≤ j) :
    ∑ m ∈ Finset.Icc 1 i, ct.degPiece c τ m = ∑ n ∈ Finset.range i, c.degStep ct.hasDR (embOf D τ) n := by
  refine Finset.sum_bij' (fun m _ => m - 1) (fun n _ => n + 1) ?_ ?_ ?_ ?_ fun m hm => ?_
  all_goals simp only [Finset.mem_Icc, Finset.mem_range] at *
  · omega
  · omega
  · omega
  · omega
  · exact ct.degPiece_of_le c τ hm.1 (hm.2.trans h)

theorem sum_degPiece_tail (h : j ≤ i) : -∑ m ∈ Finset.Icc (i + 1) N, ct.degPiece c τ m =
    ∑ n ∈ Finset.range (N - i), c.degStep ct.hasDR (conjEmb (embOf D τ)) n := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_bij' (fun m _ => N - m) (fun n _ => N - n) ?_ ?_ ?_ ?_ fun m hm => ?_
  all_goals simp only [Finset.mem_Icc, Finset.mem_range] at *
  · omega
  · omega
  · omega
  · omega
  · rw [ct.degPiece_of_lt c τ (by omega) hm.2, neg_neg]

theorem degWt_intCast (l : PsiT D → ℕ → ℤ) {L : LB ct.YY.X} (h : IsGrLB ct.YY (ct.expo l) L) :
    ct.degWt c (fun τ i => l τ i) = VB.degLB k (L.pull c.f) := by
  rw [← c.degGr_eq ct.hasDR h, expo_eq_sum, degWt, ← finsum_comp_equiv D.eTau, finsum_eq_sum_of_fintype]
  simp only [degPiece, map_sum, map_zsmul, map_neg]
  simp

end At

end Place

end GlobalTheory.LocM
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.Points
open GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.LocM

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {T T' : X.Opens}

def affPt (hT : IsAffineOpen T) : Sp Γ(X, T) ⟶ X := hT.fromSpec

theorem le_preimage_affPt (hT : IsAffineOpen T) : ⊤ ≤ affPt hT ⁻¹ᵁ T := hT.fromSpec_preimage_self.ge

theorem valR_affPt (hT : IsAffineOpen T) (a : Γ(X, T)) : valR (affPt hT) T a = a := by
  have h := valMap_specMap_fromSpec hT (C := Γ(X, T)) (𝟙 _) (le_preimage_specMap_fromSpec hT _)
  have e : Spec.map (𝟙 (CommRingCat.of Γ(X, T))) ≫ hT.fromSpec = affPt hT := by
    rw [Spec.map_id]
    exact Category.id_comp _
  rw [← e]
  exact (valR_eq _ _ (le_preimage_specMap_fromSpec hT (C := Γ(X, T)) (𝟙 _)) a).trans congr(($h).hom a)

theorem spMap_affPt (hT : IsAffineOpen T) (hT' : IsAffineOpen T') (h : T' ≤ T) :
    spMap (resG X h) ≫ affPt hT = affPt hT' := hT.map_fromSpec hT' _

def CoordOpen (T : X.Opens) : Prop :=
  IsAffineOpen T ∧ ∃ (W : t.G.left.Opens) (h : T ≤ unitSec t.G ⁻¹ᵁ W) (n : ℕ) (f : Fin n → Γ(t.G.left, W)),
    VB.IsFrame fun b => dUnit t.G h (f b)

theorem exists_coordOpen {V : X.Opens} {x : X} (hx : x ∈ V) : ∃ T, CoordOpen t T ∧ x ∈ T ∧ T ≤ V := by
  have := t.semi
  have := t.semi.smooth
  obtain ⟨U, n, s, hU, hs⟩ := exists_isFrame_omega t.G x
  obtain ⟨T, W, hT, hle, c⟩ := Conormal.exists_isChart (sec_hom η[t.G]) (V := V ⊓ U) ⟨hx, hU⟩
  choose f hf using fun b => c.d_surjective (sec_hom η[t.G]) (resM (omega t.G) (hle.trans inf_le_right) (s b))
  exact ⟨T, ⟨c.affine_base, W, c.le, n, f, (funext hf :) ▸ hs.res (hle.trans inf_le_right)⟩, hT, hle.trans inf_le_left⟩

variable {t}

theorem CoordOpen.mono (h : CoordOpen t T) (hT' : IsAffineOpen T') (e : T' ≤ T) : CoordOpen t T' := by
  obtain ⟨-, W, hW, n, f, hf⟩ := h
  exact ⟨hT', W, e.trans hW, n, f, by simpa only [resM_dUnit] using hf.res e⟩

theorem tanEv_dUnit_eq {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (h : ⊤ ≤ x ⁻¹ᵁ T) {W : t.G.left.Opens} (hW : T ≤ unitSec t.G ⁻¹ᵁ W) (f : Γ(t.G.left, W)) :
    ⊤ ≤ v ⁻¹ᵁ W ∧ tanEv t hv h (dUnit t.G hW f) = (valR v W f).snd := by
  have hv' : ⊤ ≤ v ⁻¹ᵁ W := fun z _ => by
    obtain ⟨s, rfl⟩ := surjective_sec_epsZero z
    have h₁ : s ∈ (x ≫ unitSec t.G) ⁻¹ᵁ W := hW (h trivial)
    rw [← epsZero_comp_of_isTanAtG t hv] at h₁
    exact h₁
  exact ⟨hv', (tanEv_dUnit t hv h hW hv' f).trans (congrArg TrivSqZeroExt.snd (valR_eq v W hv' f).symm)⟩

def IsSecOf (hT : IsAffineOpen T) (v : TanM (affPt hT) t.G) (l : Γ(Lie t.G, T)) : Prop :=
  ∀ s : Γ(omega t.G, T), dualApp l le_rfl s = tanEv t (isTan_tv v) (le_preimage_affPt hT) s

theorem CoordOpen.exists_equiv (h : CoordOpen t T) :
    ∃ Θ : TanM (affPt h.1) t.G ≃ₗ[Γ(X, T)] Γ(Lie t.G, T), ∀ v, IsSecOf h.1 v (Θ v) := by
  obtain ⟨hT, W, hW, n, f, hf⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LocM.TanPair.exists_tanM_equiv E H X t _ (affPt hT) T (le_preimage_affPt hT) n _ hf
  refine ⟨Φ ≪≫ₗ (hf.dual.basis le_rfl).equivFun.symm, fun v s => ?_⟩
  let ev : Γ(omega t.G, T) →ₗ[Γ(X, T)] Γ(X, T) :=
    { toFun := tanEv t (isTan_tv v) (le_preimage_affPt hT)
      map_add' := tanEv_add t _ _
      map_smul' := fun a s => (tanEv_smul t _ _ a s).trans
        (congrArg (· * _) ((valR_eq _ _ (le_preimage_affPt hT) a).symm.trans (valR_affPt hT a))) }
  refine LinearMap.congr_fun (g := ev) ((hf.basis le_rfl).ext fun b => ?_) s
  rw [IsFrame.basis_apply, ← hf.dual_basis_repr le_rfl, resM_self, LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply, hΦ]
  rfl

theorem IsSecOf.eq_resM (h : CoordOpen t T) {hT' : IsAffineOpen T'} (e : T' ≤ T) {v : TanM (affPt h.1) t.G}
    {v' : TanM (affPt hT') t.G} {l : Γ(Lie t.G, T)} {l' : Γ(Lie t.G, T')} (hl : IsSecOf h.1 v l) (hl' : IsSecOf hT' v' l')
    (hv : (tv v').left = spMap (dualMap (resG X e)) ≫ (tv v).left) : l' = resM _ e l := by
  obtain ⟨hT, W, hW, n, f, hf⟩ := h
  refine hf.dual_ext e fun b => ?_
  obtain ⟨h₁, h₂⟩ := tanEv_dUnit_eq (isTan_tv v) (le_preimage_affPt hT) hW (f b)
  rw [hl', dualApp_res, dualApp_resM l le_rfl e, hl, h₂, resM_dUnit, (tanEv_dUnit_eq _ _ _ _).2, hv,
    valR_spMap_comp _ _ _ h₁]
  simp [Formalism.L2.Pj.dualMap]

theorem exists_tangent_equiv {C : Scheme.{0}} {t' : SAB H C} {g : C ⟶ X} (m : SABMap t' t g) :
    ∃ Ψ : ∀ (T : C.Opens) (h : CoordOpen t' T) (x : Sp Γ(C, T) ⟶ X), affPt h.1 ≫ g = x →
      (TanM x t.G ≃ₗ[Γ(C, T)] Γ(Lie t'.G, T)),
      ∀ T h x hx T' h' x' hx' (e : T' ≤ T) u u', (tv u').left = spMap (dualMap (resG C e)) ≫ (tv u).left →
        Ψ T' h' x' hx' u' = resM _ e (Ψ T h x hx u) := by
  choose Θ hΘ using fun T (h : CoordOpen t' T) => h.exists_equiv
  refine ⟨fun T h x hx => (pushE m _ hx).symm ≪≫ₗ Θ T h, fun T h x hx T' h' x' hx' e u u' hu => ?_⟩
  obtain ⟨v, rfl⟩ := (pushE m _ hx).surjective u
  obtain rfl : pushE m _ hx' (tanOf (isTan_map _ (spMap_affPt h.1 h'.1 e) (isTan_tv v))) = u' :=
    tan_ext (by rw [hu, left_pushE, left_pushE, left_tanOf, Category.assoc])
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (hΘ T h v).eq_resM h e (hΘ T' h' _) rfl

end Sections

section Inhabitants

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem Mdl.exists_point (h1 : 1 ≤ Dw.p + Dw.q) (Z : Mdl Y i₀) {k : Type} [Field k] [IsAlgClosed k]
    (φ : Z.i.c.V W →+* k) : ∃ x : Sp k ⟶ Z.X, x ≫ Z.s = spMap φ := by
  have := SharedLaws.isProper_toroidalModel_structureMap Z
  have := Z.flat
  obtain ⟨z⟩ := SharedLaws.nonempty_model h1 Z
  have : Surjective Z.s := ⟨fun y => by
    have h₀ : IsLocalRing.closedPoint (Z.i.c.V W) ∈ Set.range Z.s :=
      (IsLocalRing.specializes_closedPoint (Z.s z)).mem_closed Z.s.isClosedMap.isClosed_range ⟨z, rfl⟩
    exact (Flat.generalizingMap Z.s).stableUnderGeneralization_range (IsLocalRing.specializes_closedPoint y) h₀⟩
  let f := pullback.snd Z.s (spMap φ)
  have : CompactSpace ↥(pullback Z.s (spMap φ)) := QuasiCompact.compactSpace_of_compactSpace f
  have : Nonempty ↥(pullback Z.s (spMap φ)) := f.surjective.nonempty
  obtain ⟨y, -, hy⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback Z.s (spMap φ))) Set.univ_nonempty
  exact ⟨pointOfClosedPoint f y hy ≫ pullback.fst _ _, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]⟩

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

instance At.nonempty_crv (ct : At S κ p) : Nonempty ct.Crv := by
  have := Fact.mk ct.hp
  have := ct.YY.i.c.fin
  have : NumberField ct.YY.i.c.F := NumberField.mk
  have hV := SharedLaws.mem_nonunits_V ct.YY.i.c ct.hp.ne_zero ct.hW
  obtain ⟨-, h₂⟩ := GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField (ct.YY.i.c.V ct.W) ct.hp.ne_zero hV
  have : CharP (IsLocalRing.ResidueField (ct.YY.i.c.V ct.W)) p := (CharP.charP_iff_prime_eq_zero ct.hp).2 (by
    rw [← map_natCast (IsLocalRing.residue _), IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hV)
  letI := ZMod.algebra (IsLocalRing.ResidueField (ct.YY.i.c.V ct.W)) p
  letI := ZMod.algebra ct.Fbar p
  let ψ : IsLocalRing.ResidueField (ct.YY.i.c.V ct.W) →ₐ[ZMod p] ct.Fbar := IsAlgClosed.lift
  obtain ⟨x, -⟩ := ct.YY.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge))
    (ψ.toRingHom.comp (IsLocalRing.residue _))
  exact Curve.nonempty_of_point x

instance At.nonempty_crvQ (ct : At S κ p) : Nonempty ct.CrvQ := by
  have := ct.YY.i.c.fin
  let ψ : ct.YY.i.c.F →ₐ[ℚ] AlgebraicClosure κ.c.F := IsAlgClosed.lift
  obtain ⟨x, -⟩ := ct.YY.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge))
    (ψ.toRingHom.comp (ct.YY.i.c.V ct.W).subtype)
  exact Curve.nonempty_of_point x

end Inhabitants

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀}

theorem IntChart.left_vec_map (q : IntChart Z) {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {x : Sp R ⟶ Z.X}
    {x' : Sp R' ⟶ Z.X} (hx : spMap ψ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ q.U) (h' : ⊤ ≤ x' ⁻¹ᵁ q.U) (σ : E →+* ℂ)
    (a : Fin (Dw.mult σ)) : (tv (q.vec x' h' σ a)).left = spMap (dualMap ψ) ≫ (tv (q.vec x h σ a)).left := by
  have e : spMap (ψ.comp (valMap x _ h).hom) ≫ q.aff.fromSpec = x' := by
    rw [← hx, ← spMap_comp_spMap, Category.assoc, spMap_valMap]
  rw [q.vec_eq _ e, IntChart.vec, left_tanOf, left_tanOf, Vecs.bc, Vecs.bc, dual_comp]

theorem IntChart.exists_basis (q : IntChart Z) {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ q.U)
    (σ : E →+* ℂ) : ∃ (n : ℕ) (e : Fin (Dw.mult σ) ↪ Fin n) (b : Module.Basis (Fin n) R (TanM (x ≫ Z.π) (Y Z.i).t.G)),
      ∀ a, b (e a) = q.vec x h σ a := by
  obtain ⟨n, v, e, he, hv, hb⟩ := q.int.1 σ
  have hx : spMap (valMap x _ h).hom ≫ q.aff.fromSpec ≫ Z.π = x ≫ Z.π := by rw [← Category.assoc, spMap_valMap]
  have hv' := fun i => isTan_map _ hx (hv i)
  have key (u : TanM (x ≫ Z.π) (Y Z.i).t.G) : ∃! cf : Fin n → R, ∑ i, cf i • tanOf (hv' i) = u := by
    simpa only [comb_iff hv' _ (isTan_tv u), eq_comm (b := ∑ _, _), show tanOf (isTan_tv u) = u from tan_ext rfl] using
      basis_map _ hx hv hb _ (isTan_tv u)
  refine ⟨n, e, .mk (v := fun i => tanOf (hv' i)) (Fintype.linearIndependent_iffₛ.2 fun f g hfg =>
    congrFun ((key _).unique hfg rfl)) fun u _ => (Submodule.mem_span_range_iff_exists_fun R).2 (key u).exists,
    fun a => ?_⟩
  rw [Module.Basis.mk_apply]
  exact tan_ext (by rw [IntChart.vec, left_tanOf, left_tanOf, he a]; rfl)

namespace Curve

variable {k : Type} [Field k] (c : Curve k Z.X) (hZ : HasDR Z)

theorem isAffineOpen_inf {T T' : c.C.Opens} (hT : IsAffineOpen T) (hT' : IsAffineOpen T') : IsAffineOpen (T ⊓ T') := by
  have := c.isProjCurve.isProperCurve.isProper
  have : IsSeparated (terminal.from c.C) := by
    rw [← terminal.comp_from (strHom k c.C)]
    infer_instance
  exact hT.inf hT'

theorem exists_subsheaf {α : Type} [Fintype α] (rk : α → ℕ) (σ : α → (E →+* ℂ)) (ix : ∀ a, Fin (Dw.mult (σ a))) (P : Prop)
    (hb : ∀ (q : IntChart Z) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ q.U),
      ∃ (κ : Type) (_ : Fintype κ) (e : α ↪ κ) (b : Module.Basis κ R (TanM (x ≫ Z.π) (Y Z.i).t.G)),
        (P → Function.Surjective e) ∧ ∀ a, b (e a) = q.vec x h (σ a) (ix a))
    (ht : ∀ (q q' : IntChart Z) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ q.U) (h' : ⊤ ≤ x ⁻¹ᵁ q'.U) (a : α),
      ∃ cf : α → R, cf a = valR x _ (q'.chg q hZ (σ a) (ix a) (ix a)) ∧ (∀ b, b ≠ a → rk a ≤ rk b → cf b = 0) ∧
        q'.vec x h' (σ a) (ix a) = ∑ b, cf b • q.vec x h (σ b) (ix b))
    (S : Finset α) (hS : ∀ a ∈ S, ∀ b, rk b < rk a → b ∈ S) :
    ∃ (G : c.C.Modules) (i : G ⟶ c.lie), IsCohSub i ∧ deg k G = ∑ a ∈ S, c.degStep hZ (σ a) (ix a) ∧
      (P → S = Finset.univ → IsIso i) := by
  obtain ⟨Ψ, hΨ⟩ := exists_tangent_equiv c.tMap
  obtain ⟨g, hg⟩ := c.exists_isVB_lie
  have := hg.isQuasicoherent
  let J := {q : c.C.Opens × IntChart Z // CoordOpen c.t q.1 ∧ q.1 ≤ c.f ⁻¹ᵁ q.2.U}
  have hin {T : c.C.Opens} (hT : IsAffineOpen T) {U : Z.X.Opens} (h : T ≤ c.f ⁻¹ᵁ U) : ⊤ ≤ (affPt hT ≫ c.f) ⁻¹ᵁ U :=
    fun z hz => h (le_preimage_affPt hT hz)
  have hc : ⨆ j : J, j.1.1 = ⊤ := top_unique fun x _ => by
    obtain ⟨q, hq⟩ := hZ.exists_intChart (c.f x)
    obtain ⟨T, hT, hx, hle⟩ := exists_coordOpen c.t (V := c.f ⁻¹ᵁ q.U) hq
    exact Opens.mem_iSup.2 ⟨⟨(T, q), hT, hle⟩, hx⟩
  choose κ _ e b hP hbe using fun j : J => hb j.1.2 _ (affPt j.2.1.1 ≫ c.f) (hin _ j.2.2)
  let B (j : J) := (b j).map (Ψ _ j.2.1 _ (Category.assoc _ _ _).symm)
  have hB (j : J) : VB.IsFrame (B j) := Summand.isFrame_of_affine_basis j.2.1.1 _
  have hres (j : J) {T : c.C.Opens} (hT : CoordOpen c.t T) (h : T ≤ j.1.1) (a : α) : resM c.lie h (B j (e j a)) =
      Ψ T hT _ (Category.assoc _ _ _).symm (j.1.2.vec _ (hin hT.1 (h.trans j.2.2)) (σ a) (ix a)) := by
    rw [Module.Basis.map_apply, hbe]
    exact (hΨ _ _ _ _ _ _ _ _ h _ _ (j.1.2.left_vec_map _ (by rw [← Category.assoc, spMap_affPt]) _ _ _ _)).symm
  obtain ⟨G, i, hi, hd, hs⟩ := GlobalTheory.TriangularFrames.exists_isCohSub_deg_eq_sum k c.C c.isProjCurve c.lie J _ hc κ (fun j => B j) hB α rk e
    (fun a => (grLB hZ (-oneAt Dw (σ a) (ix a))).pull c.f) (fun a => LB.isLB_pull (isLB_grLB hZ _) _)
    (fun _ j _ => j.1.2) (fun a j => j.2.2.trans (GlobalTheory.LB.pull_U (L := grLB hZ _) c.f fun _ => j.1.2).ge)
    (fun j j' a => by
      have hT := j.2.1.mono (c.isAffineOpen_inf j.2.1.1 j'.2.1.1) inf_le_left
      have h := hin hT.1 (inf_le_left.trans j.2.2)
      have h' := hin hT.1 (inf_le_right.trans j'.2.2)
      obtain ⟨cf, h₁, h₂, h₃⟩ := ht j.1.2 j'.1.2 _ _ h h' a
      refine ⟨cf, h₁.trans (.symm ?_), h₂, ?_⟩
      · refine (GlobalTheory.LB.resG_pull_g (L := grLB hZ _) c.f _ _ _).trans ((valR_affPt hT.1 _).symm.trans
          ((valR_appLE _ _ _ (le_preimage_affPt hT.1) _).trans ?_))
        exact (congrArg _ (IntChart.tr_neg_oneAt j.1.2 j'.1.2 hZ _ _)).trans (valR_res _ _ (le_preimage_inf h h') _)
      · simp only [hres _ hT, h₃, map_sum, map_smul]) S hS
  refine ⟨G, i, hi, hd, fun hp hS => ?_⟩
  have := hi.mono
  refine Twist.isIso_of_cover i hc fun j V hV => ⟨QCoh.injective_app_of_mono i V, fun x => (hs j V hV x).2 ?_⟩
  refine Submodule.span_mono ?_ ((isFrame_iff.1 (hB j) V hV).2 Submodule.mem_top)
  rintro _ ⟨m, rfl⟩
  obtain ⟨a, rfl⟩ := hP j hp m
  exact ⟨a, by simp [hS], rfl⟩

theorem isMaxSubDeg_Pm : IsMaxSubDeg k c.lie c.Pm := by
  obtain ⟨g, hg⟩ := c.exists_isVB_lie
  obtain ⟨P, hP⟩ := exists_isMaxSubDeg_iff.2 (GlobalTheory.VB.bddAbove_subDegs_of_isVB k c.C c.isProjCurve _ g hg)
  rwa [c.Pm_eq hP]

theorem sum_degStep_mem (σ : E →+* ℂ) (n : ℕ) : ∑ m ∈ Finset.range n, c.degStep hZ σ m ∈ subDegs k c.lie := by
  obtain ⟨G, i, hi, hd, -⟩ := c.exists_subsheaf hZ (α := Fin (Dw.mult σ)) Fin.val (fun _ => σ) id False
    (fun q R _ x h => have ⟨_, e, b, hb⟩ := q.exists_basis x h σ; ⟨_, inferInstance, e, b, False.elim, hb⟩)
    (fun q q' R _ x h h' a => ⟨_, rfl, fun b hb hab => by
      rw [q'.chg_eq_zero q hZ σ (lt_of_le_of_ne hab hb.symm), valR_zero_fn], q'.vec_eq_sum q hZ x h' h σ a⟩)
    (Finset.univ.filter fun a => a.val < n) (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  refine ⟨G, i, hi, hd.trans ?_⟩
  refine Finset.sum_bij_ne_zero (fun a _ _ => a.val) (fun a ha _ => by simpa using ha)
    (fun _ _ _ _ _ _ => Fin.ext) (fun m hm h0 => ?_) fun _ _ _ => rfl
  have : m < Dw.mult σ := lt_of_not_ge fun h => h0 (c.degStep_eq_zero hZ h)
  exact ⟨⟨m, this⟩, by simpa using hm, h0, rfl⟩

theorem sum_degStep_le (σ : E →+* ℂ) (n : ℕ) : ∑ m ∈ Finset.range n, c.degStep hZ σ m ≤ c.Pm :=
  c.isMaxSubDeg_Pm.2 (c.sum_degStep_mem hZ σ n)

theorem deg_lie (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (hu : ¬ p ∣ (discr E).natAbs) :
    deg k c.lie = ∑ σ, ∑ m ∈ Finset.range (Dw.mult σ), c.degStep hZ σ m := by
  classical
  obtain ⟨G, i, -, hd, hi⟩ := c.exists_subsheaf hZ (α := Σ σ : E →+* ℂ, Fin (Dw.mult σ)) (fun a => a.2.val) Sigma.fst
    Sigma.snd True
    (fun q R _ x h => by
      obtain ⟨b, hb⟩ := GlobalTheory.TotalFrame.exists_basis_of_intFrame E H Dw Xo p W hp hW hu Y i₀ Z q.U q.aff q.w q.int R _ x (spMap_valMap q.aff x h)
      exact ⟨_, inferInstance, .refl _, b, fun _ => Function.surjective_id, fun a => tan_ext (hb a.1 a.2)⟩)
    (fun q q' R _ x h h' ⟨σ, a⟩ => by
      refine ⟨fun b => (Pi.single σ (fun b => valR x _ (q'.chg q hZ σ a b)) : ∀ σ, Fin (Dw.mult σ) → R) b.1 b.2,
        by simp, fun ⟨σ', b⟩ hb hab => ?_, ?_⟩
      · by_cases e : σ' = σ
        · subst e
          simp only [Pi.single_eq_same]
          rw [q'.chg_eq_zero q hZ σ' (lt_of_le_of_ne hab fun e : a = b => hb (e ▸ rfl)), valR_zero_fn]
        · simp [e]
      · rw [Fintype.sum_sigma, Finset.sum_eq_single σ (fun σ' _ e => by simp [e]) (by simp)]
        simpa only [Pi.single_eq_same] using q'.vec_eq_sum q hZ x h' h σ a)
    Finset.univ (by simp)
  have := hi trivial rfl
  rw [← deg_congr k (asIso i), hd, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Fin.sum_univ_eq_sum_range (c.degStep hZ σ) _

end Curve

end Steps

section Place

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem sum_emb_eq (D : D7) (F : (D.host.E →+* ℂ) → ℤ) :
    ∑ σ, F σ = ∑ᶠ τ : PsiT D, (F (embOf D τ) + F (conjEmb (embOf D τ))) := by
  have := Fintype.ofEquiv _ D.eTau
  have e (τ : PsiT D) : embOf D τ = D.host.emb τ := by rw [embOf, DV.tauEmb, Equiv.apply_symm_apply]
  rw [finsum_eq_sum_of_fintype, Finset.sum_add_distrib]
  refine (Fintype.sum_bijective _ (GlobalTheory.Mem.BaseEx.sum_emb_bijective D.host) _ _ ?_).symm.trans (Fintype.sum_sum_type
    (Sum.elim (fun τ => F (embOf D τ)) fun τ => F (conjEmb (embOf D τ))))
  rintro (τ | τ)
  · exact congrArg F (e τ)
  · exact congrArg (fun σ => F (conjEmb σ)) (e τ)

namespace At

variable (ct : At S κ p) {k : Type} [Field k] (c : Curve k ct.YY.X)

theorem degLie_false (τ : PsiT D) : ct.degLie c τ false =
    ∑ m ∈ Finset.range (S.Dw.mult (embOf D τ)), c.degStep ct.hasDR (embOf D τ) m := by
  rw [mult_embOf]
  exact ct.sum_degPiece_head c τ le_rfl

theorem degLie_true (τ : PsiT D) : ct.degLie c τ true =
    ∑ m ∈ Finset.range (S.Dw.mult (conjEmb (embOf D τ))), c.degStep ct.hasDR (conjEmb (embOf D τ)) m := by
  rw [mult_conj_embOf]
  exact ct.sum_degPiece_tail c τ le_rfl

theorem eDeg_eq (hu : DV.UnramE D p) : c.eDeg = -∑ᶠ τ, (ct.degLie c τ false + ct.degLie c τ true) := by
  simp only [degLie_false, degLie_true]
  rw [Curve.eDeg, c.deg_lie ct.hasDR ct.hp ct.hW hu, sum_emb_eq]

end At

def crdTrue (ct : At S κ p) : CrDSt ct where
  nefQ := ct.nefQ
  Crv := ct.Crv
  eDeg c := c.eDeg
  Pm c := c.Pm
  Pm_nonneg c := c.isMaxSubDeg_Pm.nonneg
  degLie c := ct.degLie c
  degLdR c := ct.degWt c
  CrvQ := ct.CrvQ
  degGrQ c := ct.degPiece c
  nefQ_def _ := Iff.rfl
  degGrD c := ct.degPiece c
  degLdR_def _ _ := rfl
  degLie_f _ _ := rfl
  degLie_alt _ _ := rfl
  eDeg_def hu c := ct.eDeg_eq c hu
  Pm_head c τ _ _ h := (ct.sum_degPiece_head c τ h).trans_le (c.sum_degStep_le _ _ _)
  Pm_tail c τ _ h _ := (ct.sum_degPiece_tail c τ h).trans_le (c.sum_degStep_le _ _ _)

example (ct : At S κ p) : (crdTrue ct).nefQ 0 := fun c => by simp [At.degWt]

example (ct : At S κ p) (c : ct.Crv) (τ : PsiT D) (hj : 1 ≤ j) :
    (crdTrue ct).degGrD c τ 1 ∈ subDegs ct.Fbar c.lie ∧
      (crdTrue ct).degLdR c (fun τ' i => At.indWt τ 1 τ' i) = -((crdTrue ct).degGrD c τ 1 : ℝ) := by
  refine ⟨?_, ?_⟩
  · have := c.sum_degStep_mem ct.hasDR (embOf D τ) 1
    rwa [← ct.sum_degPiece_head c τ hj, Finset.Icc_self, Finset.sum_singleton] at this
  · refine (ct.degWt_intCast c _ (isGrLB_grLB ct.hasDR _)).trans ?_
    rw [← c.degGr_eq ct.hasDR (isGrLB_grLB ct.hasDR _)]
    change _ = -((c.degGr ct.hasDR (-_) : ℤ) : ℝ)
    simp

example (ct : At S κ p) : Nonempty (crdTrue ct).Crv ∧ Nonempty (crdTrue ct).CrvQ := ⟨ct.nonempty_crv, ct.nonempty_crvQ⟩

end Place

end GlobalTheory.LocM
end
end
