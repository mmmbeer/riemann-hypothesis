import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRealDimOneIsFractionRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosExtTMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOverClosureOfIsFractionRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.Poinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GSep.MemberModel


variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {L : Type} [AddCommGroup L] {mo : L → V} {hL : I → L → L}

theorem nonempty_of_regular (hact : IsAct X₁ act) (hz : X₁.S.R ≤ X₁.M.O z₁) (hV : IsCN V)
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (hev : IsLocalHom ev) (L : Type) [AddCommGroup L] [Subsingleton L]
    (hL : I → L → L) : Nonempty (GMem X₁ z₁ act V ev L (fun _ => 1) hL) := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  let yV : X₁.S.R →+* V := (RatModel.valLoc (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) z₁ (sp _)).comp
    (Subalgebra.inclusion hz).toRingHom
  let P := StrictPull.polPull X₁.ρ.P (spMap yV)
  letI := P.isAb.comm
  obtain ⟨D, A, U, ψ, hX, hψ, hL', hE⟩ := Sep.exists_unif_good hV P
  have r : LBIso P.L (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom (spMap yV))) := PolBaseChange.lbIso_refl P.isLB
  obtain ⟨wl, hwl⟩ := LBIso.trans A.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hL' (lbIso_pull_comp r ψ)
  haveI := hV.2.2.2
  obtain ⟨r₀, hr₀, -, -, hu⟩ := (PsiCoordLocal.main V D hV.2.1 0).1
  refine ⟨{
    cn := hV
    loc := hev
    reg := fun a ha => RatModel.O_le_of_specializes (sp _) (hz ha)
    yK := (algebraMap V (FractionRing V)).comp yV
    yK_eq := fun a => (RatModel.val_spMap_comp (M := X₁.M) (algebraMap V (FractionRing V)) _ (sp _) ⟨a.1, hz a.2⟩).symm
    D := D
    e₈ := ⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩,
      fun _ _ => Subsingleton.elim _ _⟩
    G := P.A
    semi := isSemiAbelian_of_isAbelianScheme _ P.isAb
    A := A
    U := U
    φ := ψ ≫ pullback.fst X₁.ρ.P.A.hom (spMap yV)
    cart := (hψ.comp (isGrpPullback_pullback X₁.ρ.P.A (spMap yV))).congr
      (Spec.map_comp (CommRingCat.ofHom yV) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a => ?_
    psi := fun mu => ⟨(hu rfl).unit, ?_⟩ }⟩
  · have := hact a
    obtain ⟨E, h⟩ := hE ((Over.pullback (spMap yV)).map (act a))
      (inferInstanceAs (IsMonHom ((Over.pullback (spMap yV)).map (act a))))
    refine ⟨E, ?_, fun _ => Subsingleton.elim _ _⟩
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans
      ((congrArg (ψ ≫ ·) (pullback.lift_fst _ _ _)).trans (Category.assoc _ _ _).symm)))
  · rw [_root_.mul_one]
    exact hr₀


def towerSelf (X₁ : GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (h : IsAct X₁ act) : Tower X₁ act where
  X₂ := X₁
  act₂ := act
  isAct := h
  alg := Algebra.id _
  fd := inferInstance
  gal := inferInstance
  d := 1
  lev := by simp
  om := RingHom.id _
  om_eq _ := rfl
  om_fin := RingHom.Finite.id _
  sR _ := RingHom.id _
  sR_eq σ a := (σ.commutes a).symm
  p := 𝟙 _
  p_fin := inferInstance
  p_pt := by
    rw [show spMap (algebraMap X₁.Ω₁ X₁.Ω₁) = 𝟙 _ from Spec.map_id _]; simp
  φ := 𝟙 _
  cart := by rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact Wit.grpPullback_id _
  lb := ⟨Wit.idPull _, Wit.idPull_isGen X₁.ρ.P.isLB⟩
  act_eq _ := by simp
  lam := AddMonoidHom.id _
  lam_pt a := by
    rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  lam_range a := ⟨a, by simp⟩
  gl _ := AddMonoidHom.id _
  gl_pt σ a := by
    rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact (Category.id_comp _).symm
  gl_lam _ _ := rfl

def ofTower {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {Y₁ : Setup F W i} {ac : Matrix (Fin 8) (Fin 8) ℤ → (Y₁.ρ.P.A ⟶ Y₁.ρ.P.A)} (T : Sep.Tower Y₁ ac)
    (k : I → Matrix (Fin 8) (Fin 8) ℤ) : Tower (ofSetup Y₁) (fun a => ac (k a)) where
  X₂ := ofSetup T.X₂
  act₂ a := T.act₂ (k a)
  isAct a := T.isAct.isMonHom (k a)
  alg := T.alg
  fd := T.fd
  gal := T.gal
  d := T.d
  lev := T.lev
  om := T.om
  om_eq := T.om_eq
  om_fin := T.om_fin
  sR := T.sR
  sR_eq := T.sR_eq
  p := T.p
  p_fin := T.p_fin
  p_pt := T.p_pt
  φ := T.φ
  cart := T.cart
  lb := T.lb
  act_eq a := T.act_eq (k a)
  lam := T.lam
  lam_pt := T.lam_pt
  lam_range := T.lam_range
  gl := T.gl
  gl_pt := T.gl_pt
  gl_lam := T.gl_lam

theorem d_pos (T : Tower X₁ act) : 0 < T.d := by
  rcases Nat.eq_zero_or_pos T.d with h | h
  · have h1 := T.lev
    rw [h, mul_zero] at h1
    have := T.X₂.S.r_pos
    have := T.X₂.S.N_ge
    have : 0 < T.X₂.S.r * T.X₂.S.N := Nat.mul_pos (by omega) (by omega)
    omega
  · exact h


theorem char_eq (𝔪 : GMem X₁ z₁ act V ev L mo hL) (a : I) (E : EndU 𝔪.U.toUnifPre)
    (hE : E.aA.left ≫ 𝔪.φ = 𝔪.φ ≫ (act a).left) (mu : L) : E.h (𝔪.e₈ mu) = 𝔪.e₈ (hL a mu) := by
  obtain ⟨E', hE', h⟩ := 𝔪.equiv a
  have e₁ : E.aA = E'.aA := Over.OverMorphism.ext (𝔪.cart.1.hom_ext (hE.trans hE'.symm) ((Over.w _).trans (Over.w _).symm))
  haveI := (GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)).1
  haveI := (GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)).2
  haveI := 𝔪.semi.smooth
  haveI := 𝔪.semi.separated
  have e₂ : E.aG = E'.aG := GlobalTheory.ExtUnique.pullback_map_injective (jK V) _ _
    ((cancel_mono 𝔪.U.gen.hom).1 (E.ext.trans (e₁ ▸ E'.ext.symm)))
  haveI := 𝔪.cn.1
  rw [(GlobalTheory.EndCalc.congr_data ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩ E E' e₂).2, h]


theorem terms_sum (𝔪 : GMem X₁ z₁ act V ev L mo hL) {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam}
    {T : L → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]

section
open GlobalTheory.UPoinc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}


end



theorem n_eq (T : Tower X₁ act) : T.X₂.ρ.n = X₁.ρ.n := by
  obtain ⟨j, hj, h₁⟩ := X₁.ρ.r_eq
  obtain ⟨j', -, h₂⟩ := T.X₂.ρ.r_eq
  have h := T.lev
  rw [h₁, h₂, T.X₂.ρ.N_eq, ← pow_mul, ← pow_add] at h
  have : X₁.ρ.n ∣ T.X₂.ρ.n ^ (j' + T.X₂.ρ.k * 2) :=
    h ▸ ((dvd_pow_self _ (by omega)).mul_right _).mul_right _
  exact ((Nat.prime_dvd_prime_iff_eq X₁.ρ.n_prime T.X₂.ρ.n_prime).1 (X₁.ρ.n_prime.dvd_of_dvd_pow this)).symm

section
open GlobalTheory.UPoinc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}



end

end GlobalTheory.GSep.MemberModel
