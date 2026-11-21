import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwInputs.Move.Forms

set_option maxHeartbeats 4000000 in

theorem hecke_geo {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hsp : HEq D.sp D'.sp)
    (j : Fin D.R.m) (j' : Fin D'.R.m) (hj : (j : ℕ) = j') :
    GA D (Wc D j) = GA D' (Wc D' j') ∧ HEq (Wc D j) (Wc D' j') ∧
    ∀ (β : GL (Fin (Wc D j).rank) (Lev.EAf D)) (β' : GL (Fin (Wc D' j').rank) (Lev.EAf D')), HEq β β' →
    ∀ (Pg : Finset (Pl D.host.E)) (Pg' : Finset (Pl D'.host.E)), HEq Pg Pg' →
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → ∀ (k : ℕ) (α' : GA D' (Wc D' j')) (R' : Finset (GA D' (Wc D' j'))),
      IsHeckeAt (Wc D' j') P' k α' →
      Bridge.IsDC (Lev.levG (Wc D' j') β' (Lev.datY _ D'.R.r D'.R.t 0 (r_le_rank_Wc j') Pg' ∅ (LevelP.triv _ _ _)
        (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α' R' →
      ∃ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α ∧
        Bridge.IsDC (Lev.levG (Wc D j) β (Lev.datY _ D.R.r D.R.t 0 (r_le_rank_Wc j) Pg ∅ (LevelP.triv _ _ _)
          (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α R ∧
        ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' j') R' F') := by
  cases D; cases D'
  dsimp only at hR hH hsp
  subst hR; subst hH; subst hsp
  cases Fin.ext hj
  refine ⟨rfl, HEq.rfl, fun β β' hβ Pg Pg' hPg P P' hP k α R h1 h2 => ?_⟩
  subst hβ; subst hPg; subst hP
  exact ⟨α, R, h1, h2, fun F F' hF => by subst hF; rfl⟩

set_option maxHeartbeats 4000000 in

theorem exists_sameVec {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hT : D.what₂.Tau = D'.what₂.Tau)
    (he : HEq D.eTau D'.eTau) {V : HSp D} {V' : HSp D'} (hV : HEq V V') {P : D.what₂.Tau → SPar} {P' : D'.what₂.Tau → SPar}
    {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (hM : SameModel M M') (v' : M'.Vec) : ∃ v : M.Vec, SameVec v v' := by
  obtain ⟨h1, h2, h3, h4, -, -, h5⟩ := hM
  obtain ⟨R, H, sp, vol, vp, what₂, eT⟩ := D
  obtain ⟨R', H', sp', vol', vp', rows', eT'⟩ := D'
  dsimp only at hR hH hT he
  subst hR; subst hH
  cases what₂; cases rows'
  dsimp only at hT he
  subst hT; subst he; subst hV
  cases M; cases M'
  dsimp only at h1 h2 h3 h4 h5
  subst h1; subst h2; subst h3; subst h4; subst h5
  exact ⟨v', fun τ τ' h => by subst h; rfl⟩

set_option maxHeartbeats 4000000 in

theorem place_geo {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') :
    PlE H = PlE H' ∧ ∀ (P : PlE H) (P' : PlE H'), HEq P P' → (IsSplitPl H P ↔ IsSplitPl H' P') ∧
      Nat.card (kP P) = Nat.card (kP P') ∧
      (∀ (χ : Formalism.L2.Host.HChar H.E) (χ' : Formalism.L2.Host.HChar H'.E), HEq χ χ' → χ.val P = χ'.val P') := by
  subst hR; subst hH
  refine ⟨rfl, fun P P' hP => ?_⟩
  subst hP
  exact ⟨Iff.rfl, rfl, fun _ _ h => by subst h; rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem record_heq {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hB : HEq Y.Bsup Y'.Bsup) (hd : HEq X.delta X'.delta) {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') :
    (∀ j b (x : Y.Fm i j b) (x' : Y'.Fm i' j b), HEq x x' → (x ∈ Y.Bsup i j b ↔ x' ∈ Y'.Bsup i' j b) ∧
      (∀ g g', HEq g g' → HEq (Y.actG i j b g x) (Y'.actG i' j b g' x')) ∧
      ∀ k P P', HEq P P' → HEq (Y.hkF i j b k P x) (Y'.hkF i' j b k P' x')) ∧
    (∀ (ε : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ε' : ∀ i, Bool → (FractionRing (X'.O i) →+* ℂ)), HEq ε ε' →
      ∀ b a a', HEq a a' → ε i b a = ε' i' b a') ∧
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → (P ∈ X.S0 i ↔ P' ∈ X'.S0 i') ∧
      ∀ σ' : Formalism.ConjugateSelfDual.G D'.host.E N'.Om, IsFrob (F := D'.host.E) (N'.plOm.1 P') (normV P') σ' →
        ∃ σ : Formalism.ConjugateSelfDual.G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ ∧ ∀ b : Bool,
          HEq (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i)
              ((if b then X.delta i σ else (X.delta i σ)⁻¹ : (X.O0 i)ˣ) : X.O0 i)))
            (algebraMap (X'.O i') (FractionRing (X'.O i')) (algebraMap (X'.O0 i') (X'.O i')
              ((if b then X'.delta i' σ' else (X'.delta i' σ')⁻¹ : (X'.O0 i')ˣ) : X'.O0 i'))) := by
  obtain ⟨a1, a2, -, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  have xTw := h2.Tw
  have fixedFieldTransport_baseIntegerRing_heq := h2.O0
  have fixedFieldTransport_baseIntegerCommRing_heq := h2.crO0
  have xO := h2.O
  have xcrO := h2.crO
  have xalgO := h2.algO
  have fixedFieldTransport_initialPlaceSet_heq := h2.S0
  have yFm := h3.Fm
  have yacgFm := h3.acgFm
  have ymodFmK := h3.modFmK
  have ymodFmO := h3.modFmO
  have yactG := h3.actG
  have yhkF := h3.hkF
  clear h2 h3
  cases D; cases D'
  dsimp only at a1 a2
  subst a1; subst a2
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xTw fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq xO xcrO xalgO fixedFieldTransport_initialPlaceSet_heq hd
  subst xTw; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst xO; subst xcrO; subst xalgO; subst fixedFieldTransport_initialPlaceSet_heq; subst hd
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yhkF hB
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yhkF; subst hB
  subst hi
  refine ⟨fun j b x x' hx => ?_, fun ε ε' hε b a a' ha => ?_, fun P P' hP => ?_⟩
  · subst hx
    exact ⟨Iff.rfl, fun g g' h => by subst h; rfl, fun k P P' h => by subst h; rfl⟩
  · subst hε; subst ha; rfl
  · subst hP
    exact ⟨Iff.rfl, fun σ hσ => ⟨σ, hσ, fun _ => HEq.rfl⟩⟩

section Ext

variable {LL LL' Ks Ks' WL WL' G G' : Type} [Field LL] [Field LL'] [NumberField LL']
  [Field Ks] [NumberField Ks] [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL']
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [IsScalarTower Ks LL WL]
  [AddCommGroup WL'] [Module LL' WL'] [Module Ks' WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  [IsScalarTower Ks' LL' WL']
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {W' : (LL' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
  [Group G] [Group G']
  {ι : LL →+* LL'} {eK : Ks ≃+* Ks'} {γ : G ≃* G'} {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL' Ks' WL' W' G'}

end Ext

end GlobalTheory.TwInputs.Move.Forms

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwInputs.Move.Forms

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def fiOfEq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) : NX.FormsIso (X.R.FW a) (X.R.FW b) :=
  hab ▸
    { eK := RingEquiv.refl _
      eK_LL := fun _ => rfl
      e := LinearEquiv.refl _ _
      eG := MulEquiv.refl _
      eW := fun _ => LinearIsometryEquiv.refl _ _
      wk := fun _ => Iff.rfl
      mkK := fun _ => Iff.rfl
      rho := fun _ _ => rfl
      chi := fun _ => rfl
      j := fun _ _ => rfl }

theorem fiOfEq_eG (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (g : X.Γ) : (fiOfEq X hab).eG g = g := by
  subst hab; rfl

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
  (YS : NX.NExpRealS X.R X.cG S)

theorem fiOfEq_forms (j : Fin D.R.m) {a b : Fin D'.R.m} (ha : (j : ℕ) = a) (hb : (j : ℕ) = b) (hab : a = b) (x : (X.R.FW j).WK) :
    (fiOfEq X' hab).e ((m.forms j a ha).φ x) = (m.forms j b hb).φ x := by
  subst hab; rfl

include h in
theorem lt_m {n : ℕ} (h2 : n + 1 ≤ D'.R.m) : n < D.R.m := by
  have h3 : D.R.m = D'.R.m := by rw [h.gal.R]
  omega

abbrev dat : NX.RatDat D'.ntw :=
  NX.ratDatR X'.R X'.cG (m.kKsOf (e := e) YS (NX.idxOf D 0)) (m.kKsOf_spec h YS _)

abbrev back (i' : D'.ntw.Tw) : D.ntw.Tw := cast h.Tw_eq.symm i'

theorem back_heq (i' : D'.ntw.Tw) : HEq (back h i') i' := cast_heq _ _

def eFm (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) : 1 ≤ j → j ≤ D'.R.m →
    (D'.nexp.Fm i' j b ≃ₗ[FractionRing (D'.ntw.O i')] NX.Fm (dat h m YS) i' j b) :=
  match j with
  | 0 => fun h1 _ => absurd h1 (by decide)
  | n + 1 => fun _ h2 => m.eFOf h YS _ _ (back_heq h i') ⟨n, lt_m h h2⟩ b

def ks (j : Fin D.R.m) : KsIso ι (show S.Ks ≃+* (dat h m YS).Ks from (YS.fi j).eK.trans m.eK)
    (show S.G ≃* (dat h m YS).G from (YS.fi j).eG.trans m.γ) (S.A ((j : ℕ) + 1)) ((dat h m YS).A ((j : ℕ) + 1)) := m.ksOf h YS j

theorem eFm_cast {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (h1 h2)
    (x : D.nexp.Fm i ((j : ℕ) + 1) b) :
    eFm h m YS i' ((j : ℕ) + 1) b h1 h2 (h.fmCast hi _ b x) =
      fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) (YS.eF i _ b (Nat.le_add_left _ _) j.2 x) := by
  obtain rfl : i = back h i' := eq_of_heq (hi.trans (back_heq h i').symm)
  exact h.eFMove_fmCast hi (S' := dat h m YS) (ks h m YS j) _ x

theorem sup_move (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (x : D'.nexp.Fm i' j b) :
    x ∈ D'.nexp.Bsup i' j b ↔ eFm h m YS i' j b h1 h2 x ∈ NX.Bsup (dat h m YS) i' j b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  rw [eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2 x, fmOf_mem_Bsup, ← hsup]
  exact ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).1.symm

theorem rho_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.RhoStab (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (KsIso.rhoStab_iff (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩)).1 (YS.rho _ h1 (lt_m h h2))

theorem chi_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.ChiInLL0 (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact KsIso.chiInLL0 (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩) h.LL0 (YS.chi _ h1 (lt_m h h2))

theorem act_move (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (g : G0g D'.nd) (x : D'.nexp.Fm i' j b) :
    eFm h m YS i' j b h1 h2 (D'.nexp.actG i' j b g x) =
      NX.actG (dat h m YS) i' j b (rho_move h m YS j h1 h2) (chi_move h m YS j h1 h2) g (eFm h m YS i' j b h1 h2 x) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨g, rfl⟩ := h.grpEquiv.surjective g
  have e1 : D'.nexp.actG i' (n + 1) b (h.grpEquiv g) (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.actG _ (n + 1) b g x) :=
    eq_of_heq ((((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.1 _ _
      (h.grpEquiv_heq g).symm).symm.trans (h.fmCast_heq hi _ b _).symm)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, YS.act]
  refine fmOf_actG (S' := dat h m YS) _ _ _ _ _ _ _ _ ?_ _
  refine (dat h m YS).eG.symm_apply_eq.2 ?_
  refine Eq.symm ((m.cG_eG h _).trans (congrArg h.grpEquiv ?_))
  exact (YS.geq _ _).trans (S.eG.apply_symm_apply g)

def tie (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) : NX.NExpRealS X'.R X'.cG (dat h m YS) where
  fi j := fiOfEq X' (NX.idxOf_succ D' j)
  geq j g := congrArg (fun g => X'.cG (X'.R.eG g)) (fiOfEq_eG X' _ g)
  rho := rho_move h m YS
  chi := chi_move h m YS
  eF := eFm h m YS
  bsup i j b h1 h2 := ⟨1, one_ne_zero, fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).1 hx,
    fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).2 hx⟩
  act := act_move h m YS

theorem read_move (j : Fin D.R.m) (y : (S.A ((j : ℕ) + 1)).WK) :
    SameMap (evidence X j ((YS.fi j).e y))
      (evidence X' (h.cm j) ((fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e ((ks h m YS j).φ y).1)) := by
  have e1 := fiOfEq_forms m j (a := NX.idxOf D' ((j : ℕ) + 1)) (b := h.cm j)
    (congrArg Fin.val (NX.idxOf_succ D' (h.cm j))).symm rfl (NX.idxOf_succ D' (h.cm j)) ((KsIso.ofFormsIso (YS.fi j)).φ y)
  exact (congrArg (fun z => SameMap (evidence X j ((YS.fi j).e y)) (evidence X' (h.cm j) z)) e1).mpr
    (m.read j (h.cm j) rfl ((KsIso.ofFormsIso (YS.fi j)).φ y))

theorem rdRel_move (hsup) (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) (hs : SameSetup ρ ρ') (hρ : ρ.Good) (hρ' : ρ'.Good) (c : ℂ) :
    RdRel h (fun i j b => realRd YS X.geo.v₀ hρ i j b c) (fun i j b => realRd (tie h m YS hsup) X'.geo.v₀ hρ' i j b c) := by
  intro i i' hi j b f
  have hG := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).1
  refine Function.hfunext hG.symm fun g' g hg => heq_of_eq ?_
  change c⁻¹ * evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b
      (eFm h m YS i' ((j : ℕ) + 1) b (Nat.le_add_left _ _) (h.cm j).2 (h.fmCast hi _ b f)) g' =
    c⁻¹ * evK YS X.geo.v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) g
  have key : ∀ z : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) z) g' =
        evK YS X.geo.v₀ hρ i j b z g := fun z => by
    induction z using TensorProduct.induction_on with
    | zero =>
      exact (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_zero).trans
          ((congrFun (map_zero _) _).trans (congrFun (evK YS X.geo.v₀ hρ i j b).map_zero g).symm)
    | add x y hx hy =>
      refine (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        ((fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_add x y)).trans ?_
      refine (congrFun ((evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b).map_add _ _) g').trans ?_
      rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
    | tmul a y =>
      exact congrArg₂ (· * ·)
        ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).2.1 _ _ hs.e b _ _ (h.frac_heq hi a).symm).symm
        (read_move h m YS j y _ _ (m.v₀ j (h.cm j) rfl) _ _ hg.symm).symm
  exact congrArg (c⁻¹ * ·) ((congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
    (eFm_cast h m YS hi j b _ _ f)).trans (key _))

variable {YS} (H : NX.NExpRealH X.R X.cG S YS)

omit H in
include h m in

theorem hecke_sameMap (j : Fin D.R.m) {R : Finset (GA D (Wc D j))} {R' : Finset (GA D' (Wc D' (h.cm j)))}
    (hF : ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' (h.cm j)) R' F'))
    {T₁ T₂ : Mult.MMap (model X j)} {T₁' T₂' : Mult.MMap (model X' (h.cm j))} (h1 : SameMap T₁ T₁') (h2 : SameMap T₂ T₂') {c : ℂ}
    (h3 : T₁ = c • Mult.heckeOn (model X j) R T₂) : T₁' = c • Mult.heckeOn (model X' (h.cm j)) R' T₂' := by
  obtain ⟨hG, hW, -⟩ := hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl
  refine MultilinearMap.ext fun v' => funext fun g' => ?_
  obtain ⟨v, hv⟩ := exists_sameVec h.gal.R h.gal.host h.Tau h.eTau hW (m.MW j (h.cm j) rfl) v'
  obtain ⟨g, hg⟩ : ∃ g : GA D (Wc D j), HEq g g' := ⟨cast hG.symm g', cast_heq _ _⟩
  have e1 := hF (T₂ v) (T₂' v') (Function.hfunext hG fun a a' haa => heq_of_eq (h2 v v' hv a a' haa))
  have e2 : ∀ {A B : Type} {f : A → ℂ} {f' : B → ℂ} {a : A} {b : B}, A = B → HEq f f' → HEq a b → f a = f' b := by
    intro A B f f' a b h1 h2 h3
    subst h1; subst h2; subst h3; rfl
  rw [← h1 v v' hv g g' hg, h3]
  exact congrArg (c * ·) (e2 hG e1 hg)

def hecke (hsup) (hL : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL ((dat h m YS).WL j))
    (hs : ∀ j, NX.HeckeStabR (dat h m YS) j (hL j))
    (hc : ∀ (j : Fin D.R.m) (k : ℕ) (P : PlE D.host) (P' : PlE D'.host), HEq P P' → ∀ y : (S.A ((j : ℕ) + 1)).WK,
      ((ks h m YS j).φ ⟨H.hL _ k P y, H.hs _ (Nat.le_add_left _ _) j.2 k P _ y.2⟩ : (dat h m YS).WL ((j : ℕ) + 1)) =
        hL ((j : ℕ) + 1) k P' ((ks h m YS j).φ y)) : NX.NExpRealH X'.R X'.cG (dat h m YS) (tie h m YS hsup) where
  hL := hL
  hs j _ _ := hs j
  cHk i' b k P' := fracEquiv (h.oEquiv (back_heq h i')) (H.cHk _ b k (cast (place_geo h.gal.R h.gal.host).1.symm P'))
  cHk_zero i' b P' := by rw [H.cHk_zero, map_one]
  cHk_unit i' b P' := (H.cHk_unit _ b _).map _
  cHk_pow i' b k P' := by rw [H.cHk_pow, map_pow]
  hkEq i' j b h1 h2 k P' x p1 p2 p3 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
    have hi := back_heq h i'
    have hP : HEq (cast (place_geo h.gal.R h.gal.host).1.symm P') P' := cast_heq _ _
    generalize cast (place_geo h.gal.R h.gal.host).1.symm P' = P at hP ⊢
    obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
    obtain ⟨r1, -, r3⟩ := record_heq h.gal h.set h.frm h.Bsup h.delta hi
    have e1 : D'.nexp.hkF i' (n + 1) b k P' (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.hkF _ (n + 1) b k P x) :=
      eq_of_heq (((r1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.2 k _ _ hP).symm.trans (h.fmCast_heq hi _ b _).symm)
    change eFm h m YS i' (n + 1) b h1 h2 _ = _ • NX.hkFR (dat h m YS) i' (n + 1) b (hL (n + 1)) (hs (n + 1)) k P'
      (eFm h m YS i' (n + 1) b h1 h2 _)
    rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2,
      H.hkEq _ _ b _ _ k P x (fun hh => p1 ((r3 P P' hP).1.1 hh)) (((place_geo h.gal.R h.gal.host).2 P P' hP).1.2 p2)
        (by rw [h.gal.R]; exact p3), fmOf_smul]
    exact congrArg _ (fmOf_restrict (S' := dat h m YS) (h.scal hi b) (ks h m YS ⟨n, lt_m h h2⟩) _ _ _ (hs (n + 1) k P')
      (hc ⟨n, lt_m h h2⟩ k P P' hP) _)

end GlobalTheory.TwInputs.Move.Forms

end
end
