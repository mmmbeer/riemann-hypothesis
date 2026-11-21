import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ActEqZeroOfQK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfMemCcAt
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.GlobalTheoremInputs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst

section
noncomputable section

namespace UpperTheory.GalC.Gen

open Formalism.BasicNotions Formalism.MainNotions NumberField
open GlobalTheory.HeightCounting

structure Raw (D : D7) where
  η : ℕ → D.what₂.places.Pl → ℚ
  hη : ∀ j w, 0 ≤ η j w
  P : @NLay0 D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0
  hZ : @NLay0.ZOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P
  hE : @NLay0.EtaOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P

@[reducible] def Raw.rec' {D : D7} (Λ : Raw D) : D7 := setRaw D Λ.η Λ.hη Λ.P Λ.hZ Λ.hE

variable {D : D7} (Λ : Raw D)

set_option maxHeartbeats 1600000

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ Λ.rec' := { L with }

@[reducible] def instTr {L : SizeData₂ D} (X : G.Inst D L) : G.Inst Λ.rec' (ledTr Λ L) := { X with }

@[reducible] def gatTr (x : GatTies D) : GatTies Λ.rec' := { x with }

@[reducible] def latTr (x : G.LatInst D) : G.LatInst Λ.rec' := { x with }

@[reducible] def cmpTr (x : LatCmp D) : LatCmp Λ.rec' := { x with }

@[reducible] def twTr (x : TwForms D) : TwForms Λ.rec' := { x with }

@[reducible] def thTr (x : ThetaX D) : ThetaX Λ.rec' := { x with }

@[reducible] def errTr (x : ErrX D) : ErrX Λ.rec' := { x with }
open DivX (md) in

@[reducible] def divTr (X : DivX D) : DivX Λ.rec' := { X with md := fun S κ p _ la z => { md X S κ p la z with } }
section Local

variable {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p j : ℕ)

theorem VV_tr : G.VV (instTr Λ X) K a b p = G.VV X K a b p := by
  have e1 : G.Cand _ (ledTr Λ L) K p = G.Cand D L K p := rfl
  have e2 : G.goodReps (instTr Λ X) p = G.goodReps X p := rfl
  have e3 : G.Sig (instTr Λ X) K a b p = G.Sig X K a b p := rfl
  unfold G.VV; rw [e1, e2, e3]; rfl

theorem tau_translate : G.tauP (instTr Λ X) K a b p = G.tauP X K a b p := by
  unfold G.tauP; rw [VV_tr]; rfl

theorem ioP_instTr : G.ioP (instTr Λ X) K a b p = G.ioP X K a b p := by
  unfold G.ioP; rw [VV_tr]; rfl

theorem gainP_instTr : G.gainP (instTr Λ X) K a b p j = G.gainP X K a b p j := by
  unfold G.gainP; rw [VV_tr]; rfl

theorem TTP_tr : G.TTP (instTr Λ X) K a b p = G.TTP X K a b p := by
  unfold G.TTP; rw [VV_tr]; rfl

theorem fills_tr (w : D.what₂.places.Pl) (H : G.ParametersFill X K w) : G.ParametersFill (instTr Λ X) K w :=
  ⟨H.1, H.2.1, H.2.2.1.trans (TTP_tr Λ X K _ _ _).symm,
    fun h1 h2 j hj => (H.2.2.2.1 h1 h2 j hj).trans (gainP_instTr Λ X K _ _ _ _).symm,
    H.2.2.2.2.1.trans (tau_translate Λ X K _ _ _).symm, H.2.2.2.2.2.1.trans (ioP_instTr Λ X K _ _ _).symm, H.2.2.2.2.2.2⟩

theorem NP_tr (Y : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    G.NP (instTr Λ X) (latTr Λ Y) K u w hg = G.NP X Y K u w hg := by
  have e0 : G.aL (ledTr Λ L) = G.aL L := rfl
  have e1 : G.bL (ledTr Λ L) = G.bL L := rfl
  have e2 : ∀ a b p t, G.Sv (instTr Λ X) K a b p t = G.Sv X K a b p t := fun _ _ _ _ => rfl
  unfold G.NP
  simp only [e0, e1, e2, VV_tr, tau_translate]
  rfl

end Local

def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) (nch : NChoice Λ.rec') (tie : NChTie Λ.rec' nch) (xd : ThData Λ.rec')
    (p0 : BaseLevelRowSide Λ.rec') (rr0 : p0.s.RRDef) (amb : AmbForm Λ.rec' (RowSide.sharp Λ.rec')) (amb0 : AmbForm Λ.rec' p0.s)
    (ks : kapSharp Λ.rec' = kapSharp D) :
    Extra Λ.rec' (ledTr Λ L) (gatTr Λ gatT) (instTr Λ Gx) (latTr Λ Gy) K (divTr Λ X) cX where
  lev := ex.lev
  th := thTr Λ ex.th
  th_io := ex.th_io
  cmp := cmpTr Λ ex.cmp
  lat := ⟨ex.lat.vram, fun u w hg hv x => by
    erw [NP_tr]; exact ex.lat.served u w hg (by rw [← VV_tr Λ]; exact hv) x, ex.lat.atT⟩
  tw := twTr Λ ex.tw
  ker := fun u w g => { ex.ker u w g with }
  ep_def := ex.ep_def
  ep_tie := ex.ep_tie
  kapI_def := ex.kapI_def
  fills_all := ex.fills_all
  nu_unserved := fun u w h1 h2 => ex.nu_unserved u w h1 (by rw [← VV_tr Λ]; exact h2)
  idx := { ex.idx with }
  kap_def := ex.kap_def
  lam_def := ex.lam_def
  kapR_def := ex.kapR_def.trans ks.symm
  errX := errTr Λ ex.errX
  err := { ex.err with }
  nch := nch
  nch_tie := tie
  xd := xd
  p0 := p0
  rationalRoots_def := rr0
  amb := amb
  amb0 := amb0
  fdef := ex.fdef
  duStar_def := ex.duStar_def
  Dstar_def := ex.Dstar_def
  gauge := ex.gauge
  gauge_def := ex.gauge_def

@[reducible] def parTr {L : SizeData₂ D} (P : ParameterChoice' D L) : ParameterChoice' Λ.rec' (ledTr Λ L) := { P with }

@[reducible] def parTTr {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : ParamsT Λ.rec' (ledTr Λ L) (parTr Λ P) := { T with }

set_option smartUnfolding false in
theorem buDefQ_eta (h : Rows.BuDefQ D.what₂) : Rows.BuDefQ (rowsEta D.what₂ Λ.η Λ.hη) := by
  have e : (rowsEta D.what₂ Λ.η Λ.hη).sec D.what₂.mu0 = D.what₂.sec D.what₂.mu0 := by
    first
      | rfl
      | with_unfolding_all rfl
  intro u φ x
  have := h u φ x
  rw [← e] at this
  exact this

theorem tiesTr (h : Ties D) (k : TwCoverPair Λ.rec') : Ties Λ.rec' := { h with bu_def := buDefQ_eta Λ h.bu_def, tw_cover := k }

set_option smartUnfolding false in
theorem rrDefTr (h : DV.RRDef D) : DV.RRDef Λ.rec' := by
  have e : (rowsEta D.what₂ Λ.η Λ.hη).RRset = D.what₂.RRset := by
    first
      | rfl
      | with_unfolding_all rfl
  intro x
  have := h x
  rw [← e] at this
  exact this

end UpperTheory.GalC.Gen
end
end

section
noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)

set_option maxHeartbeats 1600000

@[reducible] def sideTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) :
    RowSide (cut D Λ) EE := { S with }

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem downTo_tr (μ : D.what₂.Tup) (j : ℕ) : (sideTr Λ S).downTo μ j = S.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun f => f.comp (S.io μ j)) ih

theorem iota_tr (μ : D.what₂.Tup) : (sideTr Λ S).iota μ = S.iota μ := by
  unfold RowSide.iota; rw [downTo_tr]; rfl

theorem Qsp_tr (μ : D.what₂.Tup) : (sideTr Λ S).Qsp μ = S.Qsp μ := by
  unfold RowSide.Qsp RowSide.Usp; rw [iota_tr]; rfl

theorem RRset_tr (μ : D.what₂.Tup) : (sideTr Λ S).RRset μ = S.RRset μ := by
  unfold RowSide.RRset RowSide.LamSet; rw [iota_tr]; simp only [Qsp_tr]; rfl

theorem iiStar_tr : (sideTr Λ S).iiStar = S.iiStar := by
  have key : ∀ (f f' : S.Amb D.what₂.mu0 →ₗ[ℂ] EE) (Q Q' : Submodule ℂ (S.Amb D.what₂.mu0)), f = f' → Q = Q' →
      f.domRestrict Q ∘ₗ LinearMap.adjoint (f.domRestrict Q) = f'.domRestrict Q' ∘ₗ LinearMap.adjoint (f'.domRestrict Q') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact key _ _ _ _ (iota_tr Λ S _) (Qsp_tr Λ S _)

theorem kapOf_tr {n : ℕ} (ty : Fin n → D.what₂.FT) : (sideTr Λ S).kapOf ty = S.kapOf ty := by
  unfold RowSide.kapOf RowSide.kapRatio; rw [iiStar_tr]; rfl

theorem rrDef_tr (H : S.RRDef) : (sideTr Λ S).RRDef := by
  have e : (sideTr Λ S).RRset = S.RRset := funext (RRset_tr Λ S)
  unfold RowSide.RRDef; rw [e]; exact H

end Side

theorem kapSharp_tr : kapSharp (cut D Λ) = kapSharp D := kapOf_tr Λ (RowSide.sharp D) _

def ambTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (x : AmbForm D S) :
    AmbForm (cut D Λ) (sideTr Λ S) := { x with }

end UpperTheory.GalC
end
end

section
noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)

set_option maxHeartbeats 1600000

@[reducible] def nchTr (x : NChoice D) : NChoice (cut D Λ) := { x with }

@[reducible] def xdTr (x : ThData D) : ThData (cut D Λ) := { x with }

theorem nchTie_tr {x : NChoice D} (H : NChTie D x) : NChTie (cut D Λ) (nchTr Λ x) :=
  { H with
    twOf_eq := fun a => H.twOf_eq a.1
    twSide_eq := fun a => H.twSide_eq a.1
    Q_eq := fun a => H.Q_eq a.1
    psi_eq := H.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

theorem sLen_tr (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))) (ψ : BlochKatoReduction.Gen.GE D.nd →* (D.ntw.Ok i k)ˣ) :
    BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 (cut D Λ)) i s k Q ψ = BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ := by
  delta BlochKatoReduction.Gen.sLen BlochKatoReduction.Gen.selT BlochKatoReduction.Gen.bk BlochKatoReduction.Gen.Trep BlochKatoReduction.Gen.Tgl BlochKatoReduction.Gen.IsImgK BlochKatoReduction.Gen.IsFrac BlochKatoReduction.Gen.phiK BlochKatoReduction.Gen.chiS BlochKatoReduction.Gen.Spl BlochKatoReduction.bk0 BlochKatoReduction.Gen.PDv BlochKatoReduction.Gen.repV BlochKatoReduction.Gen.DecV BlochKatoReduction.Gen.GE
  dsimp +instances only [cut, GlobalTheory.HeightCounting.setRaw, GlobalTheory.HeightCounting.NLay0.reEta, layCut, ndCut, GlobalTheory.HeightCounting.rowsEta]
  congr 1

theorem twAt_tr {x : NChoice D} {y : ThData D} (H : LocalQuadraticParts.TWAt D x y) : LocalQuadraticParts.TWAt (cut D Λ) (nchTr Λ x) (xdTr Λ y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr Λ _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

end UpperTheory.GalC
end
end

section
noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (c : CutD D)

def raw : Gen.Raw D :=
  ⟨(layCut D c).eta, (layCut D c).eta_nonneg, (layCut D c).reEta _ (layCut D c).eta_nonneg, (layerCut_admissible D c).reEta _ _,
    (layCut D c).etaOk_reEta⟩

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ (cut D c) := Gen.ledTr (raw c) L

theorem tiesTr (h : Ties D) : Ties (raw c).rec' := Gen.tiesTr (raw c) h h.tw_cover

set_option maxHeartbeats 1600000 in

def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) :
    Extra (raw c).rec' (Gen.ledTr (raw c) L) (Gen.gatTr (raw c) gatT) (Gen.instTr (raw c) Gx) (Gen.latTr (raw c) Gy) K
      (Gen.divTr (raw c) X) cX :=
  Gen.extraTr (raw c) ex (nchTr c ex.nch) (nchTie_tr c ex.nch_tie) (xdTr c ex.xd)
    (show BaseLevelRowSide (cut D c) from ⟨sideTr c ex.p0.s⟩) (rrDef_tr c _ ex.rationalRoots_def) (ambTr c ex.amb) (ambTr c ex.amb0) (kapSharp_tr c)

end UpperTheory.GalC
end
end

section
noncomputable section

namespace UpperTheory.GalC.Alg

open Formalism.BasicNotions TensorProduct

theorem length_le_of_span {O Q C : Type} [CommRing O] [AddCommGroup Q] [Module O Q] [AddCommGroup C] [Module O C] {m : ℕ}
    (b : Fin m → Q) (hb : Submodule.span O (Set.range b) = ⊤) (π : Q →ₗ[O] C) (hπ : Function.Surjective π) (A : O)
    (hA : ∀ q, A • π q = 0) : Module.length O C ≤ m * Module.length O (O ⧸ Ideal.span {A}) := by
  classical
  have hI : ∀ i, (Ideal.span {A} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O C (π (b i))) := by
    intro i x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    simp [LinearMap.mem_ker, mul_smul, hA]
  let g : (Fin m → O ⧸ Ideal.span {A}) →ₗ[O] C :=
    ∑ i, ((Ideal.span {A} : Submodule O O).liftQ (LinearMap.toSpanSingleton O C (π (b i))) (hI i)).comp
      (LinearMap.proj i)
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨q, rfl⟩ := hπ c
    have hq : q ∈ Submodule.span O (Set.range b) := hb ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hq
    refine ⟨fun i => Submodule.Quotient.mk (r i), ?_⟩
    simp [g, ← hr, map_sum, map_smul]
    exact Finset.sum_congr rfl fun i _ => rfl
  calc Module.length O C ≤ Module.length O (Fin m → O ⧸ Ideal.span {A}) := Module.length_le_of_surjective g hg
    _ = m * Module.length O (O ⧸ Ideal.span {A}) := by simp

variable {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X)
  [Fintype X] (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y)

include hs in
theorem decomp : ∃ (f : X → T) (d : O), d ≠ 0 ∧ (∀ x y, y ≠ x → (f x : X → O) y = 0) ∧
    ∀ v : FractionRing O ⊗[O] M, d • v = ∑ x, (act (f x)).baseChange (FractionRing O) v := by
  classical
  choose f hf0 hf1 using exists_sep T hs
  set d : O := ∏ x, (f x : X → O) x with hd
  let g : X → T := fun x => (∏ y ∈ Finset.univ.erase x, (f y : X → O) y) • f x
  have hg0 : ∀ x y, y ≠ x → (g x : X → O) y = 0 := by
    intro x y hyx
    simp [g, hf1 x y hyx]
  have hsum : (∑ x, g x) = d • (1 : T) := by
    apply Subtype.ext
    funext z
    simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      OneMemClass.coe_one, Pi.one_apply, mul_one]
    rw [Finset.sum_eq_single z]
    · simp only [g, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
      rw [hd, Finset.prod_erase_mul _ _ (Finset.mem_univ z)]
    · intro x _ hxz
      exact hg0 x z (Ne.symm hxz)
    · intro h
      exact absurd (Finset.mem_univ z) h
  refine ⟨g, d, ?_, hg0, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun x _ => hf0 x
  · intro v
    have hlin : ∀ s : Finset X, ∑ x ∈ s, (act (g x)).baseChange (FractionRing O) v =
        (act (∑ x ∈ s, g x)).baseChange (FractionRing O) v := by
      intro s
      refine Finset.induction_on s (by simp) ?_
      intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, map_add, LinearMap.baseChange_add, LinearMap.add_apply]
    rw [hlin, hsum, map_smul, map_one, LinearMap.baseChange_smul, LinearMap.smul_apply]
    simp

include hs in

theorem qK_eq_zero_iff {v : FractionRing O ⊗[O] M} : qK T act S v = 0 ↔ v ∈ ⨆ x ∈ Sᶜ, heckeEig T act x := by
  constructor
  · intro hv
    obtain ⟨g, d, hd, hg0, hdec⟩ := decomp T act hs
    have hdv : (algebraMap O (FractionRing O) d) • v ∈ ⨆ x ∈ Sᶜ, heckeEig T act x := by
      rw [algebraMap_smul, hdec v]
      refine Submodule.sum_mem _ fun x _ => ?_
      by_cases hx : x ∈ S
      · rw [act_eq_zero_of_qK T act S hv (g x) (fun y hy => hg0 x y (fun h => hy (by rw [h]; exact hx)))]
        exact Submodule.zero_mem _
      · exact (le_iSup₂ (f := fun x (_ : x ∈ Sᶜ) => heckeEig T act x) x hx) (sep_mem T act (hg0 x) v)
    have hd' : algebraMap O (FractionRing O) d ≠ 0 := by
      simpa using (IsFractionRing.injective O (FractionRing O)).ne hd
    have := Submodule.smul_mem _ (algebraMap O (FractionRing O) d)⁻¹ hdv
    rwa [smul_smul, inv_mul_cancel₀ hd', one_smul] at this
  · intro hv
    refine (iSup₂_le (fun x hx => ?_) : (⨆ x ∈ Sᶜ, heckeEig T act x) ≤ LinearMap.ker (qK T act S)) hv
    intro u hu
    exact qK_out T act S hs hx hu

abbrev inL (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] : Submodule O (FractionRing O ⊗[O] M) :=
  LinearMap.range (TensorProduct.mk O (FractionRing O) M 1)

abbrev upL (Y : Set X) : Submodule O (FractionRing O ⊗[O] M) :=
  (⨆ x ∈ Y, heckeEig T act x).restrictScalars O ⊓ (inL O M ⊔ (⨆ x ∈ Yᶜ, heckeEig T act x).restrictScalars O)

abbrev lowL (Y : Set X) : Submodule O (FractionRing O ⊗[O] M) := inL O M ⊓ (⨆ x ∈ Y, heckeEig T act x).restrictScalars O

include hs in
theorem map_sum_le (Y : Set X) (Y' : Set S) (h : ∀ x : S, x.1 ∈ Y → x ∈ Y') {v : FractionRing O ⊗[O] M}
    (hv : v ∈ ⨆ x ∈ Y, heckeEig T act x) : qK T act S v ∈ ⨆ x ∈ Y', heckeEig (cutT T S) (cutAct T act S) x := by
  have key : (⨆ x ∈ Y, heckeEig T act x) ≤
      (⨆ x ∈ Y', heckeEig (cutT T S) (cutAct T act S) x).comap (qK T act S) := by
    refine iSup₂_le fun x hx => ?_
    intro u hu
    rw [Submodule.mem_comap]
    by_cases hxS : x ∈ S
    · exact (le_iSup₂ (f := fun (z : S) (_ : z ∈ Y') => heckeEig (cutT T S) (cutAct T act S) z) ⟨x, hxS⟩
        (h ⟨x, hxS⟩ hx)) (qK_mem T act S (x := ⟨x, hxS⟩) hu)
    · rw [qK_out T act S hs hxS hu]
      exact Submodule.zero_mem _
  exact key hv

omit [Fintype X] in
theorem finrank_sum_le [Module.Finite O M] (Z : Finset X) :
    Module.finrank (FractionRing O) ↥(⨆ x ∈ (Z : Set X), heckeEig T act x) ≤ ∑ x ∈ Z, heckeMult T act x := by
  classical
  unfold heckeMult
  refine Finset.induction_on Z (by simp) ?_
  intro a s ha ih
  rw [Finset.coe_insert, iSup_insert, Finset.sum_insert ha]
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

private theorem exists_ne_zero_smul_upL_mem_lowL (hs' : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (Y : Set X) :
    ∃ d : O, d ≠ 0 ∧ ∀ u ∈ upL T act Y, d • u ∈ lowL T act Y := by
  classical
  obtain ⟨g, d, hd, hg0, hdec⟩ := decomp T act hs'
  refine ⟨d, hd, fun u hu => ?_⟩
  have hkill : ∀ (W : Set X) x, x ∉ W → ∀ w ∈ ⨆ y ∈ W, heckeEig T act y,
      (act (g x)).baseChange (FractionRing O) w = 0 := by
    intro W x hx w hw
    have hle : (⨆ y ∈ W, heckeEig T act y) ≤ LinearMap.ker ((act (g x)).baseChange (FractionRing O)) := by
      refine iSup₂_le fun y hy => ?_
      intro z hz
      rw [LinearMap.mem_ker, (mem_eig T act).mp hz (g x), hg0 x y (fun h => hx (by rw [← h]; exact hy)),
        map_zero, zero_smul]
    exact hle hw
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.mp hu2
  obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hl
  rw [hdec u]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : x ∈ Y
  · have hw0 : (act (g x)).baseChange (FractionRing O) w = 0 := hkill Yᶜ x (fun h => h hx) w hw
    have hux : (act (g x)).baseChange (FractionRing O) u = (1 : FractionRing O) ⊗ₜ[O] (act (g x) m) := by
      rw [← hlw, map_add, hw0, add_zero, TensorProduct.mk_apply, LinearMap.baseChange_tmul]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hux]
      exact LinearMap.mem_range.mpr ⟨act (g x) m, rfl⟩
    · exact (le_iSup₂ (f := fun y (_ : y ∈ Y) => heckeEig T act y) x hx) (sep_mem T act (hg0 x) u)
  · rw [hkill Y x hx u hu1]
    exact Submodule.zero_mem _

private theorem isNoetherian_upL [IsNoetherianRing O] [Module.Finite O M]
    (hs' : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (Y : Set X) :
    IsNoetherian O ↥(upL T act Y) := by
  obtain ⟨d, hd, hdu⟩ := exists_ne_zero_smul_upL_mem_lowL T act hs' Y
  haveI hL : IsNoetherian O ↥(inL O M) :=
    isNoetherian_of_surjective (LinearMap.rangeRestrict (TensorProduct.mk O (FractionRing O) M 1))
      (LinearMap.range_rangeRestrict _)
  let ψ : ↥(upL T act Y) →ₗ[O] ↥(inL O M) :=
    LinearMap.codRestrict (inL O M) (d • (upL T act Y).subtype) (fun u => (Submodule.mem_inf.mp (hdu u u.2)).1)
  refine isNoetherian_of_injective ψ ?_
  intro u v huv
  have h1 : d • ((u : FractionRing O ⊗[O] M) - v) = 0 := by
    have this : d • (u : FractionRing O ⊗[O] M) = d • (v : FractionRing O ⊗[O] M) := congrArg Subtype.val huv
    rw [smul_sub, this, sub_self]
  rw [← algebraMap_smul (FractionRing O), smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd ((IsFractionRing.injective O (FractionRing O)).eq_iff.mp (h1.trans (map_zero _).symm)) hd
  · exact Subtype.ext (sub_eq_zero.mp h1)

private theorem smul_eq_of_mem_iSup_heckeEig_of_forall_eigen (Y : Set X)
    (φ : FractionRing O ⊗[O] M →ₗ[FractionRing O] FractionRing O ⊗[O] M) (c : FractionRing O)
    (h : ∀ x ∈ Y, ∀ u ∈ heckeEig T act x, φ u = c • u) {u : FractionRing O ⊗[O] M}
    (hu : u ∈ ⨆ x ∈ Y, heckeEig T act x) : φ u = c • u := by
  have hle : (⨆ x ∈ Y, heckeEig T act x) ≤ LinearMap.ker (φ - c • LinearMap.id) := by
    refine iSup₂_le fun x hx => ?_
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, h x hx w hw, sub_self]
  have := hle hu
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at this

set_option maxHeartbeats 1000000 in
include hs in
theorem length_le [IsPrincipalIdealRing O] [Module.Finite O M] (Z : Finset X) (Y' : Set S) (hY : ∀ x : S, x ∈ Y' ↔ x.1 ∈ Z)
    (α : Module.End O M) (A : O) (hA : A ≠ 0)
    (h1 : ∀ x ∈ Z, ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = A • u)
    (h0 : ∀ x, x ∉ S → ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = 0) :
    Module.length O (↥(upL T act (Z : Set X)) ⧸ (lowL T act (Z : Set X)).comap (upL T act (Z : Set X)).subtype) ≤
      Module.length O (↥(upL (cutT T S) (cutAct T act S) Y') ⧸
        (lowL (cutT T S) (cutAct T act S) Y').comap (upL (cutT T S) (cutAct T act S) Y').subtype) +
      (∑ x ∈ Z, heckeMult T act x : ℕ) * Module.length O (O ⧸ Ideal.span {A}) := by
  classical
  haveI : IsNoetherian O ↥(upL T act (Z : Set X)) := isNoetherian_upL T act hs _
  have hY1 : ∀ x : S, x.1 ∈ (Z : Set X) → x ∈ Y' := fun x hx => (hY x).mpr hx
  have hY2 : ∀ x : S, x.1 ∈ (Z : Set X)ᶜ → x ∈ Y'ᶜ := fun x hx hx' => hx ((hY x).mp hx')
  have hqL : ∀ l ∈ inL O M, qK T act S l ∈ inL O (cutM T act S) := by
    intro l hl
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hl
    exact LinearMap.mem_range.mpr ⟨(outM T act S).mkQ m, by simp only [TensorProduct.mk_apply, qK_tmul]⟩
  have hup : ∀ u ∈ upL T act (Z : Set X), qK T act S u ∈ upL (cutT T S) (cutAct T act S) Y' := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
    refine Submodule.mem_inf.mpr ⟨map_sum_le T act S hs (Z : Set X) Y' hY1 hu1, ?_⟩
    obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.mp hu2
    rw [map_add]
    exact Submodule.add_mem_sup (hqL l hl) (map_sum_le T act S hs (Z : Set X)ᶜ Y'ᶜ hY2 hw)
  have hlow : ∀ u ∈ lowL T act (Z : Set X), qK T act S u ∈ lowL (cutT T S) (cutAct T act S) Y' := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
    exact Submodule.mem_inf.mpr ⟨hqL u hu1, map_sum_le T act S hs (Z : Set X) Y' hY1 hu2⟩
  let U := upL T act (Z : Set X)
  let Lo := (lowL T act (Z : Set X)).comap U.subtype
  let U' := upL (cutT T S) (cutAct T act S) Y'
  let Lo' := (lowL (cutT T S) (cutAct T act S) Y').comap U'.subtype
  let Φ0 : ↥U →ₗ[O] ↥U' :=
    LinearMap.codRestrict U' (((qK T act S).restrictScalars O).comp U.subtype) (fun u => hup u u.2)
  have hΦ0 : Lo ≤ Lo'.comap Φ0 := fun u hu => hlow u hu
  let Φ : (↥U ⧸ Lo) →ₗ[O] (↥U' ⧸ Lo') := Lo.mapQ Lo' Φ0 hΦ0
  have hexact : Function.Exact (LinearMap.ker Φ).subtype Φ.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hex := Module.length_eq_add_of_exact (LinearMap.ker Φ).subtype Φ.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.surjective_rangeRestrict Φ) hexact
  have hran : Module.length O ↥(LinearMap.range Φ) ≤ Module.length O (↥U' ⧸ Lo') :=
    Module.length_le_of_injective (LinearMap.range Φ).subtype (Submodule.subtype_injective _)
  have hKA : ∀ k ∈ LinearMap.ker Φ, A • k = 0 := by
    intro k hk
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Lo k
    have hk' : Lo'.mkQ (Φ0 u) = 0 := LinearMap.mem_ker.mp hk
    have hq : Φ0 u ∈ Lo' := (Submodule.Quotient.mk_eq_zero _).mp hk'
    have hu1 : (u : FractionRing O ⊗[O] M) ∈ ⨆ x ∈ (Z : Set X), heckeEig T act x := (Submodule.mem_inf.mp u.2).1
    obtain ⟨hqL', -⟩ := Submodule.mem_inf.mp hq
    obtain ⟨m', hm⟩ := LinearMap.mem_range.mp hqL'
    obtain ⟨m0, rfl⟩ := Submodule.mkQ_surjective _ m'
    have hz : qK T act S ((u : FractionRing O ⊗[O] M) - (1 : FractionRing O) ⊗ₜ[O] m0) = 0 := by
      have hm2 : qK T act S (u : FractionRing O ⊗[O] M) = (1 : FractionRing O) ⊗ₜ[O] (outM T act S).mkQ m0 := hm.symm
      rw [map_sub, qK_tmul, hm2, sub_self]
    have hw := (qK_eq_zero_iff T act S hs).mp hz
    have hα1 : α.baseChange (FractionRing O) (u : FractionRing O ⊗[O] M) = A • (u : FractionRing O ⊗[O] M) := by
      have := smul_eq_of_mem_iSup_heckeEig_of_forall_eigen T act (Z : Set X) (α.baseChange (FractionRing O)) (algebraMap O (FractionRing O) A)
        (fun x hx w hw => by rw [h1 x hx w hw, algebraMap_smul]) hu1
      rwa [algebraMap_smul] at this
    have hα0 := smul_eq_of_mem_iSup_heckeEig_of_forall_eigen T act Sᶜ (α.baseChange (FractionRing O)) 0
        (fun x hx w hw => by rw [h0 x hx w hw, zero_smul]) hw
    have hAu : A • (u : FractionRing O ⊗[O] M) = (1 : FractionRing O) ⊗ₜ[O] α m0 := by
      rw [zero_smul, map_sub, sub_eq_zero, LinearMap.baseChange_tmul] at hα0
      rw [← hα1, hα0]
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show A • (u : FractionRing O ⊗[O] M) ∈ lowL T act (Z : Set X)
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hAu]
      exact LinearMap.mem_range.mpr ⟨α m0, rfl⟩
    · show A • (u : FractionRing O ⊗[O] M) ∈ ⨆ x ∈ (Z : Set X), heckeEig T act x
      rw [← algebraMap_smul (FractionRing O)]
      exact Submodule.smul_mem _ _ hu1
  have hK : Module.length O ↥(LinearMap.ker Φ) ≤
      (∑ x ∈ Z, heckeMult T act x : ℕ) * Module.length O (O ⧸ Ideal.span {A}) := by
    let P : Submodule O ↥U := (LinearMap.ker Φ).comap Lo.mkQ
    let π : ↥P →ₗ[O] ↥(LinearMap.ker Φ) := Lo.mkQ.restrict (fun x hx => hx)
    have hπ : Function.Surjective π := by
      intro k
      obtain ⟨y, hy⟩ := Submodule.mkQ_surjective Lo k.1
      exact ⟨⟨y, show Lo.mkQ y ∈ LinearMap.ker Φ from hy ▸ k.2⟩, Subtype.ext hy⟩
    have hA' : ∀ q, A • π q = 0 := fun q => Subtype.ext (hKA (Lo.mkQ q) q.2)
    haveI hV : Module.IsTorsionFree O (FractionRing O ⊗[O] M) :=
      Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) _
    haveI : Module.IsTorsionFree O ↥P :=
      Function.Injective.moduleIsTorsionFree (fun p : P => ((p : ↥U) : FractionRing O ⊗[O] M))
        (fun a b hab => Subtype.ext (Subtype.ext hab)) (fun r p => rfl)
    haveI : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    let b := Module.finBasis O ↥P
    have hlen := length_le_of_span (fun i => b i) b.span_eq π hπ A hA'
    have hr : Module.finrank O ↥P ≤ ∑ x ∈ Z, heckeMult T act x := by
      have hinj : LinearMap.ker (U.subtype ∘ₗ P.subtype) = ⊥ :=
        LinearMap.ker_eq_bot.mpr (fun a c hac => Subtype.ext (Subtype.ext hac))
      have hv := b.linearIndependent.map' (U.subtype ∘ₗ P.subtype) hinj
      have hv' := hv.localization (FractionRing O) (nonZeroDivisors O)
      have hsub : Submodule.span (FractionRing O) (Set.range ((U.subtype ∘ₗ P.subtype) ∘ b)) ≤ ⨆ x ∈ (Z : Set X), heckeEig T act x := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (Submodule.mem_inf.mp (b i : ↥U).2).1
      calc Module.finrank O ↥P = Fintype.card (Fin (Module.finrank O ↥P)) := (Fintype.card_fin _).symm
        _ = Module.finrank (FractionRing O) ↥(Submodule.span (FractionRing O) (Set.range ((U.subtype ∘ₗ P.subtype) ∘ b))) :=
          (finrank_span_eq_card hv').symm
        _ ≤ Module.finrank (FractionRing O) ↥(⨆ x ∈ (Z : Set X), heckeEig T act x) := Submodule.finrank_mono hsub
        _ ≤ ∑ x ∈ Z, heckeMult T act x := finrank_sum_le T act Z
    refine hlen.trans ?_
    have hr' : (Module.finrank O ↥P : ℕ∞) ≤ ((∑ x ∈ Z, heckeMult T act x : ℕ) : ℕ∞) := Nat.cast_le.mpr hr
    exact mul_le_mul_of_nonneg_right hr' zero_le
  rw [hex, add_comm]
  exact add_le_add hran hK

include hs in
theorem length_ne_top [IsDiscreteValuationRing O] [Module.Finite O M] (Z : Finset X) :
    Module.length O (↥(upL T act (Z : Set X)) ⧸ (lowL T act (Z : Set X)).comap (upL T act (Z : Set X)).subtype) ≠ ⊤ := by
  classical
  haveI : IsNoetherian O ↥(upL T act (Z : Set X)) := isNoetherian_upL T act hs _
  obtain ⟨d, hd, hdu⟩ := exists_ne_zero_smul_upL_mem_lowL T act hs (Z : Set X)
  obtain ⟨k, b, hb⟩ := Module.Finite.exists_fin (R := O) (M := ↥(upL T act (Z : Set X)))
  have hle := length_le_of_span b hb ((lowL T act (Z : Set X)).comap (upL T act (Z : Set X)).subtype).mkQ
    (Submodule.mkQ_surjective _) d (fun q => by
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hdu q q.2)
  have hfin : Module.length O (O ⧸ Ideal.span {d}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hd))
  exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.coe_ne_top k) hfin) hle

theorem lenUnit_le_add {O : Type} [CommRing O] (l : ℕ) {B C E : Type} [AddCommGroup B] [Module O B] [AddCommGroup C] [Module O C]
    [AddCommGroup E] [Module O E] (n : ℕ) (hE : Module.length O E ≠ ⊤) (hB : Module.length O C = ⊤ → Module.length O B = ⊤)
    (h : Module.length O B ≤ Module.length O C + n * Module.length O E) :
    lenUnit (O := O) l B ≤ lenUnit (O := O) l C + n * lenUnit (O := O) l E := by
  unfold lenUnit
  have key : ((Module.length O B).toNat : ℚ) ≤ (Module.length O C).toNat + n * (Module.length O E).toNat := by
    by_cases hC : Module.length O C = ⊤
    · rw [hB hC]
      simp only [ENat.toNat_top, Nat.cast_zero]
      positivity
    · obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hC
      obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hE
      rw [← hc, ← he] at h
      have h' : Module.length O B ≤ ((c + n * e : ℕ) : ℕ∞) := by
        push_cast
        exact h
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) h')
      rw [← hk] at h'
      rw [← hk, ← hc, ← he]
      simp only [ENat.toNat_coe]
      have := ENat.coe_le_coe.mp h'
      exact_mod_cast this
  rw [mul_div_assoc', ← add_div]
  gcongr

end UpperTheory.GalC.Alg
end
end

section
noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting Alg TensorProduct

variable {D : D7} {c : CutD D}

theorem mem_Zgood {i : (cut D c).nd.Loc} {x : (cut D c).nd.X i} : x ∈ (cut D c).nd.Zgood i ↔ x.1 ∈ D.nd.Zgood i.1 := by
  classical
  exact Finset.mem_subtype

theorem mem_ZgoodN {i : (cut D c).nd.Loc} {x : (cut D c).nd.X i} :
    x ∈ ZgoodN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZgoodN D.nd D.naut i.1 :=
  ((cut D c).Zgood_tie i x).symm.trans (mem_Zgood.trans (D.Zgood_tie i.1 x.1))

theorem CutD.Good.hG (h : c.Good) (i : (cut D c).nd.Loc) : HG (cut D c).nd (cut D c).naut i := by
  obtain ⟨x, hx⟩ := (h.keep i.1).1 i.2
  exact ⟨⟨x, h.good _ x hx⟩, mem_ZgoodN.2 ((D.Zgood_tie i.1 x).1 hx)⟩

theorem eta_le (h : c.Good) (i : (cut D c).nd.Loc) : D.nd.etaLoc i.1 ≤ (cut D c).nd.etaLoc i +
    (∑ x ∈ D.nd.Zgood i.1, D.nd.mult i.1 x : ℕ) * (padicValNat (D.nd.l i.1) D.what₂.restRowsFiniteGroupCard : ℚ) := by
  classical
  obtain ⟨α, -, hα1, hα2⟩ := h.op i.1 i.2
  have hn : D.what₂.restRowsFiniteGroupCard ≠ 0 := (D.what₂.restRowsFiniteGroupCard_pos).ne'
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) ≠ 0 := by
    intro hz
    have h1 : ((D.what₂.restRowsFiniteGroupCard : D.what₂.LL) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h2 : D.nd.embK i.1 (D.what₂.restRowsFiniteGroupCard : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i.1) (FractionRing (D.nd.O i.1))), hz, map_zero]
    exact h1 ((map_eq_zero_iff _ (D.nd.embK i.1).injective).mp h2)
  have hα1' : ∀ x ∈ D.nd.Zgood i.1, ∀ u ∈ heckeEig (D.nd.T i.1) (D.nd.act i.1) x,
      (LinearMap.baseChange (FractionRing (D.nd.O i.1)) α) u = ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) • u := by
    intro x hx u hu
    rw [hα1 x hx u hu, Int.cast_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hY : ∀ x : ↥(c.Xs i.1), x ∈ (((cut D c).nd.Zgood i : Finset ((cut D c).nd.X i)) : Set ((cut D c).nd.X i)) ↔
      (x : D.nd.X i.1) ∈ D.nd.Zgood i.1 :=
    fun x => Iff.trans Finset.mem_coe mem_Zgood
  have key := Alg.length_le (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (D.nd.Zgood i.1) _ hY α _ hA hα1' hα2
  have hfinE : Module.length (D.nd.O i.1) (D.nd.O i.1 ⧸ Ideal.span {((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1)}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hA))
  have hpad := GlobalTheory.CutAtGood.lenUnit_natCast_le i.1 D.what₂.restRowsFiniteGroupCard hn
  refine (Alg.lenUnit_le_add (D.nd.l i.1) _ hfinE (fun hC => absurd hC ?_) key).trans ?_
  · exact Alg.length_ne_top ((cut D c).nd.T i) ((cut D c).nd.act i) ((cut D c).nd.T_sep i) ((cut D c).nd.Zgood i)
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpad (Nat.cast_nonneg _))

theorem eta_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.Zgood i = ∅) :
    N.etaLoc i = 0 := by
  have hsum : N.eigSum i ↑(N.Zgood i) = ⊥ := by
    rw [h]
    simp [NData.eigSum]
  have hup : N.MtUp i = ⊥ := by
    simp [NData.MtUp, hsum]
  have hsub : Subsingleton (N.MtUp i) := by
    rw [hup]
    infer_instance
  have hq : Subsingleton (↥(N.MtUp i) ⧸ Submodule.comap (N.MtUp i).subtype (N.MtLow i)) := by
    infer_instance
  unfold NData.etaLoc lenUnit
  rw [Module.length_eq_zero]
  simp

theorem etaJ_le (h : c.Good) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (D.what₂.etaJ j w : ℝ) ≤ ((cut D c).what₂.etaJ j w : ℝ) +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℝ) := by
  classical
  let F : D.nd.Loc → ℚ := fun i => if hk : c.keep i then (cut D c).nd.etaLoc (⟨i, hk⟩ : (cut D c).nd.Loc) else 0
  have hcut : (cut D c).what₂.etaJ j w = ∑ i ∈ D.nd.locs j w, F i := by
    rw [(cut D c).etaJ_tie j w h1 h2]
    show ∑ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = _
    have hF : ∀ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = F i.1 := by
      intro i _
      simp only [F, dif_pos i.2]
    rw [Finset.sum_congr rfl hF, Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_filter_of_ne ?_
    intro i _ hne
    by_contra hk
    exact hne (dif_neg hk)
  have hD := D.etaJ_tie j w h1 h2
  have hpt : ∀ i ∈ D.nd.locs j w, D.nd.etaLoc i ≤ F i +
      (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) * (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    intro i hi
    have hw : D.nd.w i = w := ((D.nd.locs_mem j w i).mp hi).2
    have hl : D.what₂.places.resChar w = D.nd.l i := by
      rw [← hw]
      exact D.nd.w_l i
    rw [hl]
    by_cases hk : c.keep i
    · have hb := eta_le h (⟨i, hk⟩ : (cut D c).nd.Loc)
      simp only [F, dif_pos hk]
      push_cast at hb
      exact hb
    · have hz : D.nd.Zgood i = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        exact fun hne => hk ((h.keep i).mpr hne)
      rw [eta_zero D.nd i hz]
      simp only [F, dif_neg hk, zero_add]
      positivity
  have hQ : D.what₂.etaJ j w ≤ (cut D c).what₂.etaJ j w +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    rw [hD, hcut, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  exact_mod_cast hQ

end UpperTheory.GalC
end
end

section
noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField

theorem lw_ram_nonneg (D : D7) (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
  refine mul_nonneg ?_ (Nat.cast_nonneg _)
  unfold SizeData₂.lwP lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

open Classical in
theorem sum_val_le {D : D7} (L : SizeData₂ D) (N : ℕ) (hN : N ≠ 0) :
    ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) ≤ Real.log N := by
  have h1 : Real.log N = ∑ l ∈ N.primeFactors, (padicValNat l N : ℝ) * Real.log l := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not _ (fun w => D.what₂.places.resChar w ∈ N.primeFactors)]
  have h0 : ∑ w ∈ (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).filter
      (fun w => ¬ D.what₂.places.resChar w ∈ N.primeFactors),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    have h2 := (Finset.mem_filter.1 hw).2
    have h3 : ¬ D.what₂.places.resChar w ∣ N := fun h =>
      h2 (Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, h, hN⟩)
    rw [padicValNat.eq_zero_of_not_dvd h3]; simp
  rw [h0, add_zero, ← Finset.sum_fiberwise_of_maps_to (g := fun w => D.what₂.places.resChar w) (t := N.primeFactors)
    (fun w hw => (Finset.mem_filter.1 hw).2)]
  refine Finset.sum_le_sum fun l hl => ?_
  have hm := TwistedPlaces.admissibleMeanCondition_holds L l (Nat.prime_of_mem_primeFactors hl)
  calc _ = (padicValNat l N : ℝ) * ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr ?_ fun w hw => ?_
        · ext w
          simp only [Finset.mem_filter, TwistedPlaces.mem_twAt, TwistedPlaces.TwPl]
          constructor
          · rintro ⟨⟨⟨a, b⟩, -⟩, e⟩; exact ⟨a, b, e⟩
          · rintro ⟨a, b, e⟩; exact ⟨⟨⟨a, b⟩, e ▸ hl⟩, e⟩
        · rw [(TwistedPlaces.mem_twAt.1 hw).2.2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)

open Classical in
theorem etaSum_le_add {D : D7} (L : SizeData₂ D) (j : ℕ) (η : D.what₂.places.Pl → ℝ) (d : ℝ) (hd : 0 ≤ d) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      (D.what₂.etaJ j w : ℝ) ≤ η w + d * (padicValNat (D.what₂.places.resChar w) N : ℝ)) :
    Formalism.MainNotions.etaSum L j ≤ (∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * η w) + d * Real.log N := by
  refine le_trans ?_ (add_le_add_right (mul_le_mul_of_nonneg_left (sum_val_le L N hN) hd) _)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  have := mul_le_mul_of_nonneg_left (h w (Finset.mem_filter.1 hw).2) (lw_ram_nonneg D w)
  linarith

theorem ev_pow_le_exp (C eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x ≥ x0, x ^ C ≤ Real.exp (x ^ eps) ∧ 1 ≤ x ^ eps := by
  have h2 := ((isLittleO_log_rpow_atTop he).const_mul_left C).bound one_pos
  obtain ⟨x0, h⟩ := Filter.eventually_atTop.1 (h2.and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a, b⟩ := h x hx
  have x0' : 0 < x := by linarith
  refine ⟨?_, Real.one_le_rpow b he.le⟩
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg x0'.le _), Real.norm_eq_abs] at a
  rw [Real.rpow_def_of_pos x0', mul_comm]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans a)

end UpperTheory.GalC
end
end

section
noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField

variable {eps : ℝ}

set_option maxHeartbeats 800000 in

def gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i)) : FamP eps :=
  { Fm with
    D := fun x i => (raw (c x i)).rec'
    L := fun x i => Gen.ledTr (raw (c x i)) (Fm.L x i)
    params := fun x hx i => Gen.parTr (raw (c x i)) (Fm.params x hx i)
    parT := fun x hx i => Gen.parTTr (raw (c x i)) (Fm.parT x hx i)
    ties := fun x i => tiesTr (c x i) (Fm.ties x i)
    gatT := fun x i => Gen.gatTr (raw (c x i)) (Fm.gatT x i)
    X := fun x i => Gen.divTr (raw (c x i)) (Fm.X x i)
    Gx := fun x i => Gen.instTr (raw (c x i)) (Fm.Gx x i)
    Gy := fun x i => Gen.latTr (raw (c x i)) (Fm.Gy x i)
    fills := fun x hx i w => Gen.fills_tr (raw (c x i)) _ _ w (Fm.fills x hx i w)
    rrDef := fun x hx i => Gen.rrDefTr (raw (c x i)) (Fm.rrDef x hx i)
    ex := fun x hx i => extraTr (c x i) (Fm.ex x hx i) }

theorem twGood_gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i)) (h : TwGood Fm) : TwGood (gd Fm c) := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx0 hx i => twAt_tr (c x i) (h x hx0 hx i)⟩

open Classical in

theorem linkN_of_gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i))
    (hc : ∀ x, Fm.x1 < x → ∀ i, (c x i).Good ∧ GlobalTheory.NLink.MultLe (Fm.L x i) ∧ TwistedPlaces.adm3 (Fm.L x i))
    (h : LinkN (gd Fm c)) : LinkN Fm := by
  obtain ⟨C, x0, h⟩ := h
  obtain ⟨C1, x1, hC1, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨x2, hev⟩ := ev_pow_le_exp C1 eps he
  refine ⟨C + C1, max (max x0 x1) (max x2 (Fm.x1 + 1)), fun x hx i hS j hj hsum => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨a0, a1⟩, a2, a3⟩ := hx
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hg, hm, h3⟩ := hc x hx1 i
  have k := h x a0 i hS j hj hsum
  have hj' : 1 ≤ j ∧ j ≤ (Fm.D x i).R.m := Finset.mem_Icc.1 hj
  have hN : (Fm.D x i).what₂.restRowsFiniteGroupCard ≠ 0 := (Fm.D x i).what₂.restRowsFiniteGroupCard_pos.ne'
  have e := etaSum_le_add (Fm.L x i) j (fun w => ((cut (Fm.D x i) (c x i)).what₂.etaJ j w : ℝ)) ((Fm.L x i).dZ0 j)
    (Nat.cast_nonneg _) _ hN fun w hw => by
      refine (etaJ_le hg j w hj'.1 hj'.2).trans (add_le_add_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) _)
      have := hm j hj w hw
      rwa [h3 j hj w hw] at this
  have hlog : Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C1 * (Fm.L x i).sc.x ^ C1 * (Fm.L x i).sc.L :=
    (hpar x a1 hx1 i).2.2.2.2.2.2.2
  have ex : (Fm.L x i).sc.x = x := Fm.L_x x i (by linarith [Fm.one_lt_family_threshold])
  have ee : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hL : 1 ≤ (Fm.L x i).sc.L := by rw [Scale.L, ex, ee]; exact (hev x a2).2
  have hb : (Fm.L x i).sc.x ^ C1 ≤ (Fm.L x i).sc.b := by rw [Scale.b, Scale.L, ex, ee]; exact (hev x a2).1
  have hm1 : (1 : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj'.1.trans hj'.2
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := (Fm.D x i).R.m_le_f
    exact hm1.trans (by exact_mod_cast this)
  have hb0 : 0 ≤ (Fm.L x i).sc.b := (Real.exp_pos _).le
  have hNc : 0 ≤ Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ) := mul_nonneg (sq_nonneg _) (by
    have := (Fm.L x i).sc.one_lt_alt
    have x0 : 0 < (Fm.L x i).sc.x := by linarith
    unfold SizeData₂.Nc budgetNc rankBudget bSize
    positivity)
  have t1 : (Fm.L x i).sc.x ^ C1 * (Fm.L x i).sc.L ≤
      ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 := by
    have u1 : (1 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m := one_le_mul_of_one_le_of_one_le hf1 hm1
    have u2 : (Fm.L x i).sc.L ≤ (Fm.L x i).sc.L ^ 2 := by nlinarith
    calc _ ≤ (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 := mul_le_mul hb u2 (by linarith) hb0
      _ = 1 * ((Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2) := (one_mul _).symm
      _ ≤ _ := by rw [mul_assoc (_ * _)]; exact mul_le_mul_of_nonneg_right u1 (by positivity)
  have t2 : Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C1 * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b *
      (Fm.L x i).sc.L ^ 2 + Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ)) := by
    rw [mul_assoc] at hlog
    exact hlog.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have k' : (∑ w ∈ (Fm.L x i).supp.filter (fun w => (Fm.D x i).what₂.muAt w ≠ (Fm.D x i).what₂.mu0),
      SizeData₂.lwP w * ((Fm.D x i).what₂.places.ramIdx w : ℝ) * ((cut (Fm.D x i) (c x i)).what₂.etaJ j w : ℝ)) ≤
      ((Fm.L x i).dZ0 j : ℝ) * (C * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 +
        Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ)) + ∑' l, vvTerm (Fm.D x i) l) := k
  have t3 := mul_le_mul_of_nonneg_left t2 (Nat.cast_nonneg (α := ℝ) ((Fm.L x i).dZ0 j))
  refine e.trans ?_
  calc _ ≤ _ := add_le_add k' t3
    _ = _ := by ring

end UpperTheory.GalC
end
end
