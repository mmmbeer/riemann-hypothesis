import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsMuIsRamified
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotMtStableOfFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsParametersOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt

noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  have L : ∀ {C : FC} {K K' : TransportedAlt} {CH : ℝ}, C.Large (K.sup K') CH → C.Large K CH ∧ C.Large K' CH := fun h =>
    ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (L hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (L hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem ev_all {p : Ctx → Prop} (h : ∀ K, p K) : Ev p :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0,
    fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

theorem rowLay_iff {D : D7} (Y : Lay D) : RowLay D Y.p0 Y.X ↔ ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m →
    D.what₂.Ij D.what₂.mu0 j w = 0 ∧ D.what₂.jw D.what₂.mu0 j w = 0 :=
  ⟨fun h => h.untw, fun h => ⟨Y.rrDef, Y.rationalRoots_def, Y.kap_def, Y.lam_def, Y.ties.bu_def, Y.ties.ft_occ, h, Y.idx, Y.kapR_def⟩⟩

def coreOfLay {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} (Y : Lay X.toD7) (hO : K.Over X.B.toPre)
    (hR : RecOK K.s K.C K.cD X.toD7) (hL : LedOK K.s K.C K.cD K.ch Y K.a K.b)
    (xi : X.C.Tup → HChar X.B.host.E) (Wt : Set X.B.places.Pl) (mu : MuIsW X f T Wt xi)
    (forced : ∀ p : ℕ, p.Prime → ((∃ i, p = X.B.host.g i) ∨ p = X.B.host.d ∨ (p : ℝ) ≤ K.s.X'' X.B.R.n) → p ∈ T.pl)
    (gatNum : GatNum K.s X.toD7)
    (untw : ∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m →
      X.toD7.what₂.Ij X.toD7.what₂.mu0 j w = 0 ∧ X.toD7.what₂.jw X.toD7.what₂.mu0 j w = 0)
    (mt : DQ.MtStableAt X.toD7) (real : Formalism.L2.Theta.RealTied X.toD7)
    (dsig_eq : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ))
    (chiT : ∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
      ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1)))
    (nch_Q : ∀ w ∈ Wt, Y.nch.Q w = T.Q w ∧ Y.nch.k' w = T.k w) : Core K X f T where
  isOver := hO
  xi := xi
  Wt := Wt
  mu := mu
  forced := forced
  fval := fun L a b c w hw => (hL L a b c).1 w (mu.off w hw)
  O := layObj Y
  col := ⟨Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, fun u μ => (Y.dgam u μ).2, hR.mink, hR.atT⟩
  gatNum := gatNum
  gy := ⟨Y.vram, Y.fills_all, fun L a b c I d e g h => ((hL L a b c).2 I d e g h).1⟩
  row := (rowLay_iff Y).2 untw
  mtStable := mt
  th_io := Y.th_io
  gauge_def := Y.gauge_def
  real := real
  dsig_eq := dsig_eq
  del := hR.del
  etaF := hR.etaF
  chiT := chiT
  nch_tie := Y.nch_tie
  nch_Q := nch_Q


theorem exists_forced (K : Ctx) (P : Pre) : ∃ S : Finset ℕ,
    ∀ p : ℕ, p.Prime → ((∃ i, p = P.host.g i) ∨ p = P.host.d ∨ (p : ℝ) ≤ K.s.X'' P.R.n) → p ∈ S := by
  refine ⟨{P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1), ?_⟩
  rintro p - (⟨i, rfl⟩ | rfl | h)
  · fin_cases i <;> simp
  · simp
  · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h)))

theorem lg_forced (K : Ctx) : large₂ K fun B _ T =>
    ∀ p : ℕ, p.Prime → ((∃ i, p = B.host.g i) ∨ p = B.host.d ∨ (p : ℝ) ≤ K.s.X'' B.R.n) → p ∈ T.pl := by
  choose S hS using exists_forced K
  exact ⟨fun _ _ _ => ∅, fun P _ _ _ => S P, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B _ _ _ _ h _ p hp h' => h (hS _ p hp h')⟩


theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

theorem ev_recOK : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (_ : Core K X f T), RecOK K.s K.C K.cD X.toD7 :=
  ev_imp TamePow.tame_of_pow fun _ hK X _ T c =>
    ⟨c.del, c.etaF, fun w hw j h1 h2 => by
        have a := c.row.untw w hw j h1 h2
        have b := c.row.untw (X.toD7.what₂.places.conj w) ((X.toD7.what₂.muAt_conj w).trans hw) j h1 h2
        unfold Rows.Data.Aj
        rw [hw, a.1, a.2, b.1]
        rfl,
      (TwFin.finite_pl X.B T.pl).subset fun w hw => c.mu.sub w ((mem_iff c.mu w).2 hw),
      (Full.dgam_pos_and_full X.toD7).1, (Full.dgam_pos_and_full X.toD7).2, hK X c.isOver c.chiT, c.col.mink, c.col.atT⟩

theorem ev_exists_sizeData : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (_ : Core K X f T),
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ WtEq L K.a K.b ∧ Val K.C K.cD K.ch L := by
  have h : Ev fun K => ∀ D : D7, Over D K.P K.Lv → RecOK K.s K.C K.cD D →
      ∃ L : SizeData₂ D, L.sc = K.s ∧ WtEq L K.a K.b ∧ Val K.C K.cD K.ch L := by
    refine ⟨1, one_pos, fun eps _ a1 _ a3 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C b1 _ _ => ⟨0, fun cD hcD =>
      ⟨402, fun ch hch => ?_⟩⟩⟩⟩
    obtain ⟨x0, h⟩ := exists_sizeData_over eps cD ch C a1 a3 b1 hcD hch
    refine ⟨x0, ?_⟩
    rintro K rfl rfl rfl d4 d5 D hO hR
    exact (h K.s K.P K.q1 K.a K.b K.c K.Lv D d4 d5 K.ok K.Gam_eq hO hR).2.1
  refine ev_imp (ev_and h ev_recOK) fun K H X f T c => H.1 _ ?_ (H.2 X f T c)
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := c.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, X, h, rfl⟩


def someBase (P : Pre) : Base := (BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)).choose



variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)

include hH hLP hSP h2b in

theorem not_exTrue_false {KP : ∀ B : Base, Fr B.toPre → Prop} (hK : KsCond KP) : ¬ ExTrue KP fun _ _ _ _ _ => False := fun hE => by
  refine Inh.not_ev_false hH hLP hSP h2b ?_
  refine ev_imp (ev_and (ev_and (ev_preX_frame h2b) hK.ex) hE) ?_
  rintro K ⟨⟨hfr, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩
  obtain ⟨P, hP⟩ := Inh.exists_over K
  obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
  obtain ⟨f₀⟩ := (hfr _ hP).2
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks B₀ f₀ (S₁ B₀.toPre f₀)
    (fun F F₀ => S₂ B₀.toPre f₀ F F₀ {1, f₀.del, f₀.del'}) hP (a₁ _ _) (fun F F₀ => a₂ _ _ F F₀ _)
  generalize B₀.toPre = P₀ at *
  subst hB
  obtain rfl := eq_of_heq hf
  have hs : (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)).set f = {1, f.del, f.del'} := by
    refine Set.union_eq_left.2 ?_
    rintro _ ⟨w, rfl⟩
    change (if _ then f.del' else f.del) * 1 ∈ _
    rw [mul_one]
    split_ifs
    · exact .inr (.inr rfl)
    · exact .inr (.inl rfl)
  obtain ⟨_, _, _, _, _, _, _, h⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hP
    ⟨hH₁, by rw [hs]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _)) hKP
  exact h

include hH hLP hSP h2b in

theorem not_ksCond_false : ¬ KsCond fun _ _ => False := fun hK =>
  not_exTrue_false hH hLP hSP h2b hK (ev_all fun _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    by simp, by simp, fun _ _ _ _ _ _ _ h => h.elim⟩)

include hH hLP hSP h2b in

theorem not_exTrue_confined {KP : ∀ B : Base, Fr B.toPre → Prop} (hK : KsCond KP) {Q : Slot}
    (g : Ctx → ∀ P : Pre, Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℕ)
    (hQ : ∀ K X f T c, Q K X f T c → ∀ w ∈ c.Wt, X.B.places.resChar w ∈ g K X.B.toPre f X.B.KsC X.B.fixedCoefficientFieldInComplex) : ¬ ExTrue KP Q := fun hE => by
  classical
  refine Inh.not_ev_false hH hLP hSP h2b ?_
  refine ev_imp (ev_and (ev_and (ev_preX_frame h2b) hK.ex) hE) ?_
  rintro K ⟨⟨hfr, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩
  obtain ⟨P, hP⟩ := Inh.exists_over K
  obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
  obtain ⟨f₀⟩ := (hfr _ hP).2
  have hl : ∀ F F₀, ∃ l : ℕ, l.Prime ∧ l ∉ g K B₀.toPre f₀ F F₀ := fun F F₀ =>
    let ⟨l, h1, h2⟩ := Nat.infinite_setOf_prime.exists_notMem_finset (g K B₀.toPre f₀ F F₀); ⟨l, h1, h2⟩
  choose l hl hl' using hl
  choose Ξ hΞ using fun F F₀ => Inh.exists_family B₀.toPre f₀ (insert (l F F₀) (P₁ B₀.toPre f₀ F F₀)) (A B₀.toPre f₀ F F₀)
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks B₀ f₀ (S₁ B₀.toPre f₀)
    (fun F F₀ => S₂ B₀.toPre f₀ F F₀ (Ξ F F₀)) hP (a₁ _ _) (fun F F₀ => a₂ _ _ F F₀ _)
  obtain ⟨T, t1, t2, t3, t4⟩ := hΞ B.KsC B.fixedCoefficientFieldInComplex B hB
  clear hΞ hks
  generalize B₀.toPre = P₀ at *
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨C, W, V, S, N, G, c, h⟩ := hlg B f T hP ⟨hH₁, by rw [t4]; exact hH₂⟩ (t1 ▸ Finset.subset_insert _ _) t2 hKP
  obtain ⟨w, hw⟩ := GlobalTheory.Mem.PsiExist.exists_place_over B.LL (hl B.KsC B.fixedCoefficientFieldInComplex)
  have e : B.places.resChar w = l B.KsC B.fixedCoefficientFieldInComplex :=
    Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime _) (hl _ _) (Examples₂.PlacesToy.resCharW_mem w) hw
  have hw' : w ∈ c.Wt := by_contra fun hn => t3 w (e ▸ Finset.mem_insert_self _ _) (c.mu.supp w hn)
  exact hl' _ _ (e ▸ hQ _ _ _ _ c h w hw')





theorem FromCore.elim {Q : Slot} {D : D7} {Y : Lay D} (h : FromCore Q D Y) :
    ∃ (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : Core K X f T) (e : D = X.toD7), Q K X f T c ∧
      layObj (e ▸ Y) = c.O := by
  obtain ⟨K, X, f, T, c, q, e⟩ := h
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  exact ⟨K, X, f, T, c, rfl, q, eq_of_heq e2⟩

open RowsModel in

def plainRows {B : Base} {C : Cols B} (W : RowsRest B C) (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ)
    (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ) : RowsRest B C :=
  { GaloisStage.adapt W with
    Mtilde := fun μ => DQ.Model.sat B.embLL (W.Mtilde μ)
    FT := {_x : Unit // 0 < W.Drows ∨ 0 < W.D0}
    instFT := inferInstance
    instFTd := inferInstance
    ft := fun i => ⟨(), .inl i.pos⟩
    ft0 := fun i => ⟨(), .inr i.pos⟩
    Bu := fun _ _ _ => 0
    Bu_linL := fun _ _ => ⟨by simp, by simp⟩
    Bu_linR := fun _ _ => ⟨by simp, by simp⟩
    Mj := fun _ => Euc 0
    instMj := fun _ => inferInstance
    instMji := fun _ => inferInstance
    instMjf := fun _ => inferInstance
    MjLat := fun _ => stdOLat _ _ 0
    kaBig := kb
    kaSmall := ks
    Mt := fun _ _ => Euc 0
    instMt := fun _ _ => inferInstance
    instMti := fun _ _ => inferInstance
    instMtf := fun _ _ => inferInstance
    MtLat := fun _ _ => stdOLat _ _ 0
    MtL := fun _ _ => Fin 0 → B.LL
    instMtL := fun _ _ => inferInstance
    instMtLm := fun _ _ => inferInstance
    jMt := fun _ _ => coordEmb B.embLL 0
    jMt_basis := fun _ _ b => coordEmb_basis B.embLL 0 b
    MtLat_sub := fun _ _ x hx => by
      obtain ⟨i, rfl⟩ := mem_stdOLat hx
      exact ⟨_, coordEmb_single _ _ i⟩
    eMt := fun _ _ => 0
    eMt_idem := fun _ _ => LinearMap.zero_comp _
    eMt_sa := fun _ _ => LinearMap.IsSymmetric.zero
    eMt_LL := fun _ _ _ => ⟨0, map_zero _⟩
    thetaP := fun _ _ => 0
    isot := fun _ _ => ⊥
    lamP := fun _ _ _ => 1
    Ij := fun _ _ _ => 0
    jw := fun _ _ _ => 0 }

def glue {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module (𝓞 L) V]
    (A : HeightOneSpectrum (𝓞 L) → Submodule (𝓞 L) V) : Submodule (𝓞 L) V where
  carrier := {x | ∀ w, ∃ d : 𝓞 L, d ∉ w.asIdeal ∧ d • x ∈ A w}
  add_mem' := fun {x y} hx hy w => by
    obtain ⟨d, h1, h2⟩ := hx w
    obtain ⟨e, h3, h4⟩ := hy w
    refine ⟨d * e, fun h => (w.isPrime.mem_or_mem h).elim h1 h3, ?_⟩
    rw [smul_add]
    exact add_mem (by rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h2) (by rw [mul_smul]; exact Submodule.smul_mem _ _ h4)
  zero_mem' := fun w => ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := fun a x hx w => by
    obtain ⟨d, h1, h2⟩ := hx w
    exact ⟨d, h1, by rw [smul_comm]; exact Submodule.smul_mem _ _ h2⟩

def setRR {B : Base} {C : Cols B} {W : RowsRest B C} (V : DivStage B C W) (η : ℝ) : DivStage B C W :=
  let R : HLat B.LL := { V.div.RR with
    L := glue fun w => Submodule.span (𝓞 B.LL) {y | V.jEE y ∈ W.what₂.RRset (W.muAt w)} }
  { V with
    div := { V.div with
      RR := R
      etaF := η
      HH := sFrame V.div.Nu V.div.h + R.muMax
      HH_ge := le_rfl } }

theorem lidx_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [Subsingleton V] (p : Ideal R) [p.IsPrime]
    (A B : Submodule R V) : Formalism.HermitianLatticesTheory.lidx p A B = 0 := by
  rw [Subsingleton.elim A B]
  unfold Formalism.HermitianLatticesTheory.lidx
  exact sub_self _

set_option maxHeartbeats 1000000 in

theorem exists_rowLay_of (X : Stages) (η : ℝ) :
    ∃ (W : RowsRest X.B X.C) (V : DivStage X.B X.C W) (S : SStage X.B X.C W) (N : NStage X.B X.C W),
      W.muAt = X.W.muAt ∧ W.muTw = X.W.muTw ∧ W.Drows = X.W.Drows ∧ V.div.etaF = η ∧ DQ.MtStableAt (assemble X.B X.C W V S N X.G) ∧
      ∃ p0 Z, RowLay (assemble X.B X.C W V S N X.G) p0 Z := by
  obtain ⟨kb, ks, hk⟩ := DV.exists_blocks X.toD7
  let W := plainRows X.W kb ks
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_of_rows X.B X.C W X.N.toLocStage (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl)
  let V₀ : DivStage X.B X.C W := { X.V with }
  let S : SStage X.B X.C W := { X.S with }
  let D := assemble X.B X.C W (setRR V₀ η) S N X.G
  obtain ⟨p0, hp, -⟩ := GlobalTheory.ProvRowSide.exists_p0Side D
  haveI i1 : ∀ j, Subsingleton (D.what₂.Mj j) := fun _ => inferInstanceAs (Subsingleton (RowsModel.Euc 0))
  haveI i2 : ∀ μ j, Subsingleton (D.what₂.MtL μ j) := fun _ _ => inferInstanceAs (Subsingleton (Fin 0 → X.B.LL))
  obtain ⟨Z, hZ⟩ := GlobalTheory.exists_provisionalDivX D fun j _ _ =>
    ⟨0, Module.Basis.empty _, fun _ _ i => i.elim0⟩
  refine ⟨W, setRR V₀ η, S, N, rfl, rfl, rfl, rfl,
    fun (μ : X.C.Tup) a y hy => DQ.Model.sat_stable X.B.embLL (X.W.Mtilde μ) a y hy, p0, Z, fun _ => Iff.rfl, hp, fun j _ _ τ => hk j τ,
    fun _ _ _ _ _ h => absurd rfl h, fun u φ x => ?_, fun π => π.2.imp (fun h => ⟨⟨0, h⟩, rfl⟩) (fun h => ⟨⟨0, h⟩, rfl⟩), fun _ _ _ _ _ => ⟨rfl, rfl⟩,
    ⟨fun μ j w _ _ => ?_, fun μ j w _ _ => (lidx_zero _ _ _).symm⟩, hZ⟩
  · have h0 : D.what₂.sec D.what₂.mu0 x = 0 := by
      have : D.what₂.sec D.what₂.mu0 x ∈ D.what₂.Qsp D.what₂.mu0 := Subtype.property _
      obtain ⟨y, hy⟩ := this.1
      exact hy.symm
    exact (h0 ▸ D.perCol_zero u φ).symm
  · haveI : Subsingleton (Z.MjH j).V := (Idx.jM_inj Z j).subsingleton
    exact (lidx_zero _ _ _).symm


theorem hasLetters_of_over (K : Ctx) (P : Pre) (hO : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hO
  have hx : 0 < K.s.x := by linarith [K.s.one_lt_alt]
  refine ⟨(Delv K.s K.cD : ℚ), K.c, ?_, K.ok.inj, fun u τ l h => ?_, K.ok.code⟩
  · exact_mod_cast Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)
  · have a := (K.ok.hc u).1 τ ⟨l, by exact lt_of_le_of_lt (Nat.le_succ _) h⟩
    have b := (K.ok.hc u).1 τ ⟨l + 1, h⟩
    have h' : l + 1 < K.P.R.k - 1 := h
    have e : ((K.P.R.k - 2 - l : ℕ) : ℚ) = ((K.P.R.k - 2 - (l + 1) : ℕ) : ℚ) + 1 := by
      exact_mod_cast (by omega : K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1)
    refine (congrArg₂ (· - ·) a b).trans ?_
    simp only [e]
    ring




end GlobalTheory.Mem.Top.V4.Model

end
