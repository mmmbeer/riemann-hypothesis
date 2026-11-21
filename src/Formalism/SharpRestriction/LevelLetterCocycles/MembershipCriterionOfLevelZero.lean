import Formalism.SharpRestriction.LevelLetterCocycles.DvOZeroHigh

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

structure Ctx : Prop where
  hbij : Function.Bijective (algebraMap K₀ K)
  hs : W.s = 1
  hp2 : PD.p ≠ 2
  h5p : 5 ≤ PD.p
  hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W
  h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h
  h3 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p3 W T
  hmod : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀
  hΔ : IsUnit ((W.DelF.card : ℕ) : O)
  hsat : SATcore W
  hsatP : SATPcore W
  hTr : Formalism.MainNotions.LiftingTheory.coreTr W
  hH : Formalism.MainNotions.LiftingTheory.coreH W
  hinj : Function.Injective (algebraMap O LL)
  hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x
  hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v
  hp0 : ((PD.p : ℕ) : O) ≠ 0

variable {W}

theorem Ctx.hCA (C : Ctx W) : Formalism.MainNotions.LiftingTheory.CaseA W := ⟨C.hbij, C.hs, C.hp2⟩

theorem exists_smul_pow_eq_sum_of_inFNc (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (N₁ : ℕ) (hN₁ : Hw A.G₀ A.S A.η (A.ty (a + 1)) ≤ N₁) (x : W.DD T) (hx : InFNc W T (a + 1) 1 x) :
    ∃ (r : ℕ) (bb : Fin r → W.DD T) (β : Fin r → LetA O n), (∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a (bb j)) ∧
      (∀ j, β j ∈ W.AΔ) ∧ ps W 0 ^ N₁ • x = ∑ j, β j • W.φD T (bb j) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y, hyN, hya, rfl⟩ := hx
  rw [one_smul]
  have hyl : y ∈ W.Nl T (a + 1) := ⟨y, hyN.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hya⟩
  have h1 := Formalism.MainNotions.UnusedSlot80.ArcC.iter_down W C.hs T h5T (a + 1) 1 y hyl
  rw [Finset.prod_range_one, pow_zero, AlgHom.one_apply, Nat.cast_zero, sub_zero, Nat.cast_one,
    add_sub_cancel_right] at h1
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hN₁
  have e1 : ps W 0 ^ N₁ • y = (w' ^ N₁ * W.q ^ dd) • (W.q ^ Hw A.G₀ A.S A.η (A.ty (a + 1)) • y) := by
    rw [hp0w, smul_smul, hdd]; congr 1; ring
  have h2 := Submodule.smul_mem _ (w' ^ N₁ * W.q ^ dd) h1
  rw [← e1] at h2
  obtain ⟨⟨r, bb0, hb0, huniq, -⟩, -⟩ := C.hmod T hT.1
  have h3 := Formalism.MainNotions.UnusedSlot80.ArcC.span_pow_le W T bb0 (fun z hz => (huniq z hz).exists) a 1 h2
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h3
  have hbΔ : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a ((letE a : LetA O n) • bb0 j) := fun j =>
    ⟨Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (hb0 j),
      ⟨bb0 j, (hb0 j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩
  have hp0Δ : ps W 0 ^ N₁ ∈ W.AΔ := W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) N₁
  obtain ⟨dd, hd, hzd⟩ := Formalism.MainNotions.WachCoordinates.Br.average C.hΔ cc
    (fun j => (W.φD T ^ 1 : Module.End O (W.DD T)) ((letE a : LetA O n) • bb0 j))
    (fun j δ hδ => φD_pow_Δ W T (hbΔ j).1.2 1 δ hδ)
    (fun δ hδ => (Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T hp0Δ hyN).2 δ hδ) hcc.symm
  refine ⟨r, fun j => (letE a : LetA O n) • bb0 j, dd, hbΔ, hd, ?_⟩
  rw [hzd]
  simp only [pow_one]

theorem up1 (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (H : ℕ) (hH : Mw A.G₀ A.S A.η (A.ty (a + 1)) ≤ H) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFNc W T a 1 y) : InFNc W T (a + 1) 1 ((ps W 0 ^ H * vv) • W.φD T y) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y', hy'N, hy'l, rfl⟩ := hy
  rw [one_smul]
  have hQ : W.Q = W.q := by simp [LocWach.Q, C.hs]
  have hyl : y' ∈ W.Nl T (a + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨y', hy'N.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hy'l⟩
  have hM := h5T.1 (a + 1) y' hyl
  rw [hQ] at hM
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  have hN : (ps W 0 ^ H * vv) • W.φD T y' ∈ W.N T := by
    obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hH
    have e1 : (ps W 0 ^ H * vv) • W.φD T y' = (w' ^ H * W.q ^ dd * vv) •
        (W.q ^ Mw A.G₀ A.S A.η (A.ty (a + 1)) • W.φD T y') := by
      rw [hp0w, smul_smul]; congr 1; rw [hdd]; ring
    rw [e1]
    exact (W.N T).smul_mem _ hM
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((ps W 0 ^ H * vv) • W.φD T y') = (ps W 0 ^ H * vv) • W.φD T y' := by
    intro δ hδ
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', (W.AΔ.mul_mem (W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) H) hv) δ hδ,
      ← W.φγ_comm, hy'N.2 δ hδ]
  refine ⟨_, ⟨hN, hΔ⟩, ?_, by rw [one_smul]⟩
  rw [smul_comm]
  congr 1
  have := φD_pow_letter W T a y' hy'l 1
  simpa using this

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

def Good (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) : Prop :=
  InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z) ∧
  ∀ (k : ℕ) (f : Fin d → W.EE),
    RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k • z) f →
    (∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f m)) →
    ∃ κ : ℕ, SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ * f m

theorem lE_mul (s t : ℕ) (y : W.EE) : lE W s * (lE W t * y) = lE W (s + t) * y := by
  unfold lE; rw [pow_add]; ring

theorem lE_eq (t : ℕ) : lE W t = algebraMap (LetA O n) W.EE (lA W ^ t) := by
  unfold lE lA; rw [map_pow, map_natCast]

theorem repVV_lA (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) (f : Fin d → W.EE) (s t : ℕ)
    (h : RepVV W T c' e M Λ b sol (lA W ^ t • z) f) :
    RepVV W T c' e M Λ b sol (lA W ^ (t + s) • z) (fun m => lE W s * f m) := by
  have := repVV_smul W T c' e M Λ b sol _ f (lA_mem W s) h
  rwa [lA_smul_smul, ← lE_eq] at this

theorem good_of_sec (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (k₀ : ℕ) (f₀ : Fin d → W.EE)
    (hrep₀ : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k₀ • z) f₀)
    (hfr₀ : ∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f₀ m)) (κ₀ : ℕ)
    (hS₀ : SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ₀ * f₀ m) :
    Good A c' e T b sol z := by
  refine ⟨hz, fun k f hrep hfr => ?_⟩
  have r1 := repVV_lA T c' e _ _ b sol z f k₀ k hrep
  have r2 := repVV_lA T c' e _ _ b sol z f₀ k k₀ hrep₀
  rw [add_comm k₀ k] at r2
  obtain ⟨t, ht⟩ := sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p T
    (C.h3 T hT.1) (C.hmod T hT.1) A hA c' hc' hT b sol hb e _ _ _ r1 r2
    (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr m) k₀) (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₀ m) k)
  have hD := secIn_piLam W C.hR.1 A (c' + (e : ZMod n)) e T b
    (fun c₀ s hs => dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 e s hs c₀) _ ht
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hD κ₀) (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₀ (t + k))
  refine ⟨κ₀ + (t + k₀), ?_⟩
  convert hS using 1
  funext m
  simp only [Pi.add_apply, lE_mul, mul_sub]
  rw [show κ₀ + (t + k₀) = κ₀ + (t + k₀) from rfl]
  unfold lE
  ring

theorem good_of_lpow (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e K : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (h : Good A c' e T b sol (lA W ^ K • z)) :
    Good A c' e T b sol z := by
  obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _
    h.1
  obtain ⟨κ', hS⟩ := h.2 κ f hrep hfr
  rw [lA_smul_smul] at hrep
  exact good_of_sec C A hA c' hc' T hT b sol hb e z hz _ f hrep hfr κ' hS

theorem good_add (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z₁ z₂ : W.DD T)
    (h₁ : Good A c' e T b sol z₁) (h₂ : Good A c' e T b sol z₂) : Good A c' e T b sol (z₁ + z₂) := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (z₁ + z₂)) := by
    rw [smul_add]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ h₁.1 h₂.1
  obtain ⟨κ₁, f₁, hrep₁, hfr₁⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₁.1
  obtain ⟨κ₂, f₂, hrep₂, hfr₂⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₂.1
  obtain ⟨κ'₁, hS₁⟩ := h₁.2 κ₁ f₁ hrep₁ hfr₁
  obtain ⟨κ'₂, hS₂⟩ := h₂.2 κ₂ f₂ hrep₂ hfr₂
  have r1 := repVV_lA T c' e _ _ b sol z₁ f₁ κ₂ κ₁ hrep₁
  have r2 := repVV_lA T c' e _ _ b sol z₂ f₂ κ₁ κ₂ hrep₂
  rw [add_comm κ₂ κ₁] at r2
  have r := repVV_add W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2
  rw [← smul_add] at r
  refine good_of_sec C A hA c' hc' T hT b sol hb e _ hz _ _ r
    (fun m => inFr_add W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₁ m) κ₂) (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₂ m) κ₁))
    (κ'₁ + κ'₂) ?_
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₁ (κ'₂ + κ₂))
    (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₂ (κ'₁ + κ₁))
  convert hS using 1
  funext m
  simp only [Pi.add_apply]
  unfold lE
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

def SecCrit0 (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ (x : W.DD T) (k : ℕ) (f : Fin d → W.EE),
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x) →
    RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol (lA W ^ k • x) f →
    (∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * LamUp W A c' e)
      (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) (f m)) →
    (InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x ↔
      ∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
        (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m)

theorem inFNc_smul (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (a : ZMod n) {c : LetA O n} (hc : c ∈ W.AΔ)
    {x : W.DD T} (hx : InFNc W T a 1 x) : InFNc W T a 1 (c • x) := by
  obtain ⟨y, hy, hyl, rfl⟩ := hx
  exact ⟨c • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hc hy, by rw [smul_comm, hyl], by simp⟩

theorem inFP_up (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n)
    (e N : ℕ) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • y)) :
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • ((ps W 0 ^ N * vv) • W.φD T y)) := by
  obtain ⟨p, hp, hyp⟩ := hy
  rw [one_smul] at hyp
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  refine ⟨(ps W 0 ^ N * vv * ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) • W.φD T p,
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ N) hv)
      (W.AΔ.pow_mem hp0Δ _)) _ (φ_Pp W T c' e p hp), ?_⟩
  rw [one_smul, lam_succ, ← hyp, φD_smulA, smul_smul, smul_smul]
  unfold LamUp
  congr 1; ring

theorem good_zero (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) : Good A c' e T b sol 0 := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (0 : W.DD T)) := by
    rw [smul_zero]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W C.hO2 C.hH C.hCA T hT.1 c' b sol hb (A.M PD.p)
  refine good_of_sec C A hA c' hc' T hT b sol hb e 0 hz 0 (fun _ => 0)
    ⟨κ, 0, Hh, fun _ => 0, hHh, fun k => ⟨W.AΔ.zero_mem, by simp⟩, by
      simp only [smul_zero, zero_smul, Finset.sum_const_zero, sub_zero]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _⟩
    (fun m => inFr_zero W) 0 ?_
  simpa using secIn_zero W (condNN W T (c' + (e : ZMod n)) e b) (a := c' + (e : ZMod n)) (e := e)

theorem good_sum (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) {ι : Type} (s : Finset ι) (z : ι → W.DD T)
    (h : ∀ j ∈ s, Good A c' e T b sol (z j)) : Good A c' e T b sol (∑ j ∈ s, z j) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_zero C A hA c' hc' T hT b sol hb e
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact good_add C A hA c' hc' T hT b sol hb e _ _ (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem φE_lE (t : ℕ) : W.φE (lE W t) = lE W t := by
  unfold lE; rw [map_pow, map_natCast]

theorem step_mp (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (IH : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol)
    (h0 : SecCrit0 A c' e T b sol) (x : W.DD T)
    (hxP : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x))
    (hxN : InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x) : Good A c' (e + 1) T b sol x := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  have ha' : c' + ((e + 1 : ℕ) : ZMod n) = a + 1 := by rw [hadef]; push_cast; ring
  set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
  set hq : ℕ := Hw A.G₀ A.S A.η (A.ty (a + 1)) with hqdef
  set U : LetA O n := LamUp W A c' e with hUdef
  have hUΔ : U ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W C.hR.1 A _ e)
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W C.hR.1 0
  obtain ⟨m₀, u₀, hu₀, u₁, hu₁, hl, ⟨r₀, hr₀, hu₀e⟩, ⟨s₁, hs₁, hu₁e⟩⟩ :=
    crt W (W.AΔ.mul_mem C.hR.1 (W.AΔ.pow_mem hUΔ 2)) (W.AΔ.pow_mem hp0Δ (H + hq))
      (cop_lamUp W C.hR C.hp0 A c' e (H + hq))

  have g0 : Good A c' (e + 1) T b sol (u₀ • x) := by
    have hz : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u₀ • x)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₀ hxP
    obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' (e + 1) T hT.1
      b sol hb x hxP
    have hrep0 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₀ hrep
    rw [smul_comm] at hrep0
    have hfr0 : ∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * U) (ps W 0 ^ H)
        (algebraMap (LetA O n) W.EE u₀ * f m) := by
      intro m
      obtain ⟨t, ht, hft⟩ := hfr m
      refine ⟨r₀ * t, W.AΔ.mul_mem hr₀ ht, ?_⟩
      rw [lam_succ] at hft
      rw [hu₀e]
      simp only [map_mul, map_pow, map_one] at hft ⊢
      linear_combination (algebraMap (LetA O n) W.EE W.π₀ * algebraMap (LetA O n) W.EE U *
        algebraMap (LetA O n) W.EE r₀) * hft
    obtain ⟨κ₀, hS⟩ := (h0 (u₀ • x) κ _ hz hrep0 hfr0).1 (inFNc_smul C.hR.1 T _ hu₀ hxN)
    exact good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ hz κ _ hrep0 (fun m => inFr_mulA W (hfr m) hu₀) κ₀ hS

  obtain ⟨r, bb, β, hbb, hβ, hdec⟩ := exists_smul_pow_eq_sum_of_inFNc C T A hA hT a hq le_rfl x (by rwa [ha'] at hxN)
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  have gj : ∀ j, Good A c' (e + 1) T b sol ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
    intro j
    have hbl : (letE a : LetA O n) • bb j = bb j := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T a (hbb j).2
    have hbN : InFNc W T a 1 (bb j) := ⟨bb j, (hbb j).1, hbl, (one_smul _ _).symm⟩
    have hbP : InFP W T c' e 1 (abelian₂ W A a e • bb j) :=
      Formalism.MainNotions.UnusedSlot80.ArcC.arc_down W C.hs C.hR T A hA h5T (C.hmod T hT.1) C.hΔ c' hc' e (bb j) hbN
    obtain ⟨κj, fj, hrepj, hfrj⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1
      b sol hb (bb j) hbP
    obtain ⟨κ'j, hSj⟩ := (IH (bb j) κj fj hbP hrepj hfrj).1 hbN
    have hv : s₁ * β j ∈ W.AΔ := W.AΔ.mul_mem hs₁ (hβ j)
    have hPκ : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (lA W ^ κj • bb j)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W κj) hbP
    obtain ⟨-, hrep', -⟩ := transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
      (by simpa using hrepj) hfrj H le_rfl hv
    have hel : (ps W 0 ^ H * (s₁ * β j)) • W.φD T (lA W ^ κj • bb j) =
        lA W ^ κj • ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
      rw [φD_smulA, φA_lA, smul_comm]
    rw [hel] at hrep'
    have hlow0 : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ)) := by
      intro c₀
      have := dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 (e + 1) 0 (by omega) c₀
      rw [hHdef, ha']; rwa [ha'] at this
    have hS' := secIn_transport W T a e b H hv C.hR.1 hlow0 _ hSj
    rw [← ha'] at hS'
    refine good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ (inFP_up C.hR T A c' e H hv (bb j) hbP) κj _ hrep'
      (fun m => (transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
        (by simpa using hrepj) hfrj H le_rfl hv).2.2 m) κ'j ?_
    convert hS' using 1
    funext m
    rw [map_mul W.φE, φE_lE]
    ring
  have hu₁x : u₁ • x = ∑ j, (ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j) := by
    rw [hu₁e, show ps W 0 ^ (H + hq) * s₁ = (ps W 0 ^ H * s₁) * ps W 0 ^ hq by ring, mul_smul, hdec,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]; congr 1; ring
  have g1 : Good A c' (e + 1) T b sol (u₁ • x) := by
    rw [hu₁x]
    exact good_sum C A hA c' hc' T hT b sol hb (e + 1) _ _ fun j _ => gj j
  have g2 : Good A c' (e + 1) T b sol (lA W ^ m₀ • x) := by
    rw [hl, add_smul]
    exact good_add C A hA c' hc' T hT b sol hb (e + 1) _ _ g0 g1
  exact good_of_lpow C A hA c' hc' T hT b sol hb (e + 1) m₀ x hxP g2

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

theorem inFNc_add (T : LocLat G Qp LL O) (a : ZMod n) {x y : W.DD T} (hx : InFNc W T a 1 x)
    (hy : InFNc W T a 1 y) : InFNc W T a 1 (x + y) := by
  obtain ⟨x', hx', hxl, rfl⟩ := hx
  obtain ⟨y', hy', hyl, rfl⟩ := hy
  exact ⟨x' + y', (W.NΔ T).add_mem hx' hy', by rw [smul_add, hxl, hyl], by simp⟩

theorem inFNc_neg (T : LocLat G Qp LL O) (a : ZMod n) {x : W.DD T} (hx : InFNc W T a 1 x) :
    InFNc W T a 1 (-x) := by
  obtain ⟨x', hx', hxl, rfl⟩ := hx
  exact ⟨-x', (W.NΔ T).neg_mem hx', by rw [smul_neg, hxl], by simp⟩

theorem inFNc_zero (T : LocLat G Qp LL O) (a : ZMod n) : InFNc W T a 1 (0 : W.DD T) :=
  ⟨0, (W.NΔ T).zero_mem, smul_zero _, by simp⟩

theorem mem_of_sec_eq (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (x z : W.DD T) (k k' t : ℕ) (f : Fin d → W.EE)
    (hxP : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x))
    (hzP : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z))
    (hzN : InFNc W T (c' + (e : ZMod n)) 1 z)
    (hx : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k • x) f)
    (hz : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k' • z)
      (fun m => lE W t * f m)) :
    InFNc W T (c' + (e : ZMod n)) 1 x := by
  set Λ := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  have r1 := repVV_lA T c' e _ _ b sol x f (k + k' + t) k hx
  have r2 := repVV_lA T c' e _ _ b sol z _ (k' + k) k' hz
  have hsec : (fun m => lE W (k' + k) * (lE W t * f m)) = (fun m => lE W (k + k' + t) * f m) := by
    funext m; rw [lE_mul]; congr 2; ring
  rw [hsec] at r2
  have r3 := repVV_sub W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2
  rw [sub_self] at r3
  have hΛu := lam_unit W C.hR A (c' + (e : ZMod n)) e
  have hwP : InFP W T c' e 1 (Λ • (lA W ^ (k + (k + k' + t)) • x - lA W ^ (k' + (k' + k)) • z)) := by
    rw [smul_sub, smul_comm Λ, smul_comm Λ (lA W ^ (k' + (k' + k)))]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sub W T c' e _ (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hxP)
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hzP)
  have hw := piLam_of_sec W C.hR C.hsatP C.hCA T hT.1 A c' e _ b sol hb.1 _ hwP _ r3 (fun m => inFr_zero W)
  have hwN := inN_of_piLam W C.hR.1 T A c' e
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' e T hT) _ hw
  have hzN' := inFNc_smul C.hR.1 T _ (lA_mem W (k' + (k' + k))) hzN
  have hxN := inFNc_add T _ hwN hzN'
  rw [sub_add_cancel] at hxN
  exact Formalism.MainNotions.UnusedSlot80.ArcC.arc_sat W C.hCA C.hsat C.hR T hT.1 A c' e
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' e T hT) x hxP ⟨_, hxN⟩

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

theorem ps_unitE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) : IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  exact Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s)

theorem prod_ps_unitE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (e : ℕ) (E : ℕ → ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ E s)) := by
  rw [map_prod]
  exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    fun s _ => by rw [map_pow]; exact (ps_unitE W hR s).pow _

theorem prod_succ_φ (e : ℕ) (E : ℕ → ℕ) :
    ∏ s ∈ Finset.range (e + 1), ps W s ^ E s =
      W.φA (∏ s ∈ Finset.range e, ps W s ^ E (s + 1)) * ps W 0 ^ E 0 := by
  rw [Finset.prod_range_succ', map_prod]
  congr 1
  exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]

theorem mono_lift (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (A : ArcP n) (a : ZMod n) (e : ℕ) (α : ℕ → ℤ)
    (g : W.EE) (hg : InId W (a + 1) (e + 1) α g)
    (hα : ∀ s, s < e → -(A.Hs a e s : ℤ) ≤ α (s + 1)) (N H : ℕ) (hN : H + (-(α 0)).toNat ≤ N)
    {s₁ : LetA O n} (hs₁ : s₁ ∈ W.AΔ) :
    ∃ vv ∈ W.AΔ, ∃ g' : W.EE,
      algebraMap (LetA O n) W.EE (ps W 0 ^ N * s₁) * g =
        algebraMap (LetA O n) W.EE (ps W 0 ^ H * vv) * W.φE g' ∧
      InId W a e (fun s => α (s + 1)) g' ∧ InFr W a 1 (abelian₂ W A a e) g' := by
  obtain ⟨u, hu, hgu⟩ := hg
  set num' : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (α (s + 1)).toNat with hnum'
  set den' : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (-(α (s + 1))).toNat with hden'
  have hnum := prod_succ_φ W e (fun s => (α s).toNat)
  have hden := prod_succ_φ W e (fun s => (-(α s)).toNat)
  obtain ⟨D, hD⟩ := prod_ps_unitE W hR e (fun s => (-(α (s + 1))).toNat)
  set ι : W.EE := ((D⁻¹ : W.EEˣ) : W.EE) with hιdef
  have hι : ι * algebraMap (LetA O n) W.EE den' = 1 := by rw [hden', ← hD]; exact Units.inv_mul D
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  set E0 : ℕ := (-(α 0)).toNat with hE0
  set F0 : ℕ := (α 0).toNat with hF0
  refine ⟨ps W 0 ^ (N + F0 - E0 - H) * s₁ * u, W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ _) hs₁) hu,
    algebraMap (LetA O n) W.EE (letE a * num') * ι, ?_, ?_, ?_⟩
  ·
    obtain ⟨Dd, hDd⟩ := prod_ps_unitE W hR (e + 1) (fun s => (-(α s)).toNat)
    have hcan : ∀ y z : W.EE, algebraMap (LetA O n) W.EE
        (∏ s ∈ Finset.range (e + 1), ps W s ^ (-(α s)).toNat) * y =
        algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range (e + 1), ps W s ^ (-(α s)).toNat) * z → y = z := by
      intro y z h
      rw [← hDd] at h
      have := congrArg (fun w => ((Dd⁻¹ : W.EEˣ) : W.EE) * w) h
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
    apply hcan
    have hφι : W.φE ι * algebraMap (LetA O n) W.EE (W.φA den') = 1 := by
      rw [← φE_alg, ← map_mul, hι, map_one]
    have hl : W.φA (letE a : LetA O n) = letE (a + 1) := by
      have := φA_letE W (a + 1); rwa [show a + 1 - 1 = a by ring] at this
    have hexp : N + F0 = E0 + H + (N + F0 - E0 - H) := by omega
    rw [hnum, hden] at hgu
    simp only [map_mul, map_pow] at hgu
    rw [hden]
    simp only [map_mul, map_pow, φE_alg, hl]
    have e1 : algebraMap (LetA O n) W.EE (ps W 0) ^ N * algebraMap (LetA O n) W.EE (ps W 0) ^ F0 =
        algebraMap (LetA O n) W.EE (ps W 0) ^ E0 * algebraMap (LetA O n) W.EE (ps W 0) ^ H *
          algebraMap (LetA O n) W.EE (ps W 0) ^ (N + F0 - E0 - H) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← hexp]
    rw [hden'] at hφι
    rw [hnum'] at *
    linear_combination (algebraMap (LetA O n) W.EE (ps W 0) ^ N * algebraMap (LetA O n) W.EE s₁) * hgu +
      (algebraMap (LetA O n) W.EE s₁ * algebraMap (LetA O n) W.EE u *
        algebraMap (LetA O n) W.EE (letE (a + 1)) *
        algebraMap (LetA O n) W.EE (W.φA (∏ s ∈ Finset.range e, ps W s ^ (α (s + 1)).toNat))) * e1 -
      (algebraMap (LetA O n) W.EE (ps W 0) ^ E0 * algebraMap (LetA O n) W.EE (ps W 0) ^ H *
        algebraMap (LetA O n) W.EE (ps W 0) ^ (N + F0 - E0 - H) * algebraMap (LetA O n) W.EE s₁ *
        algebraMap (LetA O n) W.EE u * algebraMap (LetA O n) W.EE (letE (a + 1)) *
        algebraMap (LetA O n) W.EE (W.φA (∏ s ∈ Finset.range e, ps W s ^ (α (s + 1)).toNat))) * hφι
  ·
    refine ⟨1, W.AΔ.one_mem, ?_⟩
    show algebraMap (LetA O n) W.EE den' * (algebraMap (LetA O n) W.EE (letE a * num') * ι) =
      algebraMap (LetA O n) W.EE (letE a * num' * 1)
    rw [mul_one, mul_comm (algebraMap (LetA O n) W.EE (letE a * num')), ← mul_assoc,
      mul_comm (algebraMap (LetA O n) W.EE den'), hι, one_mul]
  ·
    have hle : ∀ s ∈ Finset.range e, (-(α (s + 1))).toNat ≤ A.Hs a e s := by
      intro s hs
      have := hα s (Finset.mem_range.1 hs)
      omega
    set R : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (A.Hs a e s - (-(α (s + 1))).toNat) with hRdef
    refine ⟨R * num', W.AΔ.mul_mem (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (ps_mem_AΔ W hR.1 s) _)
        (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (ps_mem_AΔ W hR.1 s) _), ?_⟩
    have hsplit : abelian₂ W A a e = den' * R := by
      rw [hden', hRdef, abelian₂, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [← pow_add, Nat.add_sub_cancel' (hle s hs)]
    rw [hsplit]
    simp only [map_mul, mul_one]
    linear_combination (algebraMap (LetA O n) W.EE R * algebraMap (LetA O n) W.EE (letE a) *
      algebraMap (LetA O n) W.EE num') * hι

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

theorem repVV_zero (C : Ctx W) (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ)
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (Λ : LetA O n) :
    RepVV W T c' e (A.M PD.p) Λ b sol 0 (fun _ => 0) := by
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W C.hO2 C.hH C.hCA T hTc c' b sol hb (A.M PD.p)
  exact ⟨κ, 0, Hh, fun _ => 0, hHh, fun k => ⟨W.AΔ.zero_mem, by simp⟩, by
    simp only [smul_zero, zero_smul, Finset.sum_const_zero, sub_zero]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _⟩

theorem repVV_sum (C : Ctx W) (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ)
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (Λ : LetA O n)
    {ι : Type} (s : Finset ι) (z : ι → W.DD T) (F : ι → Fin d → W.EE)
    (h : ∀ j ∈ s, RepVV W T c' e (A.M PD.p) Λ b sol (z j) (F j)) :
    RepVV W T c' e (A.M PD.p) Λ b sol (∑ j ∈ s, z j) (fun m => ∑ j ∈ s, F j m) := by
  induction s using Finset.induction_on with
  | empty => simpa using repVV_zero C A c' e T hTc b sol hb Λ
  | insert j s hj ih =>
    have := repVV_add W C.hinj T c' e _ Λ b sol _ _ _ _ (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert hj]
    convert this using 1
    funext m
    rw [Finset.sum_insert hj]
    rfl

theorem inFNc_sum (T : LocLat G Qp LL O) (a : ZMod n) {ι : Type} (s : Finset ι) (z : ι → W.DD T)
    (h : ∀ j ∈ s, InFNc W T a 1 (z j)) : InFNc W T a 1 (∑ j ∈ s, z j) := by
  induction s using Finset.induction_on with
  | empty => simpa using inFNc_zero T a
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact inFNc_add T a (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem secCrit_zero (A : ArcP n) (c' : ZMod n) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' 0 T d b sol := by
  intro x k f hx _ hfr
  have hc : c' + ((0 : ℕ) : ZMod n) = c' := by simp
  constructor
  · intro _
    refine ⟨0, d, fun m => lE W 0 * f m, fun m => Pi.single m 1, fun _ _ => 0, fun m => ⟨?_, fun s hs => absurd hs (by omega)⟩,
      fun k => ?_⟩
    · obtain ⟨u, hu, hfu⟩ := hfr m
      refine ⟨lA W ^ 0 * u, W.AΔ.mul_mem (lA_mem W 0) hu, ?_⟩
      rw [lam_zero, map_one, one_mul] at hfu
      simp only [Finset.range_zero, Finset.prod_empty, pow_zero, map_one, one_mul, mul_one, map_mul] at hfu ⊢
      rw [show lE W 0 = 1 by simp [lE], one_mul]
      exact hfu
    · simp [Pi.single_apply]
  · intro _
    rw [lam_zero, one_smul] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [one_smul]
    have : ∀ y ∈ Pp W T c' 0, InFNc W T (c' + ((0 : ℕ) : ZMod n)) 1 y := by
      refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c' 0 _ (inFNc_zero T _) (fun x y hx hy => inFNc_add T _ hx hy)
        (fun x hx => inFNc_neg T _ hx) ?_
      intro a ha y hy
      rw [pow_zero, Module.End.one_apply]
      obtain ⟨hyN, ⟨y', -, hyl⟩⟩ := hy
      refine ⟨a • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T ha hyN, ?_, (one_smul _ _).symm⟩
      rw [hc, ← hyl, LinearMap.smul_apply, LinearMap.id_apply, smul_comm (letE c' : LetA O n) a,
        smul_smul (letE c' : LetA O n) (letE c' : LetA O n), Formalism.MainNotions.WachCoordinates.Br.letE_mul_self]
    exact this p hp

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

theorem step_mpr (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (IH : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol)
    (h0 : SecCrit0 A c' e T b sol) (x : W.DD T) (k : ℕ) (f : Fin d → W.EE)
    (hxP : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x))
    (hrep : RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol
      (lA W ^ k • x) f)
    (hfr : ∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) (f m))
    (κ : ℕ) (hS : SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b)
      fun m => lE W κ * f m) :
    InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  have ha' : c' + ((e + 1 : ℕ) : ZMod n) = a + 1 := by rw [hadef]; push_cast; ring
  set a' : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with ha'def
  set H : ℕ := A.Hs a' (e + 1) 0 with hHdef
  set U : LetA O n := LamUp W A c' e with hUdef
  set Λ' : LetA O n := abelian₂ W A a' (e + 1) with hΛ'def
  have hUΔ : U ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W C.hR.1 A _ e)
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W C.hR.1 0
  have hS' := hS
  obtain ⟨I, g, c₀, α, hg, hF⟩ := hS
  set N : ℕ := H + ∑ i, (-(α i 0)).toNat with hNdef
  obtain ⟨m₀, u₀, hu₀, u₁, hu₁, hl, ⟨r₀, hr₀, hu₀e⟩, ⟨s₁, hs₁, hu₁e⟩⟩ :=
    crt W (W.AΔ.mul_mem C.hR.1 (W.AΔ.pow_mem hUΔ 2)) (W.AΔ.pow_mem hp0Δ N) (cop_lamUp W C.hR C.hp0 A c' e N)

  have hx0 : InFNc W T a' 1 (u₀ • x) := by
    have hz : InFP W T c' (e + 1) 1 (Λ' • (u₀ • x)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₀ hxP
    have hrep0 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₀ hrep
    rw [smul_comm] at hrep0
    have hfr0 : ∀ m, InFr W a' (W.π₀ * U) (ps W 0 ^ H) (algebraMap (LetA O n) W.EE u₀ * f m) := by
      intro m
      obtain ⟨t, ht, hft⟩ := hfr m
      refine ⟨r₀ * t, W.AΔ.mul_mem hr₀ ht, ?_⟩
      rw [hΛ'def, lam_succ] at hft
      rw [hu₀e]
      simp only [map_mul, map_pow, map_one] at hft ⊢
      linear_combination (algebraMap (LetA O n) W.EE W.π₀ * algebraMap (LetA O n) W.EE U *
        algebraMap (LetA O n) W.EE r₀) * hft
    refine (h0 (u₀ • x) k _ hz hrep0 hfr0).2 ⟨κ, ?_⟩
    have := secIn_mulA W hS' hu₀
    convert this using 1
    funext m; ring

  have hMH : Mw A.G₀ A.S A.η (A.ty (a + 1)) ≤ H := by
    have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
    rw [Nat.sub_self, ← ha'def, ha'] at this
    rw [hHdef, ha']; exact this
  have key : ∀ i, ∃ (t : ℕ) (z : W.DD T), InFNc W T a' 1 z ∧ InFP W T c' (e + 1) 1 (Λ' • z) ∧
      RepVV W T c' (e + 1) (A.M PD.p) Λ' b sol z
        (fun m => lE W t * (algebraMap (LetA O n) W.EE u₁ * (g i * algebraMap O W.EE (c₀ i m)))) := by
    intro i
    by_cases hci : c₀ i = 0
    · refine ⟨0, 0, inFNc_zero T a', by rw [smul_zero]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' (e + 1) _,
        ?_⟩
      convert repVV_zero C A c' (e + 1) T hT.1 b sol hb Λ' using 1
      funext m
      simp [hci]
    · have hα : ∀ s, s < e → -(A.Hs a e s : ℤ) ≤ α i (s + 1) := by
        intro s hs
        by_contra hlt
        push_neg at hlt
        apply hci
        have hcond := (hg i).2 (s + 1) (by omega)
        have hH1 : A.Hs a' (e + 1) (s + 1) = A.Hs a e s := by
          rw [hs_succ, ha', add_sub_cancel_right]
        refine dvO_zero_high W C.hbij C.hinj C.hV C.hs C.h5 A hA c' hc' T hT (C.h3 T hT.1) (C.hmod T hT.1) b hb.1
          (e + 1) (s + 1) (by omega) (-(α i (s + 1))) ?_ (c₀ i) hcond
        rw [hH1]; omega
      have hgi : InId W (a + 1) (e + 1) (α i) (g i) := by rw [← ha']; exact (hg i).1
      have hNi : H + (-(α i 0)).toNat ≤ N := by
        have := Finset.single_le_sum (f := fun j => (-(α j 0)).toNat) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        omega
      obtain ⟨vv, hvv, g', heq, hId, hFr⟩ := mono_lift W C.hR A a e (α i) (g i) hgi hα N H hNi hs₁
      have hcondE : condNN W T a e b (fun s => α i (s + 1)) (c₀ i) := by
        intro s hs
        have h1 := (hg i).2 (s + 1) (by omega)
        rw [ha', filS_succ, dvO_succ] at h1
        obtain ⟨y, hy, hye⟩ := h1
        rwa [Formalism.MainNotions.UnusedSlot80.ArcF.φVB_inj T hye] at hy
      set F : Fin d → W.EE := fun m => g' * algebraMap O W.EE (c₀ i m) with hFdef
      have hFfr : ∀ m, InFr W a 1 (abelian₂ W A a e) (F m) := fun m => by
        have := inFr_mulA W hFr (W.AΔ.algebraMap_mem (c₀ i m))
        convert this using 1
        show g' * algebraMap O W.EE (c₀ i m) = _
        rw [mul_comm, ← IsScalarTower.algebraMap_apply]
      obtain ⟨κi, y, hyP, hyrep⟩ := pOfSec' W C.hO2 C.hR C.hH C.hCA A c' e (A.M PD.p) T hT.1 b sol hb F hFfr
      have hyN : InFNc W T a 1 y := by
        have hrepy : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ 0 • y)
            (fun m => lE W κi * F m) := by simpa using hyrep
        refine (IH y 0 _ hyP hrepy (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hFfr m) κi)).2 ⟨0, ?_⟩
        refine ⟨1, fun _ => lE W κi * g', fun _ => c₀ i, fun _ s => α i (s + 1),
          fun _ => ⟨Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W hId κi, hcondE⟩, fun m => ?_⟩
        simp only [Fin.sum_univ_one, hFdef]
        rw [show lE W 0 = 1 by simp [lE]]
        ring
      have hzN := up1 C T A hA hT a H hMH hvv y hyN
      obtain ⟨hzP, hzrep, -⟩ := transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol y (fun m => lE W κi * F m) hyP hyrep
        (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hFfr m) κi) H le_rfl hvv
      refine ⟨κi, (ps W 0 ^ H * vv) • W.φD T y, by rw [ha']; exact hzN, hzP, ?_⟩
      convert hzrep using 1
      funext m
      rw [hFdef]
      simp only [map_mul W.φE, φE_lE, AlgHom.commutes]
      rw [hu₁e]
      linear_combination (lE W κi * algebraMap O W.EE (c₀ i m)) * heq
  choose t z hzN hzP hzrep using key
  set Tt : ℕ := ∑ i, t i with hTt
  have htle : ∀ i, t i ≤ Tt := fun i =>
    Finset.single_le_sum (f := t) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hZrep : RepVV W T c' (e + 1) (A.M PD.p) Λ' b sol (∑ i, lA W ^ (Tt - t i) • z i)
      (fun m => lE W (Tt + κ) * (algebraMap (LetA O n) W.EE u₁ * f m)) := by
    have h1 := repVV_sum C A c' (e + 1) T hT.1 b sol hb Λ' Finset.univ (fun i => lA W ^ (Tt - t i) • z i)
      (fun i m => lE W (Tt - t i) * (lE W (t i) * (algebraMap (LetA O n) W.EE u₁ *
        (g i * algebraMap O W.EE (c₀ i m))))) (fun i _ => by
          have := repVV_smul W T c' (e + 1) _ Λ' b sol _ _ (lA_mem W (Tt - t i)) (hzrep i)
          rwa [← lE_eq] at this)
    convert h1 using 1
    funext m
    simp only [lE_mul]
    have : ∀ i, Tt - t i + t i = Tt := fun i => Nat.sub_add_cancel (htle i)
    simp only [this]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hF m]
    unfold lE; rw [pow_add]; ring
  have hZN : InFNc W T a' 1 (∑ i, lA W ^ (Tt - t i) • z i) :=
    inFNc_sum T a' _ _ fun i _ => inFNc_smul C.hR.1 T a' (lA_mem W _) (hzN i)
  have hZP : InFP W T c' (e + 1) 1 (Λ' • ∑ i, lA W ^ (Tt - t i) • z i) := by
    rw [Finset.smul_sum]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sum W T c' (e + 1) _ _ _ fun i _ => by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ (lA_mem W _) (hzP i)
  have hx1P : InFP W T c' (e + 1) 1 (Λ' • (u₁ • x)) := by
    rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₁ hxP
  have hrep1 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₁ hrep
  rw [smul_comm] at hrep1
  have hx1 := mem_of_sec_eq C A hA c' hc' T hT b sol hb (e + 1) (u₁ • x) _ k 0 (Tt + κ) _ hx1P hZP hZN hrep1
    (by rw [pow_zero, one_smul]; exact hZrep)
  have hsum := inFNc_add T a' hx0 hx1
  rw [← add_smul, ← hl] at hsum
  exact Formalism.MainNotions.UnusedSlot80.ArcC.arc_sat W C.hCA C.hsat C.hR T hT.1 A c' (e + 1)
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' (e + 1) T hT) x hxP ⟨m₀, hsum⟩

theorem secCrit_all (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (h0 : ∀ e, SecCrit0 A c' e T b sol) :
    ∀ e, Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol := by
  intro e
  induction e with
  | zero => exact secCrit_zero A c' T b sol
  | succ e IH =>
    intro x k f hxP hrep hfr
    constructor
    · intro hxN
      exact (step_mp C A hA c' hc' T hT b sol hb e IH (h0 e) x hxP hxN).2 k f hrep hfr
    · rintro ⟨κ, hS⟩
      exact step_mpr C A hA c' hc' T hT b sol hb e IH (h0 e) x k f hxP hrep hfr κ hS

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

def SecCrit0L (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
    ∀ (A : Formalism.MainNotions.ArcLiftingSetup.ArcP (Module.finrank ℚ_[l] ↥(K0 K))), A.OK → ∀ c' ∈ A.cuts,
      ∀ T, Formalism.MainNotions.ArcLiftingSetup.Win ((HW l).W K 1 LL hG) A T → ∀ (d : ℕ) (b : Fin d → ((HW l).W K 1 LL hG).DD T)
        (sol : Fin d → ℕ → Fin d → ↥LL.1), Formalism.MainNotions.ArcLiftingSetup.IsHor ((HW l).W K 1 LL hG) T c' b sol →
          ∀ e : ℕ, LevC.SecCrit0 (W := (HW l).W K 1 LL hG) A c' e T b sol

theorem ctx_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) (l : ℕ) [Fact l.Prime] (K LL : FinExt l)
    (hG : Good K 1 LL) (hCA : CaseA K LL) (h5l : 5 ≤ l) :
    haveI := neZero_finrank_max_unramified K
    LevC.Ctx ((HW l).W K 1 LL hG) := by
  obtain ⟨h3, -, h5, h9, hH, hTr, -, hSat⟩ := h
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hCW : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hG) := caseA_of_unram' (D.loc l) (HW l) hG hCA.1 hCA.2.1
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hCA.2.1
  have hK := finrank_K0_eq_one_of_le_Kur hCA.1
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hmod : ∀ T, IsCrys ((D.loc l).PD K) T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters ((HW l).W K 1 LL hG) T
      ((HW l).W K 1 LL hG).π₀ := fun T hT => ((h9 l K 1 LL hG T hT hs hp).2.2 hK).2
  have hc1 := Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hG)
  have := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hΔ : IsUnit ((((HW l).W K 1 LL hG).DelF.card : ℕ) : ↥(OL LL)) :=
    cardΔ_of (W := (HW l).W K 1 LL hG) (not_isUnit_p ((HW l).W K 1 LL hG) (valRing_rec (D.loc l) LL))
      (card_DelF (W := (HW l).W K 1 LL hG) hs hp hK (h9 l K 1 LL hG _ hc1))
  have hV := valRing_rec (D.loc l) LL
  have h5p : 5 ≤ ((D.loc l).PD K).p := by rw [(D.loc l).PD_p]; exact h5l
  refine ⟨hCW.1, hs, hp, h5p, hR, h5 l K 1 LL hG, h3 l K 1 LL hG, hmod, hΔ, hSat l K LL hG hCA h5l,
    saturation_pullback_of_ring_condition D HW F h9 l K LL hG hCA h5l, hTr l K 1 LL hG, hH l K 1 LL hG, hV.1, hV.2.1, hV, ?_⟩
  intro h0
  have := congrArg (algebraMap (↥(OL LL)) ↥LL.1) h0
  rw [map_natCast, map_zero] at this
  exact Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero ((HW l).W K 1 LL hG) this

theorem membership_criterion_of_level_zero (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) (h0 : SecCrit0L D HW) : SecCritL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  have C := ctx_of D HW F Cm h l K LL hG hCA h5l
  intro _ _ A hA c hc e _ _ T hT d b sol hb
  have hc' : c - ((A.len c : ℕ) : ZMod _) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  exact LevC.secCrit_all C A hA _ hc' T hT b sol hb (h0 l K LL hG hCA h5l A hA _ hc' T hT d b sol hb) e

theorem arc_coordinates_of_level_zero (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h0 : SecCrit0L D HW) : ArcCoordinatesTheorem D HW F Cm := fun h =>
  arc_coordinates_of_membership D HW F Cm (membership_criterion_of_level_zero D HW F Cm h h0) h

end Formalism.MainNotions.UnusedSlot80
end
end
