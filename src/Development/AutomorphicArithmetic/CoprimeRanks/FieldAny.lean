import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation
import Development.AutomorphicArithmetic.QuadraticCharacters.MemRealCyclotomicSubgroup
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.ExistsHostAxEven

section
open Formalism.HC Formalism.FrobeniusOrbits

noncomputable section

namespace HostParam.Seam

def IsRes (E : AbField) {M : ℕ} (r : (ZMod M)ˣ →* E.Gal) : Prop :=
  ∀ (a : ℕ) (h : a.Coprime E.N) (h' : a.Coprime M), r (ZMod.unitOfCoprime a h') = E.res (ZMod.unitOfCoprime a h)

structure FrameIso (C : Core) (φ : Frame) where
  iso : C.E.Gal ≃* φ.GG
  e_eq : φ.e = C.e
  ps_eq : ∀ g, φ.psC (iso g) = C.psG g
  ch_eq : ∀ g, φ.chC (iso g) = C.chG g
  conj_eq : iso C.E.conj = φ.cc
  iota_eq : iso C.iota = φ.iod
  A0_eq_image : ∀ g, g ∈ C.A0 ↔ ∃ s ∈ φ.A0, iso g = φ.tau1 s
  h_eq : ∀ (u : (ZMod C.E.N)ˣ) (v : (ZMod (2 ^ (φ.e + 2)))ˣ),
    (v : ZMod (2 ^ (φ.e + 2))) = (((u : ZMod C.E.N).val : ℕ) : ZMod (2 ^ (φ.e + 2))) →
    φ.hH (iso (C.E.res u)).2 = hcl φ.e v

structure Comparison₂ (C : Core) {φ : Frame} (H : HostRaw φ) extends FrameIso C φ where
  d_eq : H.d = C.d
  art_res : ∀ (a : ℕ) (h : a.Coprime C.E.N) (h' : a.Coprime H.condN),
    H.art (ZMod.unitOfCoprime a h') = iso (C.E.res (ZMod.unitOfCoprime a h))

def Comparison₂.resMap {C : Core} {φ : Frame} {H : HostRaw φ} (t : Comparison₂ C H) : (ZMod H.condN)ˣ →* C.E.Gal :=
  t.iso.symm.toMonoidHom.comp H.art



def FrameIso.pull {C : Core} {φ : Frame} (F : FrameIso C φ) (θ : φ.Char) : C.E.Gal →* ℂˣ := θ.comp F.iso.toMonoidHom

structure AdmQ (C : Core) (q : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_split : SplitsIn C.d q
  q_inertia : Nat.card (C.E.inertia q) ≤ 2

structure admitted (C : Core) (q QS : ℕ) : Prop extends AdmQ C q where
  QS_pos : 0 < QS
  QS_coprime : Nat.Coprime QS (q * C.d)
  QS_split : ∀ l : ℕ, l.Prime → l ∣ QS → SplitsIn C.d l
  cond_dvd : C.E.conductor ∣ QS * q * C.d

def ofP (ψ : PChar) : PrimChar := ⟨ψ.N, ψ.χ⟩

def toP (κ : PrimChar) (h : 0 < κ.1) (hp : κ.2.IsPrimitive) : PChar := @PChar.mk κ.1 ⟨h.ne'⟩ κ.2 hp


theorem ofP_fst_pos (ψ : PChar) : 0 < (ofP ψ).1 := Nat.pos_of_ne_zero (NeZero.ne ψ.N)

theorem ofP_snd_isPrimitive (ψ : PChar) : (ofP ψ).2.IsPrimitive := ψ.prim

structure TypeTie (T : HostType) (T' : HType) (κ : HConst) : Prop where
  eps_eq : T'.eps = T.eps
  kept_eq : ofP '' (T'.KEPT : Set PChar) = T.kept
  psK_eq : T'.psK.map ofP = T.psK
  P0_eq : T'.P0 = T.P0
  t_eq : T'.t = T.t
  Ct_eq : T'.Ct = T.Ct
  o_le : T.o ≤ κ.oB
  rB_eq : κ.rB = T.rrBound
  c_eq : κ.c = T.cA
  C_eq : κ.C = T.CB

def rescale (T : HostType) (T' : HType) (X : ℝ) : ℝ := X ^ ((T'.J : ℝ) / T.J)


structure RecordRows {φ : Frame} (H : HostRaw φ) (b : ℕ) : Prop where
  QS_exact : H.Exact
  QS_le : H.QS ≤ φ.ord ^ 2
  o_pow : φ.o ^ 64 ≤ 2 ^ φ.e
  q_ne_three : H.q ≠ 3
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(H.d : ℤ)) p = 1
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → 4 * l ≤ b

structure PreRows (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostRaw φ) (rr rr' : ℕ) : Prop where
  one_le_X : 1 ≤ X
  x_ge : X ^ ((1 : ℝ) / T.J) ≤ x
  x_le : x ≤ X
  ha5 : φ.TorsionIndexBounded κ.oB
  ha6 : H.OddPrimesSplitBelow (T.z X)
  ha7 : H.SmallPrimeSizeBounds T.SM (T.z X)
  ha8 : H.DiscriminantConductorSizes (T.z' X)
  ha9 : H.ModulusSizeBounds (T.z X)
  ha12 : H.PrimePairSizeCondition (T.z X) κ.rB rr rr'


end HostParam.Seam

end
end

section
open NumberField Formalism.HC Formalism.FrobeniusOrbits

namespace HostParam.Seam

private theorem ord_eq_mul (D : ModData) : D.frame.ord = Nat.card (D.cl.ker.map D.ξ) * 2 ^ D.e := by
  have h1 : Nat.card D.p1.ker = Nat.card (D.cl.ker.map D.ξ) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨D.p2 x.1, ?_⟩) ⟨fun x y h => ?_, ?_⟩)
    · obtain ⟨⟨_, u, rfl⟩, hx⟩ := x
      exact ⟨u, hx, rfl⟩
    · have h2 : D.p2 x.1 = D.p2 y.1 := congrArg Subtype.val h
      have h3 : D.p1 x.1 = D.p1 y.1 := (x.2 : D.p1 x.1 = 1).trans (y.2 : D.p1 y.1 = 1).symm
      exact Subtype.ext (Subtype.ext (Prod.ext h3 h2))
    · rintro ⟨_, u, hu, rfl⟩
      exact ⟨⟨D.eta.rangeRestrict u, hu⟩, rfl⟩
  rw [D.ord_eq, ← h1, ← Subgroup.card_mul_index D.p1.ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr D.projection_surjective, Subgroup.card_top, (hostGroup D.e).2.2.2.2.2.2.1]

private theorem cl_eq_one_iff (D : ModData) (u : (ZMod D.m)ˣ) :
    D.cl u = 1 ↔ ZMod.unitsMap D.tower u = 1 ∨ ZMod.unitsMap D.tower u = -1 :=
  hcl_eq_hcl_iff (e := D.e) (u := ZMod.unitsMap D.tower u) (v := 1)

private theorem unitsMap_unitsMap {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (u : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]

private theorem step {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) (b : EvenGrp.B Ξ)
    (hb : b ∈ (AnyGrp.data Ξ (e + 1)).cl.ker.map (AnyGrp.data Ξ (e + 1)).ξ) :
    b ∈ (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ := by
  obtain ⟨v, hv, rfl⟩ := hb
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective (EvenGrp.QS_dvd Ξ (e + 1)) v
  have hp : 2 ^ (e + 2) ∣ 2 ^ (e + 1 + 2) := pow_dvd_pow 2 (by omega)
  have hd : Nat.lcm (2 ^ (e + 2)) M ∣ Nat.lcm (2 ^ (e + 1 + 2)) M :=
    Nat.lcm_dvd (hp.trans (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)
  refine ⟨ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hd u), ?_, ?_⟩
  · have h1 := (cl_eq_one_iff (AnyGrp.data Ξ (e + 1)) _).mp hv
    refine (cl_eq_one_iff (AnyGrp.data Ξ e) _).mpr ?_
    have h2 : ZMod.unitsMap (EvenGrp.good_QS Ξ e).2.1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hd u)) =
        ZMod.unitsMap hp (ZMod.unitsMap (EvenGrp.good_QS Ξ (e + 1)).2.1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) u)) := by
      simp only [unitsMap_unitsMap]
    rcases h1 with h1 | h1
    · exact Or.inl (h2.trans ((congrArg (ZMod.unitsMap hp) h1).trans (map_one _)))
    · exact Or.inr (h2.trans ((congrArg (ZMod.unitsMap hp) h1).trans (D7.unitsMap_neg_one hp)))
  · refine (EvenGrp.xi_unitsMap Ξ e _).trans (Eq.trans ?_ (EvenGrp.xi_unitsMap Ξ (e + 1) u).symm)
    simp only [EvenGrp.xiW, MonoidHom.comp_apply, unitsMap_unitsMap]

private theorem ord_succ_le {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    (AnyGrp.frame Ξ (e + 1)).ord ≤ 2 * (AnyGrp.frame Ξ e).ord := by
  let U : ℕ → Subgroup (EvenGrp.B Ξ) := fun e => (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ
  have h0 : (AnyGrp.frame Ξ e).ord = Nat.card (U e) * 2 ^ e := ord_eq_mul (AnyGrp.data Ξ e)
  have h1 : (AnyGrp.frame Ξ (e + 1)).ord = Nat.card (U (e + 1)) * 2 ^ (e + 1) := ord_eq_mul (AnyGrp.data Ξ (e + 1))
  have h2 : Nat.card (U (e + 1)) ≤ Nat.card (U e) := Subgroup.card_le_of_le fun b hb => step Ξ e b hb
  rw [h0, h1]
  calc Nat.card (U (e + 1)) * 2 ^ (e + 1) ≤ Nat.card (U e) * 2 ^ (e + 1) := Nat.mul_le_mul_right _ h2
    _ = _ := by ring

private theorem ord_le {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    (AnyGrp.frame Ξ e).ord ≤ Nat.card Ξ * 2 ^ e := by
  let U : Subgroup (EvenGrp.B Ξ) := (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ
  have h0 : (AnyGrp.frame Ξ e).ord = Nat.card U * 2 ^ e := ord_eq_mul (AnyGrp.data Ξ e)
  rw [h0, ← EvenGrp.card_B]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_card_group _)

theorem anyFrame_window :
    ∀ {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)),
      (∀ e : ℕ, (AnyGrp.frame Ξ (e + 1)).ord ≤ 2 * (AnyGrp.frame Ξ e).ord) ∧
      (∀ (e : ℕ) (hev : ∀ χ ∈ Ξ, χ.Even), (EvenGrp.frame Ξ e hev).ord = (AnyGrp.frame Ξ e).ord) ∧
      ∀ (e₀ : ℕ) (W : ℝ), ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ) ≤ W →
        ∃ e : ℕ, e₀ ≤ e ∧ W ≤ (AnyGrp.frame Ξ e).ord ∧ ((AnyGrp.frame Ξ e).ord : ℝ) ≤ 2 * W := by
  intro M _ Ξ
  refine ⟨ord_succ_le Ξ, fun e hev => ?_, fun e₀ W hW => ?_⟩
  · exact (EvenData.ord_eq _).trans (ModData.ord_eq (AnyGrp.data Ξ e)).symm
  · classical
    have hex : ∃ k : ℕ, W ≤ (AnyGrp.frame Ξ (e₀ + k)).ord := by
      obtain ⟨n, hn⟩ := exists_nat_ge W
      refine ⟨n, hn.trans ?_⟩
      have h2 : 2 ^ (e₀ + n) ≤ (AnyGrp.frame Ξ (e₀ + n)).ord := (AnyGrp.frame Ξ (e₀ + n)).two_pow_le_ord
      have h3 : e₀ + n < 2 ^ (e₀ + n) := Nat.lt_two_pow_self
      exact_mod_cast (by omega : n ≤ (AnyGrp.frame Ξ (e₀ + n)).ord)
    refine ⟨e₀ + Nat.find hex, Nat.le_add_right _ _, Nat.find_spec hex, ?_⟩
    rcases h : Nat.find hex with _ | k
    · have h1 : ((AnyGrp.frame Ξ (e₀ + 0)).ord : ℝ) ≤ ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ) :=
        Nat.cast_le.mpr (ord_le Ξ e₀)
      have h2 : (0 : ℝ) ≤ ((Nat.card Ξ * 2 ^ e₀ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · have h1 := not_le.mp (Nat.find_min hex (by omega : k < Nat.find hex))
      have h2 : ((AnyGrp.frame Ξ (e₀ + (k + 1))).ord : ℝ) ≤ ((2 * (AnyGrp.frame Ξ (e₀ + k)).ord : ℕ) : ℝ) :=
        Nat.cast_le.mpr (ord_succ_le Ξ (e₀ + k))
      push_cast at h2
      linarith

end HostParam.Seam
end

section
open NumberField Formalism.FrobeniusOrbits Formalism.HC

noncomputable section

namespace HostParam.Seam

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M))

private theorem conductor_divisor_bounds {φ : Frame} {H : HostRaw φ} {e b : ℕ} (hQ : H.QS ∣ Nat.lcm (2 ^ (e + 2)) M) (hb : 4 * M ≤ b) :
    (∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → l ∣ M ∧ 4 * l ≤ b) ∧ H.QS ≤ 4 * M * 2 ^ e := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 := hQ.trans (Nat.lcm_dvd_mul _ _)
  refine ⟨fun l hl h2 h => ?_, (Nat.le_of_dvd (by positivity) h1).trans (le_of_eq (by ring))⟩
  have h3 : l ∣ M := (hl.dvd_mul.1 (h.trans h1)).resolve_left fun h4 =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h4))
  have := Nat.le_of_dvd hM h3
  exact ⟨h3, by omega⟩

theorem exists_fieldRows_any_ord {e q d b : ℕ} (hH : HostHyp q d) (hq3 : q ≠ 3) (hc : Nat.Coprime M (q * d))
    (he : 4 * M ≤ 2 ^ e) (ho : Nat.card Ξ ^ 64 ≤ 2 ^ e) (hb : 4 * M ≤ b)
    (hs : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(d : ℤ)) p = 1) :
    ∃ (φ : Frame) (H : HostAx φ), φ.ord = (AnyGrp.frame Ξ e).ord ∧ φ.e = e ∧ H.q = q ∧ H.d = d ∧ φ.o = Nat.card Ξ ∧ FieldRows H.toHostRaw b ∧
      H.QS ∣ Nat.lcm (2 ^ (e + 2)) M ∧ H.QS ≤ 4 * M * φ.ord ∧
      H.KeptInXp (Level.ofSub Ξ).KEPT ∧ H.ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK ∧
      (Nat.Coprime M 15 → H.CoprimeFifteen) ∧ ((∃ j : ℕ, Nat.card Ξ = 2 ^ j) → φ.TwoGroup) ∧
      ((∀ χ ∈ Ξ, χ.Even) → H.MuPM ∧ H.KeptEqChat (Level.ofSub Ξ).KEPT) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have he2 : 2 ≤ e := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 (by omega)
  have hs' : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1 := fun l hl h2 h =>
    hs l hl h2 (by have := Nat.le_of_dvd hM h; omega)
  have fin : ∀ {φ : Frame} {H : HostRaw φ}, φ.e = e → H.QS ≤ 4 * M * 2 ^ e → H.QS ≤ 4 * M * φ.ord := fun {φ H} h1 h2 =>
    h2.trans (Nat.mul_le_mul_left _ (h1 ▸ φ.two_pow_le_ord))
  by_cases hev : ∀ χ ∈ Ξ, χ.Even
  · obtain ⟨r1, r2⟩ := conductor_divisor_bounds (H := EvenGrp.host Ξ e hev hH hc he2 hs') (EvenGrp.QS_dvd Ξ e) hb
    exact ⟨_, HostAx.ofRaw (EvenGrp.host Ξ e hev hH hc he2 hs'), (anyFrame_window Ξ).2.1 e hev, rfl, rfl, rfl,
      EvenGrp.o_eq Ξ e hev,
      ⟨EvenGrp.psQ Ξ e hev hH hc he2 hs', EvenGrp.exists_sqq Ξ e hev hH hc he2 hs', EvenGrp.exact Ξ e hev hH hc he2 hs',
        EvenGrp.QS_le Ξ e hev he, by rw [EvenGrp.o_eq]; exact ho, hq3, hs, fun l h1 h2 h3 => (r1 l h1 h2 h3).2⟩,
      EvenGrp.QS_dvd Ξ e, fin rfl r2, EvenGrp.keptInXp Ξ e hev hH hc he2 hs', EvenGrp.exceptional_character_condition Ξ e hev hH hc he2 hs',
      EvenGrp.coprimeFifteen_of_coprime Ξ e hev hH hc he2 hs', EvenGrp.twoGroup Ξ e hev,
      fun _ => ⟨EvenGrp.muPM Ξ e hev hH hc he2 hs' hq3, EvenGrp.keptEqChat Ξ e hev hH hc he2 hs'⟩⟩
  · obtain ⟨r1, r2⟩ := conductor_divisor_bounds (H := AnyGrp.host Ξ e hH hc he2 hs') (EvenGrp.QS_dvd Ξ e) hb
    exact ⟨_, HostAx.ofRaw (AnyGrp.host Ξ e hH hc he2 hs'), rfl, rfl, rfl, rfl, AnyGrp.o_eq Ξ e,
      ⟨AnyGrp.psQ Ξ e hH hc he2 hs', AnyGrp.exists_sqq Ξ e hH hc he2 hs', AnyGrp.exact Ξ e hH hc he2 hs',
        AnyGrp.QS_le Ξ e he, by rw [AnyGrp.o_eq]; exact ho, hq3, hs, fun l h1 h2 h3 => (r1 l h1 h2 h3).2⟩,
      EvenGrp.QS_dvd Ξ e, fin rfl r2, AnyGrp.keptInXp Ξ e hH hc he2 hs', AnyGrp.exceptional_character_condition Ξ e hH hc he2 hs',
      AnyGrp.coprimeFifteen_of_coprime Ξ e hH hc he2 hs', AnyGrp.twoGroup Ξ e, fun h => absurd h hev⟩

end HostParam.Seam

end
end
