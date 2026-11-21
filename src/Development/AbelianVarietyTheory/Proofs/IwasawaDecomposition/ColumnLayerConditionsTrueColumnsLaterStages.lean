import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.HermitianColumns.SymAll
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeUOperatorRationalInvertibleRamifiedForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReLev0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumnsStatement
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ErrTies

theorem trace_rat {R : Ranks} (H : Host R) (x : H.E) (hx : x ∈ H.K) :
    ∃ r : ℚ, (r : H.E) = x + H.conj x := by
  have h1 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x, hx⟩
  have h2 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x + 1, add_mem hx (one_mem _)⟩
  refine ⟨Algebra.norm ℚ (⟨x + 1, add_mem hx (one_mem _)⟩ : H.K) -
    Algebra.norm ℚ (⟨x, hx⟩ : H.K) - 1, ?_⟩
  rw [eq_ratCast] at h1 h2
  push_cast
  rw [h1, h2]
  simp only [map_add, map_one]
  ring

theorem no_ramified_norm {T d : ℕ} (hT : T.Prime) (hd : d.Prime) (h2 : T ≠ 2) (hTd : T ≠ d)
    (a : ℤ) (s : ℚ) (h : ((T : ℚ) * a) ^ 2 - 4 * T = -d * s ^ 2) : False := by
  have hTZ : Prime (T : ℤ) := Nat.prime_iff_prime_int.1 hT
  have hq : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hs : s * s.den = s.num := Rat.mul_den_eq_num s
  have hZ : (T : ℤ) * ((T * a ^ 2 - 4) * (s.den : ℤ) ^ 2) = -d * s.num ^ 2 := by
    have : (T : ℚ) * ((T * a ^ 2 - 4) * (s.den : ℚ) ^ 2) = -d * (s.num : ℚ) ^ 2 := by
      rw [← hs]
      linear_combination (s.den : ℚ) ^ 2 * h
    exact_mod_cast this
  have hnd : ¬ (T : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg, Int.natCast_dvd_natCast]
    exact fun h => hTd ((Nat.prime_dvd_prime_iff_eq hT hd).1 h)
  have hp : (T : ℤ) ∣ s.num :=
    hTZ.dvd_of_dvd_pow ((hTZ.dvd_or_dvd ⟨_, hZ.symm⟩).resolve_left hnd)
  obtain ⟨p, hp'⟩ := hp
  have hT0 : (T : ℤ) ≠ 0 := hTZ.ne_zero
  have hZ2 : (T * a ^ 2 - 4) * (s.den : ℤ) ^ 2 = T * (-d * p ^ 2) := by
    apply mul_left_cancel₀ hT0
    rw [hZ, hp']; ring
  have h4 : (T : ℤ) ∣ 2 ^ 2 * (s.den : ℤ) ^ 2 :=
    ⟨a ^ 2 * (s.den : ℤ) ^ 2 + d * p ^ 2, by linear_combination -hZ2⟩
  rcases hTZ.dvd_or_dvd h4 with h5 | h5
  · have h6 : (T : ℤ) ∣ ((2 : ℕ) : ℤ) := hTZ.dvd_of_dvd_pow h5
    rw [Int.natCast_dvd_natCast] at h6
    exact h2 ((Nat.prime_dvd_prime_iff_eq hT Nat.prime_two).1 h6)
  · have h6 : T ∣ s.den := Int.natCast_dvd_natCast.1 (hTZ.dvd_of_dvd_pow h5)
    have h7 : T ∣ s.num.natAbs := Int.natCast_dvd.1 ⟨p, hp'⟩
    have h8 := Nat.dvd_gcd h7 h6
    rw [s.reduced] at h8
    exact hT.one_lt.ne' (Nat.dvd_one.1 h8)

theorem not_both_mem {R : Ranks} (H : Host R) {T : ℕ} (hT : T.Prime) (π π' : 𝓞 H.E)
    (hK : (π : H.E) ∈ H.K) (hc : (π' : H.E) = H.conj π) (hN : (π : H.E) * H.conj π = T)
    (M : ℕ) (hM : 2 * H.d ∣ M) (hcong : π - 1 ∈ Ideal.span {(M : 𝓞 H.E)})
    (P : Ideal (𝓞 H.E)) (hP : P ≠ ⊤) (h1 : π ∈ P) (h2 : π' ∈ P) : False := by
  have hTe : π * π' = (T : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    push_cast
    rw [← hN, ← hc]
  have hTP : (T : 𝓞 H.E) ∈ P := hTe ▸ P.mul_mem_right _ h1
  have hTM : ¬ T ∣ M := by
    rintro ⟨k, hk⟩
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hcong
    have : (1 : 𝓞 H.E) = π - c * k * T := by
      rw [hk] at hc
      push_cast at hc
      linear_combination hc
    rw [this]
    exact P.sub_mem h1 (P.mul_mem_left _ hTP)
  have hT2 : T ≠ 2 := fun h => hTM (h ▸ (Dvd.intro _ rfl).trans hM)
  have hTd : T ≠ H.d := fun h => hTM (h ▸ (Dvd.intro_left _ rfl).trans hM)
  obtain ⟨r, hr⟩ := trace_rat H π hK
  have hint : IsIntegral ℤ r := by
    have : IsIntegral ℤ (algebraMap ℚ H.E r) := by
      rw [eq_ratCast, hr, ← hc]
      exact π.isIntegral_coe.add π'.isIntegral_coe
    exact (isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [eq_intCast] at ha
  have haE : (a : 𝓞 H.E) = π + π' := by
    apply RingOfIntegers.ext
    push_cast
    rw [← ha] at hr
    push_cast at hr
    rw [← hc] at hr
    exact (map_intCast (algebraMap (𝓞 H.E) H.E) a).trans hr
  have hTa : (T : ℤ) ∣ a := by
    by_contra hn
    have hcop : IsCoprime (T : ℤ) a :=
      ((Nat.prime_iff_prime_int.1 hT).irreducible.coprime_iff_not_dvd).2 hn
    obtain ⟨x, y, hxy⟩ := hcop
    apply hP
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 H.E) = x * T + y * (π + π') := by
      rw [← haE]
      exact_mod_cast (congrArg (fun z : ℤ => (z : 𝓞 H.E)) hxy).symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hTP) (P.mul_mem_left _ (P.add_mem h1 h2))
  obtain ⟨a', rfl⟩ := hTa
  set b := H.sqd with hb
  have hb0 : b ≠ 0 := Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero H
  have hb2 : b ^ 2 = -(H.d : H.E) := Examples₂.bE_sq H
  have hbc : H.conj b = -b := Examples₂.conj_bE H
  obtain ⟨s, hs⟩ := trace_rat H ((π : H.E) / b) (div_mem hK (Formalism.MainNotions.UnusedSlot33.HK.bE_mem H))
  rw [map_div₀, hbc] at hs
  have hs' : (s : H.E) * b = π - H.conj π := by
    rw [hs]; field_simp; ring
  refine no_ramified_norm hT H.hyp.2.1 hT2 hTd a' s ?_
  have hE : (((T : ℚ) * a') ^ 2 - 4 * T : ℚ) = ((-(H.d : ℚ) * s ^ 2 : ℚ) : H.E) := by
    rw [← ha] at hr
    push_cast at hr ⊢
    rw [hr, ← hN, ← hb2]
    linear_combination (-((s : H.E) * b) - (π - H.conj π)) * hs'
  exact_mod_cast hE

theorem embLL_tauLL (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    D.what₂.embLL (tauLL D τ x) = D.host.emb (D.eTau τ).1 x := by
  rw [tauLL, Host.emb, ← D.embE_φ₀]
  rfl

def errOfTies (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : ErrX D where
  piG := (H.levelZeroCompatibility D.u₀).piG
  piG_K := (H.levelZeroCompatibility D.u₀).piG_K
  piG_norm i := by rw [← Examples₂.star_eq_conj]; exact (H.levelZeroCompatibility D.u₀).piG_norm i
  piT u := (H.atT u).piU
  piT_K u := (H.atT u).piU_K
  piT_norm u := (H.atT u).piU_norm
  piT_cong u := (H.atT u).piU_cong
  vPl u v := (H.base.vT u v).1
  vPl_inj u := fun _ _ h => (H.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal u v := (H.base.vT u v).2

theorem seenDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : SeenDef D (errOfTies D H) := by
  intro u w hw
  obtain ⟨v⟩ : Nonempty (D.mem u).A.vT := by
    letI := (D.mem u).A.vTFin
    rw [← Fintype.card_pos_iff, (D.mem u).A.card_vT]
    unfold Ranks.f Ranks.n
    positivity
  have hτ : ∀ τ, tauLL D τ ((H.atT u).piU : D.host.E) = D.embE ((H.atT u).piU : D.host.E) := by
    intro τ
    rw [tauLL, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host _ (D.eTau τ).2 _ (H.atT u).piU_K]
  have key := (H.atT u).seen w hw v (H.atT u).piU _ (embLL_tauLL D _ _)
  rw [hτ] at key
  change _ ↔ ∀ τ, 0 < D.what₂.places.val w (tauLL D τ ((H.atT u).piU : D.host.E))
  simp only [hτ]
  constructor
  · intro hs _
    rw [if_pos hs] at key
    exact key.2 ((H.atT u).Pv_pi v)
  · intro h
    by_contra hs
    rw [if_neg hs, Formalism.L2.Col.mem_conjIdeal] at key
    refine not_both_mem D.host (D.mem u).A.T_prime (H.atT u).piU _ (H.atT u).piU_K ?_
      (H.atT u).piU_norm _ ?_ (H.atT u).piU_cong _ ((H.atT u).Pv_max v).ne_top
      ((H.atT u).Pv_pi v) (key.1 (h ((D.fm u).tauOf w v)))
    · exact Examples₂.star_eq_conj D.host _
    · obtain ⟨c, hc⟩ := D.host.two_dvd_QS
      refine ⟨c * D.host.q * (D.host.g 0 * D.host.g 1) ^ 2, ?_⟩
      trans D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2
      · ring
      · rw [hc]
        ring

theorem tauOfDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : TauOfDef D (errOfTies D H) := by
  intro u w hw v x
  have key := (H.atT u).seen w hw v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) _ (embLL_tauLL D _ _)
  have hx : x ∈ (H.base.vT u v).1.asIdeal ↔
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ (H.atT u).Pv v := by
    rw [← (H.atT u).Pv_over v, Ideal.mem_comap]
  have hc : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    exact (Examples₂.star_eq_conj D.host _).trans ((Examples₂.conj_eq_self_iff D.host _).2 (x : D.host.F).2)
  refine hx.trans (Iff.trans ?_ key.symm)
  split_ifs
  · rfl
  · rw [Formalism.L2.Col.mem_conjIdeal, hc]

theorem exists_errX : ∀ (D : D7) (H : Formalism.L2.Herm.ColsHermS D), ∃ eX : ErrX D, eX.piG = (H.levelZeroCompatibility D.u₀).piG ∧ (∀ u, eX.piT u = (H.atT u).piU) ∧ (∀ u v, eX.vPl u v = (H.base.vT u v).1) ∧ PiGLevel D H.base.lev0 eX ∧ PiTLevel D H.base.lev0 eX ∧ SeenDef D eX ∧ TauOfDef D eX := by
  intro D H
  refine ⟨errOfTies D H, rfl, fun _ => rfl, fun _ _ => rfl, ?_, ?_, seenDef D H, tauOfDef D H⟩
  · intro u i v h
    have := (H.levelZeroCompatibility u).splitG_pi i v h
    rw [H.piG u D.u₀, Examples₂.star_eq_conj] at this
    exact this
  · intro u v z hz y
    exact (H.levelZeroCompatibility u).fM_pi _ _ z hz y

end GlobalTheory.Mem.ErrTies
end
end

section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.L2.Col

theorem le_N_of_mem_gamRanks (R : Ranks) {n : ℕ} (hn : n ∈ gamRanks R) : n ≤ R.N R.m := by
  have hY : ∀ j, j ≤ R.m → R.rankY j ≤ R.N R.m := by
    intro j hj
    have : j * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ hj
    unfold Ranks.rankY Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have hm := R.two_le_m
  simp only [gamRanks, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj.2) _
  · exact hY _ le_rfl
  · exact hY _ (Nat.sub_le _ _)
  · simpa [Ranks.rankY, Ranks.nV] using hY 1 (by omega)

theorem DGam_dvd_of_minkMult : ∀ {X : Fields} (R : Ranks), X.Ok →
    ∀ M, Formalism.MainNotions.MinkMult (2 * X.f * R.N R.m) M → DGam X.E R ∣ M := by
  intro X R hX M hM
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  refine DGam_dvd (posStar_of_ok hX) R fun a ha => ?_
  obtain ⟨n, hn, N, h1, -, rfl⟩ := Set.mem_iUnion₂.1 ha
  haveI := autO_finite (posStar_of_ok hX) h1
  refine GlobalTheory.DGamOnRecord.card_dvd_of_minkMult hM ?_ _
  rw [hE]
  exact Nat.mul_le_mul_left _ (le_N_of_mem_gamRanks R hn)

end GlobalTheory.Mem.Col2
end
end

section
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_kv_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by

  have hval : Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) :
      v.adicCompletion F)) < 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem (K := F) _).2 h
  have hmax : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    (Valuation.mem_maximalIdeal_iff _ Valued.v).2 hval
  have hres := (IsLocalRing.residue_eq_zero_iff _).2 hmax
  simpa using hres

theorem mem_range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp : (B.host.g i).Prime := B.host.g_prime i

  have hmem : B.host.g i * (B.host.g i - 1) ∈ [B.toPre.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1),
      B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4] := by
    fin_cases i <;> simp
  obtain ⟨z0, -, hz0⟩ := B.roots_Ks _ hmem
  have hN : B.host.g i * (B.host.g i - 1) ≠ 0 :=
    Nat.mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot (B.embLL z0) (B.host.g i * (B.host.g i - 1)) := by
    rw [hz0]; exact Complex.isPrimitiveRoot_exp _ hN

  have hprim' : IsPrimitiveRoot (B.embLL z0 ^ (B.host.g i - 1)) (B.host.g i) :=
    hprim.pow (Nat.pos_of_ne_zero hN) (mul_comm _ _)
  have : NeZero (B.host.g i) := ⟨hp.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim'.eq_pow_of_pow_eq_one hz
  exact ⟨(z0 ^ (B.host.g i - 1)) ^ k, by rw [map_pow, map_pow, hk]⟩

theorem psi0Rat (X : Stages) (T : ∀ u, Forms0 X.toD7 u) (u : X.toD7.what₂.Word) : Formalism.L2.G.LevelZeroCharacterRational T u := by
  intro i v h x

  have hx : ((T u).gl.psi0 i v h x) ^ X.toD7.host.g i = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_kv_eq_zero _ v _ h, zero_mul,
      AddChar.map_zero_eq_one]
  exact mem_range_of_pow_g X.B i _ hx

variable {D : D7}

def levOf (C : ColsTiedSym D) : LevelData D := C.herm.base.lev0

def formsOf (C : ColsTiedSym D) (u : D.what₂.Word) : Forms0 D u := (C.forms u).to0

def errOf (H : Formalism.L2.Herm.ColsHermS D) : ErrX D := (GlobalTheory.Mem.ErrTies.exists_errX D H).choose

theorem errOf_piG (H : Formalism.L2.Herm.ColsHermS D) : (errOf H).piG = (H.levelZeroCompatibility D.u₀).piG :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.1

theorem errOf_piT (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) : (errOf H).piT u = (H.atT u).piU :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.1 u

theorem errOf_vPl (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    (errOf H).vPl u v = (H.base.vT u v).1 :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.2.1 u v

theorem joint0 (C : ColsTiedSym D) (u : D.what₂.Word) : Joint0 (levOf C) u (formsOf C u) := by
  unfold levOf formsOf
  exact C.joint0 u

theorem dGamChoice_of_lcm (X : Stages) (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) :
    DGamChoice_at X.toD7 := by
  intro M hM u

  have hc : (X.toD7.mem u).C = X.C.chTw u X.C.mu0 := (X.C.memberColumns_twistedChain_base u).symm
  rw [hc, hDG u X.C.mu0]
  have hf : X.B.fields.f = X.B.R.f := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws X.B).2
  refine GlobalTheory.Mem.Col2.DGam_dvd_of_minkMult X.B.R (GlobalTheory.Mem.FieldsLaws.fields_ok (B := X.B)) M ?_
  rw [hf]
  exact hM

theorem colLay_of_herm (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R)
    (H : Formalism.L2.Herm.ColsHermS X.toD7) (T : ∀ u, Forms0 X.toD7 u) (hJ : ∀ u, Joint0 H.base.lev0 u (T u)) :
    ColLay X.toD7 H.base.lev0 (errOf H) where
  piG_lev := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.1
  piT_lev := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.1
  seen := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.2.1
  tauOf := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.2.2
  one u μ := by
    have h0 : (X.C.chTw X.B.u₀ X.C.mu0).DGam = (X.C.mem X.B.u₀).C.DGam :=
      congrArg (fun c => c.DGam) (X.C.memberColumns_twistedChain_base X.B.u₀)
    exact (hDG u μ).trans ((hDG X.B.u₀ X.C.mu0).symm.trans h0)
  mink := dGamChoice_of_lcm X hDG
  atT := GlobalTheory.T.heckeUOperator_rational_invertible_ramifiedForms X hX H T hJ (fun u => psi0Rat X T u)

theorem colLay_of_tied (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) (C : ColsTiedSym X.toD7) :
    ColLay X.toD7 (levOf C) (errOf C.herm) :=
  colLay_of_herm X hX hDG C.herm (formsOf C) (joint0 C)

end GlobalTheory.Mem.Top.ColOwe

end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ExtraTie

open Formalism.L2.Herm

theorem errX_eq {D : D7} (X : FullTiedS D) (H : ColsHermS D) (hX : X.cols = H) (e : ErrX D)
    (h1 : e.piG = (H.levelZeroCompatibility D.u₀).piG) (h2 : ∀ u, e.piT u = (H.atT u).piU)
    (h3 : ∀ u v, e.vPl u v = (H.base.vT u v).1) : e = toErrXS X := by
  subst hX
  obtain ⟨piG, piG_K, piG_norm, piT, piT_K, piT_norm, piT_cong, vPl, vPl_inj, norm_mem_place_ideal⟩ := e
  have e1 : piG = (X.levelZeroCompatibility D.u₀).piG := h1
  have e2 : piT = fun u => (X.atT u).piU := funext h2
  have e3 : vPl = fun u v => (X.base.vT u v).1 := funext fun u => funext (h3 u)
  subst e1 e2 e3
  rfl

end GlobalTheory.Mem.Col2.TC.ExtraTie

end
end

section
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

variable {B : Base} {C : Cols B} {Z : Later B C} (Z' : Later B C)

set_option maxHeartbeats 4000000 in

def forms0Re {u : B.Word} (T : Forms0 (recOf Z) u) : Forms0 (recOf Z') u :=
  { T with
    atT := atTTRe Z' T.atT
    cls0 := clsRe Z' T.cls0
    val0 := valRe Z' T.val0
    lv0 := lvRe Z' T.lv0 }

set_option maxHeartbeats 4000000 in
theorem columnFormsAlongLaterStages_stageZero_eq (T : ColsTiedSym (recOf Z)) (u : B.Word) :
    ((colsRe Z' T).forms u).to0 = forms0Re Z' (T.forms u).to0 := rfl

open Formalism.MainNotions.G in
set_option maxHeartbeats 4000000 in

theorem forms0Re_setGat (g : ∀ u (w : (recOf Z).what₂.places.Pl),
      GIdx (recOf Z).host ((recOf Z).mem u).A.T ((recOf Z).what₂.places.resChar w) → GAtP ((recOf Z).what₂.places.resChar w))
    (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ ((recOf Z).mem u).A.Mu0) {u : B.Word} (T : Forms0 (recOf Z) u) :
    forms0Re { Z with G := { Z.G with gat := g, gat_d := hd } } T = Formalism.L2.G.forms0Set (recOf Z) g hd T := rfl

end Re

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

section Std

variable (l : I.Laws) {Z : Later B (I.cols l)} (Z' : Later B (I.cols l))

set_option maxHeartbeats 8000000 in

theorem stdC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (h : I.StdC l Z T) : I.StdC l Z' (colsRe Z' T) := fun u =>
  { h u with gl := { (h u).gl with } }

set_option maxHeartbeats 8000000 in

theorem stdLvC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (u : B.Word) (h : I.StdLvC l Z u (T.forms u)) :
    I.StdLvC l Z' u ((colsRe Z' T).forms u) := h

end Std

variable (h : I.Ok) (p : TC.Pins B X) (l : I.Laws)

variable (Z : Later B (I.cols l))

theorem dGam_cols (u : B.Word) (a : I.ι) : ((I.cols l).chTw u a).DGam = DGam B.fields.E B.R := rfl

theorem colLay_of_tie (T : ColsTiedSym (I.rec7 l Z)) : ColLay (I.rec7 l Z) T.herm.base.lev0 (errOf T.herm) :=
  colLay_of_tied ⟨B, I.cols l, Z.W, Z.V, Z.S, Z.N, Z.G⟩ ⟨X⟩ (dGam_cols I l) T

open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in

theorem colLay_colT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z),
    ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1) := by
  intro B f T w Z t
  have e : errOf t.C.herm = Formalism.L2.Herm.toErrXS t.full.1 :=
    GlobalTheory.Mem.Col2.TC.ExtraTie.errX_eq t.full.1 t.C.herm t.full.2 (errOf t.C.herm) (errOf_piG _) (errOf_piT _) (errOf_vPl _)
  have hl : t.full.1.base.lev0 = t.C.herm.base.lev0 :=
    congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) t.full.2
  rw [hl, ← e]
  exact colLay_of_tie w.I w.l Z t.C

end GlobalTheory.Mem.Top.ColOwe

end
end
