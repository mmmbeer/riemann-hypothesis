import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalRingCardinality.ConjSqrtMinusD

section
noncomputable section

namespace GlobalTheory.Mem.Cert

noncomputable def powMod (a m k : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 1) (fun _ ih e => (ih (e / 2) ^ 2 * a ^ (e % 2)) % m) k

theorem powMod_succ (a m k e : ℕ) : powMod a m (k + 1) e = (powMod a m k (e / 2) ^ 2 * a ^ (e % 2)) % m := rfl

theorem powMod_cast (a m k : ℕ) : ∀ e : ℕ, e < 2 ^ k → ((powMod a m k e : ℕ) : ZMod m) = (a : ZMod m) ^ e := by
  induction k with
  | zero =>
    intro e h
    obtain rfl : e = 0 := by omega
    simp [powMod]
  | succ k ih =>
    intro e h
    rw [powMod_succ, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      ih (e / 2) (by rw [pow_succ] at h; omega), ← pow_mul, ← pow_add]
    congr 1
    omega

theorem mem_of_dvd_prod_pow {l : List ℕ} (hl : ∀ q ∈ l, q.Prime) {n N q : ℕ} (hn : n ∣ l.prod ^ N) (hq : q.Prime)
    (h : q ∣ n) : q ∈ l := by
  obtain ⟨x, hx, hqx⟩ := hq.prime.dvd_prod_iff.1 (hq.dvd_of_dvd_pow (h.trans hn))
  rwa [(Nat.prime_dvd_prime_iff_eq hq (hl x hx)).1 hqx]

theorem prime_of_cert (p a k N : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) (hp : 1 < p) (hk : p < 2 ^ k)
    (hN : p - 1 ∣ l.prod ^ N) (h1 : powMod a p k (p - 1) % p = 1)
    (h2 : ∀ q ∈ l, powMod a p k ((p - 1) / q) % p ≠ 1) : p.Prime := by
  have key : ∀ e, e ≤ p - 1 → ((a : ZMod p) ^ e = 1 ↔ powMod a p k e % p = 1) := fun e he => by
    rw [← powMod_cast a p k e (by omega), ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp]
  refine lucas_primality p a ((key _ le_rfl).2 h1) fun q hq hd h => ?_
  exact h2 q (mem_of_dvd_prod_pow hl hN hq hd) ((key _ (Nat.div_le_self _ _)).1 h)

theorem foundations_prime_fact_ter : Nat.Prime 10944929 :=
  prime_of_cert _ 3 24 5 [2, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem prime_128860109809 : Nat.Prime 128860109809 :=
  prime_of_cert _ 13 40 4 [2, 3, 47, 167, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem foundations_prime_fact : Nat.Prime 328347841 :=
  prime_of_cert _ 11 32 6 [2, 3, 5, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem foundations_prime_fact_bis : Nat.Prime 1395478321 :=
  prime_of_cert _ 11 32 4 [2, 3, 5, 17, 571, 599] (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem siteGood_prime_torsion : Nat.Prime (1 + 599 * (123 * (16 * 571 * 599 * (10944929 * 128860109809) ^ 2)) ^ 2) :=
  prime_of_cert _ 5 320 8 [2, 3, 41, 571, 599, 10944929, 128860109809]
    (by
      have h0 := foundations_prime_fact_ter
      have h1 := prime_128860109809
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, h0, h1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem not_exc {g e l k : ℕ} (hl : 1 < l) (he : 1 ≤ e) (hg : l ^ (4 * k) ≤ g) (h : ¬ l ^ (k + 1) ∣ g ^ e - 1) :
    ¬ Formalism.CyclotomicNorms.Exc g e l := by
  rintro ⟨-, hlt⟩
  have hv : padicValNat l (g ^ e - 1) ≤ k := by
    by_contra hc
    exact h ((pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd)
  have h1 : l ^ (4 * padicValNat l (g ^ e - 1)) ≤ l ^ (4 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : g ≤ g ^ e := Nat.le_self_pow (by omega) g
  omega

theorem bb_disjoint : Disjoint (Formalism.CyclotomicNorms.BB 9 10944929) (Formalism.CyclotomicNorms.BB 9 128860109809) := by
  have key : ∀ g l : ℕ, g.Prime → l ∈ Formalism.CyclotomicNorms.BB 9 g → l.Prime ∧ l ∣ g * ∏ i ∈ Finset.range 9, (g ^ (i + 1) - 1) := by
    rintro g l hg (h | ⟨e, h1, h9, h⟩)
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨hg, Dvd.intro _ rfl⟩
    · exact ⟨h.1, (Formalism.MainNotions.Inhab.exc_dvd_prod hg.pos h1 h9 h).trans (Dvd.intro_left _ rfl)⟩
  rw [Set.disjoint_left]
  intro l h0 h1
  obtain ⟨hl, d0⟩ := key _ _ foundations_prime_fact_ter h0
  have hmem : l ∈ [2, 3, 5, 7, 19, 571, 599] :=
    mem_of_dvd_prod_pow (N := 43) (by norm_num) (by decide +kernel) hl (Nat.dvd_gcd d0 (key _ _ prime_128860109809 h1).2)
  rcases h1 with h | ⟨e, h1, h9, h⟩
  · rw [Set.mem_singleton_iff.1 h] at hmem
    exact absurd hmem (by decide +kernel)
  · have hall : ∀ x ∈ [(2, 7), (3, 3), (5, 1), (7, 2), (19, 1), (571, 1), (599, 1)], 1 < x.1 ∧
        x.1 ^ (4 * x.2) ≤ 128860109809 ∧ ∀ e < 10, 1 ≤ e → ¬ x.1 ^ (x.2 + 1) ∣ 128860109809 ^ e - 1 := by
      decide +kernel
    obtain ⟨k, hk⟩ : ∃ k, (l, k) ∈ [(2, 7), (3, 3), (5, 1), (7, 2), (19, 1), (571, 1), (599, 1)] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨a1, a2, a3⟩ := hall _ hk
    exact not_exc a1 h1 a2 (a3 e (by omega) h1) h

end GlobalTheory.Mem.Cert

namespace GlobalTheory.Mem.Explicit

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField GlobalTheory.Mem.Cert
open scoped Pointwise

theorem hyp : HostHyp 571 599 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

def modulus : ℕ := 16 * 571 * 599 * (10944929 * 128860109809) ^ 2

def level : ℕ := 1 + 599 * (123 * modulus) ^ 2

theorem level_prime : level.Prime := siteGood_prime_torsion

section

variable {L : Type} [Field L] [NumberField L] {ζ a b : L} (hl : IsLayer (R0.e + 2) 571 599 ζ a b)

def ax : Formalism.HC.HostAx R0.toFrame := Formalism.HC.D7.hostAx R0.toFrame exampleRanks_h_injective hyp le_rfl hl

theorem cm_nonempty : (ax hl).cmType.Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [(ax hl).der.cmType.2.1]
  simp

theorem half_exists : ∃ 𝔟 : Ideal (𝓞 (ax hl).E),
    differentIdeal (𝓞 (ax hl).K) (𝓞 (ax hl).E) = 𝔟 * ((ax hl).conj • 𝔟) ∧ 𝔟 ⊔ (ax hl).conj • 𝔟 = ⊤ ∧
    ∀ σ : (ax hl).E ≃ₐ[ℚ] (ax hl).E, (ax hl).gal σ ∈ R0.Psi → σ • 𝔟 = 𝔟 :=
  (ax hl).der.principal

def host : Host R0 where
  toHostAx := ax hl
  flPS := Formalism.HC.D7.psQ R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  sqq := Formalism.HC.D7.sqq R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  sqq_sq := Formalism.HC.D7.sqq_sq R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  gal_sqq := Formalism.HC.D7.gal_sqq R0.toFrame hyp hl
  QS_exact := Formalism.HC.D7.exact R0.toFrame exampleRanks_h_injective hyp le_rfl hl
  QS_le := (by norm_num : 16 ≤ 4 ^ 2)
  o_pow := by rw [exampleRanks_o]; simp
  q_ne_three := (by norm_num : 571 ≠ 3)
  qd_big := (by norm_num : 4 * 15 * 9 + 1 < 571 ∧ 4 * 15 * 9 + 1 < 599)
  splitBound := 5
  split_small := by
    intro p hp h2 h5
    change jacobiSym (-((599 : ℕ) : ℤ)) p = 1
    have := hp.two_le
    interval_cases p
    · exact absurd rfl h2
    · norm_num
    · exact absurd hp (by norm_num)
    · norm_num
  small_le := fun l hp h2 hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow (show l ∣ 2 ^ 4 from hd))) h2
  φ₀ := (cm_nonempty hl).some
  φ₀_mem := (cm_nonempty hl).some_mem
  𝔟 := (half_exists hl).choose
  𝔟_spec := ⟨(half_exists hl).choose_spec.1, (half_exists hl).choose_spec.2.1⟩
  𝔟_stable := (half_exists hl).choose_spec.2.2
  levelPrimes := {10944929, 128860109809, 328347841, 1395478321, level}
  level_coprimeS := by
    intro p hp
    change Nat.Coprime p 16
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  g := ![10944929, 128860109809]
  g_prime := by intro i; fin_cases i; exacts [foundations_prime_fact_ter, prime_128860109809]
  g_ne := by simp
  g_level := by intro i; fin_cases i <;> simp
  pde := 328347841
  pde' := 1395478321
  pde_prime := foundations_prime_fact
  pde'_prime := foundations_prime_fact_bis
  pde_ne := by norm_num
  pde_level := by simp
  pde_mod := by norm_num
  pde_ne_g := by intro i; fin_cases i <;> simp
  ccK := ⊤
  ccK_ne_bot := top_ne_bot
  ccK_primitive := fun m hm => Formalism.MainNotions.Inhab.top_primitive m hm
  ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
  ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
  ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
  TT := {0}
  T2 := {0}
  u0 := 0
  Lw := 2
  two_le_Lw := le_rfl
  second_set_range := by intro s hs; simp at hs; subst hs; simp [exampleRanks_baseRank]
  second_set_no_relation := by
    intro s₁ h₁ s₂ h₂ _ _ h12
    simp at h₁ h₂
    exact absurd (h₁.trans h₂.symm) h12
  CT2 := 0

end

def rootInt {R : Ranks} (H : Host R) : 𝓞 H.E :=
  ⟨H.sqrtMinusD, IsIntegral.of_pow two_pos (by
    rw [show H.sqrtMinusD ^ 2 = -(H.d : H.E) from H.sqd_sq]
    exact (isIntegral_natCast _).neg)⟩

theorem norm_one_add {R : Ranks} (H : Host R) (c : ℕ) :
    ((1 + c * rootInt H : 𝓞 H.E) : H.E) * H.conj ((1 + c * rootInt H : 𝓞 H.E) : H.E) = ((1 + H.d * c ^ 2 : ℕ) : H.E) := by
  have h : ((1 + c * rootInt H : 𝓞 H.E) : H.E) = 1 + c * H.sqrtMinusD := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_one, map_mul, map_natCast]
    rfl
  have h1 : H.conj H.sqrtMinusD = -H.sqrtMinusD := H.conj_sqd
  have h2 : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  rw [h, map_add, map_one, map_mul, map_natCast, h1]
  push_cast
  linear_combination (-(c : H.E) ^ 2) * h2

theorem one_add_mem {R : Ranks} (H : Host R) (c : ℕ) : ((1 + c * rootInt H : 𝓞 H.E) : H.E) ∈ H.K := by
  have h : ((1 + c * rootInt H : 𝓞 H.E) : H.E) = 1 + c * H.sqrtMinusD := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_one, map_mul, map_natCast]
    rfl
  rw [h]
  exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _))

theorem window {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    (4 * x ^ s / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / s) * (2 : ℝ) ^ (-(2 : ℝ) / s) = x := by
  rw [Nat.cast_one, div_one, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx.le,
    mul_one_div_cancel hs.ne', Real.rpow_one, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num), mul_right_comm, ← Real.rpow_add (by norm_num)]
  rw [show (2 : ℝ) * (1 / s) + -2 / s = 0 by ring, Real.rpow_zero, one_mul]

section

variable {L : Type} [Field L] [NumberField L] {ζ a b : L} (hl : IsLayer (R0.e + 2) 571 599 ζ a b)

theorem gen_norm : letI := (host hl).cmStar;
    star ((1 + (123 * modulus : ℕ) * rootInt (host hl) : 𝓞 (host hl).E) : (host hl).E) *
      ((1 + (123 * modulus : ℕ) * rootInt (host hl) : 𝓞 (host hl).E) : (host hl).E) = (level : (host hl).E) := by
  rw [mul_comm, bridge_star_holds R0 (host hl)]
  exact norm_one_add (host hl) _

def pre : Pre where
  R := R0
  host := host hl
  ccK_top := rfl
  level_cond := by
    intro p hp
    change p.Prime ∧ p % (16 * 571 * 599) = 1
    simp only [host, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [⟨foundations_prime_fact_ter, by norm_num⟩, ⟨prime_128860109809, by norm_num⟩, ⟨foundations_prime_fact, by norm_num⟩, ⟨foundations_prime_fact_bis, by norm_num⟩,
      ⟨level_prime, by decide +kernel⟩]
  BB_disj := bb_disjoint
  sp := letI := (host hl).cmStar
    spacesNorm R0 (host_cmData R0 (host hl)) level level_prime _ (gen_norm hl)
  Y_sigval := letI := (host hl).cmStar; fun j _ τ => spacesNorm_Y_sig R0 _ _ _ _ _ j τ
  auxiliaryFrame := letI := (host hl).cmStar; fun j _ hj => auxiliary_frame_normalized_spaces R0 _ _ _ _ _ j hj
  V_pos := fun _ _ _ => rfl
  z_norm := letI := (host hl).cmStar; spacesNorm_z_norm R0 _ _ _ _ _
  Word := Bool
  u₀ := false
  hc := fun _ => hcParamOfCodeWord R0 2 0 18 le_rfl le_rfl fun _ => false
  hcW := fun u _ => hcParamOfCodeWord R0 2 0 18 le_rfl le_rfl fun _ => u
  hcW_base := rfl
  hcW_v := fun _ _ => rfl
  hcW_b := fun _ _ => rfl
  hcW_e := fun _ _ => rfl
  hcW_first := fun _ _ _ => rfl
  hcW_last := fun _ _ _ => by simp [hcParamOfCodeWord]
  T := fun _ => level
  T_level := fun _ => by simp [host]
  T_norm := fun _ => ⟨1 + (123 * modulus : ℕ) * rootInt (host hl), one_add_mem _ _, norm_one_add (host hl) _, by
    rw [add_sub_cancel_left, Ideal.mem_span_singleton]
    refine Dvd.dvd.mul_right (Nat.cast_dvd_cast ?_) _
    exact Dvd.intro_left 123 rfl⟩
  sp_T := rfl
  cOf := fun _ => 1
  cOf_ne := fun _ => one_ne_zero
  cOf_eq := fun _ => by simp
  T_ne_pde := fun _ => by
    change level ≠ 328347841 ∧ level ≠ 1395478321
    decide +kernel
  duStar := fun _ => 1
  duStar_pos := fun _ => one_pos
  Dstar := 4 * (level : ℝ) ^ ((R0.f : ℝ) * R0.k)
  Dstar_pos := by
    have : (0 : ℝ) < level := by exact_mod_cast level_prime.pos
    positivity
  GamP := 2
  one_lt_gammaP := one_lt_two
  T_win := fun _ => by
    have h : (0 : ℝ) < level := by exact_mod_cast level_prime.pos
    have hs : (0 : ℝ) < (R0.f : ℝ) * R0.k := by simp
    rw [window h hs]
    refine ⟨le_rfl, le_mul_of_one_le_left h.le ?_⟩
    have := one_div_pos.2 hs
    linarith

theorem pre_hcW_injective : Function.Injective (pre hl).hcW := by
  have hne : Nonempty (Tau R0) := ⟨1⟩
  obtain ⟨τ⟩ := hne
  intro u u' h
  have h1 := congrArg (fun x => (x τ).u ⟨1, (by norm_num : 1 < 8)⟩) h
  revert h1
  change Bool at u u'
  cases u <;> cases u' <;> simp [pre, hcParamOfCodeWord] <;> norm_num

end

end GlobalTheory.Mem.Explicit

theorem GlobalTheory.Mem.exists_pre : ∃ B : GlobalTheory.Mem.Pre, Fintype.card B.Word = 2 ∧ Function.Injective B.hcW := by
  obtain ⟨L, _, _, ζ, a, b, hl⟩ := Formalism.TwoAdicCyclotomicDecomposition.layerExists (Formalism.BasicNotions.Examples₂.R0.e + 2) 571 599
  exact ⟨GlobalTheory.Mem.Explicit.pre hl, rfl, GlobalTheory.Mem.Explicit.pre_hcW_injective hl⟩

end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseField

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

theorem span_image_span (s : Set K) :
    Submodule.span (𝓞 K') (f '' (Submodule.span (𝓞 K) s : Set K)) = Submodule.span (𝓞 K') (f '' s) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : f (a • x) = RingOfIntegers.mapRingHom f a • f x := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 K') K' where
  toFun M := Submodule.span (𝓞 K') (f '' (M : Set K))
  map_one' := by
    rw [Submodule.one_eq_span, span_image_span, Submodule.one_eq_span]; simp
  map_mul' M N := by
    conv_lhs => rw [← M.span_eq, ← N.span_eq, Submodule.span_mul_span, span_image_span]
    rw [Submodule.span_mul_span, Set.image_mul]

theorem extend_span (s : Set K) :
    extend f (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K') (f '' s) := span_image_span f s

end ext

section host

variable {R : Ranks} (H : Host R)

theorem conjugate_emb (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  exact (H.conjE_apply (H.emb g) x).symm

theorem conjugate_emb_apply (g : R.GG) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g) x = H.emb g (H.conj x) := by
  rw [conjugate_emb, Formalism.L2.Geo.emb_mul_cc_comp]; rfl

theorem ex_emb_iff (g : R.GG) :
    (∃ t : Tau R, H.emb t = H.emb g) ↔ g ∈ R.Psi :=
  ⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

theorem emb_cm (σ : H.E →+* ℂ) :
    (∃ t : Tau R, H.emb t = σ) ↔ ¬ ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  rw [conjugate_emb, ex_emb_iff, ex_emb_iff]
  rw [Formalism.HC.Frame.mem_Psi_iff, Formalism.HC.Frame.mem_Psi_iff]
  show g.1.2 = 1 ↔ ¬ g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> decide

theorem sum_emb_bijective : Function.Bijective
    (Sum.elim (fun t : Tau R => H.emb t) fun t : Tau R => ComplexEmbedding.conjugate (H.emb t)) := by
  have hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b := fun h => Subtype.ext ((factEmb R H).1.1 h)
  constructor
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hi h]
    · exact absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)
    · have := congrArg ComplexEmbedding.conjugate h
      rw [hc, hc] at this
      rw [hi this]
  · intro σ
    by_cases h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
    · obtain ⟨t, ht⟩ := (emb_cm H σ).2 h
      exact ⟨Sum.inl t, ht⟩

open Classical in

def typeExp (p q : ℕ) (σ : H.E →+* ℂ) : ℕ := if ∃ t : Tau R, H.emb t = σ then p else q

theorem typeExp_emb (p q : ℕ) (t : Tau R) : typeExp H p q (H.emb t) = p := if_pos ⟨t, rfl⟩

theorem typeExp_conj (p q : ℕ) (t : Tau R) :
    typeExp H p q (ComplexEmbedding.conjugate (H.emb t)) = q := if_neg ((emb_cm H _).1 ⟨t, rfl⟩)

theorem typeExp_add (p q : ℕ) (σ : H.E →+* ℂ) :
    typeExp H p q σ + typeExp H p q (ComplexEmbedding.conjugate σ) = p + q := by
  unfold typeExp
  by_cases h : ∃ t : Tau R, H.emb t = σ
  · rw [if_pos h, if_neg ((emb_cm H σ).1 h)]
  · rw [if_neg h, if_pos (not_not.1 (fun h' => h ((emb_cm H σ).2 h'))), add_comm]

theorem prod_typeExp {M : Type} [CommMonoid M] (p q : ℕ) (F : (H.E →+* ℂ) → M) :
    ∏ σ, F σ ^ typeExp H p q σ =
      ∏ t : Tau R, (F (H.emb t) ^ p * F (ComplexEmbedding.conjugate (H.emb t)) ^ q) := by
  rw [← (sum_emb_bijective H).prod_comp, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  simp only [Sum.elim_inl, Sum.elim_inr, typeExp_emb, typeExp_conj]

end host

theorem isAlgebraic_exp (N : ℕ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simpa using isAlgebraic_one
  · exact ((Complex.isPrimitiveRoot_exp N h.ne').isIntegral h).tower_top.isAlgebraic

theorem exists_gens (E : Type) [Field E] [NumberField E] : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → ∀ (τ : E →+* ℂ) x, τ x ∈ K := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), ?_, ?_⟩
  · intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (b p.2)).algHom p.1.toRatAlgHom
  · intro K hK τ x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact K.smul_mem (hK _ (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩))

@[instance_reducible] def starOf (K : IntermediateField ℚ ℂ) (h : ∀ z ∈ K, starRingEnd ℂ z ∈ K) : StarRing K where
  star x := ⟨starRingEnd ℂ x, h _ x.2⟩
  star_involutive x := Subtype.ext (Complex.conj_conj _)
  star_mul x y := Subtype.ext (by
    show starRingEnd ℂ ((x : ℂ) * y) = starRingEnd ℂ y * starRingEnd ℂ x
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add (starRingEnd ℂ) (x : ℂ) (y : ℂ))


def toTop (K : IntermediateField ℚ ℂ) : K →+* (⊤ : IntermediateField ℚ K) :=
  (IntermediateField.topEquiv (F := ℚ) (E := K)).symm

theorem image_top {E : Type} [Field E] (K : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) (τ : E →+* ℂ) (e : E → K)
    (he : ∀ a, (e a : ℂ) = τ a) :
    extend (toTop K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)}) =
      Submodule.span (𝓞 (⊤ : IntermediateField ℚ K))
        {x : (⊤ : IntermediateField ℚ K) | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨x.1, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

theorem exists_base : ∀ (B : Pre) (S₀ S₁ S₂ : Finset ℂ), (∀ z ∈ S₀, IsAlgebraic ℚ z) → (∀ z ∈ S₁, IsAlgebraic ℚ z) → (∀ z ∈ S₂, IsAlgebraic ℚ z) → ∃ B' : Base, B'.toPre = B ∧ (∀ z ∈ S₀, ∃ x ∈ B'.Ks, B'.embLL x = z) ∧ (∀ z ∈ S₁, ∃ x ∈ B'.LL0, B'.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S₀ S₁ S₂ h₀ h₁ h₂
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  have hgal : IsGalois ℚ B.host.E := B.host.hostE_isGalois
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.host.E
  choose MainNotions hSK hK using fun j : ℕ => GlobalTheory.Mem.exists_finset_typeNorm_principal B.host.E
    (typeExp B.host (B.R.sigW j).1 (B.R.sigW j).2) _ (typeExp_add B.host _ _)
  obtain ⟨SC, hSC, hC⟩ := GlobalTheory.Mem.exists_finset_capitulation B.host.E B.host.φ₀
  let l : List ℕ := [B.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1), B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4]
  let l' : List ℕ := [B.host.pde, B.host.pde', classNumber B.host.E]
  let SN : Finset ℕ := l.toFinset ∪ l'.toFinset ∪ {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := SN.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, hI, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable
    (S₀ ∪ S₁ ∪ S₂ ∪ SE ∪ SC ∪ SR ∪ (Finset.range (B.R.m + 1)).biUnion MainNotions) (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_biUnion] at hz
      rcases hz with (((((hz | hz) | hz) | hz) | hz) | hz) | ⟨j, -, hz⟩
      exacts [h₀ z hz, h₁ z hz, h₂ z hz, hSE z hz, hSC z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N, hSK j z hz])
  simp only [Finset.mem_union, Finset.mem_biUnion] at hS
  have hEK := hE K fun z hz => hS z (by tauto)
  have : NumberField K := {}
  let f := toTop K
  have hR : ∀ N ∈ SN, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN =>
    hS _ (Or.inl (Or.inr (Finset.mem_image.2 ⟨N, hN, rfl⟩)))
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K (hEK _)
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := ⊤
            Ks_le := le_rfl
            E_le_Ks := fun _ => trivial
            roots_Ks := fun N hN => ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
            roots_Ks' := fun N hN => ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_singleton_self _)))⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR _ (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩
            capit := ?_
            kPsi := ?_ }, rfl, ?_, ?_, ?_⟩
  · intro 𝔞
    obtain ⟨β, hβ⟩ := hC K (fun z hz => hS z (by tauto)) (hEK _) 𝔞
    have h := congrArg (extend f) hβ
    rw [extend_span, Set.image_singleton] at h
    exact ⟨f β, h.trans (image_top K 𝔞 B.host.φ₀ (fun a => B.host.φ₀.codRestrict K (hEK _) a) fun _ => rfl)⟩
  · intro j _ hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hK j K
      (fun z hz => hS z (Or.inr ⟨j, Finset.mem_range.2 (by omega), hz⟩)) hEK 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [prod_typeExp, extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_top K 𝔞 (B.host.emb g)
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_top K 𝔞 (ComplexEmbedding.conjugate (B.host.emb g))
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g (B.host.conj a)))
      fun a => (conjugate_emb_apply B.host g a).symm
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, rfl⟩

end GlobalTheory.Mem.BaseField

end
end
