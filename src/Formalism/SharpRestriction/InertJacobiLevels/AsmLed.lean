import Formalism.SharpRestriction.InertJacobiLevels.EtaSz
import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

structure HostOk (x eps Cp : ℝ) {R : Ranks} (H : Host R) : Prop where
  good : QDGood x eps H.q H.d
  split_tie : ⌊x ^ (eps / 5)⌋₊ ≤ H.splitBound
  g_win : ∀ i, Yof R x eps ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * Yof R x eps
  g_norm : ∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_norm1 : ∀ i, ∃ π ρ : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (ρ : H.E) ∈ H.K ∧
    (π : H.E) - 1 = ((H.QS * H.q * H.d : ℕ) : H.E) * ρ ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_mod : ∀ i, H.g i % (H.QS * H.q * H.d) = 1
  thyp : THyp H
  g_split : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  g_cls : ∀ i, H.cls (H.g i) = .splitK
  pde_split : (Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E
  pde_cls : H.cls H.pde = .splitK ∧ H.cls H.pde' = .splitK
  pde_log : Real.log H.pde < x ^ (eps / 3) ∧ Real.log H.pde' < x ^ (eps / 3)
  ccK_norm : Ideal.absNorm H.ccK = 1
  secondSet_card_lower_bound : H.secondSet_card_lower_bound
  secondTorsion_card_pos : 0 < H.T2.card
  secondTorsion_card_le : H.T2.card ≤ R.n0
  o_tie : (R.o : ℝ) ≤ x ^ (eps / 1000)
  QS_tie : (H.QS : ℝ) ≤ 4 * R.n * x ^ (eps / 1000)


theorem norm_mod {R : Ranks} (H : Host R) {M T : ℕ} (hM : 0 < M) (π : 𝓞 H.E)
    (h2 : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h3 : (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD M] := by
  obtain ⟨ρ, hρ⟩ := Ideal.mem_span_singleton.1 h3
  have hπ : (π : H.E) = 1 + (M : H.E) * (ρ : H.E) := by
    have : ((π - 1 : 𝓞 H.E) : H.E) = (((M : ℕ) : 𝓞 H.E) * ρ : 𝓞 H.E) := by rw [hρ]
    push_cast at this
    linear_combination this
  have hint : IsIntegral ℤ (H.conj (ρ : H.E)) := map_isIntegral_int H.conj ρ.2
  set ρ' : 𝓞 H.E := ⟨H.conj (ρ : H.E), hint⟩ with hρ'
  have hρc : ((ρ' : 𝓞 H.E) : H.E) = H.conj (ρ : H.E) := rfl
  set w : 𝓞 H.E := ρ + ρ' + (M : 𝓞 H.E) * ρ * ρ' with hw
  have hwc : (w : H.E) = (ρ : H.E) + H.conj (ρ : H.E) + (M : H.E) * ρ * H.conj (ρ : H.E) := by
    rw [hw, ← hρc]; push_cast; rfl
  have key : (T : H.E) - 1 = (M : H.E) * (w : H.E) := by
    rw [← h2, hπ, hwc]
    simp only [map_add, map_mul, map_one, map_natCast]
    ring
  have hM0 : (M : H.E) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : algebraMap ℚ H.E (((T : ℚ) - 1) / M) = (w : H.E) := by
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, key, mul_div_cancel_left₀ _ hM0]
  have hi : IsIntegral ℤ (((T : ℚ) - 1) / M) := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective, hr]
    exact w.2
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hz' : (T : ℤ) - 1 = M * z := by
    have : (T : ℚ) - 1 = M * z := by
      have h5 : (z : ℚ) = ((T : ℚ) - 1) / M := by simpa using hz
      rw [h5]; field_simp
    exact_mod_cast this
  rw [← Int.natCast_modEq_iff]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact ⟨z, by push_cast; exact hz'⟩



variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

theorem one_lt_cond : 1 < B.condN :=
  lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero B.condN_ne_zero) B.two_dvd_condN)


theorem first_prime_modEq_one : B.g0 ≡ 1 [MOD B.condN] := by
  obtain ⟨u, v, h⟩ := B.first_prime_norm_form; exact form_mod h
theorem second_prime_modEq_one : B.g1 ≡ 1 [MOD B.condN] := by
  obtain ⟨u, v, h⟩ := B.second_prime_norm_form; exact form_mod h


end Base




def Base.MT : ℕ := B.condN * (B.g0 * B.g1) ^ 2


section Indep

variable (u0 u0' : R.A) (ex ex' : Finset ℕ)


end Indep

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

abbrev Core : Type 1 := Σ R : Ranks, Host R × (↥(R.Psi) → HCParam R)

def coreOf (D : D7) : Core := ⟨D.R, D.host, fun g => D.hc (D.eTau.symm g)⟩

def plPsi (φ : Formalism.HC.Frame) (c : Bool) (t : φ.A) : ↥φ.Psi :=
  ⟨if c then φ.tau2 t else φ.tau1 t, by
    rw [(factPlaces φ).1]
    cases c
    · exact Or.inl ⟨t, by simp⟩
    · exact Or.inr ⟨t, by simp⟩⟩

def wjv (R : Ranks) (hc : ↥(R.Psi) → HCParam R) (j : ℕ) (c : Bool) (v : ℕ) : ℝ :=
  if h : j - 1 < R.m then (((hc (plPsi R.toFrame c (R.ofNat v))).e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

def Core.rh (X : Core) : Σ R : Ranks, Host R := ⟨X.1, X.2.1⟩

def Core.wjv (X : Core) : ℕ → Bool → ℕ → ℝ := Inhab.wjv X.1 X.2.2


def inertBaseShadowData {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT) (etaSz Sc : ℝ) (offS : ℕ → ℕ → ℝ) (kapI : KapI)
    (ep : ℕ → ℕ) : Shd0 where
  R := R
  TTn := B.TT.image Formalism.HC.Frame.A.val
  T2 := B.T2
  q := B.q
  d := B.d
  g := ![B.g0, B.g1]
  pde := B.pde
  pde' := B.pde'
  bits := fun _ => false
  etaSz := etaSz
  Sc := Sc
  hP := (fieldDataH ⟨R, host2 B 0 ∅⟩).hval
  offS := offS
  kapI := kapI
  ep := ep

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure LedHyp (D : D7) (sc : Scale) (aT bT : D.host.TT → ℤ) (η Cc Ct CGam : ℝ) (j0 : ℕ) : Prop where
  aT_win : ∀ t, sc.a ≤ (aT t : ℝ) ∧ (aT t : ℝ) ≤ sc.a + sc.a / ((D.R.k : ℝ) * sc.x ^ (Scale.A / 2))
  bT_ge : ∀ t, sc.b' ≤ (bT t : ℝ)
  top_u : ∀ τ (t : D.host.TT) (h0 : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).u ⟨0, h0⟩ : ℚ) : ℝ) = aT t + ((D.R.k : ℝ) - 1) / 2 ∧
    (((D.hc τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = -(bT t : ℝ) - ((D.R.k : ℝ) - 1) / 2
  top_b : ∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3
  b_le : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ sc.b ^ 2
  untw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0
  logFiveDepth_le : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0
  weightLength_ge_depth : 10 * j0 + 20 ≤ D.host.Lw
  split_tie : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ D.host.splitBound
  o_tie : (D.R.o : ℝ) ≤ sc.x ^ (sc.eps / 100)
  QS_tie : (D.host.QS : ℝ) ≤ 4 * D.R.n * sc.x ^ (sc.eps / 100)
  secondTorsion_card_pos : 0 < D.host.T2.card
  secondTorsion_card_le : D.host.T2.card ≤ D.R.n
  win_thick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
    sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + η + 1
  win_top : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (bT t : ℝ) + sc.b' / sc.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + sc.b' / sc.x + η
  win_thin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
    sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ sc.w'' D.R.n + η
  cloud_gap : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
    (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
  cloud_v : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
    (((D.hc τ).v i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  cloud_u : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
    0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  be_close : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η
  eta_pos : 0 < η
  Del_pos : 0 < (D.s.Del : ℝ)
  t_win : 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ sc.x ^ Ct
  CGam_pos : 0 < CGam
  Gam_eq : ∀ u, Real.log (D.mem u).A.GamP = CGam * (D.R.m : ℝ) ^ 5 * D.R.f * sc.L

def baseL {D : D7} {sc : Scale} {aT bT : D.host.TT → ℤ} {η Cc Ct CGam : ℝ} {j0 : ℕ}
    (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S0 : Finset D.what₂.places.Pl) (E0 : D.what₂.Word → ℕ → D.what₂.places.Pl → ℝ)
    (hE0 : ∀ u j w, w ∉ S0 → E0 u j w = 0) : SizeData₂ D where
  sc := sc
  aT := aT
  aT_win := h.aT_win
  bT := bT
  bT_ge := h.bT_ge
  top_u := h.top_u
  top_b := h.top_b
  supp := S0
  gain := fun _ _ => 0
  F := fun _ _ => 0
  E := E0
  tau := fun _ => 0
  io := fun _ => 0
  gain_supp := fun _ _ _ => rfl
  F_supp := fun _ _ _ => rfl
  E_supp := hE0
  tau_supp := fun _ _ => rfl
  io_supp := fun _ _ => rfl
  gain_g := fun _ _ _ => rfl
  b_le := h.b_le
  untwisted := fun w hw j h1 h2 => ⟨h.untw w hw j h1 h2, rfl⟩
  not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
  drop := ∅
  drop_alt := fun _ => Set.notMem_empty _
  F_conj := fun _ _ => rfl
  F_above := by intros; rfl
  j0 := j0
  logFiveDepth_le := h.logFiveDepth_le
  weightLength_ge_depth := h.weightLength_ge_depth
  logDerivativeAtOne := dlogL D 1
  logDerivative_at_one_eq := rfl
  split_tie := h.split_tie
  o_tie := h.o_tie
  QS_tie := h.QS_tie
  NuLat := Nu
  de2 := (D.host.T2.card : ℝ) / D.R.n
  thickDensity_pos := by
    have h1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
    have h2 : (0 : ℝ) < D.host.T2.card := by exact_mod_cast h.secondTorsion_card_pos
    positivity
  thickDensity_le_one := by
    have h1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
    rw [div_le_one (by linarith)]
    exact_mod_cast h.secondTorsion_card_le
  typeDensity_eq_card_div := rfl
  LaG := 0
  Sc := (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  etaSz := η
  Cc := Cc
  win_thick := h.win_thick
  win_top := h.win_top
  win_thin := h.win_thin
  cloud_gap := h.cloud_gap
  cloud_v := h.cloud_v
  cloud_u := h.cloud_u
  be_close := h.be_close
  Sc_pos := by
    have h1 : (0 : ℝ) < D.R.k := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 0 < D.R.k)
    have := h.Del_pos
    positivity
  Sc_eq := rfl
  etaSz_pos := h.eta_pos
  TTw := fun _ => Finset.univ
  TTw_full := fun _ _ => rfl
  Ct := Ct
  t_win := h.t_win
  CGam := CGam
  CGam_pos := h.CGam_pos
  Gam_eq := h.Gam_eq
  wPart := fun _ _ _ _ => 1
  wPart_ge := fun _ _ _ _ => le_rfl
  lenMN := fun _ _ => 0

end Formalism.MainNotions.Inhab

end
end
