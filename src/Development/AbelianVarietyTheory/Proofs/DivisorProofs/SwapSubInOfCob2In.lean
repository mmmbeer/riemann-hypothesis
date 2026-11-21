import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubInStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroups

section
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace CobSymCoc

open GlobalTheory.Katz.CobCob

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (elim_has hu hv)]
  congr 1
  funext k
  cases k <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map φ (op μ u v i) = op (fun j => map φ (μ j)) (fun j => map φ (u j)) (fun j => map φ (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem map_threeGroupsFirstVariables (φ : R →+* S) : (fun j => map φ (x1 (R := R) (d := d) j)) = x1 := by
  funext j; exact map_X φ _
theorem map_threeGroupsSecondVariables (φ : R →+* S) : (fun j => map φ (x2 (R := R) (d := d) j)) = x2 := by
  funext j; exact map_X φ _
theorem map_threeGroupsThirdVariables (φ : R →+* S) : (fun j => map φ (x3 (R := R) (d := d) j)) = x3 := by
  funext j; exact map_X φ _

theorem map_assocL (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ x1 (op μ x2 x3) i)) =
      op (fun j => map φ (μ j)) x1 (op (fun j => map φ (μ j)) x2 x3) := by
  funext i
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables (op_const h constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables), map_threeGroupsFirstVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem map_assocR (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ (op μ x1 x2) x3 i)) =
      op (fun j => map φ (μ j)) (op (fun j => map φ (μ j)) x1 x2) x3 := by
  funext i
  rw [map_op φ μ (op_const h constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables, map_threeGroupsThirdVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables]

end CobSymCoc

open CobSymCoc CobCob in

theorem cob_symCoc_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL N f hf
  have hM : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, constantCoeff_map, hL.const i, map_zero]
  obtain ⟨A, Bs, -⟩ := formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hM f
  refine ⟨?_, ?_⟩
  · rw [A]
    have eL : op (up Q μ) x1 (op (up Q μ) x2 x3) = up Q (op μ x1 (op μ x2 x3)) :=
      (map_assocL (algebraMap B Q) μ hL.const).symm
    have eR : op (up Q μ) (op (up Q μ) x1 x2) x3 = up Q (op μ (op μ x1 x2) x3) :=
      (map_assocR (algebraMap B Q) μ hL.const).symm
    rw [eL, eR]
    refine GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p B O Q θ hF (RingHom.ker θ) ?_ (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) N f _ _ hf
      (op_const hL.const constantCoeff_threeGroupsFirstVariables (op_const hL.const constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables))
      (op_const hL.const (op_const hL.const constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables) ?_
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
      exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
    · intro i α
      rw [RingHom.mem_ker, ← coeff_map, map_sub]
      have h1 := congrFun (map_assocL θ μ hL.const) i
      have h2 := congrFun (map_assocR θ μ hL.const) i
      rw [h1, h2, hL.law.assoc, sub_self, map_zero]
  · have hs : (fun i => swap (up Q μ i)) = up Q μ := by
      funext i
      have e : map (algebraMap B Q) (swap (μ i)) = swap (map (algebraMap B Q) (μ i)) := by
        unfold swap
        rw [mvPowerSeriesMap_evalTwoGroups (algebraMap B Q) (μ i) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
        simp only [map_X]
      show swap (map (algebraMap B Q) (μ i)) = map (algebraMap B Q) (μ i)
      rw [← e, hL.comm i]
    rw [hs, sub_self] at Bs
    exact sub_eq_zero.1 Bs

end GlobalTheory
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  atlas_forward_decl GlobalTheory.cob_symCoc_mod
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → DIn N (subst (up Q u) f) ∧ (In N f → In N (subst (up Q u) f)) := by
  first | exact @GlobalTheory.QLog.dIn_subst_up | exact GlobalTheory.QLog.dIn_subst_up | (intros; apply GlobalTheory.QLog.dIn_subst_up <;> assumption)
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.SymCocycleMV

theorem choose_pow_modEq (p : ℕ) [hp : Fact p.Prime] : ∀ (j x : ℕ), x.choose (p ^ j) ≡ x / p ^ j [MOD p]
  | 0, x => by simp [Nat.ModEq]
  | j + 1, x => by
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat x (p * p ^ j) p _
    rw [Nat.mul_mod_right, Nat.choose_zero_right, one_mul, Nat.mul_div_cancel_left _ hp.out.pos] at h
    rw [pow_succ']
    refine h.trans ?_
    rw [← Nat.div_div_eq_div_mul]
    exact choose_pow_modEq p j (x / p)

theorem not_dvd_choose_pow_iff (p : ℕ) [hp : Fact p.Prime] (j x : ℕ) :
    ¬ p ∣ x.choose (p ^ j) ↔ ¬ p ∣ x / p ^ j :=
  not_congr ((choose_pow_modEq p j x).dvd_iff dvd_rfl)

theorem not_dvd_choose_pow_mul_add (p : ℕ) [hp : Fact p.Prime] :
    ∀ (s A B : ℕ), B < p ^ s → ¬ p ∣ (p ^ s * A + B).choose B := by
  intro s
  induction s with
  | zero =>
    intro A B hB
    have : B = 0 := by simpa using hB
    subst this; simpa using hp.out.not_dvd_one
  | succ s ih =>
    intro A B hB hd
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _
    have e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A) := by ring
    rw [e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self,
      one_mul] at h
    have hB' : B / p < p ^ s := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]; exact hB
    apply ih A (B / p) hB'
    rw [add_comm (p ^ s * A)]
    rw [e0] at hd
    exact (h.dvd_iff dvd_rfl).1 hd

theorem prod_choose_single {d : ℕ} (y : Fin d →₀ ℕ) (i : Fin d) (q : ℕ) :
    ∏ k, (y k).choose (Finsupp.single i q k) = (y i).choose q := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ i) h

variable {p : ℕ} [hp : Fact p.Prime] {M : Type} [AddCommGroup M] {d : ℕ}

def IsSym (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) : Prop := ∀ a, a ≤ n → c a = c (n - a)

def IsRel (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) : Prop :=
  ∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n →
    (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) =
      (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a

omit hp in
theorem smul_eq_zero_of_not_dvd (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m)
    (hpp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k) {m : M} (h : k • m = 0) : m = 0 := by
  have hc : Nat.Coprime k p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 hk)
  exact (hu k hc).1 (by simp only [h, smul_zero])

theorem eq_zero_of_le (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (x y : Fin d →₀ ℕ) (hx : x ≠ 0) (hxy : x ≤ y) (hy : y ≤ n) (hyn : y ≠ n)
    (hd : ¬ p ∣ ∏ k, (y k).choose (x k)) (h0 : c x = 0) : c y = 0 := by
  by_cases he : x = y
  · rw [← he]; exact h0
  · have hb : y - x ≠ 0 := by
      intro h; exact he (le_antisymm hxy (tsub_eq_zero_iff_le.1 h))
    have h := hrel x (y - x) hx hb (by rwa [add_tsub_cancel_of_le hxy]) (by rwa [add_tsub_cancel_of_le hxy])
    rw [add_tsub_cancel_of_le hxy, h0, smul_zero] at h
    exact smul_eq_zero_of_not_dvd hu hp.out hd h

theorem not_dvd_prod (f : Fin d → ℕ) (h : ∀ k, ¬ p ∣ f k) : ¬ p ∣ ∏ k, f k := by
  intro hd
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finset_prod_iff hp.out.prime f).1 hd
  exact h k hk

theorem eq_zero_of_atoms (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (hat : ∀ i j, p ^ j ≤ n i → Finsupp.single i (p ^ j) ≠ n → c (Finsupp.single i (p ^ j)) = 0) :
    ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = 0 := by
  intro a han ha0 han'
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha0 (Finsupp.ext fun i => by simp [h i])
  obtain ⟨j, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p hp.out.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at he; exact hi he)
  have hja : p ^ j ≤ a i := by rw [he]; exact Nat.le_mul_of_pos_right _ hm0
  have hle : Finsupp.single i (p ^ j) ≤ a := Finsupp.single_le_iff.2 hja
  have hne : Finsupp.single i (p ^ j) ≠ n := fun h => han' (le_antisymm han (h ▸ hle))
  have hjn : p ^ j ≤ n i := le_trans hja (Finsupp.le_def.1 han i)
  refine eq_zero_of_le n c hu hrel _ a (Finsupp.single_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero))
    hle han han' ?_ (hat i j hjn hne)
  rw [prod_choose_single, not_dvd_choose_pow_iff, he, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos j)]
  exact hm

theorem tsub_single_ne (n : Fin d →₀ ℕ) (i : Fin d) (q : ℕ) (hq : 0 < q) (hqn : q ≤ n i) :
    n - Finsupp.single i q ≠ n := by
  intro h
  have := congrArg (fun f : Fin d →₀ ℕ => f i) h
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at this
  omega

theorem atom_cross (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (hsym : IsSym n c) (i' : Fin d) (j' : ℕ) (hj' : ¬ p ∣ n i' / p ^ j') (hjn' : p ^ j' ≤ n i')
    (h0 : c (Finsupp.single i' (p ^ j')) = 0) :
    ∀ i j, i ≠ i' → p ^ j ≤ n i → c (Finsupp.single i (p ^ j)) = 0 := by
  intro i j hii hj
  have htn : Finsupp.single i (p ^ j) ≤ n := Finsupp.single_le_iff.2 hj
  rw [hsym _ htn]
  refine eq_zero_of_le n c hu hrel _ _ (Finsupp.single_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_
    tsub_le_self (tsub_single_ne n i _ (pow_pos hp.out.pos j) hj) ?_ h0
  · rw [Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_neg hii, Nat.sub_zero]
    exact hjn'
  · rw [prod_choose_single, not_dvd_choose_pow_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_neg hii,
      Nat.sub_zero]
    exact hj'

theorem atom_line (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (hsym : IsSym n c) (i0 : Fin d) (s K : ℕ) (hN : n i0 = p ^ s * K) (hK : 2 ≤ K)
    (hK' : ∀ j, s < j → p ^ j < n i0 → ¬ p ∣ (n i0 - p ^ j) / p ^ s)
    (h0 : c (Finsupp.single i0 (p ^ s)) = 0) :
    ∀ j, p ^ j < n i0 → c (Finsupp.single i0 (p ^ j)) = 0 := by
  intro j hj
  have hps : 0 < p ^ s := pow_pos hp.out.pos s
  have hpj : 0 < p ^ j := pow_pos hp.out.pos j
  have htn : Finsupp.single i0 (p ^ j) ≤ n := Finsupp.single_le_iff.2 hj.le
  have hyn := tsub_single_ne n i0 _ hpj hj.le
  rw [hsym _ htn]
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hK1 : p ^ s ≤ p ^ s * K' := Nat.le_mul_of_pos_right _ (by omega)
  have hN' : n i0 = p ^ s * K' + p ^ s := by rw [hN]; ring
  rcases (show j ≤ s ∨ s < j from (by omega)) with hjs | hjs
  · have hjs' : p ^ j ≤ p ^ s := Nat.pow_le_pow_right hp.out.pos hjs
    have hsn : Finsupp.single i0 (p ^ s) ≤ n := Finsupp.single_le_iff.2 (by omega)
    have hx0 : c (n - Finsupp.single i0 (p ^ s)) = 0 := by rw [← hsym _ hsn]; exact h0
    refine eq_zero_of_le n c hu hrel _ _ ?_ ?_ tsub_le_self hyn ?_ hx0
    · intro h
      have := congrArg (fun f : Fin d →₀ ℕ => f i0) h
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    · rw [Finsupp.le_def]; intro k
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    · apply not_dvd_prod; intro k
      by_cases hk : k = i0
      · subst hk
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        have e1 : n k - p ^ j = p ^ s * K' + (p ^ s - p ^ j) := by omega
        have e2 : n k - p ^ s = p ^ s * K' := by omega
        rw [e1, e2, Nat.choose_symm_add]
        exact not_dvd_choose_pow_mul_add p s K' _ (by omega)
      · simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hk), Nat.sub_zero,
          Nat.choose_self]
        exact hp.out.not_dvd_one
  · have hq := hK' j hjs hj
    have hle : p ^ s ≤ n i0 - p ^ j := by
      by_contra hlt; push_neg at hlt
      exact hq (by rw [Nat.div_eq_of_lt hlt]; exact dvd_zero p)
    refine eq_zero_of_le n c hu hrel _ _ (Finsupp.single_ne_zero.2 hps.ne') ?_ tsub_le_self hyn ?_ h0
    · rw [Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]; exact hle
    · rw [prod_choose_single, not_dvd_choose_pow_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]
      exact hq

theorem exists_smul_eq (hdiv : ∀ m : M, ∃ m', p • m' = m)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) :
    ∀ k : ℕ, 0 < k → ∀ m : M, ∃ g : M, k • g = m := by
  have hpow : ∀ v : ℕ, ∀ m : M, ∃ g : M, p ^ v • g = m := by
    intro v
    induction v with
    | zero => intro m; exact ⟨m, by rw [pow_zero, one_smul]⟩
    | succ v ih =>
      intro m
      obtain ⟨g, hg⟩ := ih m
      obtain ⟨g', hg'⟩ := hdiv g
      exact ⟨g', by rw [pow_succ, mul_smul, hg', hg]⟩
  intro k hk m
  obtain ⟨v, u, hu', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hp.out.one_lt.ne'
  obtain ⟨g1, hg1⟩ := hpow v m
  have hc : Nat.Coprime u p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu')
  obtain ⟨g, hg⟩ := (hu u hc).2 g1
  exact ⟨g, by rw [mul_smul]; simp only at hg; rw [hg, hg1]⟩

theorem sub_isSym (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) (g : M) (hsym : IsSym n c) :
    IsSym n (fun a => c a - (∏ i, (n i).choose (a i)) • g) := by
  intro a ha
  simp only
  rw [← hsym a ha]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.tsub_apply, Nat.choose_symm (Finsupp.le_def.1 ha i)]

theorem sub_isRel (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) (g : M) (hrel : IsRel n c) :
    IsRel n (fun a => c a - (∏ i, (n i).choose (a i)) • g) := by
  intro a b ha hb hab hab'
  simp only [smul_sub]
  rw [hrel a b ha hb hab hab', smul_smul, smul_smul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := Finsupp.le_def.1 hab i
  simp only [Finsupp.add_apply, Finsupp.tsub_apply] at hi ⊢
  have h := Nat.choose_mul (n := n i) (k := a i + b i) (s := a i) (by omega)
  rw [Nat.add_sub_cancel_left] at h
  rw [mul_comm, h, mul_comm]

theorem exists_eq_smul_prod_choose : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M],
    (∀ m : M, ∃ m', p • m' = m) → (∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun m : M => n • m) →
    ∀ (d : ℕ) (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M), (∀ a, a ≤ n → c a = c (n - a)) →
    (∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n →
      (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) =
        (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a) →
    ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g := by
  intro p _ M _ hdiv hu d n c hsym hrel
  have hp : p.Prime := Fact.out
  have hps : ∀ j, 0 < p ^ j := fun j => pow_pos hp.pos j

  have mk : ∀ i0 j0, p ^ j0 ≤ n i0 → ∃ g : M,
      (fun a => c a - (∏ i, (n i).choose (a i)) • g) (Finsupp.single i0 (p ^ j0)) = 0 := by
    intro i0 j0 hj0
    obtain ⟨g, hg⟩ := exists_smul_eq hdiv hu ((n i0).choose (p ^ j0)) (Nat.choose_pos hj0)
      (c (Finsupp.single i0 (p ^ j0)))
    exact ⟨g, by simp only; rw [prod_choose_single, hg, sub_self]⟩
  have fin : ∀ g : M, (∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a - (∏ i, (n i).choose (a i)) • g = 0) →
      ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g :=
    fun g h => ⟨g, fun a h1 h2 h3 => sub_eq_zero.1 (h a h1 h2 h3)⟩
  have hsym' := fun g => sub_isSym n c g hsym
  have hrel' := fun g => sub_isRel n c g hrel
  by_cases hA : ∃ i0 i1, i0 ≠ i1 ∧ n i0 ≠ 0 ∧ n i1 ≠ 0
  · obtain ⟨i0, i1, hne, h0, h1⟩ := hA
    obtain ⟨s, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 p hp.one_lt.ne'
    obtain ⟨s1, m1, hm1, he1⟩ := Nat.exists_eq_pow_mul_and_not_dvd h1 p hp.one_lt.ne'
    have hs : p ^ s ≤ n i0 := by
      rw [he]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at he; exact h0 he))
    have hs1 : p ^ s1 ≤ n i1 := by
      rw [he1]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at he1; exact h1 he1))
    obtain ⟨g, hg⟩ := mk i0 s hs
    refine fin g (eq_zero_of_atoms n _ hu (hrel' g) ?_)
    have hc1 := atom_cross n _ hu (hrel' g) (hsym' g) i0 s
      (by rw [he, Nat.mul_div_cancel_left _ (hps s)]; exact hm) hs hg
    intro i j hj _
    by_cases hi : i = i0
    · subst hi
      exact atom_cross n _ hu (hrel' g) (hsym' g) i1 s1
        (by rw [he1, Nat.mul_div_cancel_left _ (hps s1)]; exact hm1) hs1 (hc1 i1 s1 (Ne.symm hne) hs1) i j hne hj
    · exact hc1 i j hi hj
  · push_neg at hA
    by_cases h2 : ∃ i0, 2 ≤ n i0
    · obtain ⟨i0, hN2⟩ := h2
      have hz : ∀ k, k ≠ i0 → n k = 0 := fun k hk => hA i0 k (Ne.symm hk) (by omega)
      obtain ⟨r, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n i0 ≠ 0) p hp.one_lt.ne'
      obtain ⟨s, K, hN, hK, hK'⟩ : ∃ s K, n i0 = p ^ s * K ∧ 2 ≤ K ∧
          (∀ j, s < j → p ^ j < n i0 → ¬ p ∣ (n i0 - p ^ j) / p ^ s) := by
        by_cases hm1 : m = 1
        · subst hm1
          rw [mul_one] at he
          have hr : 0 < r := by
            rcases Nat.eq_zero_or_pos r with h | h
            · subst h; simp at he; omega
            · exact h
          refine ⟨r - 1, p, ?_, hp.two_le, ?_⟩
          · rw [he, ← pow_succ]; congr 1; omega
          · intro j hj hlt
            exfalso
            have : p ^ r ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
            omega
        · have hm0 : m ≠ 0 := by rintro rfl; simp at he; omega
          refine ⟨r, m, he, by omega, ?_⟩
          intro j hj hlt
          have ej : p ^ j = p ^ r * p ^ (j - r) := by rw [← pow_add]; congr 1; omega
          rw [he, ej] at hlt ⊢
          have hlt' : p ^ (j - r) < m := Nat.lt_of_mul_lt_mul_left hlt
          rw [← Nat.mul_sub, Nat.mul_div_cancel_left _ (hps r)]
          intro hd
          apply hm
          have h3 := Nat.dvd_add hd (dvd_pow_self p (by omega : j - r ≠ 0))
          rwa [Nat.sub_add_cancel hlt'.le] at h3
      have hsle : p ^ s ≤ n i0 := by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
      obtain ⟨g, hg⟩ := mk i0 s hsle
      refine fin g (eq_zero_of_atoms n _ hu (hrel' g) ?_)
      intro i j hj hne
      have hi : i = i0 := by
        by_contra hi; rw [hz i hi] at hj; exact absurd hj (by have := hps j; omega)
      subst hi
      refine atom_line n _ hu (hrel' g) (hsym' g) i s K hN hK hK' hg j ?_
      rcases Nat.lt_or_ge (p ^ j) (n i) with h | h
      · exact h
      · exfalso; apply hne
        ext k
        by_cases hk : k = i
        · subst hk; simp only [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_apply, if_neg (Ne.symm hk), hz k hk]
    · push_neg at h2
      refine fin 0 ?_
      intro a han ha0 han'
      exfalso
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra h; push_neg at h; exact ha0 (Finsupp.ext fun i => by simp [h i])
      apply han'
      ext k
      have hak := Finsupp.le_def.1 han k
      have hai := Finsupp.le_def.1 han i
      have h2i := h2 i
      by_cases hk : k = i
      · subst hk; omega
      · have := hA i k (Ne.symm hk) (by omega)
        omega

end GlobalTheory.SymCocycleMV
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_prod_choose_smul_of_choose_relation : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M], (∀ m : M, ∃ m', p • m' = m) → (∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun m : M => n • m) → ∀ (d : ℕ) (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M), (∀ a, a ≤ n → c a = c (n - a)) → (∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) = (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a) → ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g := by
  atlas_forward_decl GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobEdges

section Kill

variable {R : Type} [CommRing R]

theorem cc_kill {σ τ : Type} (e : σ ↪ τ) (f : MvPowerSeries τ R) :
    constantCoeff (killCompl e f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
    coeff_zero_eq_constantCoeff_apply]

theorem kill_subst {σ τ υ : Type} [Finite υ] (e : σ ↪ τ) {a : υ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (H : MvPowerSeries υ R) :
    killCompl e (subst a H) = subst (fun k => killCompl e (a k)) H := by
  ext x
  rw [coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero fun k => (cc_kill e _).trans (ha k))]
  refine finsum_congr fun d => ?_
  rw [← coeff_killCompl, map_finsuppProd]
  simp only [map_pow]

theorem kill_eq_subst {σ τ : Type} [Finite τ] (e : σ ↪ τ) (F : MvPowerSeries τ R) :
    killCompl e F = subst (fun t => (killCompl e (X t) : MvPowerSeries σ R)) F := by
  have h := kill_subst e (a := fun t => (X t : MvPowerSeries τ R)) (fun t => constantCoeff_X t) F
  rw [subst_self] at h
  exact h

variable {d : ℕ} {τ : Type}

theorem elim_const {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (j : Fin d ⊕ Fin d) :
    constantCoeff (Sum.elim u v j) = 0 := by
  cases j with
  | inl i => exact hu i
  | inr i => exact hv i

theorem killCompl_powerSeriesEvalTwoGroups {σ : Type} [Finite τ] (e : σ ↪ τ) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    killCompl e (at2 c u v) = at2 c (fun i => killCompl e (u i)) (fun i => killCompl e (v i)) := by
  unfold at2
  rw [kill_subst e (elim_const hu hv)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_zero_zero (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 c (fun _ => (0 : MvPowerSeries τ R)) (fun _ => 0) = C (constantCoeff c) := by
  unfold at2
  have : (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries τ R)) fun _ : Fin d => 0) =
      (0 : Fin d ⊕ Fin d → MvPowerSeries τ R) := by
    funext s; cases s <;> rfl
  rw [this, subst_zero_eq_C_constantCoeff]
  ext n
  simp [coeff_C]

theorem powerSeriesEvalTwoGroups_X_zero (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 c (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) =
      killCompl Function.Embedding.inl c := by
  rw [kill_eq_subst]
  unfold at2
  congr 1
  funext s
  cases s with
  | inl i => exact (killCompl_X (e := (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)) i).symm
  | inr i =>
    refine (killCompl_X_eq_zero ?_).symm
    rintro ⟨j, hj⟩
    exact Sum.inl_ne_inr hj

theorem powerSeriesEvalTwoGroups_zero_X (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 c (fun _ => 0) (fun i => (X i : MvPowerSeries (Fin d) R)) =
      killCompl Function.Embedding.inr c := by
  rw [kill_eq_subst]
  unfold at2
  congr 1
  funext s
  cases s with
  | inl i =>
    refine (killCompl_X_eq_zero ?_).symm
    rintro ⟨j, hj⟩
    exact Sum.inr_ne_inl hj
  | inr i => exact (killCompl_X (e := (Function.Embedding.inr : Fin d ↪ Fin d ⊕ Fin d)) i).symm

theorem mvPowerSeriesMap_evalTwoGroups {S : Type} [CommRing S] (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (elim_const hu hv))]
  congr 1
  funext s
  cases s <;> rfl

end Kill

section Main

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

theorem powerSeriesEvalTwoGroups_swapVariableGroups (c : MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (swap c) u v = at2 c v u := by
  have hs := hasSubst_of_constantCoeff_zero (elim_const hu hv)
  have hW : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp
  unfold swap at2
  rw [subst_comp_subst_apply hW hs]
  congr 1
  funext s
  cases s <;> simp [subst_X hs]

theorem op_const {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (elim_const hu hv))
    (elim_const hu hv) (h i)

theorem sumElim_zero_right (a : Fin d →₀ ℕ) :
    Finsupp.sumElim a (0 : Fin d →₀ ℕ) =
      Finsupp.embDomain (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) a := by
  ext s
  cases s with
  | inl i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inl]
    exact (Finsupp.embDomain_apply_self (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) a i).symm
  | inr i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inr, Finsupp.embDomain_of_notMem_range]
    · rfl
    · rintro ⟨j, hj⟩
      exact Sum.inl_ne_inr hj

theorem sumElim_zero_left (a : Fin d →₀ ℕ) :
    Finsupp.sumElim (0 : Fin d →₀ ℕ) a =
      Finsupp.embDomain (Function.Embedding.inr : Fin d ↪ Fin d ⊕ Fin d) a := by
  ext s
  cases s with
  | inl i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.embDomain_of_notMem_range]
    · rfl
    · rintro ⟨j, hj⟩
      exact Sum.inr_ne_inl hj
  | inr i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inr]
    exact (Finsupp.embDomain_apply_self (Function.Embedding.inr : Fin d ↪ Fin d ⊕ Fin d) a i).symm

end Main

section Lift

variable {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] {θ : B →+* O} {d : ℕ}
  {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}

theorem up_const (hL : IsLift θ μ) (i : Fin d) : constantCoeff (up Q μ i) = 0 := by
  simp [up, hL.const i]

theorem up_unit (hL : IsLift θ μ) :
    op (up Q μ) (fun i => (X i : MvPowerSeries (Fin d) Q)) (fun _ => 0) = fun i => X i := by
  funext i
  have h := congrArg (map (algebraMap B Q)) (congrFun hL.unit i)
  unfold op at h ⊢
  rw [mvPowerSeriesMap_evalTwoGroups _ _ (fun _ => constantCoeff_X _) (fun _ => map_zero _)] at h
  simpa [up] using h

theorem up_comm (hL : IsLift θ μ) (i : Fin d) : swap (up Q μ i) = up Q μ i := by
  have h := congrArg (map (algebraMap B Q)) (hL.comm i)
  unfold swap at h ⊢
  rw [mvPowerSeriesMap_evalTwoGroups _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)] at h
  simpa [up] using h

theorem up_unit_left (hL : IsLift θ μ) :
    op (up Q μ) (fun _ => 0) (fun i => (X i : MvPowerSeries (Fin d) Q)) = fun i => X i := by
  funext i
  unfold op
  rw [← up_comm hL i, powerSeriesEvalTwoGroups_swapVariableGroups _ (fun _ => map_zero _) (fun _ => constantCoeff_X _)]
  exact congrFun (up_unit hL) i

end Lift

section Edges

variable {Q : Type} [CommRing Q] {d : ℕ}

def e3 (d : ℕ) : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d) :=
  ⟨fun i => Sum.inr (Sum.inr i), fun _ _ h => by simpa using h⟩

theorem killCompl_inl_threeGroupsFirstVariables : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
    (x1 (R := Q) (d := d) i)) = fun i => X i :=
  funext fun i => killCompl_X (e := (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))) i

theorem killCompl_inl_threeGroupsSecondVariables : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
    (x2 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj)

theorem killCompl_inl_threeGroupsThirdVariables : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
    (x3 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj)

theorem killCompl_thirdBlock_threeGroupsFirstVariables : (fun i => killCompl (e3 d) (x1 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by rintro ⟨j, hj⟩; exact Sum.inr_ne_inl hj)

theorem killCompl_thirdBlock_threeGroupsSecondVariables : (fun i => killCompl (e3 d) (x2 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by
    rintro ⟨j, hj⟩
    exact Sum.inr_ne_inl (Sum.inr.inj hj))

theorem killCompl_thirdBlock_threeGroupsThirdVariables : (fun i => killCompl (e3 d) (x3 (R := Q) (d := d) i)) = fun i => X i :=
  funext fun i => killCompl_X (e := e3 d) i

theorem killCompl_formalGroupLawCoboundaryTwo {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q} (h0 : ∀ i, constantCoeff (μ i) = 0)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) Q)) (fun _ => 0) = fun i => X i)
    (hu' : op μ (fun _ => 0) (fun i => (X i : MvPowerSeries (Fin d) Q)) = fun i => X i)
    (c : MvPowerSeries (Fin d ⊕ Fin d) Q) (hc : constantCoeff c = 0) :
    killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d)) (cob2 μ c) =
        -killCompl Function.Embedding.inl c ∧
      killCompl (e3 d) (cob2 μ c) = killCompl Function.Embedding.inr c := by
  have x1c : ∀ i, constantCoeff (x1 (R := Q) (d := d) i) = 0 := fun _ => constantCoeff_X _
  have x2c : ∀ i, constantCoeff (x2 (R := Q) (d := d) i) = 0 := fun _ => constantCoeff_X _
  have x3c : ∀ i, constantCoeff (x3 (R := Q) (d := d) i) = 0 := fun _ => constantCoeff_X _
  have h12 := op_const h0 x1c x2c
  have h23 := op_const h0 x2c x3c
  have opz : op μ (fun _ => (0 : MvPowerSeries (Fin d) Q)) (fun _ => 0) = fun _ => 0 := by
    funext i
    unfold op
    rw [powerSeriesEvalTwoGroups_zero_zero, h0, map_zero]
  refine ⟨?_, ?_⟩
  · have k12 : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
        (op μ x1 x2 i)) = fun i => X i := by
      rw [← hu]
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x1c x2c, killCompl_inl_threeGroupsFirstVariables, killCompl_inl_threeGroupsSecondVariables]
    have k23 : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
        (op μ x2 x3 i)) = fun _ => 0 := by
      rw [← opz]
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x2c x3c, killCompl_inl_threeGroupsSecondVariables, killCompl_inl_threeGroupsThirdVariables]
    unfold cob2
    rw [map_sub, map_add, map_sub, killCompl_powerSeriesEvalTwoGroups _ c x2c x3c, killCompl_powerSeriesEvalTwoGroups _ c h12 x3c,
      killCompl_powerSeriesEvalTwoGroups _ c x1c h23, killCompl_powerSeriesEvalTwoGroups _ c x1c x2c, killCompl_inl_threeGroupsFirstVariables, killCompl_inl_threeGroupsSecondVariables, killCompl_inl_threeGroupsThirdVariables, k12, k23,
      powerSeriesEvalTwoGroups_zero_zero, hc, map_zero, powerSeriesEvalTwoGroups_X_zero]
    abel
  · have k12 : (fun i => killCompl (e3 d) (op μ x1 x2 i)) = fun _ => 0 := by
      rw [← opz]
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x1c x2c, killCompl_thirdBlock_threeGroupsFirstVariables, killCompl_thirdBlock_threeGroupsSecondVariables]
    have k23 : (fun i => killCompl (e3 d) (op μ x2 x3 i)) = fun i => X i := by
      rw [← hu']
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x2c x3c, killCompl_thirdBlock_threeGroupsSecondVariables, killCompl_thirdBlock_threeGroupsThirdVariables]
    unfold cob2
    rw [map_sub, map_add, map_sub, killCompl_powerSeriesEvalTwoGroups _ c x2c x3c, killCompl_powerSeriesEvalTwoGroups _ c h12 x3c,
      killCompl_powerSeriesEvalTwoGroups _ c x1c h23, killCompl_powerSeriesEvalTwoGroups _ c x1c x2c, killCompl_thirdBlock_threeGroupsFirstVariables, killCompl_thirdBlock_threeGroupsSecondVariables, killCompl_thirdBlock_threeGroupsThirdVariables, k12, k23,
      powerSeriesEvalTwoGroups_zero_zero, hc, map_zero, powerSeriesEvalTwoGroups_zero_X]
    abel

end Edges

theorem coeff_edges_mem : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), constantCoeff c = 0 → In N (cob2 (up Q μ) c) → ∀ a : Fin d →₀ ℕ, (∃ b ∈ N, coeff (Finsupp.sumElim a 0) c = algebraMap B Q b) ∧ (∃ b ∈ N, coeff (Finsupp.sumElim 0 a) c = algebraMap B Q b) := by
  intro B O Q _ _ _ _ θ d μ hL N c hc hN a
  obtain ⟨k1, k3⟩ := killCompl_formalGroupLawCoboundaryTwo (up_const (Q := Q) hL) (up_unit hL) (up_unit_left hL) c hc
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb, e⟩ := hN (Finsupp.embDomain Function.Embedding.inl a)
    refine ⟨-b, N.neg_mem hb, ?_⟩
    rw [← coeff_killCompl, k1, map_neg, coeff_killCompl, ← sumElim_zero_right] at e
    rw [map_neg, ← e, neg_neg]
  · obtain ⟨b, hb, e⟩ := hN (Finsupp.embDomain (e3 d) a)
    refine ⟨b, hb, ?_⟩
    rw [← coeff_killCompl, k3, coeff_killCompl, ← sumElim_zero_left] at e
    exact e

end GlobalTheory.CobEdges
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_edges_mem_of_coboundaryTwo_coeffsInIdeal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), constantCoeff c = 0 → In N (cob2 (up Q μ) c) → ∀ a : Fin d →₀ ℕ, (∃ b ∈ N, coeff (Finsupp.sumElim a 0) c = algebraMap B Q b) ∧ (∃ b ∈ N, coeff (Finsupp.sumElim 0 a) c = algebraMap B Q b) := by
  atlas_forward_decl GlobalTheory.CobEdges.coeff_edges_mem
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_cob1_homog_lift_binomial : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (m : ℕ) (h : MvPowerSeries (Fin d) Q), m ≠ 0 → (∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) → ∀ a e : Fin d →₀ ℕ, (a + e).degree ≤ m → coeff (Finsupp.sumElim a e) (cob1 (up Q μ) h) = if a ≠ 0 ∧ e ≠ 0 then (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h else 0 := by
  first | exact @GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial | exact GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial | (intros; apply GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial <;> assumption)
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] (S : Submodule B Q) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), (∀ i, constantCoeff (u i) = 0) → (∀ α, coeff α f ∈ S) → ∀ β, coeff β (subst (up Q u) f) ∈ S := by
  first | exact @GlobalTheory.SubstSub.coeff_subst_up_mem | exact GlobalTheory.SubstSub.coeff_subst_up_mem | (intros; apply GlobalTheory.SubstSub.coeff_subst_up_mem <;> assumption)
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' : ∀ (R : Type) [CommRing R] (σ τ : Type) [Fintype σ] (u : σ → MvPowerSeries τ R) (f : MvPowerSeries σ R) (M : ℕ), (∀ i, constantCoeff (u i) = 0) → (∀ α : σ →₀ ℕ, α.degree < M → coeff α f = 0) → ∀ β : τ →₀ ℕ, β.degree < M → coeff β (subst u f) = 0 := by
  first | exact @GlobalTheory.coeff_subst_eq_zero_of_degree_lt | exact GlobalTheory.coeff_subst_eq_zero_of_degree_lt | (intros; apply GlobalTheory.coeff_subst_eq_zero_of_degree_lt <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace LawUp

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (CobCob.elim_has hu hv)]
  congr 1
  funext j
  cases j <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => map φ (op μ u v i)) =
      op (fun i => map φ (μ i)) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  funext i
  exact mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem isLaw_map (φ : R →+* S) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : IsLaw μ) :
    IsLaw (fun i => map φ (μ i)) := by
  have h12 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
  have h23 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have e := map_op φ μ (τ := Fin d) (u := fun i => (X i : MvPowerSeries (Fin d) R))
      (v := fun _ => 0) (fun _ => constantCoeff_X _) (fun _ => map_zero _)
    rw [h.unit] at e
    simp only [map_X, map_zero] at e
    exact e.symm
  · have e := mvPowerSeriesMap_evalTwoGroups φ (μ i) (τ := Fin d ⊕ Fin d)
      (u := fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (v := fun i => X (Sum.inl i)) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
    simp only [map_X] at e
    unfold swap
    rw [← e]
    exact congrArg (map φ) (h.comm i)
  · have e1 := map_op φ μ h12 CobCob.constantCoeff_threeGroupsThirdVariables
    have e2 := map_op φ μ CobCob.constantCoeff_threeGroupsFirstVariables h23
    have e3 := map_op φ μ (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
    have e4 := map_op φ μ (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
    have hx1 : (fun i => map φ (x1 (R := R) (d := d) i)) = x1 := by funext i; exact map_X _ _
    have hx2 : (fun i => map φ (x2 (R := R) (d := d) i)) = x2 := by funext i; exact map_X _ _
    have hx3 : (fun i => map φ (x3 (R := R) (d := d) i)) = x3 := by funext i; exact map_X _ _
    rw [hx1, hx2] at e3
    rw [hx2, hx3] at e4
    rw [e3, hx3] at e1
    rw [e4, hx1] at e2
    rw [← e1, ← e2, h.assoc]

end LawUp

theorem formalGroupLawCoboundaryTwo_coboundaryOne_fractions : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  intro B Q _ _ _ d μ h g
  have hL : IsLaw (up Q μ) := LawUp.isLaw_map (algebraMap B Q) h
  exact ((formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hL.const g).2.2.2.2.2 hL).1

end GlobalTheory
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  atlas_forward_decl GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CobSwap

theorem hasSubst_swapVars {R : Type} [CommRing R] {d : ℕ} :
    HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
  hasSubst_of_constantCoeff_zero fun j => by cases j <;> simp

theorem swap_map {B Q : Type} [CommRing B] [CommRing Q] (h : B →+* Q) {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) B) : swap (map h c) = map h (swap c) := by
  unfold swap at2
  rw [map_subst hasSubst_swapVars]
  congr 1
  funext j
  cases j <;> simp

theorem swap_subst {R : Type} [CommRing R] {d : ℕ} (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hν : ∀ i, constantCoeff (ν i) = 0) (f : MvPowerSeries (Fin d) R) :
    swap (subst ν f) = subst (fun i => swap (ν i)) f := by
  unfold swap at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hν) hasSubst_swapVars]

theorem swap_inL {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inL f) = inR f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inR f) = inL f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_sub {R : Type} [CommRing R] {d : ℕ} (a b : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap (a - b) = swap a - swap b := by
  unfold swap at2
  exact subst_sub hasSubst_swapVars a b

theorem swap_cob1_eq_of_swap_eq : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) →
    (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q,
    swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  intro B Q _ _ _ d μ h0 hs g
  have h0' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, h0 i]
  have hs' : ∀ i, swap (up Q μ i) = up Q μ i := fun i => by
    simp only [up]; rw [swap_map, hs i]
  unfold cob1
  rw [swap_sub, swap_sub, swap_subst _ h0', swap_inL, swap_inR]
  simp only [hs']
  abel

end GlobalTheory.CobSwap
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swapVariableGroups_formalGroupLawCoboundaryOne_comm : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q, swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  atlas_forward_decl GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.CobLin

theorem powerSeriesEvalTwoGroups_sub {R : Type} [CommRing R] {d : ℕ} {τ : Type} (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (c - c') u v = at2 c u v - at2 c' u v := by
  unfold at2
  exact subst_sub (hasSubst_of_constantCoeff_zero fun s => by
    cases s with
    | inl s => exact hu s
    | inr s => exact hv s) c c'

theorem constantCoeff_op_eq_zero {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 := by
  have ha : ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by
    cases s with
    | inl s => exact hu s
    | inr s => exact hv s
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (hμ i)

theorem sub_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (f f' : MvPowerSeries (Fin d) R), cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧
    swap (c - c') = swap c - swap c' ∧ cob1 μ (f - f') = cob1 μ f - cob1 μ f' := by
  intro R _ d μ hμ c c' f f'
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · unfold cob2
    rw [powerSeriesEvalTwoGroups_sub c c' _ _ h2 h3, powerSeriesEvalTwoGroups_sub c c' _ _ (constantCoeff_op_eq_zero hμ _ _ h1 h2) h3,
      powerSeriesEvalTwoGroups_sub c c' _ _ h1 (constantCoeff_op_eq_zero hμ _ _ h2 h3), powerSeriesEvalTwoGroups_sub c c' _ _ h1 h2]
    abel
  · unfold swap
    exact powerSeriesEvalTwoGroups_sub c c' _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
  · unfold cob1 inL inR
    rw [subst_sub (hasSubst_of_constantCoeff_zero hμ),
      subst_sub (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_sub (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    abel

end GlobalTheory.CobLin
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) (f f' : MvPowerSeries (Fin d) R), cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧ swap (c - c') = swap c - swap c' ∧ cob1 μ (f - f') = cob1 μ f - cob1 μ f' := by
  atlas_forward_decl GlobalTheory.CobLin.sub_rules
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_sumElim_powerSeriesSwapVariableGroups : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  first | exact @GlobalTheory.SwapCoeff.coeff_swap | exact GlobalTheory.SwapCoeff.coeff_swap | (intros; apply GlobalTheory.SwapCoeff.coeff_swap <;> assumption)
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

def V (p : ℕ) (J : Ideal B) : Submodule B Q where
  carrier := {q | ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * q = algebraMap B Q b}
  zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
  add_mem' := by
    rintro q₁ q₂ ⟨k₁, b₁, hb₁, h₁⟩ ⟨k₂, b₂, hb₂, h₂⟩
    refine ⟨k₁ + k₂, (p : B) ^ k₂ * b₁ + (p : B) ^ k₁ * b₂,
      J.add_mem (J.mul_mem_left _ hb₁) (J.mul_mem_left _ hb₂), ?_⟩
    simp only [map_add, map_mul, map_pow, map_natCast, ← h₁, ← h₂]
    ring
  smul_mem' := by
    rintro b q ⟨k, b₁, hb₁, h₁⟩
    refine ⟨k, b * b₁, J.mul_mem_left _ hb₁, ?_⟩
    simp only [Algebra.smul_def, map_mul, ← h₁]
    ring

def NS (N : Ideal B) : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N

theorem mem_NS {N : Ideal B} {q : Q} : q ∈ (NS N : Submodule B Q) ↔ ∃ b ∈ N, q = algebraMap B Q b := by
  simp only [NS, Submodule.mem_map, Algebra.linearMap_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩

theorem in_iff {σ : Type} {N : Ideal B} {f : MvPowerSeries σ Q} :
    In N f ↔ ∀ α, coeff α f ∈ (NS N : Submodule B Q) := by
  simp only [In, mem_NS, eq_comm]

theorem degree_sumElim {d : ℕ} (a e : Fin d →₀ ℕ) :
    (Finsupp.sumElim a e).degree = (a + e).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.sumElim_inl, Finsupp.sumElim_inr,
    Finsupp.add_apply, Finset.sum_add_distrib]

theorem exists_sumElim {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) : ∃ a e : Fin d →₀ ℕ, α = Finsupp.sumElim a e := by
  obtain ⟨⟨a, e⟩, h⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective α
  exact ⟨a, e, by rw [← h, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]⟩

theorem up_inl {d : ℕ} : up Q (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) B)) =
    fun i => X (Sum.inl i) := by
  funext i; simp [up, map_X]

theorem up_inr {d : ℕ} : up Q (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B)) =
    fun i => X (Sum.inr i) := by
  funext i; simp [up, map_X]

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem up_const {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up Q μ i) = 0 := by
  simp [up, hμ i]

theorem inL_eq {d : ℕ} (f : MvPowerSeries (Fin d) Q) :
    inL f = subst (up Q (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) B))) f := by
  rw [up_inl]; rfl

theorem inR_eq {d : ℕ} (f : MvPowerSeries (Fin d) Q) :
    inR f = subst (up Q (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))) f := by
  rw [up_inr]; rfl

theorem coeff_cob1_mem_submodule {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (S : Submodule B Q) (f : MvPowerSeries (Fin d) Q)
    (hf : ∀ α, coeff α f ∈ S) (α : Fin d ⊕ Fin d →₀ ℕ) : coeff α (cob1 (up Q μ) f) ∈ S := by
  have h1 := GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f μ hμ hf α
  have h2 := GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f _ (fun i => constantCoeff_X (Sum.inl i)) hf α
  have h3 := GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule B Q (Fin d) (Fin d ⊕ Fin d) S f _ (fun i => constantCoeff_X (Sum.inr i)) hf α
  unfold cob1
  rw [inL_eq (B := B), inR_eq (B := B), map_sub, map_sub]
  exact S.sub_mem (S.sub_mem h1 h2) h3

theorem din_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : DIn N f) (hg : DIn N g) :
    DIn N (f - g) := by
  intro α i
  obtain ⟨b, hb, e⟩ := hf α i
  obtain ⟨b', hb', e'⟩ := hg α i
  exact ⟨b - b', N.sub_mem hb hb', by rw [map_sub, mul_sub, e, e', map_sub]⟩

theorem dIn_cob1_of_isFrame_of_dIn {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B} {f : MvPowerSeries (Fin d) Q}
    (hf : DIn N f) : DIn N (cob1 (up Q μ) f) := by
  have h1 := (GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f μ hf hμ).1
  have h2 := (GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f _ hf
    (fun i => constantCoeff_X (Sum.inl i))).1
  have h3 := (GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero p B O Q θ hF (Fin d) (Fin d ⊕ Fin d) N f _ hf
    (fun i => constantCoeff_X (Sum.inr i))).1
  unfold cob1
  rw [inL_eq (B := B), inR_eq (B := B)]
  exact din_sub (din_sub h1 h2) h3

theorem in_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f - g) := by
  rw [in_iff] at *
  intro α; rw [map_sub]; exact Submodule.sub_mem _ (hf α) (hg α)

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem maint {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ) {N J : Ideal B}
    {m : ℕ} (hm : m ≠ 0) {c : MvPowerSeries (Fin d ⊕ Fin d) Q} {h : MvPowerSeries (Fin d) Q}
    (hor : IsLaw μ ∨ (DIn N c ∧ DIn N h)) (h0 : constantCoeff c = 0)
    (hV : ∀ α, coeff α c ∈ (V p J : Submodule B Q)) (h2 : In N (cob2 (up Q μ) c))
    (hs : In N (swap c - c)) (hlow : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → coeff α c ∈ (NS N : Submodule B Q))
    (hhom : ∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) (hhV : ∀ α, coeff α h ∈ (V p J : Submodule B Q))
    (hcong : ∀ a e : Fin d →₀ ℕ, a ≠ 0 → e ≠ 0 → (a + e).degree = m →
      coeff (Finsupp.sumElim a e) c - (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h ∈
        (NS N : Submodule B Q)) :
    (IsLaw μ ∨ DIn N (c - cob1 (up Q μ) h)) ∧ constantCoeff (c - cob1 (up Q μ) h) = 0 ∧
      (∀ α, coeff α (c - cob1 (up Q μ) h) ∈ (V p J : Submodule B Q)) ∧
      In N (cob2 (up Q μ) (c - cob1 (up Q μ) h)) ∧
      In N (swap (c - cob1 (up Q μ) h) - (c - cob1 (up Q μ) h)) ∧
      ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m + 1 → coeff α (c - cob1 (up Q μ) h) ∈ (NS N : Submodule B Q) := by
  have hμQ := up_const (Q := Q) hμ.const
  have hlin := GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules Q d (up Q μ) hμQ
  have hsw := GlobalTheory.T.swapVariableGroups_formalGroupLawCoboundaryOne_comm B Q d μ hμ.const hμ.comm h
  have hco := GlobalTheory.T.coeff_cob1_homog_lift_binomial B O Q θ d μ hμ m h hm hhom
  have hedge := GlobalTheory.T.coeff_edges_mem_of_coboundaryTwo_coeffsInIdeal B O Q θ d μ hμ N c h0 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hor with hl | ⟨hc, hh⟩
    · exact Or.inl hl
    · exact Or.inr (din_sub hc (dIn_cob1_of_isFrame_of_dIn hF hμ.const hh))
  · have := hco 0 0 (by simp)
    have hz : Finsupp.sumElim (0 : Fin d →₀ ℕ) (0 : Fin d →₀ ℕ) = 0 := by ext x; cases x <;> simp
    simp only [hz, add_zero, ne_eq, not_true_eq_false, false_and, if_false] at this
    rw [← coeff_zero_eq_constantCoeff_apply, map_sub, this, coeff_zero_eq_constantCoeff_apply, h0, sub_zero]
  · intro α; rw [map_sub]
    exact Submodule.sub_mem _ (hV α) (coeff_cob1_mem_submodule hμ.const _ h hhV α)
  · rw [(hlin c (cob1 (up Q μ) h) 0 0).1]
    rcases hor with hl | ⟨hc, hh⟩
    · rw [GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw B Q d μ hl h, sub_zero]; exact h2
    · have h3 := (GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod p B O Q θ hF d μ hμ N h hh).1
      refine in_sub h2 ?_
      intro α
      obtain ⟨b, hb, e⟩ := h3 α
      have hle : RingHom.ker θ * N ≤ N := Ideal.mul_le_inf.trans inf_le_right
      exact ⟨b, hle hb, e⟩
  · rw [(hlin c (cob1 (up Q μ) h) 0 0).2.1, hsw]
    have : swap c - cob1 (up Q μ) h - (c - cob1 (up Q μ) h) = swap c - c := by abel
    rw [this]; exact hs
  · intro α hα
    obtain ⟨a, e, rfl⟩ := exists_sumElim α
    rw [degree_sumElim] at hα
    have hco' := hco a e (by omega)
    rw [map_sub, hco']
    rcases Nat.lt_or_ge (a + e).degree m with hlt | hge
    · have : coeff (a + e) h = 0 := hhom _ (by omega)
      rw [this, mul_zero, ite_self, sub_zero]
      exact hlow _ (by rw [degree_sumElim]; exact hlt)
    · have heq : (a + e).degree = m := by omega
      by_cases hae : a ≠ 0 ∧ e ≠ 0
      · rw [if_pos hae]; exact hcong a e hae.1 hae.2 heq
      · rw [if_neg hae, sub_zero]
        rcases not_and_or.1 hae with ha | he
        · rw [not_not.1 ha]
          obtain ⟨b, hb, eb⟩ := (hedge e).2
          exact mem_NS.2 ⟨b, hb, eb⟩
        · rw [not_not.1 he]
          obtain ⟨b, hb, eb⟩ := (hedge a).1
          exact mem_NS.2 ⟨b, hb, eb⟩

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem degree_mono {d : ℕ} {a b : Fin d →₀ ℕ} (h : a ≤ b) : a.degree ≤ b.degree := by
  simp only [Finsupp.degree_eq_sum]; exact Finset.sum_le_sum fun i _ => h i

theorem prod_choose_pred {d : ℕ} (α : Fin d →₀ ℕ) (i : Fin d) (hi : α i ≠ 0) :
    (∏ j, Nat.choose (α j) ((α - Finsupp.single i 1 : Fin d →₀ ℕ) j) : ℕ) = α i := by
  rw [Finset.prod_eq_single i]
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.choose_symm (by omega), Nat.choose_one_right]
  · intro j _ hj
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hj), Nat.sub_zero, Nat.choose_self]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem build {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ) {N J : Ideal B}
    (hNJ : N ≤ J) {m : ℕ} (hm : 2 ≤ m) {c : MvPowerSeries (Fin d ⊕ Fin d) Q}
    (hV : ∀ α, coeff α c ∈ (V p J : Submodule B Q)) (h2 : In N (cob2 (up Q μ) c))
    (hs : In N (swap c - c)) (hlow : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → coeff α c ∈ (NS N : Submodule B Q)) :
    ∃ h : MvPowerSeries (Fin d) Q, (∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) ∧
      (∀ α, coeff α h ∈ (V p J : Submodule B Q)) ∧ (DIn N c → DIn N h) ∧
      ∀ a e : Fin d →₀ ℕ, a ≠ 0 → e ≠ 0 → (a + e).degree = m →
        coeff (Finsupp.sumElim a e) c - (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h ∈
          (NS N : Submodule B Q) := by
  set VJ : Submodule B Q := V p J
  set K : Submodule B VJ := (NS N : Submodule B Q).comap VJ.subtype
  have hK : ∀ x y : VJ, (Submodule.Quotient.mk x : VJ ⧸ K) = Submodule.Quotient.mk y ↔
      (x : Q) - y ∈ (NS N : Submodule B Q) := by
    intro x y; rw [Submodule.Quotient.eq]; rfl
  have hns : ∀ (k : ℕ) (x : VJ), k • (Submodule.Quotient.mk x : VJ ⧸ K) = Submodule.Quotient.mk (k • x) :=
    fun k x => (map_nsmul K.mkQ k x).symm
  have hcoe : ∀ (k : ℕ) (x : VJ), ((k • x : VJ) : Q) = (k : Q) * x := by
    intro k x; rw [Submodule.coe_smul_of_tower, nsmul_eq_mul]
  have hdiv : ∀ x : VJ ⧸ K, ∃ x', p • x' = x := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective K x
    obtain ⟨k, b, hb, e⟩ := v.2
    have hp := hF.unit_p
    refine ⟨Submodule.Quotient.mk ⟨(hp.unit⁻¹ : Qˣ) * v, k + 1, b, hb, ?_⟩, ?_⟩
    · rw [← e, pow_succ]
      calc (p : Q) ^ k * (p : Q) * ((hp.unit⁻¹ : Qˣ) * v)
          = (p : Q) ^ k * (((p : Q) * (hp.unit⁻¹ : Qˣ)) * v) := by ring
        _ = (p : Q) ^ k * v := by rw [show (p : Q) * (hp.unit⁻¹ : Qˣ) = 1 from hp.mul_val_inv, one_mul]
    · rw [hns]; congr 1; apply Subtype.ext; rw [hcoe]
      show (p : Q) * ((hp.unit⁻¹ : Qˣ) * v) = v
      rw [← mul_assoc, hp.mul_val_inv, one_mul]
  have hbij : ∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun x : VJ ⧸ K => n • x := by
    intro n hn
    have hu := hF.unit_coprime n hn
    refine Function.bijective_iff_has_inverse.2 ⟨fun x => (hu.unit⁻¹ : Bˣ) • x, ?_, ?_⟩
    · intro x
      show (hu.unit⁻¹ : Bˣ) • (n • x) = x
      rw [← Nat.cast_smul_eq_nsmul B, Units.smul_def, smul_smul]
      rw [show ((hu.unit⁻¹ : Bˣ) : B) * (n : B) = 1 from hu.val_inv_mul, one_smul]
    · intro x
      show n • ((hu.unit⁻¹ : Bˣ) • x) = x
      rw [← Nat.cast_smul_eq_nsmul B, Units.smul_def, smul_smul]
      rw [show (n : B) * ((hu.unit⁻¹ : Bˣ) : B) = 1 from hu.mul_val_inv, one_smul]
  have hlow' : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b := by
    intro α hα; exact mem_NS.1 (hlow α hα)
  have hrel := GlobalTheory.T.coboundary_degree_part_cocycle_mod_ideal B O Q θ d μ hμ N m c hlow' h2
  have key : ∀ n : Fin d →₀ ℕ, ∃ q : VJ, n.degree = m → ∀ a, a ≤ n → a ≠ 0 → a ≠ n →
      coeff (Finsupp.sumElim a (n - a)) c - (∏ i, Nat.choose (n i) (a i) : Q) * q ∈ (NS N : Submodule B Q) := by
    intro n
    by_cases hn : n.degree = m
    swap
    · exact ⟨0, fun h => absurd h hn⟩
    let cn : (Fin d →₀ ℕ) → VJ ⧸ K := fun a =>
      Submodule.Quotient.mk ⟨coeff (Finsupp.sumElim a (n - a)) c, hV _⟩
    have hsym : ∀ a, a ≤ n → cn a = cn (n - a) := by
      intro a ha
      show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [hK]
      simp only [tsub_tsub_cancel_of_le ha]
      have := (in_iff.1 hs) (Finsupp.sumElim (n - a) a)
      rwa [map_sub, GlobalTheory.T.coeff_sumElim_powerSeriesSwapVariableGroups] at this
    have hr : ∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n →
        (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • cn (a + b) =
          (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • cn a := by
      intro a b ha hb hab hab'
      simp only [cn, hns]
      rw [hK, hcoe, hcoe]
      obtain ⟨r, hr, e⟩ := hrel n hn a b ha hb hab hab'
      push_cast
      exact mem_NS.2 ⟨r, hr, e⟩
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_eq_prod_choose_smul_of_choose_relation p (VJ ⧸ K) hdiv hbij d n cn hsym hr
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective K g
    refine ⟨q, fun _ a ha ha0 han => ?_⟩
    have h1 := hg a ha ha0 han
    simp only [cn, hns] at h1
    rw [hK, hcoe] at h1
    push_cast at h1
    exact h1
  choose qf hqf using key
  let h : MvPowerSeries (Fin d) Q := fun α => if α.degree = m then (qf α : Q) else 0
  have hh : ∀ α, coeff α h = if α.degree = m then (qf α : Q) else 0 := fun α => by
    rw [coeff_apply]
  refine ⟨h, fun α hα => by rw [hh, if_neg hα], fun α => ?_, fun hc => ?_, fun a e ha he hae => ?_⟩
  · rw [hh]; split_ifs
    · exact (qf α).2
    · exact VJ.zero_mem
  · intro α i
    by_cases hα : α.degree = m
    swap
    · exact ⟨0, N.zero_mem, by rw [hh, if_neg hα, mul_zero, map_zero]⟩
    by_cases hi : α i = 0
    · exact ⟨0, N.zero_mem, by rw [hi, Nat.cast_zero, zero_mul, map_zero]⟩
    have hle1 : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.2 (by omega)
    set a := α - Finsupp.single i 1 with ha_def
    have ha : a ≤ α := tsub_le_self
    have ha0 : a ≠ 0 := by
      intro h0
      have h3 := degree_mono (tsub_eq_zero_iff_le.1 h0)
      have h4 : (Finsupp.single i 1 : Fin d →₀ ℕ).degree = 1 := by
        simp [Finsupp.degree_eq_sum, Finsupp.single_apply]
      omega
    have han : a ≠ α := by
      intro h0
      have := congrArg (fun f : Fin d →₀ ℕ => f i) h0
      simp only [ha_def, Finsupp.tsub_apply, Finsupp.single_eq_same] at this
      omega
    have hq := hqf α hα a ha ha0 han
    rw [tsub_tsub_cancel_of_le hle1] at hq
    have hprod : (∏ j, Nat.choose (α j) (a j) : Q) = (α i : Q) := by
      rw [← Nat.cast_prod, prod_choose_pred α i hi]
    rw [hprod] at hq
    obtain ⟨b, hb, eb⟩ := hc (Finsupp.sumElim a (Finsupp.single i 1)) (Sum.inr i)
    simp only [Finsupp.sumElim_inr, Finsupp.single_eq_same, Nat.cast_one, one_mul] at eb
    have hmem : (α i : Q) * coeff α h ∈ (NS N : Submodule B Q) := by
      have e2 : (α i : Q) * coeff α h = coeff (Finsupp.sumElim a (Finsupp.single i 1)) c -
          (coeff (Finsupp.sumElim a (Finsupp.single i 1)) c - (α i : Q) * (qf α : Q)) := by
        rw [hh, if_pos hα]; ring
      rw [e2]
      exact Submodule.sub_mem _ (mem_NS.2 ⟨b, hb, eb⟩) hq
    obtain ⟨b', hb', e'⟩ := mem_NS.1 hmem
    exact ⟨b', hb', e'⟩
  · have hne : a ≠ a + e := by
      intro h0; exact he (by simpa using h0.symm)
    have hq := hqf (a + e) hae a le_self_add ha hne
    rw [add_tsub_cancel_left] at hq
    rw [hh, if_pos hae]
    exact hq

end GlobalTheory.SymCob

namespace GlobalTheory.SymCob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem degree_add' {d : ℕ} (a e : Fin d →₀ ℕ) : (a + e).degree = a.degree + e.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]

def Inv (p : ℕ) {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (N J : Ideal B) (m : ℕ)
    (c : MvPowerSeries (Fin d ⊕ Fin d) Q) : Prop :=
  (IsLaw μ ∨ DIn N c) ∧ constantCoeff c = 0 ∧ (∀ α, coeff α c ∈ (V p J : Submodule B Q)) ∧
    In N (cob2 (up Q μ) c) ∧ In N (swap c - c) ∧
    ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → coeff α c ∈ (NS N : Submodule B Q)

theorem step {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {θ : B →+* O} (hF : IsFrame p Q θ)
    {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ) {N J : Ideal B}
    (hNJ : N ≤ J) {m : ℕ} (hm : m ≠ 0) {c : MvPowerSeries (Fin d ⊕ Fin d) Q}
    (hc : Inv p μ N J m c) :
    ∃ h : MvPowerSeries (Fin d) Q, (∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ m) → coeff α h = 0) ∧
      (∀ α, coeff α h ∈ (V p J : Submodule B Q)) ∧ Inv p μ N J (m + 1) (c - cob1 (up Q μ) h) := by
  obtain ⟨hor, h0, hV, h2, hs, hlow⟩ := hc
  by_cases hm2 : 2 ≤ m
  · obtain ⟨h, hhom, hhV, hdin, hcong⟩ := build hF hμ hNJ hm2 hV h2 hs hlow
    refine ⟨h, fun α hα => hhom α (by omega), hhV, ?_⟩
    have hor' : IsLaw μ ∨ (DIn N c ∧ DIn N h) := by
      rcases hor with hl | hd
      · exact Or.inl hl
      · exact Or.inr ⟨hd, hdin hd⟩
    exact maint hF hμ hm hor' h0 hV h2 hs hlow hhom hhV hcong
  · refine ⟨0, fun α _ => by simp, fun α => by simp, ?_⟩
    have hor' : IsLaw μ ∨ (DIn N c ∧ DIn N (0 : MvPowerSeries (Fin d) Q)) := by
      rcases hor with hl | hd
      · exact Or.inl hl
      · exact Or.inr ⟨hd, fun α i => ⟨0, N.zero_mem, by simp⟩⟩
    refine maint hF hμ hm hor' h0 hV h2 hs hlow (fun α _ => by simp) (fun α => by simp) ?_
    intro a e ha he hae
    have h1 : a.degree ≠ 0 := fun h => ha ((Finsupp.degree_eq_zero_iff a).1 h)
    have h3 : e.degree ≠ 0 := fun h => he ((Finsupp.degree_eq_zero_iff e).1 h)
    rw [degree_add'] at hae
    omega

theorem coeff_cob1_low_degree_vanish {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) Q) (M : ℕ)
    (hf : ∀ β : Fin d →₀ ℕ, β.degree < M → coeff β f = 0) (α : Fin d ⊕ Fin d →₀ ℕ)
    (hα : α.degree < M) : coeff α (cob1 (up Q μ) f) = 0 := by
  have h1 := GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (up Q μ) f M (up_const hμ) hf α hα
  have h2 := GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) f M
    (fun i => constantCoeff_X _) hf α hα
  have h3 := GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' Q (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) f M
    (fun i => constantCoeff_X _) hf α hα
  unfold cob1 inL inR
  rw [map_sub, map_sub, h1, h2, h3, sub_zero, sub_zero]

end GlobalTheory.SymCob

open GlobalTheory.SymCob in
theorem GlobalTheory.symmetric_cocycle_is_coboundary_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N J : Ideal B), N ≤ J → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) Q, (IsLaw μ ∨ DIn N c) → constantCoeff c = 0 → (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → In N (swap c - c) → ∃ g : MvPowerSeries (Fin d) Q, constantCoeff g = 0 ∧ lin g = 0 ∧ (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α g = algebraMap B Q b) ∧ In N (c - cob1 (up Q μ) g) := by
  intro p _ B O Q _ _ _ _ θ hF d μ hμ N J hNJ c hor h0 hVc h2 hs
  have hV : ∀ α, coeff α c ∈ (V p J : Submodule B Q) := hVc
  have step' : ∀ (k : ℕ) (c' : MvPowerSeries (Fin d ⊕ Fin d) Q), ∃ h : MvPowerSeries (Fin d) Q,
      Inv p μ N J (k + 1) c' → (∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ k + 1) → coeff α h = 0) ∧
        (∀ α, coeff α h ∈ (V p J : Submodule B Q)) ∧ Inv p μ N J (k + 1 + 1) (c' - cob1 (up Q μ) h) := by
    intro k c'
    by_cases hP : Inv p μ N J (k + 1) c'
    · obtain ⟨h, h1, h2, h3⟩ := step hF hμ hNJ (Nat.succ_ne_zero k) hP
      exact ⟨h, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose H hH using step'
  let s : ℕ → MvPowerSeries (Fin d ⊕ Fin d) Q := fun k =>
    Nat.rec c (fun k sk => sk - cob1 (up Q μ) (H k sk)) k
  have hsS : ∀ k, s (k + 1) = s k - cob1 (up Q μ) (H k (s k)) := fun k => rfl
  have hP : ∀ k, Inv p μ N J (k + 1) (s k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨hor, h0, hV, h2, hs, fun α hα => ?_⟩
      have : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (by omega)
      subst this
      show coeff 0 c ∈ _
      rw [coeff_zero_eq_constantCoeff_apply, h0]; exact Submodule.zero_mem _
    | succ k ih => rw [hsS]; exact (hH k (s k) ih).2.2
  let piece : ℕ → MvPowerSeries (Fin d) Q := fun k => H k (s k)
  have hpz : ∀ k, ∀ α : Fin d →₀ ℕ, (α.degree < 2 ∨ α.degree ≠ k + 1) → coeff α (piece k) = 0 :=
    fun k => (hH k (s k) (hP k)).1
  have hpV : ∀ k α, coeff α (piece k) ∈ (V p J : Submodule B Q) := fun k => (hH k (s k) (hP k)).2.1
  have hμQ := up_const (Q := Q) hμ.const
  have hc0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0 := by
    have := formalCoboundary_smul hμQ (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    simpa using this
  let G : ℕ → MvPowerSeries (Fin d) Q := fun k => ∑ j ∈ Finset.range k, piece j
  have hsG : ∀ k, s k = c - cob1 (up Q μ) (G k) := by
    intro k
    induction k with
    | zero => show c = c - cob1 (up Q μ) (∑ j ∈ Finset.range 0, piece j); rw [Finset.sum_range_zero, hc0, sub_zero]
    | succ k ih =>
      rw [hsS]
      change s k - cob1 (up Q μ) (piece k) = c - cob1 (up Q μ) (∑ j ∈ Finset.range (k + 1), piece j)
      rw [ih]
      rw [Finset.sum_range_succ, formalCoboundary_add hμQ]
      abel
  let g : MvPowerSeries (Fin d) Q := fun α => ∑ j ∈ Finset.range α.degree, coeff α (piece j)
  have hg : ∀ α, coeff α g = ∑ j ∈ Finset.range α.degree, coeff α (piece j) := fun α => by
    rw [coeff_apply]
  have hgG : ∀ k (α : Fin d →₀ ℕ), α.degree ≤ k → coeff α g = coeff α (G k) := by
    intro k α hk
    rw [hg]
    show _ = coeff α (∑ j ∈ Finset.range k, piece j)
    rw [map_sum]
    refine Finset.sum_subset (Finset.range_mono hk) fun j _ hj => hpz j α (Or.inr ?_)
    rw [Finset.mem_range, not_lt] at hj
    omega
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, hg]; simp
  · funext i
    show coeff (Finsupp.single i 1) g = 0
    rw [hg]
    have hd : (Finsupp.single i 1 : Fin d →₀ ℕ).degree = 1 := by
      simp [Finsupp.degree_eq_sum, Finsupp.single_apply]
    rw [hd, Finset.sum_range_one]
    exact hpz 0 _ (Or.inl (by omega))
  · intro α
    show coeff α g ∈ (V p J : Submodule B Q)
    rw [hg]
    exact Submodule.sum_mem _ fun j _ => hpV j α
  · rw [in_iff]
    intro α
    have hdiff : coeff α (cob1 (up Q μ) (g - G α.degree)) = 0 := by
      refine coeff_cob1_low_degree_vanish hμ.const _ (α.degree + 1) (fun β hβ => ?_) α (by omega)
      rw [map_sub, hgG α.degree β (by omega), sub_self]
    rw [(GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules Q d (up Q μ) hμQ 0 0 g (G α.degree)).2.2, map_sub, sub_eq_zero] at hdiff
    rw [map_sub, hdiff, ← map_sub, ← hsG]
    exact (hP α.degree).2.2.2.2.2 α (by omega)
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_sub_in_of_cob2_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N J : Ideal B), N ≤ J → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) Q, (IsLaw μ ∨ DIn N c) → constantCoeff c = 0 → (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → In N (swap c - c) → ∃ g : MvPowerSeries (Fin d) Q, constantCoeff g = 0 ∧ lin g = 0 ∧ (∀ α, ∃ k : ℕ, ∃ b ∈ J, (p : Q) ^ k * coeff α g = algebraMap B Q b) ∧ In N (c - cob1 (up Q μ) g) := by
  atlas_forward_decl GlobalTheory.symmetric_cocycle_is_coboundary_mod
end
