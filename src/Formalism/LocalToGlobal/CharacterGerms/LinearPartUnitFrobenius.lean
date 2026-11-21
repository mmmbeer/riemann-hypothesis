import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt
import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob
import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfAdjointCongruence

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence FirstVanishing

variable {C : Type} [Field C] [CharZero C] {V : VF C} {dd : ℕ}

def FrobX (V : VF C) (P : PS C 1 dd) : Prop :=
  ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) → V.MM (MvPowerSeries.coeff μ P)

theorem coeff_l_frob {P : PS C 1 dd} (hP : IntS V P) (hPz : MvPowerSeries.constantCoeff P = 0) (hfrob : FrobX V P)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) -
      ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => intS_cv (hγ j).2
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hγ0' : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := hγ0
  obtain ⟨D1, hD1def⟩ : ∃ D1 : PS C 1 dd, ∀ μ, MvPowerSeries.coeff μ D1 =
      if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0 :=
    ⟨fun μ => if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0, fun μ => rfl⟩
  obtain ⟨D3, hD3def⟩ : ∃ D3 : PS C 1 dd, D3 = ∑ i, MvPowerSeries.monomial (Finsupp.single ((0 : Fin 1), i) V.l)
      (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) := ⟨_, rfl⟩
  have hD1 : MMS V D1 := fun μ => by
    rw [hD1def]
    split_ifs with h
    · exact hfrob μ h
    · exact mm_zero
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  have hD2 : Agr (2 * V.l) (P - D1 - D3) 0 := by
    intro μ hμ
    rw [map_sub, map_sub, map_zero, hD1def, hD3def, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    by_cases hex : ∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)
    · rw [if_pos hex, sub_self, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro rfl
      obtain ⟨i', hi'⟩ := hex
      apply hi'
      rw [Finsupp.single_apply]
      split_ifs
      · exact dvd_refl _
      · exact dvd_zero _
    · rw [if_neg hex, sub_zero]
      push Not at hex
      have hdiv : ∀ s, V.l ∣ μ s := fun s => by rw [hsq s]; exact hex s.2
      rcases FirstVanishing.divisible_small μ hdiv hμ with h0 | ⟨s, hs⟩
      · subst h0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun i _ => if_neg ?_
        intro h
        have := congrArg (fun f : Fin 1 × Fin dd →₀ ℕ => f ((0 : Fin 1), i)) h
        simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at this
        omega
      · subst hs
        rw [Finset.sum_eq_single s.2, if_pos (by rw [← hsq s]), ← hsq s, sub_self]
        · intro i _ hi
          rw [if_neg]
          intro h
          apply hi
          have := (Finsupp.single_left_inj (by omega : V.l ≠ 0)).1 h
          rw [this]
        · intro h
          exact absurd (Finset.mem_univ _) h
  have hz : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (0 : PS C 1 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hG, map_zero]
  have hsplit : P = D1 + (P - D1 - D3) + D3 := by ring
  have hdeg : (Finsupp.single () V.l).degree < 2 * V.l := by
    rw [Finsupp.degree_single]
    omega
  have hA2 := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) hD2)
    (Finsupp.single () V.l) hdeg
  rw [hz, map_zero] at hA2
  have hA2' : PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3)) = 0 :=
    hA2
  have hB1' : MMS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1) :=
    MMS.subst (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) (fun q => hγI q.2) hD1
  have hB1 : V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1)) :=
    hB1' (Finsupp.single () V.l)
  have hD3 : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 =
      ∑ i, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) * γ i ^ V.l := by
    rw [hD3def, ← MvPowerSeries.coe_substAlgHom hG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hG, MvPowerSeries.subst_monomial hG, Finsupp.prod_single_index (by simp)]
    rfl
  have hfr : ∀ i, V.MM (PowerSeries.coeff V.l (γ i ^ V.l) - (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
    intro i
    have h := mms_pow_frobTw (hγI i) (Finsupp.single () V.l)
    rw [map_sub, coeff_frobTw, if_pos (fun s => by simp)] at h
    have e : (Finsupp.single () V.l).mapRange (fun n => n / V.l) (Nat.zero_div V.l) = Finsupp.single () 1 := by
      rw [Finsupp.mapRange_single, Nat.div_self (by omega)]
    rw [e] at h
    exact h
  have eP : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1 +
        MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3) +
          MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 := by
    conv_lhs => rw [hsplit]
    rw [MvPowerSeries.subst_add hG, MvPowerSeries.subst_add hG]
  rw [eP, map_add, map_add, hA2', add_zero, hD3, map_sum]
  have e : ∀ (a : C) (s t : Fin dd → C),
      a + ∑ i, s i - ∑ i, t i = a + ∑ i, (s i - t i) := fun a s t => by
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  refine mm_add hB1 (mm_sum _ _ fun i _ => ?_)
  rw [show PowerSeries.coeff V.l (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) *
      γ i ^ V.l) = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * PowerSeries.coeff V.l (γ i ^ V.l) from
    MvPowerSeries.coeff_C_mul _ _ _, ← mul_sub]
  exact mm_mul_ge' (hP _) (hfr i)

theorem coeff_lt_frob {P : PS C 1 dd} (hPz : MvPowerSeries.constantCoeff P = 0) (hfrob : FrobX V P)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) (n : ℕ) (hn : n < V.l) :
    V.MM (PowerSeries.coeff n (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P)) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => intS_cv (hγ j).2
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  obtain ⟨D1, hD1def⟩ : ∃ D1 : PS C 1 dd, ∀ μ, MvPowerSeries.coeff μ D1 =
      if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0 :=
    ⟨fun μ => if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0, fun μ => rfl⟩
  have hD1 : MMS V D1 := fun μ => by
    rw [hD1def]
    split_ifs with h
    · exact hfrob μ h
    · exact mm_zero
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  have hD2 : Agr V.l (P - D1) 0 := by
    intro μ hμ
    rw [map_sub, map_zero, hD1def]
    by_cases hex : ∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)
    · rw [if_pos hex, sub_self]
    · rw [if_neg hex, sub_zero]
      push Not at hex
      have hdiv : ∀ s, V.l ∣ μ s := fun s => by rw [hsq s]; exact hex s.2
      rcases FirstVanishing.divisible_small μ hdiv (by omega) with h0 | ⟨s, hs⟩
      · subst h0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz]
      · subst hs
        rw [Finsupp.degree_single] at hμ
        omega
  have hz : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (0 : PS C 1 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hG, map_zero]
  have hA2 := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0 q.2) hD2)
    (Finsupp.single () n) (by rw [Finsupp.degree_single]; exact hn)
  rw [hz, map_zero] at hA2
  have hA2' : PowerSeries.coeff n (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1)) = 0 := hA2
  have hB1' : MMS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1) :=
    MMS.subst (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0 q.2) (fun q => hγI q.2) hD1
  have hB1 : V.MM (PowerSeries.coeff n (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1)) :=
    hB1' (Finsupp.single () n)
  have eP : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1 +
        MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1) := by
    conv_lhs => rw [show P = D1 + (P - D1) by ring]
    rw [MvPowerSeries.subst_add hG]
  rw [eP, map_add, hA2', add_zero]
  exact hB1

def LowMM (V : VF C) (f : PowerSeries C) : Prop := ∀ n ≤ V.l, V.MM (PowerSeries.coeff n f)

theorem LowMM.mul_int {f g : PowerSeries C} (hf : LowMM V f) (hg : IntS V g) : LowMM V (f * g) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  refine mm_sum _ _ fun p hp => mm_mul_ge (hf p.1 ?_) (hg (Finsupp.single () p.2))
  have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  omega

theorem lowMM_subst {σ : Type} [Finite σ] {a : σ → PowerSeries C} (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (haI : ∀ s, IntS V (a s)) (haL : ∀ s, LowMM V (a s)) {f : MvPowerSeries σ C} (hf : IntS V f)
    (hf0 : MvPowerSeries.constantCoeff f = 0) : LowMM V (MvPowerSeries.subst a f) := by
  intro n hn
  change V.MM (MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst a f))
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  refine finsum_induction (fun x => V.MM x) mm_zero (fun x y hx hy => mm_add hx hy) fun e => ?_
  rw [smul_eq_mul]
  by_cases he : e = 0
  · subst he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_mul]
    exact mm_zero
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp he
    have hs' : e s ≠ 0 := by simpa using hs
    have hmem : s ∈ e.support := Finsupp.mem_support_iff.2 hs'
    have hp : LowMM V (e.prod fun s m => a s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hmem]
      obtain ⟨m, hm⟩ : ∃ m, e s = m + 1 := ⟨e s - 1, by omega⟩
      rw [hm]
      show LowMM V (a s ^ (m + 1) * ∏ x ∈ e.support.erase s, a x ^ e x)
      rw [pow_succ', mul_assoc]
      refine (haL s).mul_int (intS_mul (intS_pow (haI s) _) ?_)
      exact Finset.prod_induction _ (IntS V) (fun _ _ h1 h2 => intS_mul h1 h2) intS_one fun t _ => intS_pow (haI t) _
    exact mm_mul_ge' (hf e) (hp n hn)

theorem coeff_one_subst_curve {P : PS C 1 dd} (hPz : MvPowerSeries.constantCoeff P = 0) {γ : Fin dd → PowerSeries C}
    (hγ0 : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) =
      ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) P * PowerSeries.coeff 1 (γ j) := by
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  obtain ⟨D3, hD3def⟩ : ∃ D3 : PS C 1 dd, D3 = ∑ i, MvPowerSeries.monomial (Finsupp.single ((0 : Fin 1), i) 1)
      (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) P) := ⟨_, rfl⟩
  have hD2 : Agr 2 P D3 := by
    intro μ hμ
    rw [hD3def, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    rcases Nat.lt_succ_iff.1 hμ |>.lt_or_eq with h1 | h1
    · have h0 : μ = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      subst h0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz]
      symm
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      intro h
      have := congrArg (fun f : Fin 1 × Fin dd →₀ ℕ => f ((0 : Fin 1), i)) h
      simp at this
    · obtain ⟨s, hs⟩ := degree_one h1
      subst hs
      rw [Finset.sum_eq_single s.2, if_pos (by rw [← hsq s]), ← hsq s]
      · intro i _ hi
        rw [if_neg]
        intro h
        apply hi
        have := (Finsupp.single_left_inj (by omega : (1 : ℕ) ≠ 0)).1 h
        rw [this]
      · intro h
        exact absurd (Finset.mem_univ _) h
  have hA := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0 q.2) hD2)
    (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  have hA' : PowerSeries.coeff 1 (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) =
      PowerSeries.coeff 1 (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3) := hA
  have hD3 : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 =
      ∑ i, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) P) * γ i ^ 1 := by
    rw [hD3def, ← MvPowerSeries.coe_substAlgHom hG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hG, MvPowerSeries.subst_monomial hG, Finsupp.prod_single_index (by simp)]
    rfl
  rw [hA', hD3, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_one]
  exact MvPowerSeries.coeff_C_mul _ _ _

end SelfAdjointCongruence

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def zl {C : Type} [Field C] {dd : ℕ} (v : Fin dd → C) (F : PS C 2 dd) : PS C 1 dd :=
  ∑ j, MvPowerSeries.C (v j) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), j) F)

namespace SelfAdjointLinearTerm

open PartialDerivEval FirstUnitSeriesIntegrality MulLFrob LiftedCoordinateEvaluation MvPowerSeries

variable {C : Type} [Field C] {dd : ℕ}

theorem snd_map (ν : Fin 1 × Fin dd →₀ ℕ) :
    (ν.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) = ν := by
  rw [← Finsupp.mapDomain_comp]
  have e : ((fun x : Fin dd => ((0 : Fin 1), x)) ∘ Prod.snd) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [e, Finsupp.mapDomain_id]

theorem snd_mapDomain_mapDomain (ν : Fin 1 × Fin dd →₀ ℕ) :
    (ν.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) =
      ν.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) := by
  rw [← Finsupp.mapDomain_comp]
  rfl

end SelfAdjointLinearTerm

open SelfAdjointLinearTerm in
theorem coeff_zl {C : Type} [Field C] {dd : ℕ} (v : Fin dd → C) (F : PS C 2 dd) (ν : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff ν (zl v F) = ∑ j, v j * MvPowerSeries.coeff
      (ν.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) + Finsupp.single ((1 : Fin 2), j) 1) F := by
  unfold zl
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul]
  conv_lhs => rw [← snd_map ν]
  rw [coeff_eval_second_zero, MvPowerSeries.coeff_pderiv, snd_mapDomain_mapDomain]
  have h0 : (ν.mapDomain fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) ((1 : Fin 2), j) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst hx
    exact absurd h01 (by decide)
  rw [h0]
  simp

namespace SelfAdjointLinearTerm

open PartialDerivEval FirstUnitSeriesIntegrality MulLFrob LiftedCoordinateEvaluation MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

theorem aux_statement_9 : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := by
  intro k i
  fin_cases k
  · simp [pt]
  · simp

theorem zl_sub (v : Fin dd → C) (F G : PS C 2 dd) : zl v (F - G) = zl v F - zl v G := by
  have hS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => aux_statement_9 p.1 p.2)
  simp only [zl, ev, map_sub, MvPowerSeries.subst_sub hS, mul_sub, Finset.sum_sub_distrib]

theorem zl_smul (v : Fin dd → C) (c : C) (F : PS C 2 dd) : zl v (c • F) = c • zl v F := by
  have hS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => aux_statement_9 p.1 p.2)
  simp only [zl, ev, Derivation.map_smul, LinearMap.map_smul, MvPowerSeries.subst_smul hS, Finset.smul_sum,
    mul_smul_comm]

theorem zl_expS (v : Fin dd → C) {f : PS C 2 dd} (hf : constantCoeff f = 0)
    (hf0 : ev (n := 1) ![pt C dd 0, 0] f = 0) : zl v (FB.expS C f) = zl v f := by
  unfold zl
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_expS hf, ev_mul aux_statement_9, expS_eq, ev_ex aux_statement_9 f hf, hf0, ex_zero, one_mul]

def PAB (A B : Pt C 1 dd) : Fin 2 → Pt C 2 dd := ![comp1 A (pt C (n := 2) dd 0), comp1 B (pt C (n := 2) dd 1)]

theorem constant_zero_comp_coordinate {n : ℕ} {A : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0) (k : Fin n) (i : Fin dd) :
    constantCoeff (comp1 A (pt C (n := n) dd k) i) = 0 := by
  simp only [comp1, ev]
  have hc : ∀ p : Fin 1 × Fin dd, constantCoeff ((![pt C dd k] : Fin 1 → Pt C n dd) p.1 p.2) = 0 := by
    intro p
    simp only [Matrix.cons_val_fin_one, pt, MvPowerSeries.constantCoeff_X]
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  · exact hc
  · exact hA i

theorem zPAB {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0) (hB : ∀ i, constantCoeff (B i) = 0) :
    Z0 (PAB A B) := by
  intro k i
  fin_cases k
  · simpa [PAB] using constant_zero_comp_coordinate hA 0 i
  · simpa [PAB] using constant_zero_comp_coordinate hB 1 i

theorem product_points_at_zero {A B : Pt C 1 dd} (hB : ∀ i, constantCoeff (B i) = 0) :
    (fun k i => ev (n := 1) ![pt C dd 0, 0] (PAB A B k i)) = (![A, 0] : Fin 2 → Pt C 1 dd) := by
  funext k i
  fin_cases k
  · show ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 0] (A i)) = A i
    rw [ev_ev (z0_1 _ fun j => z0_pt 0 j) aux_statement_9]
    have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k i)) =
        ![pt C (n := 1) dd 0] := by
      funext k i
      fin_cases k
      exact ev_X aux_statement_9 0 i
    rw [this, germEval_oneStandardPoint_self]
  · show ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] (B i)) = 0
    rw [ev_ev (z0_1 _ fun j => z0_pt 1 j) aux_statement_9]
    have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k i)) =
        ![(0 : Pt C 1 dd)] := by
      funext k i
      fin_cases k
      exact ev_X aux_statement_9 1 i
    rw [this, ev_zero_pt, hB i, map_zero]

theorem d_A (A : Pt C 1 dd) (j k : Fin dd) :
    pderiv C ((1 : Fin 2), j) (comp1 A (pt C (n := 2) dd 0) k) = 0 := by
  show pderiv C ((1 : Fin 2), j) (ev ![pt C (n := 2) dd 0] (A k)) = 0
  rw [pderiv_eval_single (fun j => z0_pt 0 j)]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [pderiv_pt_ne _ _ _ (show (0 : Fin 2) ≠ 1 by decide), mul_zero]

theorem d_B (B : Pt C 1 dd) (j k : Fin dd) :
    pderiv C ((1 : Fin 2), j) (comp1 B (pt C (n := 2) dd 1) k) =
      ev ![pt C (n := 2) dd 1] (pderiv C ((0 : Fin 1), j) (B k)) := by
  show pderiv C ((1 : Fin 2), j) (ev ![pt C (n := 2) dd 1] (B k)) = _
  rw [pderiv_eval_single (fun j => z0_pt 1 j), Finset.sum_eq_single j]
  · rw [pderiv_pt_same, if_pos rfl, mul_one]
  · intro m _ hm
    rw [pderiv_pt_same, if_neg hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem eval_pderiv_constant_linear (B : Pt C 1 dd) (j k : Fin dd) :
    ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] (pderiv C ((0 : Fin 1), j) (B k))) =
      MvPowerSeries.C (coeff (Finsupp.single ((0 : Fin 1), j) 1) (B k)) := by
  rw [ev_ev (z0_1 _ fun j => z0_pt 1 j) aux_statement_9]
  have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k i)) =
      ![(0 : Pt C 1 dd)] := by
    funext k i
    fin_cases k
    exact ev_X aux_statement_9 1 i
  rw [this, ev_zero_pt, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

variable {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem zl_hAB (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) (v : Fin dd → C) :
    zl v (ev (PAB A B) Y.h) = -ev (n := 1) ![A] (Y.sgP (linAct B v)) := by
  rw [ev_sgP Y _ A hA, neg_neg]
  unfold zl
  have h1 : ∀ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) (ev (PAB A B) Y.h)) =
      ∑ k, ev (n := 1) ![A, 0] (pderiv C ((1 : Fin 2), k) Y.h) *
        MvPowerSeries.C (coeff (Finsupp.single ((0 : Fin 1), j) 1) (B k)) := by
    intro j
    rw [pderiv_eval_pair (zPAB hA hB)]
    have e0 : ∑ k, ev (PAB A B) (pderiv C ((0 : Fin 2), k) Y.h) * pderiv C ((1 : Fin 2), j) (PAB A B 0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [show PAB A B 0 k = comp1 A (pt C (n := 2) dd 0) k from rfl, d_A, mul_zero]
    rw [e0, zero_add, ev_sum aux_statement_9]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show PAB A B 1 k = comp1 B (pt C (n := 2) dd 1) k from rfl, d_B, ev_mul aux_statement_9, eval_pderiv_constant_linear,
      ev_ev (zPAB hA hB) aux_statement_9, product_points_at_zero hB]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold linAct
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem height_at_zero_product (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) : ev (n := 1) ![pt C dd 0, 0] (ev (PAB A B) Y.h) = 0 := by
  rw [ev_ev (zPAB hA hB) aux_statement_9, product_points_at_zero hB]
  have h := congrArg (ev (n := 1) ![A]) Y.gauge.ax1
  rw [ev_ev aux_statement_9 (z0_1 A hA), ev_zero (z0_1 A hA)] at h
  have : (fun (k : Fin 2) (i : Fin dd) => ev (n := 1) ![A] ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) k i)) =
      (![A, 0] : Fin 2 → Pt C 1 dd) := by
    funext k i
    fin_cases k
    · exact ev_X (z0_1 A hA) 0 i
    · exact ev_zero (z0_1 A hA)
  rw [this] at h
  exact h

theorem const_hAB (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) : constantCoeff (ev (PAB A B) Y.h) = 0 :=
  const_ev (zPAB hA hB) (h_const Y)

theorem comp1_identity_left {n : ℕ} (k : Fin n) : comp1 (pt C (n := 1) dd 0) (pt C (n := n) dd k) = pt C dd k := by
  funext i
  simp only [comp1, ev, pt]
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
    simp only [Matrix.cons_val_fin_one, pt, MvPowerSeries.constantCoeff_X]))]
  rfl

theorem linAct_id (v : Fin dd → C) : linAct (pt C (n := 1) dd 0) v = v := by
  funext i
  unfold linAct
  rw [Finset.sum_eq_single i]
  · show coeff (Finsupp.single ((0 : Fin 1), i) 1) (X ((0 : Fin 1), i) : PS C 1 dd) * v i = v i
    rw [coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (X ((0 : Fin 1), i) : PS C 1 dd) * v j = 0
    rw [coeff_X, if_neg, zero_mul]
    intro h
    apply hj
    have := (Finsupp.single_left_inj (one_ne_zero)).1 h
    exact (Prod.mk.inj this).2
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem zId : ∀ i, constantCoeff (pt C (n := 1) dd 0 i) = 0 := fun i => by simp [pt]

end SelfAdjointLinearTerm

open SelfAdjointLinearTerm PartialDerivEval FirstUnitSeriesIntegrality MulLFrob in

theorem linear_part_first_unit {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (v : Fin dd → C) :
    zl v Y.u1 = (V.l : C) • Y.sgP v - ev (n := 1) ![mulL Y.B.G.F V.l] (Y.sgP v) := by
  have hM : ∀ i, MvPowerSeries.constantCoeff (mulL Y.B.G.F V.l i) = 0 := multiplication_constantCoeff_zero Y.B.G V.l
  have e1 : (![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) =
      PAB (mulL Y.B.G.F V.l) (pt C (n := 1) dd 0) := by
    unfold PAB
    rw [comp1_identity_left]
  have e2 : ev (PAB (pt C (n := 1) dd 0) (pt C (n := 1) dd 0)) Y.h = Y.h := by
    unfold PAB
    rw [comp1_identity_left, comp1_identity_left, PartialDerivEval.eval_points_two]
  have e3 : ev (n := 2) ![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] Y.h - (V.l : C) • Y.h =
      ev (PAB (mulL Y.B.G.F V.l) (pt C (n := 1) dd 0)) Y.h -
        (V.l : C) • ev (PAB (pt C (n := 1) dd 0) (pt C (n := 1) dd 0)) Y.h := by
    rw [e1, e2]
  unfold FBChart.u1
  rw [e3, zl_expS v
      (by rw [map_sub, const_hAB Y hM zId, MvPowerSeries.smul_eq_C_mul, map_mul, const_hAB Y zId zId, mul_zero,
        sub_zero])
      (by rw [ev_sub aux_statement_9, height_at_zero_product Y hM zId, MvPowerSeries.smul_eq_C_mul, ev_mul aux_statement_9, height_at_zero_product Y zId zId, mul_zero,
        sub_zero]),
    zl_sub, zl_smul, zl_hAB Y hM zId, zl_hAB Y zId zId, linAct_id, germEval_oneStandardPoint_self, smul_neg]
  ring

open SelfAdjointLinearTerm PartialDerivEval FirstUnitSeriesIntegrality MulLFrob in

theorem constant_zero_first_zero_self {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (e eb : Pt C 1 dd) (he0 : ∀ i, MvPowerSeries.constantCoeff (e i) = 0)
    (heb0 : ∀ i, MvPowerSeries.constantCoeff (eb i) = 0) (v : Fin dd → C) :
    zl v (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) =
      Y.sgP (linAct eb v) - ev (n := 1) ![e] (Y.sgP v) := by
  have e1 : (![comp1 e (pt C (n := 2) dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) = PAB e (pt C (n := 1) dd 0) := by
    unfold PAB
    rw [comp1_identity_left]
  have e2 : (![pt C (n := 2) dd 0, comp1 eb (pt C dd 1)] : Fin 2 → Pt C 2 dd) = PAB (pt C (n := 1) dd 0) eb := by
    unfold PAB
    rw [comp1_identity_left]
  rw [e1, e2, zl_expS v
      (by rw [map_sub, const_hAB Y he0 zId, const_hAB Y zId heb0, sub_zero])
      (by rw [ev_sub aux_statement_9, height_at_zero_product Y he0 zId, height_at_zero_product Y zId heb0, sub_zero]),
    zl_sub, zl_hAB Y he0 zId, zl_hAB Y zId heb0, linAct_id, germEval_oneStandardPoint_self]
  ring

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace PairPointEvaluation

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence FirstVanishing SelfAdjointCongruence MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constant_zero_pair_points {a b : Pt C 1 dd} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0) :
    Z0 (![a, b] : Fin 2 → Pt C 1 dd) := by
  intro k i
  fin_cases k
  · simpa using ha i
  · simpa using hb i

theorem eval_single_comp {a b : Pt C 1 dd} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (f : PS C 1 dd) : ev (n := 1) ![a] (ev (n := 1) ![b] f) = ev (n := 1) ![comp1 b a] f := by
  rw [ev_ev (z0_1 b hb) (z0_1 a ha)]
  congr 1
  funext k i
  fin_cases k
  rfl

theorem hom_at (G : FGLaw C dd) {e : Pt C 1 dd} (he0 : ∀ j, constantCoeff (e j) = 0)
    (hhom : comp1 e (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {a b : Pt C 1 dd} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0) :
    comp1 e (addOf G.F a b) = addOf G.F (comp1 e a) (comp1 e b) := by
  funext i
  have hab := constant_zero_pair_points ha hb
  have h := congrArg (ev (n := 1) ![a, b]) (congrFun hhom i)
  have hadd0 : ∀ j, constantCoeff (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => const_ev (z0_pp 0 1) (G.const j)
  have hc : ∀ (k : Fin 2) j, constantCoeff (comp1 e (pt C (n := 2) dd k) j) = 0 :=
    fun k j => const_ev (z0_1 _ (z0_pt k)) (he0 j)
  have hcc : Z0 (![comp1 e (pt C (n := 2) dd 0), comp1 e (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := fun k j => by
    fin_cases k
    · exact hc 0 j
    · exact hc 1 j
  have hL : ev (n := 1) ![a, b] (comp1 e (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) i) =
      comp1 e (addOf G.F a b) i := by
    show ev (n := 1) ![a, b] (ev ![addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] (e i)) =
      ev ![addOf G.F a b] (e i)
    rw [ev_ev (z0_1 _ hadd0) hab]
    congr 1
    funext k j
    fin_cases k
    show ev (n := 1) ![a, b] (ev (n := 2) ![pt C dd 0, pt C dd 1] (G.F j)) = ev ![a, b] (G.F j)
    rw [PartialDerivEval.eval_points_two]
  have hR : ev (n := 1) ![a, b] (addOf G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)) i) =
      addOf G.F (comp1 e a) (comp1 e b) i := by
    show ev (n := 1) ![a, b] (ev ![comp1 e (pt C (n := 2) dd 0), comp1 e (pt C (n := 2) dd 1)] (G.F i)) =
      ev ![comp1 e a, comp1 e b] (G.F i)
    rw [ev_ev hcc hab]
    congr 1
    funext k j
    fin_cases k
    · show ev (n := 1) ![a, b] (ev ![pt C (n := 2) dd 0] (e j)) = ev ![a] (e j)
      rw [ev_ev (z0_1 _ (z0_pt 0)) hab]
      congr 1
      funext k' j'
      fin_cases k'
      exact ev_X hab 0 j'
    · show ev (n := 1) ![a, b] (ev ![pt C (n := 2) dd 1] (e j)) = ev ![b] (e j)
      rw [ev_ev (z0_1 _ (z0_pt 1)) hab]
      congr 1
      funext k' j'
      fin_cases k'
      exact ev_X hab 1 j'
  rw [← hL, ← hR]
  exact h

theorem mulL_comm (G : FGLaw C dd) {e : Pt C 1 dd} (he0 : ∀ j, constantCoeff (e j) = 0)
    (hhom : comp1 e (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1))) (n : ℕ) :
    comp1 (mulL G.F n) e = comp1 e (mulL G.F n) := by
  induction n with
  | zero =>
    funext i
    show ev ![e] (0 : PS C 1 dd) = ev ![(0 : Pt C 1 dd)] (e i)
    rw [MulLFrob.ev_zero_pt, he0 i, map_zero, ev_zero (z0_1 e he0)]
  | succ n ih =>
    have hm0 := FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero G n
    have h1 : comp1 (mulL G.F (n + 1)) e = addOf G.F (comp1 (mulL G.F n) e) e := by
      funext i
      show ev ![e] (ev ![mulL G.F n, pt C dd 0] (G.F i)) = ev ![comp1 (mulL G.F n) e, e] (G.F i)
      rw [ev_ev (constant_zero_pair_points hm0 (z0_pt 0)) (z0_1 e he0)]
      congr 1
      funext k j
      fin_cases k
      · rfl
      · exact ev_X (z0_1 e he0) 0 j
    have h2 : comp1 e (mulL G.F (n + 1)) = addOf G.F (comp1 e (mulL G.F n)) e := by
      show comp1 e (addOf G.F (mulL G.F n) (pt C dd 0)) = _
      rw [hom_at G he0 hhom hm0 (z0_pt 0)]
      congr 1
      funext i
      exact MulLFrob.germEval_oneStandardPoint_self (e i)
    rw [h1, h2, ih]

theorem idx_apply (μ : Fin 1 × Fin dd →₀ ℕ) (i j : Fin dd) :
    (μ.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) + Finsupp.single ((1 : Fin 2), j) 1 :
      Fin 2 × Fin dd →₀ ℕ) ((0 : Fin 2), i) = μ ((0 : Fin 1), i) := by
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) := by
    intro p q h
    have h' : ((0 : Fin 2), p.2) = ((0 : Fin 2), q.2) := h
    exact Prod.ext (Subsingleton.elim _ _) (Prod.mk.inj h').2
  have hne : ((1 : Fin 2), j) ≠ ((0 : Fin 2), i) := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    intro h
    exact h10 (congrArg Prod.fst h)
  rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hne, add_zero]
  exact Finsupp.mapDomain_apply hinj μ ((0 : Fin 1), i)

theorem aLin_eq (Y : FBChart C V O dd) (u w : Fin dd → C) :
    Y.aLin u w = ∑ i, coeff (Finsupp.single ((0 : Fin 1), i) V.l) (zl w Y.u1) * u i ^ V.l := by
  simp only [coeff_zl, Finsupp.mapDomain_single]
  unfold FBChart.aLin
  have h : ∀ j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf u) =
      ∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l + Finsupp.single ((1 : Fin 2), j) 1) Y.u1 := by
    intro j
    show ∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l +
      (Finsupp.single ((0 : Fin 1), j) 1).mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1 = _
    rw [Finsupp.mapDomain_single]
  simp only [h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem intS_zl {w : Fin dd → C} (hw : ∀ i, V.Ge 0 (w i)) {F : PS C 2 dd} (hF : IntS V F) : IntS V (zl w F) := by
  intro ν
  rw [coeff_zl]
  exact VF.Ge.sum fun j _ => VF.Ge.mul_int (hw j) (hF _)

theorem linear_part_unit_frobenius (Y : FBChart C V O dd) {w : Fin dd → C} (hw : ∀ i, V.Ge 0 (w i)) : FrobX V (zl w Y.u1) := by
  intro μ hμ
  obtain ⟨i, hi⟩ := hμ
  rw [coeff_zl]
  refine mm_sum _ _ fun j _ => mm_mul_ge' (hw j) (first_unit_series_frobenius C V O dd Y _ ⟨i, ?_⟩)
  rw [idx_apply]
  exact hi

end PairPointEvaluation

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence FirstVanishing SelfAdjointCongruence PairPointEvaluation MvPowerSeries in

theorem aLinAdj_holds : ALinAdjSt := by
  intro C _ _ V O _ _ dd Y e eb heI hebI he0 heb0 hhom hW u hu hV1 v hv
  have hl := V.l_prime.two_le
  obtain ⟨M, hMdef⟩ : ∃ M : Pt C 1 dd, M = mulL Y.B.G.F V.l := ⟨_, rfl⟩
  have hM0 : ∀ j, constantCoeff (M j) = 0 := fun j => by rw [hMdef]; exact FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l j
  have hMI : ∀ j, IntS V (M j) := fun j => by rw [hMdef]; exact FirstUnitSeriesIntegrality.mulL_int Y.B.G Y.intF V.l j
  have hMF : ∀ k, FrobX V (M k) := fun k μ hμ => by rw [hMdef]; exact mulLFrob_holds C V O dd Y k μ hμ
  obtain ⟨v', hv'def⟩ : ∃ v' : Fin dd → C, v' = linAct eb v := ⟨_, rfl⟩
  have hv' : ∀ i, V.Ge 0 (v' i) := fun i => by
    rw [hv'def]
    exact VF.Ge.sum fun j _ => VF.Ge.mul_int (hebI i _) (hv j)
  obtain ⟨T, hTdef⟩ : ∃ T : PS C 1 dd, T = zl v (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) := ⟨_, rfl⟩
  have hS : ∀ w, zl w Y.u1 = MvPowerSeries.C (V.l : C) * Y.sgP w - ev (n := 1) ![M] (Y.sgP w) := fun w => by
    rw [linear_part_first_unit, hMdef, MvPowerSeries.smul_eq_C_mul]
  have hT : T = Y.sgP v' - ev (n := 1) ![e] (Y.sgP v) := by
    rw [hTdef, constant_zero_first_zero_self Y e eb he0 heb0 v, hv'def]
  have hTI : IntS V T := by rw [hTdef]; exact intS_zl hv hW
  have hsg0 : ∀ w, constantCoeff (Y.sgP w) = 0 := fun w => OActSelf.cc_sgP Y w
  have hT0 : constantCoeff T = 0 := by
    rw [hT, map_sub, hsg0, const_ev (z0_1 e he0) (hsg0 v), sub_zero]
  have hS0 : ∀ w, constantCoeff (zl w Y.u1) = 0 := fun w => by
    rw [hS, map_sub, map_mul, hsg0, const_ev (z0_1 M hM0) (hsg0 w), mul_zero, sub_zero]
  have hSI : ∀ w, (∀ i, V.Ge 0 (w i)) → IntS V (zl w Y.u1) := fun w hw => intS_zl hw (first_unit_series_integral C V O dd Y)

  have key : ev (n := 1) ![e] (zl v Y.u1) + MvPowerSeries.C (V.l : C) * T = zl v' Y.u1 + ev (n := 1) ![M] T := by
    rw [hS, hS, hT, ev_sub (z0_1 e he0), ev_mul (z0_1 e he0), ev_C, ev_sub (z0_1 M hM0), eval_single_comp he0 hM0,
      eval_single_comp hM0 he0, hMdef, mulL_comm Y.B.G he0 hhom]
    ring

  obtain ⟨γ0, hγ0def⟩ : ∃ γ0 : Fin dd → PowerSeries C, γ0 = fun i => u i • (MvPowerSeries.X () : PowerSeries C) :=
    ⟨_, rfl⟩
  have hc : ∀ i n, PowerSeries.coeff n (γ0 i) = if n = 1 then u i else 0 := fun i n => by
    rw [hγ0def]
    show PowerSeries.coeff n (u i • (MvPowerSeries.X () : PowerSeries C)) = _
    rw [map_smul, coeffX', smul_eq_mul]
    split_ifs <;> simp
  have hcv0 : IsCv V γ0 := fun i => ⟨by
      have := hc i 0
      rw [if_neg (by omega)] at this
      rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this, fun n => by
      rw [hc]
      split_ifs
      · exact hu i
      · exact VF.Ge.zero 0⟩
  have hγz : ∀ j, constantCoeff (γ0 j) = 0 := fun j => (hcv0 j).1
  have hγI : ∀ j, IntS V (γ0 j) := fun j => intS_cv (hcv0 j).2
  have hG : HasSubst (fun q : Fin 1 × Fin dd => γ0 q.2) := hasSubst_of_constantCoeff_zero fun q => hγz q.2
  have hδ0 : ∀ φ : Pt C 1 dd, (∀ j, constantCoeff (φ j) = 0) →
      ∀ k, constantCoeff (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ k)) = 0 :=
    fun φ hφ k => constantCoeff_subst_eq_zero hG (fun q => hγz q.2) (hφ k)
  have hδI : ∀ φ : Pt C 1 dd, (∀ j, IntS V (φ j)) →
      ∀ k, IntS V (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ k)) :=
    fun φ hφ k => intS_subst (a := fun q : Fin 1 × Fin dd => γ0 q.2) (fun q => hγz q.2) (fun q => hγI q.2) (hφ k)
  have hδcv : ∀ φ : Pt C 1 dd, (∀ j, constantCoeff (φ j) = 0) → (∀ j, IntS V (φ j)) →
      IsCv V (fun k => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ k)) :=
    fun φ h0 hI k => ⟨hδ0 φ h0 k, fun n => hδI φ hI k (Finsupp.single () n)⟩
  have hcomp : ∀ φ : Pt C 1 dd, (∀ j, constantCoeff (φ j) = 0) → ∀ f : PS C 1 dd,
      subst (fun q : Fin 1 × Fin dd => γ0 q.2) (ev (n := 1) ![φ] f) =
        subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ q.2)) f := by
    intro φ hφ f
    have hφS : HasSubst (fun q : Fin 1 × Fin dd => φ q.2) := hasSubst_of_constantCoeff_zero fun q => hφ q.2
    rw [eval_single_eq_subst, subst_comp_subst_apply hφS hG]
  have k2 := congrArg (subst (fun q : Fin 1 × Fin dd => γ0 q.2)) key
  rw [subst_add hG, subst_add hG, ← MvPowerSeries.smul_eq_C_mul, subst_smul hG, hcomp e he0, hcomp M hM0] at k2
  have k3 := congrArg (PowerSeries.coeff V.l) k2
  rw [map_add, map_add, map_smul, smul_eq_mul] at k3

  have hA1 := coeff_l_frob (hSI v hv) (hS0 v) (linear_part_unit_frobenius Y hv) (hδcv e he0 heI)
  have hlin : ∀ i, PowerSeries.coeff 1 (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (e i)) = linAct e u i := fun i => by
    rw [coeff_one_subst_curve (he0 i) hγz]
    unfold linAct
    exact Finset.sum_congr rfl fun j _ => by rw [hc, if_pos rfl]
  simp only [hlin] at hA1
  rw [← aLin_eq] at hA1
  have hA3 := coeff_l_frob (hSI v' hv') (hS0 v') (linear_part_unit_frobenius Y hv') hcv0
  simp only [hc, if_pos] at hA3
  rw [← aLin_eq] at hA3
  have hA2 : V.MM ((V.l : C) * PowerSeries.coeff V.l (subst (fun q : Fin 1 × Fin dd => γ0 q.2) T)) :=
    mm_l_mul (intS_subst (a := fun q : Fin 1 × Fin dd => γ0 q.2) (fun q => hγz q.2) (fun q => hγI q.2) hTI
      (Finsupp.single () V.l))
  have hLow : ∀ k, LowMM V (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M k)) := by
    intro k n hn
    rcases Nat.lt_or_ge n V.l with h | h
    · exact coeff_lt_frob (hM0 k) (hMF k) hcv0 n h
    · have hnl : n = V.l := le_antisymm hn h
      subst hnl
      have h1 := coeff_l_frob (hMI k) (hM0 k) (hMF k) hcv0
      simp only [hc, if_pos] at h1
      have h2 := hV1 k
      rw [← hMdef] at h2
      have h3 := mm_add h1 h2
      rwa [sub_add_cancel] at h3
  have hA4 : V.MM (PowerSeries.coeff V.l
      (subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M q.2)) T)) :=
    lowMM_subst (a := fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M q.2))
      (fun q => hδ0 M hM0 q.2) (fun q => hδI M hMI q.2) (fun q => hLow q.2) hTI hT0 V.l le_rfl
  rw [← hv'def]
  obtain ⟨A1, hA1d⟩ : ∃ A1, A1 = PowerSeries.coeff V.l
    (subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (e q.2)) (zl v Y.u1)) := ⟨_, rfl⟩
  obtain ⟨A3, hA3d⟩ : ∃ A3, A3 = PowerSeries.coeff V.l (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (zl v' Y.u1)) :=
    ⟨_, rfl⟩
  rw [← hA1d, ← hA3d] at k3
  rw [← hA1d] at hA1
  rw [← hA3d] at hA3
  have efin : Y.aLin (linAct e u) v - Y.aLin u v' =
      (A3 - Y.aLin u v') - (A1 - Y.aLin (linAct e u) v) + (A1 - A3) := by ring
  have e13 : A1 - A3 = PowerSeries.coeff V.l
      (subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M q.2)) T) -
        (V.l : C) * PowerSeries.coeff V.l (subst (fun q : Fin 1 × Fin dd => γ0 q.2) T) := by
    linear_combination k3
  rw [efin, e13]
  exact mm_add (mm_sub hA3 hA1) (mm_sub hA4 hA2)

end Formalism.L2.FormalSeriesBounds
end
end
