import Formalism.PeriodIntegrals.OrbAddOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetRen
import Formalism.PeriodIntegrals.OrbJetBase
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.ExpSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetMul

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries

variable (p : ℕ) [Fact p.Prime]

def Lp : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ∑ e ∈ Finset.range (n + 1), if n = (p ^ 2) ^ e then ((p : ℂ_[p]) ^ e)⁻¹ else 0

theorem Lp_const : PowerSeries.constantCoeff (Lp p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Lp]

theorem Lp_one : PowerSeries.coeff 1 (Lp p) = 1 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h : (1 : ℕ) ≠ (p ^ 2) ^ 1 := by
    rw [pow_one]; exact (Nat.one_lt_pow two_ne_zero hp).ne
  simp [Lp, Finset.sum_range_succ]
  intro h'
  have := Nat.one_lt_pow two_ne_zero hp
  omega

instance Lp_inv : Invertible (PowerSeries.coeff 1 (Lp p)) :=
  invertibleOfNonzero (by rw [Lp_one]; exact one_ne_zero)

def Ep : PowerSeries ℂ_[p] := PowerSeries.substInv (Lp p)

theorem Ep_const : PowerSeries.constantCoeff (Ep p) = 0 := PowerSeries.constantCoeff_substInv _

theorem Ep_Lp : PowerSeries.subst (Lp p) (Ep p) = PowerSeries.X :=
  PowerSeries.subst_substInv_left _ (Lp_const p)

theorem Lp_Ep : PowerSeries.subst (Ep p) (Lp p) = PowerSeries.X :=
  PowerSeries.subst_substInv_right _ (Lp_const p)

theorem hs_Lp : PowerSeries.HasSubst (Lp p) := PowerSeries.HasSubst.of_constantCoeff_zero' (Lp_const p)
theorem hs_Ep : PowerSeries.HasSubst (Ep p) := PowerSeries.HasSubst.of_constantCoeff_zero' (Ep_const p)

variable {τ : Type*}

theorem cc_psubst (g : MvPowerSeries τ ℂ_[p]) (hg : constantCoeff g = 0) (f : PowerSeries ℂ_[p])
    (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (PowerSeries.subst g f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hg f hf

def phiA (c : ℂ_[p]) : τ → MvPowerSeries τ ℂ_[p] :=
  fun v => C c * PowerSeries.subst (X v) (Lp p)

def psiA (c : ℂ_[p]) : τ → MvPowerSeries τ ℂ_[p] :=
  fun v => PowerSeries.subst (C c⁻¹ * X v) (Ep p)

variable [Finite τ]

theorem hs_phiA (c : ℂ_[p]) : HasSubst (phiA p c (τ := τ)) :=
  hasSubst_of_constantCoeff_zero fun v => by
    simp only [phiA, map_mul, cc_psubst p _ (constantCoeff_X v) _ (Lp_const p), mul_zero]

theorem hs_psiA (c : ℂ_[p]) : HasSubst (psiA p c (τ := τ)) :=
  hasSubst_of_constantCoeff_zero fun v => cc_psubst p _ (by simp) _ (Ep_const p)

theorem phi_psi_X (c : ℂ_[p]) (hc : c ≠ 0) (v : τ) :
    subst (phiA p c) (psiA p c v) = X v := by
  have hX : PowerSeries.HasSubst (C c⁻¹ * X v : MvPowerSeries τ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [psiA, PI.OrbShared.ExpSum.subst_psubst (hs_phiA p c) hX, subst_mul (hs_phiA p c), subst_X (hs_phiA p c)]
  have hC : subst (phiA p c) (C c⁻¹ : MvPowerSeries τ ℂ_[p]) = C c⁻¹ := by
    exact subst_C _
  rw [hC, phiA, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul,
    ← PowerSeries.subst_comp_subst_apply (hs_Lp p) (PowerSeries.HasSubst.X v), Ep_Lp,
    PowerSeries.subst_X (PowerSeries.HasSubst.X v)]

theorem psi_phi_X (c : ℂ_[p]) (hc : c ≠ 0) (v : τ) :
    subst (psiA p c) (phiA p c v) = X v := by
  have hX : PowerSeries.HasSubst (X v : MvPowerSeries τ ℂ_[p]) := PowerSeries.HasSubst.X v
  have hX' : PowerSeries.HasSubst (C c⁻¹ * X v : MvPowerSeries τ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hC : subst (psiA p c) (C c : MvPowerSeries τ ℂ_[p]) = C c := by
    exact subst_C _
  rw [phiA, subst_mul (hs_psiA p c), hC, PI.OrbShared.ExpSum.subst_psubst (hs_psiA p c) hX,
    subst_X (hs_psiA p c), psiA, ← PowerSeries.subst_comp_subst_apply (hs_Ep p) hX', Lp_Ep,
    PowerSeries.subst_X hX', ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]

theorem phi_psi (c : ℂ_[p]) (hc : c ≠ 0) (F : MvPowerSeries τ ℂ_[p]) :
    subst (phiA p c) (subst (psiA p c) F) = F := by
  rw [subst_comp_subst_apply (hs_psiA p c) (hs_phiA p c)]
  simp only [phi_psi_X p c hc]
  exact congrFun subst_self F

theorem psi_phi (c : ℂ_[p]) (hc : c ≠ 0) (F : MvPowerSeries τ ℂ_[p]) :
    subst (psiA p c) (subst (phiA p c) F) = F := by
  rw [subst_comp_subst_apply (hs_phiA p c) (hs_psiA p c)]
  simp only [psi_phi_X p c hc]
  exact congrFun subst_self F

omit [Finite τ] in
theorem coeff_X_Lp (v : τ) (m : τ →₀ ℕ) :
    coeff m (PowerSeries.subst (X v : MvPowerSeries τ ℂ_[p]) (Lp p)) =
      ∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
        if m = Finsupp.single v ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0 := by
  by_cases h : ∃ n, m = Finsupp.single v n
  · obtain ⟨n, rfl⟩ := h
    rw [PowerSeries.coeff_subst_single, if_pos (by simp)]
    have hT : Formalism.BasicNotions.JetTdeg (Finsupp.single v n) = n := by
      simp [Formalism.BasicNotions.JetTdeg, Finsupp.sum_single_index]
    simp only [Finsupp.single_eq_same, Lp, PowerSeries.coeff_mk, hT]
    refine Finset.sum_congr rfl fun e _ => ?_
    have : Finsupp.single v n = Finsupp.single v ((p ^ 2) ^ e) ↔ n = (p ^ 2) ^ e :=
      ⟨fun h => by simpa using congrArg (fun f => f v) h, fun h => h ▸ rfl⟩
    simp only [this]
  · rw [PowerSeries.coeff_subst_single, if_neg (fun h' => h ⟨_, h'⟩)]
    symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨_, h'⟩

theorem jetLogG_one {β : Type*} (v : ZMod 1 × β) :
    Formalism.BasicNotions.jetLogG p 1 v = PowerSeries.subst (X v : MvPowerSeries (ZMod 1 × β) ℂ_[p]) (Lp p) := by
  ext m
  rw [coeff_X_Lp]
  have h : ∀ e : ℕ, ((v.1 - 2 * (e : ZMod 1), v.2) : ZMod 1 × β) = v :=
    fun e => Prod.ext (Subsingleton.elim _ _) rfl
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod 1), v.2) ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = _
  simp only [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem logPl_one (D : Formalism.BasicNotions.D7) (hn : Formalism.MainNotions.G.nP D p = 1) {β : Type} (v : Pl D × β) :
    logPl D p v = PowerSeries.subst (X v : MvPowerSeries (Pl D × β) ℂ_[p]) (Lp p) := by
  ext m
  rw [coeff_X_Lp]
  have h : ∀ e : ℕ, ((backPl D p v.1 (2 * e), v.2) : Pl D × β) = v := by
    intro e
    refine Prod.ext ?_ rfl
    simp [backPl, hn, Formalism.BasicNotions.posPl_zero]
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
    if m = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = _
  simp only [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> first | rfl | (exfalso; tauto)

end PI.OrbJet.AO

end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]
variable {σ τ υ : Type*}

theorem rename_subst' (e : σ ↪ τ) {a : υ → MvPowerSeries σ ℂ_[p]} (ha : HasSubst a)
    (f : MvPowerSeries υ ℂ_[p]) :
    rename e (subst a f) = subst (fun s => rename e (a s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp e)]
  simp only [rename_eq_subst]

theorem subst_rename' (e : σ ↪ τ) {b : τ → MvPowerSeries υ ℂ_[p]} (hb : HasSubst b)
    (f : MvPowerSeries σ ℂ_[p]) :
    subst b (rename e f) = subst (fun w => b (e w)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp e) hb]
  simp only [Function.comp_apply, subst_X hb]

theorem rename_psubst (e : σ ↪ τ) {g : MvPowerSeries σ ℂ_[p]} (hg : PowerSeries.HasSubst g)
    (f : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst g f) = PowerSeries.subst (rename e g) f := by
  rw [PowerSeries.subst, rename_subst' e hg.const]
  rfl



end PI.OrbJet.AO

end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.OJ

section Lin

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 : ℕ} (l : ℕ) [Fact l.Prime]

theorem applyTerm_addT (T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    applyTerm l (T1 + T2) μ c = applyTerm l T1 μ c + applyTerm l T2 μ c := by
  simp [applyTerm, mul_add, map_add]

theorem applyAt0_addT (T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (T1 + T2) P = applyAt0 N0 N1 l T1 P + applyAt0 N0 N1 l T2 P := by
  simp only [applyAt0_eq_sum, applyTerm_addT, Finset.sum_add_distrib]

theorem applyAt0_zeroT (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (0 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) P = 0 := by
  simp [applyAt0_eq_sum, applyTerm]

theorem applyAt0_smulT (a : ℂ_[l]) (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (a • T) P = a • applyAt0 N0 N1 l T P := by
  simp only [applyAt0_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [applyTerm, MvPolynomial.smul_monomial, map_smul, smul_eq_mul]
  congr 1
  ring

theorem applyAt0_sumT {ι : Type*} (s : Finset ι) (T : ι → MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (∑ i ∈ s, T i) P = ∑ i ∈ s, applyAt0 N0 N1 l (T i) P := by
  induction s using Finset.induction_on with
  | empty => simp [applyAt0_zeroT]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, applyAt0_addT, ih]

theorem degree_snd_le (μ : XZ Lt N0 N1 →₀ ℕ) :
    Finsupp.degree (Finsupp.sumFinsuppEquivProdFinsupp μ).2 ≤ Finsupp.degree μ := by
  rw [Finsupp.degree_apply, Finsupp.degree_apply]
  calc ∑ j ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support, (Finsupp.sumFinsuppEquivProdFinsupp μ).2 j
      = ∑ j ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support, μ (Sum.inr j) := by
        simp [Finsupp.snd_sumFinsuppEquivProdFinsupp]
    _ = ∑ i ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support.map Function.Embedding.inr, μ i := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ i ∈ μ.support, μ i := by
        refine Finset.sum_le_sum_of_subset ?_
        intro i hi
        simp only [Finset.mem_map, Finsupp.mem_support_iff, Finsupp.snd_sumFinsuppEquivProdFinsupp] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        simpa using hj

theorem applyAt0_eq_zero_of_order (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ)
    (h : (P.totalDegree : ℕ∞) < T.order) : applyAt0 N0 N1 l T P = 0 := by
  rw [applyAt0_eq_sum]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hd : Finsupp.degree (Finsupp.sumFinsuppEquivProdFinsupp μ).2 ≤ P.totalDegree :=
    (degree_snd_le μ).trans (by rw [Finsupp.degree_apply]; exact MvPolynomial.le_totalDegree hμ)
  have : MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 T = 0 :=
    MvPowerSeries.coeff_of_lt_order (lt_of_le_of_lt (by exact_mod_cast hd) h)
  unfold applyTerm
  rw [this, mul_zero, map_zero]

end Lin

section Trunc

variable {σ : Type*} [Finite σ] {K : Type*} [Field K]

theorem trunc_split (n : ℕ) (U : MvPowerSeries σ K) :
    ∃ (S : Finset (σ →₀ ℕ)) (V : MvPowerSeries σ K),
      U = (∑ k ∈ S, MvPowerSeries.monomial k (MvPowerSeries.coeff k U)) + V ∧ (n : ℕ∞) < V.order := by
  let Q := MvPowerSeries.truncTotal (n + 1) U
  refine ⟨Q.support, U - (Q : MvPowerSeries σ K), ?_, ?_⟩
  · have hQ : (Q : MvPowerSeries σ K) = ∑ k ∈ Q.support, MvPowerSeries.monomial k (MvPowerSeries.coeff k U) := by
      conv_lhs => rw [Q.as_sum]
      rw [show ((∑ k ∈ Q.support, MvPolynomial.monomial k (MvPolynomial.coeff k Q) : MvPolynomial σ K) :
          MvPowerSeries σ K) = ∑ k ∈ Q.support, ((MvPolynomial.monomial k (MvPolynomial.coeff k Q) :
          MvPolynomial σ K) : MvPowerSeries σ K) from map_sum (MvPolynomial.coeToMvPowerSeries.ringHom) _ _]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [MvPolynomial.coe_monomial]
      congr 1
      rw [MvPowerSeries.coeff_truncTotal_eq_ite]
      split_ifs with h
      · rfl
      · exact absurd hk (by rw [MvPolynomial.mem_support_iff, MvPowerSeries.coeff_truncTotal_eq_ite, if_neg h]; simp)
    rw [← hQ]; ring
  · have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ (U - (Q : MvPowerSeries σ K)).order := by
      refine MvPowerSeries.le_order fun d hd => ?_
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite, if_pos, sub_self]
      exact_mod_cast hd
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) h1

end Trunc

end PI.OrbJet.OJ

end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

def ptE (D : D7) (z : Pl D) : ZMod 1 ↪ Pl D := ⟨fun _ => z, fun a b _ => Subsingleton.elim a b⟩

@[simp] theorem ptE_apply (D : D7) (z : Pl D) (s : ZMod 1) : ptE D z s = z := rfl

def gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) : ZMod 2 → MvPowerSeries τ ℂ_[p] :=
  fun s => if s = 0 then (X v : MvPowerSeries τ ℂ_[p]) else C ep * X v

theorem hs_gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) : HasSubst (gSub ep v) := by
  have h0 : ∀ s, constantCoeff (gSub (p := p) ep v s) = 0 := fun s => by
    unfold gSub
    split_ifs <;> simp
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  | exact ⟨fun s => by rw [h0 s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩

theorem cc_gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : constantCoeff be = 0) : constantCoeff (subst (gSub ep v) be) = 0 := by
  have h0 : ∀ s, constantCoeff (gSub (p := p) ep v s) = 0 := fun s => by
    unfold gSub
    split_ifs <;> simp
  first
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_gSub ep v) h0 hbe
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_gSub ep v) hbe h0
  | (rw [MvPowerSeries.constantCoeff_subst (hs_gSub ep v)]
     apply finsum_eq_zero_of_forall_eq_zero
     intro d
     by_cases hd : d = 0
     · subst hd
       simp [hbe]
     · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 hd
       simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
       rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 hs)]
       · simp
       · simp [h0 s, zero_pow hs])

theorem constantCoeff_zero_of_bound_two (be : MvPowerSeries (ZMod 2) ℂ_[p]) (h : OJ.B3 p 2 be) : constantCoeff be = 0 := by
  by_contra hne
  have h0 := h 0 (by simpa using hne)
  simp [bideg] at h0

def f1 (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  (sg / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub ep ((0 : ZMod 1), a, b)) be

def fAll (D : D7) (N0 N1 : ℕ) (ep sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub (ep z) (z, a, b)) (be z)

theorem constantCoeff_jet_series (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) (hbe : constantCoeff be = 0) :
    constantCoeff (f1 N0 N1 ep sg be) = 0 := by
  simp [f1, cc_gSub _ _ _ hbe]

theorem rename_jet_series (D : D7) (z : Pl D) (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (f1 N0 N1 ep sg be) =
      (sg / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub ep (z, a, b)) be := by
  simp only [f1, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [rename_subst' _ (hs_gSub _ _)]
  congr 1
  funext s
  unfold gSub
  split_ifs
  · rw [rename_X]
    rfl
  · simp [rename_X]
    left
    rfl

def Y1 (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  subst (jetLogG p 1 (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (f1 N0 N1 ep sg be))

def T1 (N0 N1 : ℕ) (c ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) (j : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  subst (psiA p c) (monomial j 1 * Y1 N0 N1 ep sg be)

theorem jetLog_eq_phiA (N0 N1 : ℕ) (c : ℂ_[p]) :
    (fun v : ZMod 1 × Fin N0 × Fin N1 => C c * jetLogG p 1 v) = phiA p c := by
  funext v
  simp [phiA, jetLogG_one]

theorem subst_log_jet_monomial (N0 N1 : ℕ) (c ep sg : ℂ_[p]) (hc : c ≠ 0) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (j : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ) :
    subst (fun v : ZMod 1 × Fin N0 × Fin N1 => C c * jetLogG p 1 v) (T1 N0 N1 c ep sg be j) =
      monomial j 1 * Y1 N0 N1 ep sg be := by
  rw [jetLog_eq_phiA]
  unfold T1
  exact phi_psi (p := p) c hc _

end PI.OrbJet.AO

end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

theorem norm_coeff_monomial_one {τ : Type*} (j m : τ →₀ ℕ) :
    ‖coeff m (monomial j (1 : ℂ_[p]))‖ ≤ 1 := by
  rw [MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

theorem admissible_jet_term {D : D7} (E : Ent D) (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (c : ℂ_[p])
    (hc : ‖c‖ = 1) (ep sg : ℂ_[p]) (hep : ‖ep‖ = 1) (hsg : sg = 1 ∨ sg = -1) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : OJ.B1 p 2 be ∧ OJ.B2 p 2 be ∧ OJ.B3 p 2 be ∧ OJ.B4 p 2 be)
    (j : ZMod 1 × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ) :
    (oneLoc E p h5 u i z (T1 (D.R.N i) (D.R.N (i + 1)) c ep sg be j)).AdmB := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  exact ⟨c, hc, be, ⟨ep, hep, sg, hsg, monomial j 1, fun m => norm_coeff_monomial_one j m,
    subst_log_jet_monomial _ _ c ep sg hc0 be j⟩, hbe⟩

def kz (D : D7) {N0 N1 : ℕ} (z : Pl D) (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun w => k (z, w.2)

theorem sum_mapDomain_kz (D : D7) {N0 N1 : ℕ} (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    ∑ z, Finsupp.mapDomain (pEmb (ptE D z) (Fin N0 × Fin N1)) (kz D z k) = k := by
  ext ⟨z0, w⟩
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single z0]
  · have h : ((z0, w) : Pl D × Fin N0 × Fin N1) =
        pEmb (ptE D z0) (Fin N0 × Fin N1) ((0 : ZMod 1), w) := rfl
    rw [h, Finsupp.mapDomain_apply (pEmb (ptE D z0) _).injective]
    rfl
  · intro z _ hz
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨a, w'⟩, h⟩
    rw [pEmb_apply] at h
    exact hz (congrArg Prod.fst h)
  · intro h
    exact absurd (Finset.mem_univ z0) h

theorem hs_logPl (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) : HasSubst (logPl D p (β := Fin N0 × Fin N1)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show logPl D p v 0 = 0
  simp only [logPl]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  exact fun h => (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero))
    (Finsupp.single_eq_zero.1 h.symm)

theorem hasSubst_log_jet (N0 N1 : ℕ) : HasSubst (jetLogG p 1 (β := Fin N0 × Fin N1)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show jetLogG p 1 v 0 = 0
  simp only [jetLogG]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  exact fun h => (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero))
    (Finsupp.single_eq_zero.1 h.symm)

theorem prod_rename_exp_jet_series (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) (ep sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hcc : ∀ z, constantCoeff (be z) = 0) :
    ∏ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z)) =
      subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (fAll D N0 N1 ep sg be)) := by
  classical
  have hE : ∀ f : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      OJ.expS ℂ_[p] f = PI.OrbShared.ExpSum.eS f := fun f => rfl
  set g : Pl D → MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] := fun z =>
    (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub (ep z) (z, a, b)) (be z) with hg
  have hgc : ∀ z, constantCoeff (g z) = 0 := fun z => by
    simp only [hg]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul]
    simp only [map_sum, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_gSub _ _ _ (hcc z),
      Finset.sum_const_zero, smul_zero]
  have hz : ∀ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z)) =
      subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (g z)) := by
    intro z
    have hl : (fun v => rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (jetLogG p 1 v)) =
        fun v => logPl D p (pEmb (ptE D z) (Fin N0 × Fin N1) v) := by
      funext v
      rw [jetLogG_one, rename_psubst _ (PowerSeries.HasSubst.of_constantCoeff_zero
        (MvPowerSeries.constantCoeff_X v)), MvPowerSeries.rename_X, logPl_one p D hn]
    rw [Y1, rename_subst' _ (hasSubst_log_jet N0 N1), hl, ← subst_rename' _ (hs_logPl D hn N0 N1), OJ.expS,
      OJ.expS, rename_psubst _ (PowerSeries.HasSubst.of_constantCoeff_zero
        (constantCoeff_jet_series N0 N1 (ep z) (sg z) (be z) (hcc z))), rename_jet_series]
  rw [Finset.prod_congr rfl (fun z _ => hz z), ← MvPowerSeries.coe_substAlgHom (hs_logPl D hn N0 N1),
    ← map_prod]
  congr 1
  rw [show fAll D N0 N1 ep sg be = ∑ z, g z from rfl, hE,
    PI.OrbShared.ExpSum.eS_sum _ _ (fun z _ => hgc z)]
  rfl

private theorem prod_monomial_one_eq_monomial_sum {ι σ : Type*} (s : Finset ι) (m : ι → σ →₀ ℕ) :
    ∏ i ∈ s, (monomial (m i) (1 : ℂ_[p]) : MvPowerSeries σ ℂ_[p]) = monomial (∑ i ∈ s, m i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    first | rfl | simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem factor (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) (c : ℂ_[p]) (hc : c ≠ 0) (ep sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hcc : ∀ z, constantCoeff (be z) = 0)
    (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    subst (psiA p c) (monomial k 1 *
        subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (fAll D N0 N1 ep sg be))) =
      ∏ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (T1 N0 N1 c (ep z) (sg z) (be z) (kz D z k)) := by
  classical
  have hpsi : ∀ z (s : ZMod 1 × Fin N0 × Fin N1),
      rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (psiA p c s) =
        psiA p c (pEmb (ptE D z) (Fin N0 × Fin N1) s) := by
    intro z s
    have hh : PowerSeries.HasSubst (C c⁻¹ * X s : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    simp only [psiA]
    rw [rename_psubst _ hh, map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
  have hT : ∀ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (T1 N0 N1 c (ep z) (sg z) (be z) (kz D z k)) =
      subst (psiA p c) (monomial (Finsupp.mapDomain (pEmb (ptE D z) (Fin N0 × Fin N1)) (kz D z k)) 1 *
        rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z))) := by
    intro z
    rw [T1, rename_subst' _ (hs_psiA p c), funext (hpsi z), ← subst_rename' _ (hs_psiA p c), map_mul,
      MvPowerSeries.rename_monomial]
  rw [Finset.prod_congr rfl (fun z _ => hT z), ← MvPowerSeries.coe_substAlgHom (hs_psiA p c), ← map_prod,
    Finset.prod_mul_distrib, prod_rename_exp_jet_series D hn N0 N1 ep sg be hcc, prod_monomial_one_eq_monomial_sum,
    sum_mapDomain_kz]

end PI.OrbJet.AO

end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

theorem bound_place {D : D7} (E : Ent D) (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (β : Pl D → ℝ)
    (hβ : ∀ z, OneGe E p h5 u i z (β z)) (c : ℂ_[p]) (hc : ‖c‖ = 1) (ep sg : Pl D → ℂ_[p])
    (hep : ∀ z, ‖ep z‖ = 1) (hsg : ∀ z, sg z = 1 ∨ sg z = -1) (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : ∀ z, OJ.B1 p 2 (be z) ∧ OJ.B2 p 2 (be z) ∧ OJ.B3 p 2 (be z) ∧ OJ.B4 p 2 (be z))
    (I : ColChoice (D.R.N (i + 1)) (E.nu u i)) (k : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ)
    (z : Pl D) (m' : Pl D × ℕ × Fin (D.R.N i) →₀ ℕ) :
    ‖MvPolynomial.coeff m' (applyAt0 (D.R.N i) (D.R.N (i + 1)) p
      (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (T1 (D.R.N i) (D.R.N (i + 1)) c (ep z) (sg z) (be z) (kz D z k)))
      (∏ c' : Fin ((E.nu u i z).rowLen 0), minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')))‖
      ≤ (p : ℝ) ^ (-β z) := by
  have hadm := admissible_jet_term E h5 u i z c hc (ep z) (sg z) (hep z) (hsg z) (be z) (hbe z) (kz D z k)
  have hK := hβ z _ hadm
  have hP : MvPolynomial.rename (xzMap (N0 := D.R.N i) (N1 := D.R.N (i + 1)) (ptE D z))
      (Gxz (D.R.N i) (D.R.N (i + 1)) (fun _ : ZMod 1 => E.nu u i z) (fun _ c' => I z c')) =
      ∏ c' : Fin ((E.nu u i z).rowLen 0),
        minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c') := by
    simp only [Gxz, map_prod, rename_minorXZ, ptE_apply, Finset.prod_const, Finset.card_univ,
      ZMod.card, pow_one]
  rw [← hP, applyAt0_rename]
  exact norm_coeff_rename_le _ _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun m => hK _ m) m'

theorem order_psi_gt (c : ℂ_[p]) {τ : Type*} [Finite τ] (n : ℕ) (V X : MvPowerSeries τ ℂ_[p])
    (hV : (n : ℕ∞) < V.order) : (n : ℕ∞) < (subst (psiA p c) (V * X)).order := by
  have hs := hs_psiA (p := p) c (τ := τ)
  have h1 : (1 : ℕ∞) ≤ ⨅ v : τ, (psiA p c v).order := by
    refine le_iInf fun v => ?_
    refine MvPowerSeries.le_order fun d hd => ?_
    have hd1 : Finsupp.degree d < 1 := by exact_mod_cast hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd1)
    rw [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact cc_psubst (p := p) _ (by simp) _ (Ep_const (p := p))
  have h2 : V.order ≤ (V * X).order :=
    le_trans le_self_add MvPowerSeries.le_order_mul
  calc (n : ℕ∞) < V.order := hV
    _ ≤ (V * X).order := h2
    _ = 1 * (V * X).order := (one_mul _).symm
    _ ≤ (⨅ v : τ, (psiA p c v).order) * (V * X).order :=
      mul_le_mul_of_nonneg_right h1 (by simp)
    _ ≤ (subst (psiA p c) (V * X)).order := MvPowerSeries.le_order_subst hs _

theorem orbitsAddAtConjugate (D : D7) (E : Ent D) : OrbitsAddAtConjugate E := by
  intro p _ h5 hn u i _ β hβ Th hB I m
  obtain ⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩ := hB
  have hep0' : ep0 ≠ 0 := by
    rintro rfl
    simp at hep0
  have hcc : ∀ z, constantCoeff (be z) = 0 := fun z => constantCoeff_zero_of_bound_two (be z) (hbe z).2.2.1
  have hphi : (fun v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) =>
      MvPowerSeries.C ep0 * logPl D p v) = phiA p ep0 := by
    funext v
    rw [logPl_one (p := p) D hn v]
    rfl
  have hEq' : subst (phiA p ep0) Th =
      U * subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be)) := by
    rw [← hphi]
    exact hEq
  have hTh : Th = subst (psiA p ep0)
      (U * subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be))) := by
    rw [← hEq', psi_phi (p := p) ep0 hep0' Th]
  have hdisj : ((Finset.univ : Finset (Pl D)) : Set (Pl D)).PairwiseDisjoint
      (fun z : Pl D => ({z} : Set (Pl D))) := by
    intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  have hprod : ∀ (k : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ)
      (m' : Pl D × ℕ × Fin (D.R.N i) →₀ ℕ),
      ‖MvPolynomial.coeff m' (applyAt0 (D.R.N i) (D.R.N (i + 1)) p
        (∏ z, rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
          (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
        (Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I))‖ ≤ (p : ℝ) ^ (-∑ z, β z) := by
    intro k m'
    have hT : ∀ z ∈ (Finset.univ : Finset (Pl D)),
        SerIn {v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) | v.1 ∈ ({z} : Set (Pl D))}
          (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
            (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k))) := by
      intro z _
      refine SerIn.mono ?_ (serIn_rename (ptE D z) _)
      rintro v ⟨s, hs⟩
      rw [ptE_apply] at hs
      exact hs.symm
    have hP : ∀ z ∈ (Finset.univ : Finset (Pl D)),
        (∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) ∈
        MvPolynomial.supported ℤ (xzLetter ⁻¹' ({z} : Set (Pl D))) := by
      intro z _
      exact Subalgebra.prod_mem _ fun c' _ => minorXZ_supported _ _ _
    have hG : Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I = ∏ z ∈ (Finset.univ : Finset (Pl D)),
        ∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c') := rfl
    have happ : applyAt0 (D.R.N i) (D.R.N (i + 1)) p
        (∏ z, rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
          (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
        (∏ z ∈ (Finset.univ : Finset (Pl D)), ∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) =
        ∏ z ∈ (Finset.univ : Finset (Pl D)), applyAt0 (D.R.N i) (D.R.N (i + 1)) p
          (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
            (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
          (∏ c' : Fin ((E.nu u i z).rowLen 0),
            minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) :=
      applyAt0_prod (l := p) _ _ hdisj _ _ hT hP
    rw [hG, happ, ← Finset.sum_neg_distrib,
      Real.rpow_sum_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos)]
    refine norm_coeff_prod_le _ ?_ ?_ m'
    · intro z _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro z _ m''
      exact bound_place E h5 u i β hβ ep0 hep0 ep sg hep hsg be hbe I k z m''
  have hfac := factor D hn (D.R.N i) (D.R.N (i + 1)) ep0 hep0' ep sg be hcc
  generalize subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
      (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be)) = L at hTh hfac
  obtain ⟨Sk, V, hUV, hV⟩ := trunc_split
    (Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I).totalDegree U
  have hs := hs_psiA (p := p) ep0 (τ := Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)))
  have hmon : ∀ k, MvPowerSeries.monomial k (MvPowerSeries.coeff k U) * L =
      MvPowerSeries.coeff k U • (MvPowerSeries.monomial k (1 : ℂ_[p]) * L) := by
    intro k
    rw [← smul_mul_assoc]
    congr 1
    have h := map_smul (MvPowerSeries.monomial k :
      ℂ_[p] →ₗ[ℂ_[p]] MvPowerSeries (Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
      (MvPowerSeries.coeff k U) (1 : ℂ_[p])
    rw [smul_eq_mul, mul_one] at h
    exact h
  have hsplit : subst (psiA p ep0) (U * L) =
      ∑ k ∈ Sk, MvPowerSeries.coeff k U •
          subst (psiA p ep0) (MvPowerSeries.monomial k (1 : ℂ_[p]) * L)
        + subst (psiA p ep0) (V * L) := by
    conv_lhs => rw [hUV]
    rw [add_mul, Finset.sum_mul, ← MvPowerSeries.coe_substAlgHom (R := ℂ_[p]) hs, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmon k, map_smul]
  have hord := order_psi_gt ep0 _ V L hV
  rw [hTh, hsplit, applyAt0_addT, applyAt0_sumT, applyAt0_eq_zero_of_order (h := hord), add_zero]
  simp only [applyAt0_smulT, hfac]
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) fun k _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
  calc _ ≤ 1 * (p : ℝ) ^ (-∑ z, β z) := mul_le_mul (hU k) (hprod k m) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end PI.OrbJet.AO

end
end
