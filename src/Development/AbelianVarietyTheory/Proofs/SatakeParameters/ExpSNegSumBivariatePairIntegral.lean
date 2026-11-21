import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetZ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

section
noncomputable section

namespace GlobalTheory.SubringSeries

open MvPowerSeries Formalism.FG.InjVAux

variable {K : Type} [Field K] {κ : Type}

def intS (A : Subring K) (κ : Type) : Subring (MvPowerSeries κ K) where
  carrier := {F | ∀ n, coeff n F ∈ A}
  mul_mem' := by
    classical
    intro a b ha hb n
    rw [coeff_mul]
    exact A.sum_mem fun x _ => A.mul_mem (ha _) (hb _)
  one_mem' := by
    classical
    intro n
    rw [coeff_one]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  add_mem' := fun ha hb n => by rw [map_add]; exact A.add_mem (ha n) (hb n)
  zero_mem' := fun n => by rw [map_zero]; exact A.zero_mem
  neg_mem' := fun ha n => by rw [map_neg]; exact A.neg_mem (ha n)

variable {A : Subring K}

theorem X_mem (k : κ) : (X k : MvPowerSeries κ K) ∈ intS A κ := by
  classical
  intro n
  rw [coeff_X]
  split_ifs
  exacts [A.one_mem, A.zero_mem]

theorem finsum_mem' {ι : Type} {f : ι → K} (h : ∀ i, f i ∈ A) : ∑ᶠ i, f i ∈ A :=
  finsum_induction (fun x => x ∈ A) A.zero_mem (fun _ _ => A.add_mem) h

theorem subst_mem {ι : Type} {a : ι → MvPowerSeries κ K} (ha : HasSubst a) (hA : ∀ i, a i ∈ intS A κ)
    {E : MvPowerSeries ι K} (hE : E ∈ intS A ι) : subst a E ∈ intS A κ := by
  intro n
  rw [coeff_subst ha]
  refine finsum_mem' fun d => ?_
  rw [smul_eq_mul]
  refine A.mul_mem (hE d) (((intS A κ).prod_mem fun i _ => (intS A κ).pow_mem (hA i) _) n)

def frob (p : ℕ) (hp : p ≠ 0) (σ : K →+* K) (κ : Type) : MvPowerSeries κ K →+* MvPowerSeries κ K :=
  (expand p hp : MvPowerSeries κ K →ₐ[K] MvPowerSeries κ K).toRingHom.comp (map σ)

section Frob

variable {p : ℕ} {hp : p ≠ 0} {σ : K →+* K}

theorem frob_apply (F : MvPowerSeries κ K) : frob p hp σ κ F = expand p hp (map σ F) := rfl

theorem frob_X (k : κ) : frob p hp σ κ (X k) = X k ^ p := by
  rw [frob_apply, map_X, expand_X]

theorem constantCoeff_frob {F : MvPowerSeries κ K} (h : constantCoeff F = 0) :
    constantCoeff (frob p hp σ κ F) = 0 := by
  rw [frob_apply, constantCoeff_expand, constantCoeff_map, h, map_zero]

theorem frob_subst {ι : Type} [Finite ι] {a : ι → MvPowerSeries κ K} (ha : ∀ i, constantCoeff (a i) = 0)
    (E : MvPowerSeries ι K) :
    frob p hp σ κ (subst a E) = subst (fun i => frob p hp σ κ (a i)) (map σ E) := by
  rw [frob_apply, map_subst (hasSubst_of_constantCoeff_zero ha), expand_subst]
  · rfl
  · exact hasSubst_of_constantCoeff_zero fun i => by rw [constantCoeff_map, ha, map_zero]

theorem frob_psubst {a : MvPowerSeries κ K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    frob p hp σ κ (f.subst a) = (PowerSeries.map σ f).subst (frob p hp σ κ a) :=
  frob_subst (ι := Unit) (a := fun _ => a) (fun _ => ha) f

end Frob

theorem hasOrd_subst_sub {f : PowerSeries K} (h1 : PowerSeries.coeff 1 f = 1) {a b : MvPowerSeries κ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {N : ℕ} (h : HasOrd (N + 1) (a - b)) :
    HasOrd (N + 2) (f.subst a - f.subst b - (a - b)) := by
  have haS := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hbS := PowerSeries.HasSubst.of_constantCoeff_zero hb
  have hg : Good N 1 a b := ⟨hasOrd_one_of_cc ha, hasOrd_one_of_cc hb, h⟩
  intro n hn
  rw [map_sub, map_sub, PowerSeries.coeff_subst haS, PowerSeries.coeff_subst hbS,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite haS f n) (PowerSeries.coeff_subst_finite hbS f n),
    finsum_eq_single _ 1]
  · simp [h1]
  · intro e he
    rw [← smul_sub, ← map_sub]
    rcases Nat.eq_zero_or_pos e with rfl | h0
    · simp
    · rw [(hg.pow e).2.2 n (by omega), smul_zero]

theorem mem_of_subst_mem {f : PowerSeries K} (h1 : PowerSeries.coeff 1 f = 1)
    (T : AddSubgroup (MvPowerSeries κ K))
    (hT : ∀ P ∈ intS A κ, constantCoeff P = 0 → f.subst P ∈ T)
    (hlow : ∀ D ∈ T, ∀ N, HasOrd (N + 1) D → ∀ n : κ →₀ ℕ, n.degree = N + 1 → coeff n D ∈ A)
    {t : MvPowerSeries κ K} (ht : constantCoeff t = 0) (hf : f.subst t ∈ T) : t ∈ intS A κ := by
  have main : ∀ N, ∀ n : κ →₀ ℕ, n.degree < N + 1 → coeff n t ∈ A := by
    intro N
    induction N with
    | zero => intro n hn; rw [hasOrd_one_of_cc ht n hn]; exact A.zero_mem
    | succ N ih =>
      intro n hn
      rcases (Nat.lt_succ_iff_lt_or_eq.1 hn) with hlt | heq
      · exact ih n hlt
      obtain ⟨P, hP⟩ : ∃ P : MvPowerSeries κ K, ∀ m, coeff m P = if m.degree < N + 1 then coeff m t else 0 :=
        ⟨fun m => if m.degree < N + 1 then coeff m t else 0, fun _ => rfl⟩
      have hPA : P ∈ intS A κ := fun m => by
        rw [hP]; split_ifs with h
        exacts [ih m h, A.zero_mem]
      have hP0 : constantCoeff P = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, hP, coeff_zero_eq_constantCoeff_apply, ht, ite_self]
      have ho : HasOrd (N + 1) (t - P) := fun m hm => by rw [map_sub, hP, if_pos hm, sub_self]
      have h2 := hasOrd_subst_sub h1 ht hP0 ho
      have h3 : HasOrd (N + 1) (f.subst t - f.subst P) := by
        have := (h2.mono (Nat.le_succ _)).add ho
        rwa [sub_add_cancel] at this
      have h4 := hlow _ (T.sub_mem hf (hT P hPA hP0)) N h3 n heq
      have h5 := h2 n hn
      rw [map_sub, sub_eq_zero] at h5
      rw [h5, map_sub, hP, if_neg (by omega), sub_zero] at h4
      exact h4
  exact fun n => main n.degree n (Nat.lt_succ_self _)

end GlobalTheory.SubringSeries
end
end

section
noncomputable section

namespace GlobalTheory.ThBe0.Inhab

open MvPowerSeries Formalism.FG.InjVAux GlobalTheory.SubringSeries Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric GlobalTheory.ThBe0

variable {l : ℕ} [hl : Fact l.Prime] {κ : Type}

theorem pow_two_mul_inj {i j : ℕ} (h : l ^ (2 * i) = l ^ (2 * j)) : i = j := by
  have := Nat.pow_right_injective hl.out.two_le h
  omega

theorem coeff_logF_pow (j : ℕ) : PowerSeries.coeff (l ^ (2 * j)) (logF l) = ((l : ℂ_[l]) ^ j)⁻¹ := by
  rw [logF, PowerSeries.coeff_mk, Finset.sum_eq_single j, if_pos rfl]
  · intro i _ hi
    rw [if_neg fun h => hi (pow_two_mul_inj h).symm]
  · intro h
    exfalso
    apply h
    have := Nat.lt_pow_self (n := 2 * j) hl.out.one_lt
    simp only [Finset.mem_range]
    omega

theorem coeff_logF_cases (n : ℕ) : (PowerSeries.coeff n (logF l) = 0 ∧ ∀ j, n ≠ l ^ (2 * j)) ∨
    ∃ j, n = l ^ (2 * j) := by
  by_cases h : ∃ j, n = l ^ (2 * j)
  · exact Or.inr h
  · push Not at h
    refine Or.inl ⟨?_, h⟩
    rw [logF, PowerSeries.coeff_mk]
    exact Finset.sum_eq_zero fun j _ => if_neg (h j)

theorem coeff_one_logF : PowerSeries.coeff 1 (logF l) = 1 := by
  simpa using coeff_logF_pow (l := l) 0

theorem coeff_zero_logF : PowerSeries.coeff 0 (logF l) = 0 := by
  rcases coeff_logF_cases (l := l) 0 with h | ⟨j, h⟩
  · exact h.1
  · exact absurd h.symm (pow_ne_zero _ hl.out.ne_zero)

theorem cc_logF : PowerSeries.constantCoeff (logF l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_logF]

def serM (l : ℕ) [Fact l.Prime] : MvPowerSeries (Fin 2) ℂ_[l] :=
  fun d => if d 0 ≤ d 1 then PowerSeries.coeff (d 0) (logF l) * PowerSeries.coeff (d 1) (logF l) else 0

theorem hasSubst_pair_padicComplex_of_constantCoeff_zero {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (fun i : Fin 2 => if i = 0 then x else y) :=
  hasSubst_of_constantCoeff_zero fun i => by split_ifs <;> assumption

theorem subst_powerSeriesEvalTwoGroups {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (E : MvPowerSeries (Fin 2) ℂ_[l]) : subst a (at2 E x y) = at2 E (subst a x) (subst a y) := by
  rw [at2, at2, subst_comp_subst_apply (hasSubst_pair_padicComplex_of_constantCoeff_zero hx hy) ha]
  congr 1
  funext i
  split_ifs <;> rfl

theorem subst_psubst {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (f : PowerSeries ℂ_[l]) :
    subst a (f.subst x) = f.subst (subst a x) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hx).const ha f

theorem isUnit_coeff_one : IsUnit (PowerSeries.coeff 1 (logF l)) := by
  rw [coeff_one_logF]; exact isUnit_one

def ex (u : MvPowerSeries κ ℂ_[l]) : MvPowerSeries κ ℂ_[l] :=
  ((logF l).substInvOfIsUnit isUnit_coeff_one).subst u

theorem cc_lg (k : κ) : constantCoeff (lg k : MvPowerSeries κ ℂ_[l]) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X k) _ cc_logF

def Wf (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] where
  carrier := {x | InWf x}
  mul_mem' := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨i + j, by convert (Wp l).mul_mem hi hj using 1; ring⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨i + j, ?_⟩
    convert (Wp l).add_mem ((Wp l).mul_mem ((Wp l).pow_mem (natCast_mem (Wp l) l) j) hi)
      ((Wp l).mul_mem ((Wp l).pow_mem (natCast_mem (Wp l) l) i) hj) using 1
    ring
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro a ⟨i, hi⟩
    exact ⟨i, by simpa using hi⟩

section Frob

variable {σ : ℂ_[l] →+* ℂ_[l]}

end Frob

end GlobalTheory.ThBe0.Inhab
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OrbitPair

open MvPowerSeries

theorem expS_neg_sum_bivariate_pair_integral : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} [NeZero n'] (om om' : Fin (n' / 2) → ℂ_[p]) (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ om om' s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → Formalism.MainNotions.GL3Theta.SimeqW (MvPowerSeries.subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) → ∃ V : MvPowerSeries (ZMod n') ℂ_[p], Formalism.MainNotions.GL3Theta.IntegralW V ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) := by
  intro p _ σ n' _ om om' b0 bv t x _hb0 hbv ht hx hlaS htx hsim
  classical
  have hxS : HasSubst x := hasSubst_of_constantCoeff_zero fun r => (hx r).2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have hzcc : ∀ s : ZMod n', constantCoeff (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = 0 := by
    intro s
    rw [← hlaS s]
    exact constantCoeff_subst_eq_zero htS ht (GlobalTheory.BeProps.constantCoeff_laS s)
  have hzS : HasSubst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) := hasSubst_of_constantCoeff_zero hzcc
  have hzOm : ∀ s : ZMod n', subst x (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = GlobalTheory.ThStr.laS p n' s := by
    intro s
    rw [← hlaS s, subst_comp_subst_apply htS hxS]
    have : (fun r => subst x (t r)) = (X : ZMod n' → MvPowerSeries (ZMod n') ℂ_[p]) := funext htx
    rw [this, subst_self]
    rfl
  have hFx : subst x (subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) = subst (GlobalTheory.ThStr.laS p n') bv := by
    rw [subst_comp_subst_apply hzS hxS]
    congr 1
    funext s
    exact hzOm s
  have hGx : subst x (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) =
      ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)) := by
    rw [← coe_substAlgHom hxS, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coe_substAlgHom hxS, GlobalTheory.ThBe0.Inhab.subst_powerSeriesEvalTwoGroups hxS (GlobalTheory.ThBe0.Inhab.cc_lg _) (GlobalTheory.ThBe0.Inhab.cc_lg _)]
    simp only [GlobalTheory.ThBe0.lg]
    rw [GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _), GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _),
      subst_X hxS, subst_X hxS]
  obtain ⟨hD0, hDint⟩ := hsim
  set F := subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv with hF
  set G := ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r)) with hG
  have ccL : constantCoeff (subst (GlobalTheory.ThStr.laS p n') bv) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => GlobalTheory.BeProps.constantCoeff_laS s)
      (fun s => GlobalTheory.BeProps.constantCoeff_laS s) hbv
  have ccD : constantCoeff (subst x (F - G)) = 0 := constantCoeff_subst_eq_zero hxS (fun r => (hx r).2) hD0
  have hneg : -(subst x G) = subst x (F - G) + -(subst (GlobalTheory.ThStr.laS p n') bv) := by
    rw [subst_sub hxS, hFx]
    ring
  refine ⟨subst x (Formalism.MainNotions.TaylorLogMetric.expMv (F - G)), ?_, ?_⟩
  · exact GlobalTheory.SubringSeries.subst_mem (A := Formalism.MainNotions.GL3Theta.Wp p) hxS (fun r => (hx r).1) hDint
  · rw [← hGx, hneg]
    show PowerSeries.subst _ (PowerSeries.exp ℂ_[p]) = _ * PowerSeries.subst _ (PowerSeries.exp ℂ_[p])
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ccD (by rw [map_neg, ccL, neg_zero]), GlobalTheory.BeProps.expMv_eq_subst hD0,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp x (fun r => (hx r).2) hD0]

end GlobalTheory.OrbitPair
end
end
