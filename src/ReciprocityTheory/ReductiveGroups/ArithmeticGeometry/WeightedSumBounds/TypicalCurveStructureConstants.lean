import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtSolveMapFixedIff

section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptNs (G : LogFGL v d) : ℕ → Fin d → MvPowerSeries (Fin d) C
  | 0 => 0
  | n + 1 => fun a => subst (Sum.elim (fun b => X b) (ptNs G n)) (G.F a)

theorem ptNs_const (G : LogFGL v d) : ∀ n a, constantCoeff (ptNs G n a) = 0
  | 0, a => by simp [ptNs]
  | n + 1, a => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact ptNs_const G n i
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (G.F_const a)

theorem ptNs_hasSubst (G : LogFGL v d) (n : ℕ) :
    HasSubst (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C)) (ptNs G n)) := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    cases i with
    | inl b => simp
    | inr b => exact ptNs_const G n b

theorem ptNs_int (G : LogFGL v d) : ∀ n a, ptNs G n a ∈ ptIntSer v (Fin d)
  | 0, a => by simp only [ptNs, Pi.zero_apply]; exact Subring.zero_mem _
  | n + 1, a => by
    refine ptIntSer_subst (ptNs_hasSubst G n) ?_ (G.F_int a)
    rintro (i | i)
    · exact ptIntSer_X i
    · exact ptNs_int G n i

theorem ptNs_lin (G : LogFGL v d) : ∀ (n : ℕ) (a s : Fin d),
    coeff (Finsupp.single s 1) (ptNs G n a) = if s = a then (n : C) else 0
  | 0, a, s => by simp [ptNs]
  | n + 1, a, s => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact ptNs_const G n i
    show coeff (Finsupp.single s 1) (subst _ (G.F a)) = _
    rw [pt_coeff_single_subst (ptNs_hasSubst G n) h0 (G.F_const a) s, Fintype.sum_sum_type]
    simp only [pt_F_lin, Sum.elim_inl, Sum.elim_inr, pt_coeff_single_X, ptNs_lin G n,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, add_zero, zero_add,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> push_cast <;> ring

theorem nsmulF_eq_subst (G : LogFGL v d) {ga : Fin d → PowerSeries C}
    (hga : HasSubst ga) : ∀ n, G.nsmulF n ga = fun a => subst ga (ptNs G n a)
  | 0 => by
    funext a
    simp only [LogFGL.nsmulF, ptNs, Pi.zero_apply]
    rw [← substAlgHom_apply hga, map_zero]
  | n + 1 => by
    funext a
    simp only [LogFGL.nsmulF, LogFGL.add, ptNs]
    rw [subst_comp_subst_apply (ptNs_hasSubst G n) hga, nsmulF_eq_subst G hga n]
    congr 1
    funext i
    rcases i with i | i
    · simp [subst_X hga]
    · rfl

theorem isCurve_iff_good {ga : Fin d → PowerSeries C} : IsCurve v ga ↔ PTGood v ga := by
  constructor
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mp (h a).2⟩
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mpr (h a).2⟩

private theorem valuation_natCast_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) (n : ℕ)
    (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have hcop : IsCoprime (p : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  obtain ⟨u, w, huw⟩ := hcop
  have hC : (u : C) * p + (w : C) * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) huw
  have hu : 0 ≤ v (u : C) := intCast_mem (ptIntSub v) u
  have hw : 0 ≤ v (w : C) := intCast_mem (ptIntSub v) w
  have hn0 : 0 ≤ v (n : C) := natCast_mem (ptIntSub v) n
  refine le_antisymm ?_ hn0
  by_contra hpos
  push_neg at hpos
  have h1 : 0 < v ((u : C) * p) := by
    rw [v.map_mul, hvp]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hu)
  have h2 : 0 < v ((w : C) * n) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_left hw)
  have h3 := v.map_add ((u : C) * p) ((w : C) * n)
  rw [hC, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

private theorem exists_eq_single_of_degree_eq_one {σ : Type} (α : σ →₀ ℕ) (h : α.degree = 1) :
    ∃ s, α = Finsupp.single s 1 := by
  have hne : α ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  refine ⟨s, ?_⟩
  have hsum : ∑ i ∈ α.support, α i = 1 := by rw [← h]; rfl
  have hle : α s ≤ 1 := hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) hs
  have hs1 : α s = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
  have hrest : ∑ i ∈ α.support.erase s, α i = 0 := by
    rw [← Finset.add_sum_erase _ _ hs, hs1] at hsum
    omega
  ext i
  by_cases hi : i = s
  · subst hi
    simp [hs1]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne'
    have hmem : i ∈ α.support.erase s :=
      Finset.mem_erase.mpr ⟨hi, Finsupp.mem_support_iff.mpr hne'⟩
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    omega

theorem nsmul_coprime_bijective_curves [CharZero C] (G : LogFGL v d) {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1)
    (n : ℕ) (hn : ¬ p ∣ n) (gb : Fin d → PowerSeries C) (hgb : IsCurve v gb) :
    ∃! ga : Fin d → PowerSeries C, IsCurve v ga ∧ G.nsmulF n ga = gb := by
  have hn0' : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  have hn0 : (n : C) ≠ 0 := by exact_mod_cast hn0'
  have hvn := valuation_natCast_eq_zero_of_not_dvd hp hvp n hn
  have hvinv : (n : C)⁻¹ ∈ ptIntSub v := by
    show 0 ≤ v (n : C)⁻¹
    have h := v.map_mul (n : C) (n : C)⁻¹
    rw [mul_inv_cancel₀ hn0, v.map_one, hvn, zero_add] at h
    rw [← h]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) C, M = (n : C) • 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin d) (Fin d) C, N = (n : C)⁻¹ • 1 := ⟨_, rfl⟩
  have hNM : N * M = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hn0, one_smul]
  have hMN : M * N = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hn0, one_smul]
  have hMab : ∀ a b, M a b = if a = b then (n : C) else 0 := by
    intro a b
    rw [hM, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hNint : ∀ i j, N i j ∈ ptIntSub v := by
    intro i j
    rw [hN, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact hvinv
    · rw [mul_zero]; exact (ptIntSub v).zero_mem
  have hMint : ∀ a b, M a b ∈ ptIntSub v := by
    intro a b
    rw [hMab]
    split_ifs
    · exact natCast_mem (ptIntSub v) n
    · exact (ptIntSub v).zero_mem
  obtain ⟨K, hK⟩ : ∃ K : Fin d → MvPowerSeries (Fin d) C,
      K = fun b => ptNs G n b - ∑ a, M a b • X a := ⟨_, rfl⟩
  have hK0 : ∀ b, constantCoeff (K b) = 0 := by
    intro b
    simp [hK, ptNs_const]
  have hKi : ∀ b, K b ∈ ptIntSer v (Fin d) := by
    intro b
    rw [hK]
    exact (ptIntSer v (Fin d)).sub_mem (ptNs_int G n b)
      ((ptIntSer v (Fin d)).sum_mem fun a _ => ptIntSer_smul (hMint a b) (ptIntSer_X a))
  have hKdeg : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → PowerSeries C, PTGood v x → PTGood v y → ∀ s ∈ α.support, x s = y s := by
    intro b α hα
    left
    by_contra hlt
    push_neg at hlt
    apply hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with hd | hd
    · rw [(Finsupp.degree_eq_zero_iff α).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        hK0 b]
    · obtain ⟨s, rfl⟩ := exists_eq_single_of_degree_eq_one α hd
      rw [hK]
      simp only [map_sub, map_sum, MvPowerSeries.coeff_smul, ptNs_lin, MvPowerSeries.coeff_X,
        Finsupp.single_left_inj one_ne_zero, hMab, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  have hf : PTGood v gb := isCurve_iff_good.mp hgb
  have key : ∀ y : Fin d → PowerSeries C, PTGood v y →
      (G.nsmulF n y = gb ↔ ∀ b, ∑ a, M a b • y a + subst y (K b) = gb b) := by
    intro y hy
    have hys : HasSubst y := MvPowerSeries.hasSubst_of_constantCoeff_zero fun a => (hy a).1
    rw [nsmulF_eq_subst G hys n]
    constructor
    · intro h b
      rw [← congrFun h b, pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), hK]
    · intro h
      funext b
      rw [pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), ← h b, hK]
  obtain ⟨x, ⟨hx, hxeq⟩, huniq⟩ := pt_solve (A := fun x => x) (K := K) (M := M) (N := N) (f := gb)
    hNM hMN hNint hf (fun x hx s => (hx s).1) (fun x hx s => (hx s).2)
    (fun k x y _ _ hxy s e he => hxy s e he) hKdeg hKi hK0
  refine ⟨x, ⟨isCurve_iff_good.mpr hx, (key x hx).mpr hxeq⟩, fun y hy => ?_⟩
  have hyg := isCurve_iff_good.mp hy.1
  exact huniq y ⟨hyg, (key y hyg).mp hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptAdd (G : LogFGL v d) {τ : Type*} (x y : Fin d → MvPowerSeries τ C) :
    Fin d → MvPowerSeries τ C :=
  fun a => subst (Sum.elim x y) (G.F a)

def ptSumL (G : LogFGL v d) {τ : Type*} :
    List (Fin d → MvPowerSeries τ C) → (Fin d → MvPowerSeries τ C)
  | [] => 0
  | x :: l => ptAdd G x (ptSumL G l)

theorem ptc_elim_const {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) :
    ∀ s, constantCoeff (Sum.elim x y s) = 0 := by
  intro s
  cases s with
  | inl s => exact hx s
  | inr s => exact hy s

private theorem hs_lemma {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero ha

private theorem pc_lemma_9 {σ τ : Type*} {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {m : σ →₀ ℕ} (hm : m ≠ 0) :
    constantCoeff (m.prod fun s n => a s ^ n) = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm (Finsupp.ext hc)
  unfold Finsupp.prod
  rw [map_prod]
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [ha s, hs])

private theorem cc_lemma_2 {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (hf : constantCoeff f = 0) :
    constantCoeff (subst a f) = 0 := by
  rw [constantCoeff_subst (hs_lemma ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · rw [hm]
    simp [hf, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [pc_lemma_9 ha hm, smul_zero]

private theorem fs_lemma_4 {α : Type*} (g : α → C) (hg : ∀ i, g i ∈ ptIntSub v) :
    ∑ᶠ i, g i ∈ ptIntSub v := by
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact Subring.sum_mem _ fun i _ => hg i
  · rw [finsum_of_infinite_support hfin]
    exact Subring.zero_mem _

private theorem int_lemma_3 {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hai : ∀ s, a s ∈ ptIntSer v τ)
    (f : MvPowerSeries σ C) (hf : MvIsInt v f) : subst a f ∈ ptIntSer v τ := by
  show ∀ e, coeff e (subst a f) ∈ ptIntSub v
  intro e
  rw [coeff_subst (hs_lemma ha)]
  apply fs_lemma_4
  intro m
  have hp : (m.prod fun s n => a s ^ n) ∈ ptIntSer v τ := by
    unfold Finsupp.prod
    exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hai s) _
  have hp' : ∀ α, coeff α (m.prod fun s n => a s ^ n) ∈ ptIntSub v := hp
  have hfm : coeff m f ∈ ptIntSub v := hf m
  rw [smul_eq_mul]
  exact Subring.mul_mem _ hfm (hp' e)

theorem ptAdd_good (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : PTGood v x) (hy : PTGood v y) : PTGood v (ptAdd G x y) := by
  have hx0 : ∀ a, constantCoeff (x a) = 0 := fun a => (hx a).1
  have hy0 : ∀ a, constantCoeff (y a) = 0 := fun a => (hy a).1
  intro a
  refine ⟨cc_lemma_2 (ptc_elim_const hx0 hy0) (G.F a) (G.F_const a), ?_⟩
  refine int_lemma_3 (ptc_elim_const hx0 hy0) ?_ (G.F a) (G.F_int a)
  intro s
  cases s with
  | inl s => exact (hx s).2
  | inr s => exact (hy s).2

theorem ptAdd_const (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    constantCoeff (ptAdd G x y a) = 0 := by
  exact cc_lemma_2 (ptc_elim_const hx hy) (G.F a) (G.F_const a)

theorem ptAdd_lg (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (ptAdd G x y) (G.lg a) = subst x (G.lg a) + subst y (G.lg a) := by
  have hxy := hs_lemma (ptc_elim_const hx hy)
  have hF := hs_lemma G.F_const
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma fun b => by simp
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma fun b => by simp
  rw [show ptAdd G x y = fun s => subst (Sum.elim x y) (G.F s) from rfl,
    ← subst_comp_subst_apply hF hxy, G.lg_F a, subst_add hxy,
    subst_comp_subst_apply hl hxy, subst_comp_subst_apply hr hxy]
  simp only [subst_X hxy, Sum.elim_inl, Sum.elim_inr]

private theorem sp_lemma_13 {σ τ : Type*} {a : σ → MvPowerSeries τ C} {m : σ →₀ ℕ} {s : σ}
    (hle : Finsupp.single s 1 ≤ m) :
    (m.prod fun s n => a s ^ n) = a s * ((m - Finsupp.single s 1).prod fun s n => a s ^ n) := by
  conv_lhs => rw [← add_tsub_cancel_of_le hle]
  rw [Finsupp.prod_add_index' (h := fun s n => a s ^ n) (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun s n => a s ^ n) (pow_zero _),
    pow_one]


theorem ptAdd_lin (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d)
    (t : τ) :
    coeff (Finsupp.single t 1) (ptAdd G x y a) =
      coeff (Finsupp.single t 1) (x a) + coeff (Finsupp.single t 1) (y a) := by
  have h0 := ptc_elim_const hx hy
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero h0
  show coeff (Finsupp.single t 1) (subst (Sum.elim x y) (G.F a)) = _
  rw [pt_coeff_single_subst hs h0 (G.F_const a) t, Fintype.sum_sum_type]
  simp only [pt_F_lin, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    if_false, add_zero, zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem ptSumL_const (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ a, constantCoeff (ptSumL G l a) = 0
  | [], _, a => by simp [ptSumL]
  | x :: l, h, a => ptAdd_const G (h x (by simp))
      (ptSumL_const G l fun x' hx' => h x' (by simp [hx'])) a

theorem ptSumL_good (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, PTGood v x) → PTGood v (ptSumL G l)
  | [], _ => ptGood_zero
  | x :: l, h => ptAdd_good G (h x (by simp)) (ptSumL_good G l fun x' hx' => h x' (by simp [hx']))


theorem ptSumL_lg (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ b, subst (ptSumL G l) (G.lg b) = (l.map fun x => subst x (G.lg b)).sum
  | [], _, b => by
    simp only [ptSumL, List.map_nil, List.sum_nil]
    exact subst_zero_of_constantCoeff_zero (G.lg_const b)
  | x :: l, h, b => by
    have hl : ∀ x' ∈ l, ∀ a, constantCoeff (x' a) = 0 := fun x' hx' => h x' (by simp [hx'])
    rw [ptSumL, ptAdd_lg G (h x (by simp)) (ptSumL_const G l hl), ptSumL_lg G l hl b]
    simp

theorem ptSumL_lin (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ a t, coeff (Finsupp.single t 1) (ptSumL G l a) =
        (l.map fun x => coeff (Finsupp.single t 1) (x a)).sum
  | [], _, a, t => by simp [ptSumL]
  | x :: l, h, a, t => by
    have hl : ∀ x' ∈ l, ∀ a, constantCoeff (x' a) = 0 := fun x' hx' => h x' (by simp [hx'])
    rw [ptSumL, ptAdd_lin G (h x (by simp)) (ptSumL_const G l hl), ptSumL_lin G l hl a t]
    simp

private theorem mu_lemma_16 {τ : Type*} {f f' g g' : MvPowerSeries τ C} (n : ℕ)
    (hf : ∀ e : τ →₀ ℕ, e.degree < n → coeff e f = coeff e f')
    (hg : ∀ e : τ →₀ ℕ, e.degree < n → coeff e g = coeff e g') :
    ∀ e : τ →₀ ℕ, e.degree < n → coeff e (f * g) = coeff e (f' * g') := by
  intro e he
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : p.1.degree + p.2.degree = e.degree := by rw [← hp, map_add]
  rw [hf p.1 (by omega), hg p.2 (by omega)]

private theorem m1_lemma_17 {τ : Type*} {f f' g g' : MvPowerSeries τ C} (n : ℕ)
    (hf0 : constantCoeff f = 0) (hf0' : constantCoeff f' = 0)
    (hg0 : constantCoeff g = 0) (hg0' : constantCoeff g' = 0)
    (hf : ∀ e : τ →₀ ℕ, e.degree < n → coeff e f = coeff e f')
    (hg : ∀ e : τ →₀ ℕ, e.degree < n → coeff e g = coeff e g') :
    ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e (f * g) = coeff e (f' * g') := by
  intro e he
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : p.1.degree + p.2.degree = e.degree := by rw [← hp, map_add]
  by_cases h1 : p.1 = 0
  · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, hf0', zero_mul, zero_mul]
  · by_cases h2 : p.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, hg0', mul_zero, mul_zero]
    · have d1 : p.1.degree ≠ 0 := fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h)
      have d2 : p.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).mp h)
      rw [hf p.1 (by omega), hg p.2 (by omega)]

private theorem tp_lemma_14 {σ τ : Type*} {x y : σ → MvPowerSeries τ C} (n : ℕ)
    (hxy : ∀ s (e : τ →₀ ℕ), e.degree < n → coeff e (x s) = coeff e (y s)) (m : σ →₀ ℕ) :
    ∀ e : τ →₀ ℕ, e.degree < n →
      coeff e (m.prod fun s k => x s ^ k) = coeff e (m.prod fun s k => y s ^ k) := by
  have hpow : ∀ s (k : ℕ), ∀ e : τ →₀ ℕ, e.degree < n → coeff e (x s ^ k) = coeff e (y s ^ k) := by
    intro s k
    induction k with
    | zero =>
      intro e _
      simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mu_lemma_16 n ih (hxy s)
  unfold Finsupp.prod
  induction m.support using Finset.induction_on with
  | empty =>
    intro e _
    simp
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact mu_lemma_16 n (hpow j (m j)) ih

private theorem ag_lemma_15 {σ τ : Type*} [Finite σ] {x y : σ → MvPowerSeries τ C}
    (hx : ∀ s, constantCoeff (x s) = 0) (hy : ∀ s, constantCoeff (y s) = 0) (n : ℕ)
    (hxy : ∀ s (e : τ →₀ ℕ), e.degree < n → coeff e (x s) = coeff e (y s))
    (r : MvPowerSeries σ C) (hr0 : constantCoeff r = 0)
    (hr1 : ∀ s, coeff (Finsupp.single s 1) r = 0) (e : τ →₀ ℕ) (he : e.degree ≤ n) :
    coeff e (subst x r) = coeff e (subst y r) := by
  rw [coeff_subst (hs_lemma hx), coeff_subst (hs_lemma hy)]
  apply finsum_congr
  intro m
  by_cases h0 : m = 0
  · rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hr0, zero_smul, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h0 (Finsupp.ext hc)
    have hle : Finsupp.single s 1 ≤ m :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs)
    by_cases hm' : m - Finsupp.single s 1 = 0
    · have hms : m = Finsupp.single s 1 := by
        rw [← add_tsub_cancel_of_le hle, hm', add_zero]
      rw [hms, hr1 s, zero_smul, zero_smul]
    · rw [sp_lemma_13 hle, sp_lemma_13 hle]
      congr 1
      exact m1_lemma_17 n (hx s) (hy s) (pc_lemma_9 hx hm') (pc_lemma_9 hy hm') (hxy s)
        (tp_lemma_14 n hxy _) e he

theorem pt_agree_of_lg (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (k : ℕ)
    (h : ∀ a (e : τ →₀ ℕ), e.degree < k →
      coeff e (subst x (G.lg a)) = coeff e (subst y (G.lg a))) : PTAgree k x y := by
  have hsx := hs_lemma hx
  have hsy := hs_lemma hy
  have hr0 : ∀ i, constantCoeff (G.lg i - X i) = 0 := fun i => by simp [G.lg_const i]
  have hr1 : ∀ i s, coeff (Finsupp.single s 1) (G.lg i - X i) = 0 := fun i s => by
    rw [map_sub, G.lg_lin]
    by_cases his : i = s
    · subst his
      simp [coeff_X]
    · have hne : ¬ Finsupp.single s 1 = Finsupp.single i 1 := fun h' =>
        his (Finsupp.single_left_injective one_ne_zero h').symm
      simp [his, coeff_X, hne]
  have key : ∀ n, ∀ i (e : τ →₀ ℕ), e.degree = n → n < k → coeff e (x i) = coeff e (y i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i e hen hnk
      have hlow : ∀ s (e' : τ →₀ ℕ), e'.degree < n → coeff e' (x s) = coeff e' (y s) :=
        fun s e' he' => ih _ he' s e' rfl (by omega)
      have h1 := h i e (by omega)
      have hlg : G.lg i = X i + (G.lg i - X i) := by ring
      rw [hlg, subst_add hsx, subst_add hsy, subst_X hsx, subst_X hsy, map_add, map_add,
        ag_lemma_15 hx hy n hlow _ (hr0 i) (hr1 i) e (le_of_eq hen)] at h1
      exact add_right_cancel h1
  intro i e he
  exact key _ i e rfl he

private theorem rs_lemma_6 (c : C) (f : PowerSeries C) (n : ℕ) :
    coeff (Finsupp.single () n) (PowerSeries.rescale c f) =
      c ^ n * coeff (Finsupp.single () n) f :=
  PowerSeries.coeff_rescale f c n

private theorem rc_lemma_8 (c : C) (f : PowerSeries C) (hf : constantCoeff f = 0) :
    constantCoeff (PowerSeries.rescale c f) = 0 := by
  have h1 := rs_lemma_6 c f 0
  rw [Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero] at h1
  exact h1

private theorem rp_lemma_7 (c : C) (ga : Fin d → PowerSeries C) (m : Fin d →₀ ℕ) :
    (m.prod fun b k => (rescaleCurve c ga b) ^ k) =
      PowerSeries.rescale c (m.prod fun b k => ga b ^ k) := by
  unfold Finsupp.prod
  rw [map_prod]
  simp only [map_pow]
  rfl

theorem pt_lg_rescale (G : LogFGL v d) (c : C) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (rescaleCurve c ga) a = PowerSeries.rescale c (G.lgCurve ga a) := by
  have hs : HasSubst ga := hs_lemma h0
  have hs' : HasSubst (rescaleCurve c ga) := hs_lemma fun b => rc_lemma_8 c (ga b) (h0 b)
  refine MvPowerSeries.ext fun e => ?_
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [rs_lemma_6, show G.lgCurve (rescaleCurve c ga) a = subst (rescaleCurve c ga) (G.lg a) from rfl,
    show G.lgCurve ga a = subst ga (G.lg a) from rfl, coeff_subst hs', coeff_subst hs,
    mul_finsum]
  apply finsum_congr
  intro m
  rw [rp_lemma_7, rs_lemma_6, smul_eq_mul, smul_eq_mul]
  ring

theorem pt_rescale_good {c : C} (hc : c ∈ ptIntSub v) {ga : Fin d → PowerSeries C}
    (h : PTGood v ga) : PTGood v (rescaleCurve c ga) := by
  intro i
  obtain ⟨h0, hi⟩ := h i
  have hi' : ∀ e, coeff e (ga i) ∈ ptIntSub v := hi
  refine ⟨rc_lemma_8 c (ga i) h0, ?_⟩
  show ∀ e, coeff e (PowerSeries.rescale c (ga i)) ∈ ptIntSub v
  intro e
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [rs_lemma_6]
  exact Subring.mul_mem _ (Subring.pow_mem _ hc n) (hi' _)

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptOn (a : Fin d) (ga : Fin d → PowerSeries C) : Fin d → MvPowerSeries (Fin d) C :=
  fun b => PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (ga b)

def ptBasisMap (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) :
    Fin d → MvPowerSeries (Fin d) C :=
  ptSumL G (List.ofFn fun a => ptOn a (γ a))

theorem ptOn_hs (a : Fin d) : HasSubst (fun _ : Unit => (X a : MvPowerSeries (Fin d) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X a

theorem ptOn_good (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    PTGood v (ptOn a ga) := by
  intro b
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X a) _ (h b).1, ?_⟩
  show ∀ α, coeff α (ptOn a ga b) ∈ ptIntSub v
  intro e
  rw [ptOn, PowerSeries.coeff_subst_single]
  split_ifs
  · exact (ptIsIntV_iff _).mp ((h b).2 _)
  · exact (ptIntSub v).zero_mem

theorem ptOn_lin (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptOn a ga b) = if s = a then tangent ga b else 0 := by
  rw [ptOn, PowerSeries.coeff_subst_single]
  by_cases hs : s = a
  · subst hs
    simp [tangent]
  · simp [Finsupp.single_apply, hs, Ne.symm hs]

theorem ptOn_lg (G : LogFGL v d) (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga)
    (b : Fin d) :
    subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve ga b) := by
  have hga : HasSubst ga := MvPowerSeries.hasSubst_of_constantCoeff_zero fun c => (h c).1
  show subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (subst ga (G.lg b))
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hga (ptOn_hs a)]
  rfl

theorem ptBasisMap_good (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) : PTGood v (ptBasisMap G γ) := by
  unfold ptBasisMap
  refine ptSumL_good G _ fun x hx => ?_
  obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
  exact ptOn_good a (hγ a)

theorem ptBasisMap_lin (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptBasisMap G γ b) = tangent (γ s) b := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  rw [ptBasisMap, ptSumL_lin G _ hc b s, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def, ptOn_lin _ (hγ _)]

theorem ptBasisMap_lg (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (b : Fin d) :
    subst (ptBasisMap G γ) (G.lg b) =
      ∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b) := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  rw [ptBasisMap, ptSumL_lg G _ hc b, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun a _ => ptOn_lg G a (hγ a) b

theorem pt_inv_int {M : Matrix (Fin d) (Fin d) C} (hM : ∀ i j, M i j ∈ ptIntSub v)
    (hdet : v M.det = 0) : IsUnit M.det ∧ ∀ i j, M⁻¹ i j ∈ ptIntSub v := by
  have hdet0 : M.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hdet
    exact WithTop.top_ne_coe hdet
  refine ⟨isUnit_iff_ne_zero.mpr hdet0, fun i j => ?_⟩
  obtain ⟨M', rfl⟩ : ∃ M' : Matrix (Fin d) (Fin d) (ptIntSub v), M = M'.map (ptIntSub v).subtype :=
    ⟨fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  have hadj : (M'.map (ptIntSub v).subtype).adjugate i j = (ptIntSub v).subtype (M'.adjugate i j) :=
    (congrArg (fun N : Matrix (Fin d) (Fin d) C => N i j) (RingHom.map_adjugate (ptIntSub v).subtype M')).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, hadj, Ring.inverse_eq_inv']
  refine (ptIntSub v).mul_mem ?_ (M'.adjugate i j).2
  show 0 ≤ v (M'.map (ptIntSub v).subtype).det⁻¹
  rw [AddValuation.map_inv, hdet, neg_zero]

theorem ptBasisMap_inv (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (Matrix.det (Matrix.of fun a b => tangent (γ a) b)) = 0) :
    ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧
      (∀ a, constantCoeff (Ψ a) = 0) ∧
      (∀ a, subst Ψ (ptBasisMap G γ a) = X a) ∧ (∀ a, subst (ptBasisMap G γ) (Ψ a) = X a) := by
  have hΦ : PTGood v (ptBasisMap G γ) := ptBasisMap_good G hγ
  have hΦs : HasSubst (ptBasisMap G γ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hΦ s).1
  let M : Matrix (Fin d) (Fin d) C := Matrix.of fun a b => tangent (γ a) b
  have hMint : ∀ i j, M i j ∈ ptIntSub v := fun i j => (ptIsIntV_iff _).mp (((hγ i) j).2 1)
  obtain ⟨hdu, hNint⟩ := pt_inv_int hMint hdet
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdu
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdu
  let K : Fin d → MvPowerSeries (Fin d) C := fun b => ptBasisMap G γ b - ∑ a, M a b • X a
  have hlin : ∀ b s, coeff (Finsupp.single s 1) (ptBasisMap G γ b) = M s b :=
    fun b s => ptBasisMap_lin G hγ b s
  have hlow : ∀ b (α : Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (K b) = 0 :=
    fun b => pt_low_of_lin (hΦ b).1 (fun a => M a b) (hlin b)
  have hK : ∀ b (α : Fin d →₀ ℕ), coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → MvPowerSeries (Fin d) C, PTGood v x → PTGood v y → ∀ s ∈ α.support, x s = y s := by
    intro b α h
    left
    by_contra h'
    push_neg at h'
    exact h (hlow b α (by omega))
  have hKi : ∀ b, K b ∈ ptIntSer v (Fin d) := fun b =>
    Subring.sub_mem _ (hΦ b).2 (Subring.sum_mem _ fun a _ => ptIntSer_smul (hMint a b) (ptIntSer_X a))
  have hK0 : ∀ b, constantCoeff (K b) = 0 := fun b => by simp [K, (hΦ b).1]
  have hA0 : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ s, constantCoeff (x s) = 0 :=
    fun x hx s => (hx s).1
  have hAi : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ s, x s ∈ ptIntSer v (Fin d) :=
    fun x hx s => (hx s).2
  have hAag : ∀ k (x y : Fin d → MvPowerSeries (Fin d) C), PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : Fin d →₀ ℕ), e.degree < k → coeff e (x s) = coeff e (y s) :=
    fun k x y _ _ hxy s e he => hxy s e he
  have hfX : PTGood v (fun b => (X b : MvPowerSeries (Fin d) C)) := fun b => ⟨by simp, ptIntSer_X b⟩
  have hsub : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ b,
      subst x (ptBasisMap G γ b) = ∑ a, M a b • x a + subst x (K b) := fun x hx b =>
    pt_subst_lin_split (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hx s).1) _ (fun a => M a b)
  obtain ⟨Ψ, ⟨hΨg, hΨeq⟩, -⟩ := pt_solve (M := M) (N := M⁻¹) (A := fun x => x) (K := K)
    (f := fun b => (X b : MvPowerSeries (Fin d) C)) hNM hMN hNint hfX hA0 hAi hAag hK hKi hK0
  have hΨs : HasSubst Ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hΨg s).1
  have hright : ∀ b, subst Ψ (ptBasisMap G γ b) = X b := fun b => (hsub Ψ hΨg b).trans (hΨeq b)
  obtain ⟨y0, -, huniq⟩ := pt_solve (M := M) (N := M⁻¹) (A := fun x => x) (K := K)
    (f := ptBasisMap G γ) hNM hMN hNint hΦ hA0 hAi hAag hK hKi hK0
  let y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (ptBasisMap G γ) (Ψ a)
  have hyg : PTGood v y := fun a =>
    ⟨MvPowerSeries.constantCoeff_subst_eq_zero hΦs (fun s => (hΦ s).1) (hΨg a).1,
      ptIntSer_subst hΦs (fun s => (hΦ s).2) (hΨg a).2⟩
  have hy : y = y0 := huniq y ⟨hyg, fun b => by
    rw [← hsub y hyg b]
    show subst (fun a => subst (ptBasisMap G γ) (Ψ a)) (ptBasisMap G γ b) = ptBasisMap G γ b
    rw [← MvPowerSeries.subst_comp_subst_apply hΨs hΦs, hright b, MvPowerSeries.subst_X hΦs]⟩
  have hX : (fun b => (X b : MvPowerSeries (Fin d) C)) = y0 := huniq _ ⟨hfX, fun b => by
    rw [← hsub _ hfX b, MvPowerSeries.subst_self]
    rfl⟩
  refine ⟨Ψ, fun a => (ptMvIsInt_iff _).mpr (hΨg a).2, fun a => (hΨg a).1, hright, fun a => ?_⟩
  exact congrFun (hy.trans hX.symm) a

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

def addMv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {τ : Type} (x y : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C :=
  fun a => subst (Sum.elim x y) (G.F a)

def sumMvList {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {τ : Type} : List (Fin d → MvPowerSeries τ C) → (Fin d → MvPowerSeries τ C)
  | [] => 0
  | x :: l => addMv G x (sumMvList G l)

def basisMap {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (γ : Fin d → Fin d → PowerSeries C) : Fin d → MvPowerSeries (Fin d) C :=
  sumMvList G (List.ofFn fun a => fun b => PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (γ a b))

def IsBasis {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (p : ℕ) {h : ℕ} (ty : Fin d → ZMod h) (γ : Fin d → Fin d → PowerSeries C) : Prop :=
  (∀ a, IsCurve v (γ a)) ∧ (∀ a, G.IsOfType p ty (ty a) (γ a)) ∧
    v (Matrix.det (Matrix.of fun a b => tangent (γ a) b)) = 0

def CoprimeMultiplicationBijective : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d : ℕ) (G : LogFGL v d) (n : ℕ), ¬ p ∣ n →
      ∀ gb : Fin d → PowerSeries C, IsCurve v gb →
        ∃! ga : Fin d → PowerSeries C, IsCurve v ga ∧ G.nsmulF n ga = gb

def TypicalCurveEigenspace : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d),
      MuAction G p h ty → ∀ (i : ZMod h) (u : Fin d → C), (∀ a, IsIntV v (u a)) →
        (∀ a, ty a ≠ i → u a = 0) →
          ∃ γ : Fin d → PowerSeries C, IsCurve v γ ∧ G.IsOfType p ty i γ ∧ tangent γ = u

def TypicalCurveBasisExists : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d),
      MuAction G p h ty →
        (∃ γ, IsBasis G p ty γ) ∧
        ∀ γ, IsBasis G p ty γ →
          (∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧
            (∀ a, constantCoeff (Ψ a) = 0) ∧
            (∀ a, subst Ψ (basisMap G γ a) = X a) ∧ (∀ a, subst (basisMap G γ) (Ψ a) = X a)) ∧
          ∀ b, subst (basisMap G γ) (G.lg b) =
            ∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b)

def TypicalCurveStructureConstants : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d) γ,
      IsBasis G p ty γ →
        ∃ sc : ℕ → Fin d → Fin d → C, (∀ s b a, IsIntV v (sc s b a)) ∧
          (∀ s b a, sc s b a ≠ 0 → ty b = ty a + (s : ZMod h) + 1) ∧
          ∀ a n, (p : C) • G.lc p (γ a) (n + 1) = ∑ m ∈ Finset.range (n + 1), ∑ b,
            (sc (n - m) b a) ^ (p ^ m) • G.lc p (γ b) m

def TypicalCurveValuationBounds : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d) γ,
      IsBasis G p ty γ → ∀ a,
        (∀ (n : ℕ) c, (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v (G.lc p (γ a) n c)) ∧
        (G.lc p (γ a) 1 = 0 → ∀ (n : ℕ) c, 1 ≤ n →
          (((1 - (n : ℝ)) : ℝ) : WithTop ℝ) ≤ v (G.lc p (γ a) n c))

def TypicalCurveRebasing : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d m : ℕ) (G : LogFGL v d) (γ : Fin m → Fin d → PowerSeries C)
      (x : Fin m → C), (∀ u, IsCurve v (γ u)) → (∀ u, IsIntV v (x u)) →
        let γ' := G.sumF fun u => rescaleCurve (x u) (γ u)
        IsCurve v γ' ∧ tangent γ' = ∑ u, x u • tangent (γ u) ∧
          (∀ n, G.lc p γ' n = ∑ u, (x u) ^ (p ^ n) • G.lc p (γ u) n) ∧
          ((∀ u, G.IsPTypical p (γ u)) → G.IsPTypical p γ')

theorem pt1 : CoprimeMultiplicationBijective := by
  intro C _ _ _ v p hp hvp d G n hn gb hgb
  exact nsmul_coprime_bijective_curves G hp hvp n hn gb hgb

end

end ReciprocityTheory.ChartRestriction.G.Sh
end
