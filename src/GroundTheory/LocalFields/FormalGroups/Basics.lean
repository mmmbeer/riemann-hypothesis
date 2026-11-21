import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsUniqueFixedPoint

section
namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

section Subst

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem le_order_subst_sub_subst {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f g : MvPowerSeries σ R} {n : ℕ∞}
    (h : n ≤ order (f - g)) : n ≤ order (subst a f - subst a g) := by
  rw [← subst_sub ha]
  refine le_trans ?_ (le_order_subst ha (f - g))
  have h1 : 1 ≤ ⨅ i, (a i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
  calc n ≤ 1 * order (f - g) := by simpa using h
    _ ≤ _ := by gcongr

private def Close (n k : ℕ∞) (u v : MvPowerSeries τ S) : Prop :=
  k ≤ order u ∧ k ≤ order v ∧ n + k ≤ order (u - v) + 1

private lemma close_one (n : ℕ∞) : Close n 0 (1 : MvPowerSeries τ S) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  simp

private lemma close_mul {n k l : ℕ∞} {u v u' v' : MvPowerSeries τ S} (h : Close n k u v)
    (h' : Close n l u' v') : Close n (k + l) (u * u') (v * v') := by
  obtain ⟨hu, hv, huv⟩ := h
  obtain ⟨hu', hv', huv'⟩ := h'
  refine ⟨(add_le_add hu hu').trans (le_order_mul), (add_le_add hv hv').trans (le_order_mul), ?_⟩
  have e : u * u' - v * v' = (u - v) * u' + v * (u' - v') := by ring
  rw [e]
  refine le_trans ?_ (add_le_add min_order_le_add le_rfl)
  rw [← min_add_add_right]
  refine le_min ?_ ?_
  · calc n + (k + l) = (n + k) + l := by rw [add_assoc]
      _ ≤ (order (u - v) + 1) + order u' := add_le_add huv hu'
      _ = (order (u - v) + order u') + 1 := by rw [add_right_comm]
      _ ≤ order ((u - v) * u') + 1 := add_le_add le_order_mul le_rfl
  · calc n + (k + l) = k + (n + l) := by rw [add_left_comm]
      _ ≤ order v + (order (u' - v') + 1) := add_le_add hv huv'
      _ = (order v + order (u' - v')) + 1 := by rw [add_assoc]
      _ ≤ order (v * (u' - v')) + 1 := add_le_add le_order_mul le_rfl

private lemma close_pow {n k : ℕ∞} {u v : MvPowerSeries τ S} (h : Close n k u v) (m : ℕ) :
    Close n (m * k) (u ^ m) (v ^ m) := by
  induction m with
  | zero => simpa using close_one (τ := τ) (S := S) n
  | succ m ih =>
    have := close_mul ih h
    rw [pow_succ, pow_succ]
    convert this using 1
    push_cast
    ring

private lemma close_prod {ι : Type*} (s : Finset ι) {n : ℕ∞} {k : ι → ℕ∞}
    {u v : ι → MvPowerSeries τ S} (h : ∀ i ∈ s, Close n (k i) (u i) (v i)) :
    Close n (∑ i ∈ s, k i) (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using close_one (τ := τ) (S := S) n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact close_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma close_monomial {n : ℕ∞} {a b : σ → MvPowerSeries τ S}
    (h : ∀ i, Close n 1 (a i) (b i)) (d : σ →₀ ℕ) :
    Close n (d.degree : ℕ∞) (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  have := close_prod d.support (k := fun i => (d i : ℕ∞) * 1) (u := fun i => a i ^ d i)
    (v := fun i => b i ^ d i) (fun i _ => close_pow (h i) (d i))
  simpa [Finsupp.prod, Finsupp.degree_apply] using this

theorem add_le_order_subst_sub_subst {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0) {n : ℕ∞} (hab : ∀ i, n ≤ order (a i - b i))
    {f : MvPowerSeries σ R} {m : ℕ∞} (hf : m ≤ order f) :
    n + m ≤ order (subst a f - subst b f) + 1 := by
  have hclose : ∀ i, Close n 1 (a i) (b i) := fun i =>
    ⟨one_le_order_iff_constCoeff_eq_zero.2 (ha0 i),
      one_le_order_iff_constCoeff_eq_zero.2 (hb0 i), add_le_add (hab i) le_rfl⟩

  have hcoeff : ∀ e : τ →₀ ℕ, (e.degree : ℕ∞) + 1 < n + m →
      coeff e (subst a f - subst b f) = 0 := by
    intro e he
    rw [map_sub, coeff_subst ha, coeff_subst hb,
      ← finsum_sub_distrib (coeff_subst_finite ha f e) (coeff_subst_finite hb f e)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : coeff d f = 0
    · simp [hd]
    rw [← smul_sub, ← map_sub]
    obtain ⟨-, -, hdc⟩ := close_monomial hclose d
    have hmd : m ≤ (d.degree : ℕ∞) := hf.trans (order_le hd)
    have : (e.degree : ℕ∞) + 1 < order ((d.prod fun s e => a s ^ e) -
        (d.prod fun s e => b s ^ e)) + 1 :=
      he.trans_le ((add_le_add le_rfl hmd).trans hdc)
    rw [coeff_of_lt_order ((ENat.add_lt_add_iff_right ENat.one_ne_top).1 this), smul_zero]
  by_contra hlt
  rw [not_le] at hlt
  have hfin : (order (subst a f - subst b f)).toNat = order (subst a f - subst b f) := by
    refine ENat.natCast_toNat fun htop => ?_
    rw [htop] at hlt
    simp at hlt
  obtain ⟨e, he, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  exact he (hcoeff e (by rw [hdeg]; exact hlt))

end Subst

section FixedPoint

variable {σ R : Type*} [CommRing R]

theorem existsUnique_fixedPoint (Φ : MvPowerSeries σ R → MvPowerSeries σ R)
    (hΦ : ∀ f g : MvPowerSeries σ R, ∀ n : ℕ, (n : ℕ∞) ≤ order (f - g) →
      ((n + 1 : ℕ) : ℕ∞) ≤ order (Φ f - Φ g)) :
    ∃! f, Φ f = f :=
  _root_.UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint Φ hΦ

end FixedPoint

end GroundTheory.LocalField.FormalGroup
end

section
namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

variable {R : Type*} [CommRing R] (F : FormalGroup R)

noncomputable def higher : MvPowerSeries (Fin 2) R :=
  F.toPowerSeries - X 0 - X 1

theorem toPowerSeries_eq_X_add_X_add_higher : F.toPowerSeries = X 0 + X 1 + higher F := by
  simp [higher]

theorem two_le_order_higher : (2 : ℕ∞) ≤ order (higher F) := by
  refine nat_le_order fun d hd => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = Finsupp.single 0 a + Finsupp.single 1 b :=
    ⟨d 0, d 1, by ext i; fin_cases i <;> simp⟩
  have hab : a + b < 2 := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  have ha : a < 2 := by omega
  have hb : b < 2 := by omega
  interval_cases a <;> interval_cases b <;> simp_all [higher, coeff_X, F.lin_coeff_X,
    F.lin_coeff_Y, F.zero_constantCoeff, Ne.symm h01]

theorem constantCoeff_higher : constantCoeff (higher F) = 0 :=
  one_le_order_iff_constCoeff_eq_zero.1 (le_trans (by norm_num) (two_le_order_higher F))

theorem subst_eq_add_add_subst_higher {τ : Type*} {a b : MvPowerSeries τ R}
    (hab : HasSubst ![a, b]) :
    subst ![a, b] F.toPowerSeries = a + b + subst ![a, b] (higher F) := by
  conv_lhs => rw [toPowerSeries_eq_X_add_X_add_higher F]
  rw [subst_add hab, subst_add hab, subst_X hab, subst_X hab]
  simp

lemma hasSubst_pair {τ : Type*} {a b : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simpa

private noncomputable def invStep (g : MvPowerSeries Unit R) : MvPowerSeries Unit R :=
  -X () - subst ![X (), g - C (constantCoeff g)] (higher F)

private lemma constantCoeff_sub_C (g : MvPowerSeries Unit R) :
    constantCoeff (g - C (constantCoeff g)) = 0 := by simp

private lemma invStep_contract (f g : MvPowerSeries Unit R) (n : ℕ)
    (h : (n : ℕ∞) ≤ order (f - g)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (invStep F f - invStep F g) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have key := add_le_order_subst_sub_subst (R := R) (m := 2) (n := (n : ℕ∞))
    (hasSubst_pair hX (constantCoeff_sub_C f)) (hasSubst_pair hX (constantCoeff_sub_C g))
    (fun i => by fin_cases i <;> simp) (fun i => by fin_cases i <;> simp) ?_
    (two_le_order_higher F)
  · have e : invStep F f - invStep F g = -(subst ![X (), f - C (constantCoeff f)] (higher F) -
        subst ![X (), g - C (constantCoeff g)] (higher F)) := by
      simp only [invStep]; ring
    rw [e, order_neg]
    have : ((n + 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) + 2 := by push_cast; ring
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (this ▸ key)
  · intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn]
      · have h0 : constantCoeff (f - g) = 0 := by
          rw [← coeff_zero_eq_constantCoeff_apply]
          exact coeff_of_lt_order (lt_of_lt_of_le (by simpa using hn) h)
        rw [map_sub, sub_eq_zero] at h0
        rw [h0]
        simpa using h

private lemma existsUnique_invStep : ∃! g, invStep F g = g :=
  existsUnique_fixedPoint _ (invStep_contract F)

noncomputable def inv : PowerSeries R :=
  (existsUnique_invStep F).exists.choose

private lemma invStep_inv : invStep F (inv F) = inv F :=
  (existsUnique_invStep F).exists.choose_spec

private lemma constantCoeff_invStep (g : MvPowerSeries Unit R) :
    constantCoeff (invStep F g) = 0 := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  rw [invStep, map_sub, map_neg, hX,
    constantCoeff_subst_eq_zero (hasSubst_pair hX (constantCoeff_sub_C g))
      (fun i => by fin_cases i <;> simp) (constantCoeff_higher F)]
  simp

theorem constantCoeff_inv : PowerSeries.constantCoeff (inv F) = 0 := by
  rw [← invStep_inv F]
  exact constantCoeff_invStep F _

theorem hasSubst_inv : PowerSeries.HasSubst (inv F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_inv F)

private lemma invStep_of_constantCoeff_eq_zero {g : MvPowerSeries Unit R}
    (hg : constantCoeff g = 0) : invStep F g = -X () - subst ![X (), g] (higher F) := by
  simp [invStep, hg]

theorem subst_X_inv :
    subst ![PowerSeries.X, inv F] F.toPowerSeries = (0 : PowerSeries R) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hi : constantCoeff (inv F : MvPowerSeries Unit R) = 0 := constantCoeff_inv F
  have := invStep_inv F
  rw [invStep_of_constantCoeff_eq_zero F hi] at this
  change subst ![X (), (inv F : MvPowerSeries Unit R)] F.toPowerSeries = 0
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hi)]
  linear_combination (-1 : MvPowerSeries Unit R) * this

theorem eq_inv_of_subst_eq_zero {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (h : subst ![PowerSeries.X, g] F.toPowerSeries = (0 : PowerSeries R)) : g = inv F := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hg' : constantCoeff (g : MvPowerSeries Unit R) = 0 := hg
  change subst ![X (), (g : MvPowerSeries Unit R)] F.toPowerSeries = 0 at h
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hg')] at h
  have hfix : invStep F g = g := by
    rw [invStep_of_constantCoeff_eq_zero F hg']
    linear_combination (-1 : MvPowerSeries Unit R) * h
  exact (existsUnique_invStep F).unique hfix (invStep_inv F)

theorem subst_subst_pair {σ : Type*} {g h : PowerSeries R} (hgh : HasSubst ![g, h])
    {x : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x) (G : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst x (subst ![g, h] G : PowerSeries R) =
      subst ![PowerSeries.subst x g, PowerSeries.subst x h] G := by
  have hx' : HasSubst (fun _ : Unit => x) := PowerSeries.hasSubst_iff.mp hx
  rw [PowerSeries.subst_def, subst_comp_subst_apply hgh hx']
  congr 1
  funext s
  fin_cases s <;> rfl

variable {σ : Type*}

noncomputable instance : Neg (F.Point σ) where
  neg x := ⟨PowerSeries.subst x.val (inv F), by
    simpa [PowerSeries.coe_substAlgHom] using (hasSubst_inv F).comp x.prop⟩

theorem neg_point_val (x : F.Point σ) : (-x).val = PowerSeries.subst x.val (inv F) := rfl

private lemma add_neg_point (x : F.Point σ) : x + -x = 0 := by
  apply Subtype.ext
  have hX : constantCoeff (PowerSeries.X : PowerSeries R) = 0 := PowerSeries.constantCoeff_X
  have h := congrArg (PowerSeries.subst x.val) (subst_X_inv F)
  rw [subst_subst_pair (hasSubst_pair hX (constantCoeff_inv F)) x.prop,
    PowerSeries.subst_X x.prop] at h
  rw [FormalGroup.add_apply, neg_point_val, h]
  rw [← PowerSeries.coe_substAlgHom x.prop, map_zero]
  rfl

noncomputable instance instAddGroupPoint : AddGroup (F.Point σ) :=
  { (inferInstance : AddMonoid (F.Point σ)) with
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      have h1 := add_neg_point F x
      have h2 := add_neg_point F (-x)
      have hx : x = -(-x) :=
        calc x = x + 0 := (add_zero x).symm
          _ = x + (-x + -(-x)) := by rw [h2]
          _ = (x + -x) + -(-x) := (add_assoc _ _ _).symm
          _ = -(-x) := by rw [h1, zero_add]
      calc -x + x = -x + -(-x) := congrArg (-x + ·) hx
        _ = 0 := h2 }

noncomputable instance instAddCommGroupPoint [F.IsComm] : AddCommGroup (F.Point σ) :=
  { instAddGroupPoint F with
    add_comm := fun x y => Subtype.ext (F.comm' x.prop y.prop) }

end GroundTheory.LocalField.FormalGroup
end

section
namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

variable {R : Type*} [CommRing R]

theorem hasSubst_powerSeries_subst {τ : Type*} {x : MvPowerSeries τ R}
    (hx : PowerSeries.HasSubst x) {φ : PowerSeries R} (hφ : PowerSeries.HasSubst φ) :
    PowerSeries.HasSubst (PowerSeries.subst x φ) := by
  simpa [PowerSeries.coe_substAlgHom] using hφ.comp hx

theorem subst_powerSeries_subst {τ υ : Type*} {a : MvPowerSeries τ R}
    (ha : PowerSeries.HasSubst a) {b : τ → MvPowerSeries υ R} (hb : HasSubst b)
    (φ : PowerSeries R) :
    subst b (PowerSeries.subst a φ) = PowerSeries.subst (subst b a) φ := by
  have ha' : HasSubst (fun _ : Unit => a) := PowerSeries.hasSubst_iff.mp ha
  rw [PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply ha' hb]

theorem subst_X_X (f : MvPowerSeries (Fin 2) R) : subst ![X 0, X 1] f = f := by
  have : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = X := by
    funext i; fin_cases i <;> rfl
  rw [this, subst_self]
  rfl

theorem constantCoeff_powerSeries_subst {τ : Type*} {a : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) :
    constantCoeff (PowerSeries.subst a φ) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha φ hφ

theorem constantCoeff_subst_of_powerSeries {φ ψ : PowerSeries R}
    (hψ : PowerSeries.constantCoeff ψ = 0) (hφ : PowerSeries.constantCoeff φ = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst ψ φ) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hψ φ hφ

theorem constantCoeff_subst_pair_of_powerSeries (G : FormalGroup R) {φ ψ : PowerSeries R}
    (hφ : PowerSeries.constantCoeff φ = 0) (hψ : PowerSeries.constantCoeff ψ = 0) :
    PowerSeries.constantCoeff (subst ![φ, ψ] G.toPowerSeries : PowerSeries R) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_pair hφ hψ)
    (fun i => by fin_cases i; exacts [hφ, hψ]) G.zero_constantCoeff

variable {F G H : FormalGroup R}

theorem point_hasSubst_pair {σ : Type*} (x y : F.Point σ) : HasSubst ![x.val, y.val] :=
  hasSubst_of_constantCoeff_nilpotent fun i => by fin_cases i; exacts [x.prop, y.prop]

noncomputable def substPoint (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    {σ : Type*} (x : F.Point σ) : G.Point σ :=
  ⟨PowerSeries.subst x.val φ,
    hasSubst_powerSeries_subst x.prop (PowerSeries.HasSubst.of_constantCoeff_zero' hφ)⟩

theorem substPoint_val (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    {σ : Type*} (x : F.Point σ) :
    (substPoint (G := G) φ hφ x).val = PowerSeries.subst x.val φ := rfl

theorem substPoint_congr {φ ψ : PowerSeries R} (e : φ = ψ) (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) {σ : Type*} (x : F.Point σ) :
    (substPoint φ hφ x : G.Point σ) = substPoint ψ hψ x := by
  subst e; rfl

theorem substPoint_X {σ : Type*} (x : F.Point σ) (h) :
    (substPoint PowerSeries.X h x : F.Point σ) = x :=
  Subtype.ext (PowerSeries.subst_X x.prop)

theorem substPoint_zero {σ : Type*} (x : F.Point σ) (h) :
    (substPoint 0 h x : G.Point σ) = 0 := by
  apply Subtype.ext
  rw [substPoint_val, ← PowerSeries.coe_substAlgHom x.prop, map_zero]
  rfl

theorem substPoint_zero_point {σ : Type*} (φ : PowerSeries R) (hφ) :
    (substPoint φ hφ (0 : F.Point σ) : G.Point σ) = 0 :=
  Subtype.ext (PowerSeries.subst_zero_of_constantCoeff_zero hφ)

theorem substPoint_substPoint {φ ψ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) (h) {σ : Type*} (x : F.Point σ) :
    (substPoint φ hφ (substPoint ψ hψ x : G.Point σ) : H.Point σ) =
      substPoint (PowerSeries.subst ψ φ) h x := by
  apply Subtype.ext
  simp only [substPoint_val]
  exact (PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hψ) x.prop φ).symm

theorem substPoint_subst_pair {φ ψ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) (h) {σ : Type*} (x : F.Point σ) :
    (substPoint (subst ![φ, ψ] G.toPowerSeries) h x : G.Point σ) =
      substPoint φ hφ x + substPoint ψ hψ x := by
  apply Subtype.ext
  rw [substPoint_val, FormalGroup.add_apply, substPoint_val, substPoint_val]
  exact subst_subst_pair (hasSubst_pair hφ hψ) x.prop _

theorem substPoint_inv_subst {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) (h)
    {σ : Type*} (x : F.Point σ) :
    (substPoint (PowerSeries.subst φ (inv G)) h x : G.Point σ) = -substPoint φ hφ x := by
  apply Subtype.ext
  rw [substPoint_val, neg_point_val, substPoint_val]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hφ)
    x.prop _

variable (F G) in

@[ext]
structure Hom where

  toPowerSeries : PowerSeries R

  constantCoeff_eq_zero : PowerSeries.constantCoeff toPowerSeries = 0

  map_add : PowerSeries.subst F.toPowerSeries toPowerSeries =
    subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) toPowerSeries,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) toPowerSeries] G.toPowerSeries

namespace Hom

theorem constantCoeff_eq_zero' (f : Hom F G) : constantCoeff f.toPowerSeries = 0 :=
  f.constantCoeff_eq_zero

noncomputable def apply (f : Hom F G) {σ : Type*} (x : F.Point σ) : G.Point σ :=
  substPoint f.toPowerSeries f.constantCoeff_eq_zero x

theorem apply_val (f : Hom F G) {σ : Type*} (x : F.Point σ) :
    (f.apply x).val = PowerSeries.subst x.val f.toPowerSeries := rfl

theorem apply_add (f : Hom F G) {σ : Type*} (x y : F.Point σ) :
    f.apply (x + y) = f.apply x + f.apply y := by
  apply Subtype.ext
  have hxy := point_hasSubst_pair x y
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) R) = 0 := fun i => by simp
  have hpair := hasSubst_pair (constantCoeff_powerSeries_subst (hX 0) f.constantCoeff_eq_zero)
    (constantCoeff_powerSeries_subst (hX 1) f.constantCoeff_eq_zero)
  have h := congrArg (subst ![x.val, y.val]) f.map_add
  rw [subst_powerSeries_subst hF hxy, subst_comp_subst_apply hpair hxy] at h
  rw [apply_val, FormalGroup.add_apply, h, FormalGroup.add_apply]
  congr 1
  funext i
  fin_cases i
  · simp [subst_powerSeries_subst (PowerSeries.HasSubst.X (0 : Fin 2)) hxy, subst_X hxy,
      apply_val]
  · simp [subst_powerSeries_subst (PowerSeries.HasSubst.X (1 : Fin 2)) hxy, subst_X hxy,
      apply_val]

theorem apply_zero (f : Hom F G) {σ : Type*} : f.apply (0 : F.Point σ) = 0 :=
  substPoint_zero_point _ _

private noncomputable def genPoint (F : FormalGroup R) (i : Fin 2) : F.Point (Fin 2) :=
  ⟨X i, PowerSeries.HasSubst.X i⟩

noncomputable def ofPoints (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    (h : ∀ x y : F.Point (Fin 2),
      (substPoint φ hφ (x + y) : G.Point (Fin 2)) = substPoint φ hφ x + substPoint φ hφ y) :
    Hom F G where
  toPowerSeries := φ
  constantCoeff_eq_zero := hφ
  map_add := by
    have := congrArg Subtype.val (h (genPoint F 0) (genPoint F 1))
    rw [substPoint_val, FormalGroup.add_apply, FormalGroup.add_apply, substPoint_val,
      substPoint_val] at this
    simpa [genPoint, subst_X_X] using this

@[simp]
theorem ofPoints_toPowerSeries (φ : PowerSeries R) (hφ) (h) :
    (ofPoints (F := F) (G := G) φ hφ h).toPowerSeries = φ := rfl

noncomputable def comp (g : Hom G H) (f : Hom F G) : Hom F H :=
  ofPoints (PowerSeries.subst f.toPowerSeries g.toPowerSeries)
    (constantCoeff_subst_of_powerSeries f.constantCoeff_eq_zero g.constantCoeff_eq_zero)
    fun x y => by
      rw [← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero,
        ← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero,
        ← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero]
      exact (congrArg g.apply (f.apply_add x y)).trans (g.apply_add _ _)

theorem toPowerSeries_comp (g : Hom G H) (f : Hom F G) :
    (g.comp f).toPowerSeries = PowerSeries.subst f.toPowerSeries g.toPowerSeries := rfl


variable (F) in

noncomputable def id : Hom F F :=
  ofPoints PowerSeries.X PowerSeries.constantCoeff_X fun x y => by
    rw [substPoint_X, substPoint_X, substPoint_X]

theorem toPowerSeries_id : (id F).toPowerSeries = PowerSeries.X := rfl

theorem comp_assoc {K : FormalGroup R} (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext1
  simp only [toPowerSeries_comp]
  exact PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' g.constantCoeff_eq_zero)
    (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero) _

theorem id_comp (f : Hom F G) : (id G).comp f = f := by
  ext1
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero)

theorem comp_id (f : Hom F G) : f.comp (id F) = f := by
  ext1
  exact PowerSeries.X_subst _

noncomputable instance : Monoid (Hom F F) where
  mul g f := g.comp f
  one := id F
  mul_assoc h g f := comp_assoc h g f
  one_mul := id_comp
  mul_one := comp_id

theorem mul_def (g f : Hom F F) : g * f = g.comp f := rfl

theorem one_def : (1 : Hom F F) = id F := rfl

noncomputable def toPoint (f : Hom F G) : G.Point Unit :=
  ⟨f.toPowerSeries, PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero⟩

theorem toPoint_injective : Function.Injective (toPoint : Hom F G → G.Point Unit) :=
  fun _ _ h => Hom.ext (congrArg Subtype.val h)

theorem toPoint_comp (g : Hom G H) (f : Hom F G) : (g.comp f).toPoint = g.apply f.toPoint := rfl

noncomputable instance : Zero (Hom F G) where
  zero := ofPoints 0 (map_zero _) fun _ _ => by
    rw [substPoint_zero, substPoint_zero, substPoint_zero, add_zero]

theorem toPowerSeries_zero : (0 : Hom F G).toPowerSeries = 0 := rfl

theorem toPoint_zero : (0 : Hom F G).toPoint = 0 := rfl

theorem zero_apply {σ : Type*} (x : F.Point σ) : (0 : Hom F G).apply x = 0 :=
  substPoint_zero x _

section Comm

variable [G.IsComm]

noncomputable instance : Add (Hom F G) where
  add f g := ofPoints (subst ![f.toPowerSeries, g.toPowerSeries] G.toPowerSeries)
    (constantCoeff_subst_pair_of_powerSeries G f.constantCoeff_eq_zero g.constantCoeff_eq_zero)
    fun x y => by
      rw [substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero,
        substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero,
        substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero]
      exact (congrArg₂ (· + ·) (f.apply_add x y) (g.apply_add x y)).trans
        (add_add_add_comm _ _ _ _)

noncomputable instance : Neg (Hom F G) where
  neg f := ofPoints (PowerSeries.subst f.toPowerSeries (inv G))
    (constantCoeff_subst_of_powerSeries f.constantCoeff_eq_zero (constantCoeff_inv G))
    fun x y => by
      rw [substPoint_inv_subst f.constantCoeff_eq_zero, substPoint_inv_subst
        f.constantCoeff_eq_zero, substPoint_inv_subst f.constantCoeff_eq_zero]
      exact (congrArg Neg.neg (f.apply_add x y)).trans (neg_add _ _)

noncomputable instance : Sub (Hom F G) where
  sub f g := f + -g

noncomputable instance : SMul ℕ (Hom F G) where
  smul := nsmulRec

noncomputable instance : SMul ℤ (Hom F G) where
  smul := zsmulRec

theorem toPowerSeries_add (f g : Hom F G) :
    (f + g).toPowerSeries = subst ![f.toPowerSeries, g.toPowerSeries] G.toPowerSeries := rfl


theorem toPoint_add (f g : Hom F G) : (f + g).toPoint = f.toPoint + g.toPoint := rfl

theorem toPoint_neg (f : Hom F G) : (-f).toPoint = -f.toPoint := rfl

theorem toPoint_sub (f g : Hom F G) : (f - g).toPoint = f.toPoint - g.toPoint := by
  rw [sub_eq_add_neg, ← toPoint_neg, ← toPoint_add]
  rfl

theorem toPoint_nsmul (f : Hom F G) (n : ℕ) : (n • f).toPoint = n • f.toPoint := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih =>
    rw [succ_nsmul, ← ih, ← toPoint_add]
    rfl

theorem toPoint_zsmul (f : Hom F G) (n : ℤ) : (n • f).toPoint = n • f.toPoint := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, natCast_zsmul, ← toPoint_nsmul]
    rfl
  | negSucc n =>
    rw [negSucc_zsmul, ← toPoint_nsmul, ← toPoint_neg]
    rfl

noncomputable instance : AddCommGroup (Hom F G) :=
  toPoint_injective.addCommGroup _ toPoint_zero toPoint_add toPoint_neg toPoint_sub
    toPoint_nsmul toPoint_zsmul

theorem add_apply (f g : Hom F G) {σ : Type*} (x : F.Point σ) :
    (f + g).apply x = f.apply x + g.apply x :=
  substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero _ x

theorem neg_apply (f : Hom F G) {σ : Type*} (x : F.Point σ) : (-f).apply x = -f.apply x :=
  substPoint_inv_subst f.constantCoeff_eq_zero _ x

theorem comp_add (g : Hom G H) [H.IsComm] (f₁ f₂ : Hom F G) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
  toPoint_injective (by rw [toPoint_comp, toPoint_add, apply_add, toPoint_add]; rfl)

omit [G.IsComm] in
theorem add_comp [H.IsComm] (g₁ g₂ : Hom G H) (f : Hom F G) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
  toPoint_injective (by rw [toPoint_comp, add_apply, toPoint_add]; rfl)

variable (F) in

theorem toPowerSeries_neg_id [F.IsComm] : (-id F).toPowerSeries = inv F :=
  PowerSeries.X_subst _

end Comm

section Ring

variable [F.IsComm]

noncomputable instance : Ring (Hom F F) :=
  { (inferInstance : AddCommGroup (Hom F F)), (inferInstance : Monoid (Hom F F)) with
    left_distrib := fun f g h => comp_add f g h
    right_distrib := fun f g h => add_comp f g h
    zero_mul := fun f => toPoint_injective (by
      rw [mul_def, toPoint_comp, zero_apply]; rfl)
    mul_zero := fun f => toPoint_injective (by
      rw [mul_def, toPoint_comp]
      exact (apply_zero f).trans rfl) }

theorem one_apply {σ : Type*} (x : F.Point σ) : (1 : Hom F F).apply x = x :=
  substPoint_X x _

theorem intCast_apply (n : ℤ) {σ : Type*} (x : F.Point σ) : (n : Hom F F).apply x = n • x := by
  induction n using Int.induction_on with
  | zero => rw [Int.cast_zero, zero_apply, zero_zsmul]
  | succ n ih => rw [Int.cast_add, Int.cast_one, add_apply, ih, one_apply, add_zsmul, one_zsmul]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg, add_apply, neg_apply, ih, one_apply,
      sub_zsmul, one_zsmul]

end Ring

end Hom

theorem two_le_order_subst_higher (F : FormalGroup R) {τ : Type*} {a b : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    (2 : ℕ∞) ≤ order (subst ![a, b] (higher F)) := by
  have := le_order_subst_sub_subst (f := higher F) (g := 0) (hasSubst_pair ha hb)
    (fun i => by fin_cases i <;> simp [ha, hb]) (by simpa using two_le_order_higher F)
  rwa [← subst_sub (hasSubst_pair ha hb), sub_zero] at this

theorem coeff_one_subst_pair (F : FormalGroup R) {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (subst ![f, g] F.toPowerSeries : PowerSeries R) =
      PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  change coeff (Finsupp.single () 1) (subst ![f, g] F.toPowerSeries) =
    coeff (Finsupp.single () 1) f + coeff (Finsupp.single () 1) g
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hf hg), map_add, map_add,
    coeff_of_lt_order (lt_of_lt_of_le (by simp) (two_le_order_subst_higher F hf hg)), add_zero]

theorem coeff_one_subst {f g : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst g f) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g := by
  set c := PowerSeries.coeff 1 f with hc
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hdec : f = PowerSeries.C c * PowerSeries.X + (f - PowerSeries.C c * PowerSeries.X) := by
    ring
  have h2 : (2 : ℕ∞) ≤ (f - PowerSeries.C c * PowerSeries.X).order := by
    refine PowerSeries.nat_le_order _ 2 fun i hi => ?_
    interval_cases i
    · simp [hf]
    · simp [hc]
  have h2' : (2 : ℕ∞) ≤ PowerSeries.order
      (PowerSeries.subst g (f - PowerSeries.C c * PowerSeries.X)) :=
    h2.trans (PowerSeries.le_order_subst_left' hg)
  conv_lhs => rw [hdec]
  rw [PowerSeries.subst_add hgs, PowerSeries.subst_mul hgs, PowerSeries.subst_X hgs, map_add,
    PowerSeries.coeff_of_lt_order 1 (lt_of_lt_of_le (by norm_num) h2'), add_zero]
  change PowerSeries.coeff 1 (PowerSeries.subst g (PowerSeries.C c) * g) = _
  rw [PowerSeries.subst_C]
  exact PowerSeries.coeff_C_mul _ _ _

namespace Hom

theorem coeff_one_comp (g : Hom G H) (f : Hom F G) :
    PowerSeries.coeff 1 (g.comp f).toPowerSeries =
      PowerSeries.coeff 1 g.toPowerSeries * PowerSeries.coeff 1 f.toPowerSeries :=
  coeff_one_subst g.constantCoeff_eq_zero f.constantCoeff_eq_zero

theorem coeff_one_add [G.IsComm] (f g : Hom F G) :
    PowerSeries.coeff 1 (f + g).toPowerSeries =
      PowerSeries.coeff 1 f.toPowerSeries + PowerSeries.coeff 1 g.toPowerSeries :=
  coeff_one_subst_pair G f.constantCoeff_eq_zero g.constantCoeff_eq_zero

theorem coeff_one_id : PowerSeries.coeff 1 (id F).toPowerSeries = 1 := by
  simp [toPowerSeries_id]

end Hom

variable (F) in

noncomputable def linearCoeff [F.IsComm] : Hom F F →+* R where
  toFun f := PowerSeries.coeff 1 f.toPowerSeries
  map_one' := Hom.coeff_one_id
  map_mul' g f := Hom.coeff_one_comp g f
  map_zero' := by simp [Hom.toPowerSeries_zero]
  map_add' f g := Hom.coeff_one_add f g

theorem linearCoeff_apply [F.IsComm] (f : Hom F F) :
    linearCoeff F f = PowerSeries.coeff 1 f.toPowerSeries := rfl

variable (F G) in

structure Iso where

  hom : Hom F G

  inv : Hom G F
  hom_comp_inv : hom.comp inv = Hom.id G
  inv_comp_hom : inv.comp hom = Hom.id F

namespace Iso

variable (F) in

noncomputable def refl : Iso F F := ⟨Hom.id F, Hom.id F, Hom.id_comp _, Hom.id_comp _⟩

def symm (e : Iso F G) : Iso G F := ⟨e.inv, e.hom, e.inv_comp_hom, e.hom_comp_inv⟩

noncomputable def trans (e : Iso F G) (e' : Iso G H) : Iso F H where
  hom := e'.hom.comp e.hom
  inv := e.inv.comp e'.inv
  hom_comp_inv := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc e.hom, e.hom_comp_inv, Hom.id_comp, e'.hom_comp_inv]
  inv_comp_hom := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc e'.inv, e'.inv_comp_hom, Hom.id_comp, e.inv_comp_hom]

theorem isUnit_coeff_one (e : Iso F G) : IsUnit (PowerSeries.coeff 1 e.hom.toPowerSeries) := by
  have h := congrArg (fun f : Hom G G => PowerSeries.coeff 1 f.toPowerSeries) e.hom_comp_inv
  simp only [Hom.coeff_one_comp, Hom.coeff_one_id] at h
  exact IsUnit.of_mul_eq_one _ h

noncomputable def ofIsUnit (f : Hom F G) (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) :
    Iso F G :=
  have hψ := PowerSeries.constantCoeff_substInvOfIsUnit f.toPowerSeries hf
  have hfψ : PowerSeries.subst (PowerSeries.substInvOfIsUnit f.toPowerSeries hf)
      f.toPowerSeries = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right _ f.constantCoeff_eq_zero hf
  have hψf : PowerSeries.subst f.toPowerSeries
      (PowerSeries.substInvOfIsUnit f.toPowerSeries hf) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left _ f.constantCoeff_eq_zero hf
  { hom := f
    inv := Hom.ofPoints (PowerSeries.substInvOfIsUnit f.toPowerSeries hf) hψ fun x y => by
      set u : F.Point (Fin 2) := substPoint _ hψ x + substPoint _ hψ y
      have hu : f.apply u = x + y := by
        rw [Hom.apply_add, Hom.apply, Hom.apply, substPoint_substPoint _ _
          (by rw [hfψ]; exact PowerSeries.constantCoeff_X), substPoint_substPoint _ _
          (by rw [hfψ]; exact PowerSeries.constantCoeff_X), substPoint_congr hfψ _
          PowerSeries.constantCoeff_X, substPoint_congr hfψ _ PowerSeries.constantCoeff_X,
          substPoint_X, substPoint_X]
      rw [← hu, Hom.apply, substPoint_substPoint _ _
          (by rw [hψf]; exact PowerSeries.constantCoeff_X),
        substPoint_congr hψf _ PowerSeries.constantCoeff_X, substPoint_X]
    hom_comp_inv := Hom.ext hfψ
    inv_comp_hom := Hom.ext hψf }

@[simp]
theorem ofIsUnit_hom (f : Hom F G) (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) :
    (ofIsUnit f hf).hom = f := rfl

end Iso

end GroundTheory.LocalField.FormalGroup
end
