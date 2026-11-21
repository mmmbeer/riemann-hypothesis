import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SigmaDefectEvalPhaseOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyFirstZeroSecond
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeSecondDeriv

variable {k : Type} [CommRing k] {d : ℕ}

theorem cz12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) :=
  CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)

theorem pderiv_ev_second (h : PS k 2 d) (q : Pt k 3 d) (hq : ∀ c, constantCoeff (q c) = 0) (b : Fin d) :
    pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, q] h) =
      ∑ j, ev (n := 3) ![pt k d 0, q] (pderiv k ((1 : Fin 2), j) h) * pderiv k ((2 : Fin 3), b) (q j) := by
  have hc : CZ (![pt k (n := 3) d 0, q] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons hq CZ.nil)
  rw [pderiv_ev hc, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pderiv_pt]

theorem ev_pderiv_add (F : PS k 2 d) (b : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] F)) =
      ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) F) := by
  rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
  have e : ((1 : Fin 3) = 2) = False := by simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_pt, Prod.mk.injEq, e, false_and,
    if_false, mul_zero, Finset.sum_const_zero, zero_add, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [ev_ev czZ cz12]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ]

theorem ev_add_axis (G : FGLaw k d) (c : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) =
      pt k (n := 2) d 1 c := by
  have h1 : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 1) CZ.nil
  have e := congrArg (ev (n := 2) ![pt k d 1]) (formalGroupLaw_ev_x_zero G c)
  rw [ev_ev h1 cz1, ev_X h1] at e
  rw [ev_ev czZ cz12]
  refine Eq.trans ?_ e
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ, ev_X h1, ev_zero' h1]

theorem main : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ b : Fin d, ∃ K : PS R 2 d, ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) * pderiv k ((1 : Fin 2), j) h =
    FB.toK k K + ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h)) := by
  intro R _ d O _ _ k _ _ _ B h hc b
  have hA : ∀ c, constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) c) = 0 :=
    fun c => constantCoeff_ev cz12 ((lawK k B).const c)
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph2 (constantCoeff_second_factor B) _ hH0 hc.ph2 ((2 : Fin 3), b)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have t1 : pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 2] h)) =
      ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)) =
      ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) *
        pderiv k ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt k d 0, pt k d 1, 0]
        ((![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) i c)) =
        fun i => pt k (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis (lawK k B) c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.FK k j) b
  rw [map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3] at h2
  obtain ⟨K, hK⟩ := RingHom.mem_range.1 h2
  refine ⟨-K, ?_⟩
  rw [FB.toK, map_neg, hK]
  ring

end GlobalTheory.GaugeSecondDeriv
end
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeGermIntegral

variable {K : Type} [Field K]

def intRing (V : VF K) : Subring K where
  carrier := {a | V.Ge 0 a}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem intS_iff (V : VF K) {σ : Type} (f : MvPowerSeries σ K) :
    IntS V f ↔ f ∈ Ig (intRing V) K σ := by
  constructor
  · intro h
    exact ig_of_intAA fun n => ⟨⟨_, h n⟩, rfl⟩
  · intro h n
    obtain ⟨r, hr⟩ := intAA_of_ig h n
    rw [← hr]
    exact r.2

theorem map_self {σ : Type} (f : MvPowerSeries σ K) :
    MvPowerSeries.map (algebraMap K K) f = f := by
  ext n
  simp [coeff_map]

variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

omit [CharZero K] in
theorem FK_self (B : FB K d O) : B.FK K = B.G.F := funext fun _ => map_self _

open GlobalTheory.GaugeSecondDeriv in

theorem second_deriv (B : FB K d O) (h : PS K 2 d) (hc : B.IsCanonGauge K h) (b : Fin d) :
    ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) -
        ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b) B.ph2) := by
  have hA : ∀ c, constantCoeff (addOf B.G.F (pt K (n := 3) d 1) (pt K d 2) c) = 0 :=
    fun c => constantCoeff_ev LogPf.cz12 (B.G.const c)
  have c02 : CZ (![pt K (n := 3) d 0, pt K d 2] : Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
      Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt K d 0, pt K d 1] h +
      ev (n := 3) ![pt K d 0, pt K d 2] h -
      ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hE := hc.ph2
  rw [FB.toK, map_self, FK_self] at hE
  have hH := pderiv_expS hH0 ((2 : Fin 3), b)
  rw [← hE] at hH
  have t1 : pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt K d 0, pt K d 1, 0]
      (pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 2] h)) =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b)
      (ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h)) =
      ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt K d 0, pt K d 1, 0]
        ((![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
          Fin 2 → Pt K 3 d) i c)) = fun i => pt K (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis B.G c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.G.F j) b
  rw [hH, ev_mul czZ, B.cocycleRight_zero_thd, one_mul, map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3]
  ring

variable {V : VF K}

theorem ev_sgP (Y : FBChart K V O d) (v : Fin d → K) {n : ℕ} (a : Pt K n d)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    ev ![a] (Y.sgP v) = ∑ i, C (v i) * ev ![a] (sgOf K Y.h i) := by
  have h1 : CZ (![a] : Fin 1 → Pt K n d) := CZ.cons ha CZ.nil
  rw [FBChart.sgP, ev_neg h1, ev_sum h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : sgOf K Y.h i = -ev (n := 1) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), i) Y.h) := rfl
  rw [ev_mul h1, ev_C h1, e, ev_neg h1, mul_neg]

omit [CharZero K] in
theorem int_comb (v : Fin d → K) (hv : ∀ i, V.Ge 0 (v i)) (f : PS K 3 d) (hf : IntS V f) :
    (∑ i, C (v i) * ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), i) f)) ∈
      Ig (intRing V) K (Fin 2 × Fin d) :=
  sum_mem fun i _ => mul_mem (ig_C (R := intRing V) ⟨v i, hv i⟩)
    (ig_ev czZ integral_family_pair_zero (ig_pderiv ((intS_iff V f).1 hf) _))

theorem cocycle_integral (Y : FBChart K V O d) : GermISt Y := by
  intro v hv
  have hadd : addOf Y.B.G.F (pt K (n := 2) d 0) (pt K d 1) = Y.B.G.F := by
    funext i
    have e : (![pt K (n := 2) d 0, pt K d 1] : Fin 2 → Pt K 2 d) = fun j => pt K d j := by
      funext j
      fin_cases j <;> rfl
    rw [addOf, e, ev_pt]
  rw [intS_iff, hadd, ev_sgP Y v _ Y.B.G.const, ev_sgP Y v _ (cc_pt 0), ev_sgP Y v _ (cc_pt 1),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  convert int_comb v hv _ Y.intPh1 using 2 with i
  have e := GlobalTheory.SigmaDefect.sgOf_defect Y.B Y.h Y.gauge i
  rw [FB.toK, map_self, FK_self] at e
  rw [e]
  ring

theorem invariant_deriv_integral (Y : FBChart K V O d) : GermIISt Y := by
  intro v hv
  rw [intS_iff, ev_sgP Y v _ (cc_pt 0)]
  convert neg_mem (int_comb v hv _ Y.intPh2) using 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := second_deriv Y.B Y.h Y.gauge i
  rw [GlobalTheory.SigmaDefect.ev_sgOf _ _ _ (cc_pt 0)]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, e]
  ring

theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), GermISt Y ∧ GermIISt Y :=
  fun _ _ _ _ _ _ _ _ Y => ⟨cocycle_integral Y, invariant_deriv_integral Y⟩

end GlobalTheory.GaugeGermIntegral
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace GlobalTheory.CurveJet

def cob {k : Type} [CommRing k] {dd : ℕ} (F : Fin dd → PS k 2 dd) (b : PS k 1 dd) : PS k 2 dd :=
  ev (n := 2) ![addOf F (pt k dd 0) (pt k dd 1)] b - ev (n := 2) ![pt k dd 0] b - ev (n := 2) ![pt k dd 1] b

variable {C : Type} [Field C] {dd m : ℕ}

def inT (σ : Type) (f : PowerSeries C) : MvPowerSeries (Option σ) C :=
  MvPowerSeries.subst (fun _ : Unit => (X none : MvPowerSeries (Option σ) C)) f

def cvPt (γ : Fin dd → PowerSeries C) (m : ℕ) (p : Fin (m + 1) × Fin dd) :
    MvPowerSeries (Option (Fin m × Fin dd)) C :=
  Fin.cases (motive := fun _ => MvPowerSeries (Option (Fin m × Fin dd)) C) (inT _ (γ p.2))
    (fun j => X (some (j, p.2))) p.1

theorem cvPt_zero (γ : Fin dd → PowerSeries C) (i : Fin dd) : cvPt γ m (0, i) = inT _ (γ i) := rfl

theorem cvPt_succ (γ : Fin dd → PowerSeries C) (j : Fin m) (i : Fin dd) :
    cvPt γ m (j.succ, i) = X (some (j, i)) := rfl

theorem inT_eq_rename (σ : Type) (f : PowerSeries C) :
    inT σ f = rename (fun _ : Unit => (none : Option σ)) f := by
  rw [inT, rename_eq_subst]
  rfl

theorem constantCoeff_inT (σ : Type) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (inT σ f) = 0 := by
  rw [inT_eq_rename, constantCoeff_rename]
  exact hf

theorem cvPt_const {γ : Fin dd → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (p : Fin (m + 1) × Fin dd) : constantCoeff (cvPt γ m p) = 0 := by
  obtain ⟨j, i⟩ := p
  induction j using Fin.cases with
  | zero => rw [cvPt_zero]; exact constantCoeff_inT _ (hγ i)
  | succ j => rw [cvPt_succ]; exact constantCoeff_X _

theorem optionEquivLeft_inT (σ : Type) (f : PowerSeries C) :
    optionEquivLeft σ C (inT σ f) = PowerSeries.map (MvPowerSeries.C : C →+* MvPowerSeries σ C) f := by
  classical
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_map, coeff_C, inT_eq_rename]
  split_ifs with hμ
  · subst hμ
    let e : Unit ↪ Option σ := ⟨fun _ => none, fun _ _ _ => rfl⟩
    have he : Finsupp.optionElim n (0 : σ →₀ ℕ) = Finsupp.embDomain e (Finsupp.single () n) := by
      rw [Finsupp.embDomain_single, Finsupp.optionElim_zero]
      rfl
    rw [he]
    exact coeff_embDomain_rename e f (Finsupp.single () n)
  · apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hμ
    ext s
    have h1 : Finsupp.mapDomain (fun _ : Unit => (none : Option σ)) y (some s) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_some] at h1
    simpa using h1

theorem optionEquivLeft_rename_some {σ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    optionEquivLeft σ C (rename (some : σ → Option σ) f) = PowerSeries.C f := by
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    have he : Finsupp.optionElim 0 μ = Finsupp.embDomain (Function.Embedding.some) μ := by
      ext t
      cases t <;> simp
    rw [he]
    exact coeff_embDomain_rename _ f μ
  · rw [map_zero]
    apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hn
    have h1 : Finsupp.mapDomain (some : σ → Option σ) y none = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_none] at h1
    exact h1

theorem pderiv_coeff_optionEquivLeft {σ : Type} (f : MvPowerSeries (Option σ) C) (n : ℕ) (s : σ) :
    pderiv C s (PowerSeries.coeff n (optionEquivLeft σ C f)) =
      PowerSeries.coeff n (optionEquivLeft σ C (pderiv C (some s) f)) := by
  classical
  ext μ
  rw [coeff_pderiv, coeff_coeff_optionEquivLeft, coeff_coeff_optionEquivLeft, coeff_pderiv]
  have key : Finsupp.optionElim n (μ + Finsupp.single s 1) =
      Finsupp.optionElim n μ + Finsupp.single (some s) 1 := by
    ext t
    cases t <;> simp [Finsupp.single_apply]
  rw [key, Finsupp.optionElim_apply_some]

def jetHom {γ : Fin dd → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (m : ℕ) :
    PS C (m + 1) dd →ₐ[C] PowerSeries (PS C m dd) :=
  (optionEquivLeft (Fin m × Fin dd) C).toAlgHom.comp
    (substAlgHom (hasSubst_of_constantCoeff_zero (cvPt_const (m := m) hγ)))

end GlobalTheory.CurveJet
end
end
