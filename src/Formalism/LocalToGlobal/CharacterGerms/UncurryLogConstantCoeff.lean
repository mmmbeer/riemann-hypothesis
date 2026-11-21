import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace GeneralGermZero

open Formalism.IncomingBounds FormalGermZero

variable {C : Type} [Field C] {κ : Type} [Fintype κ]

def addK {σ : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (a b : κ → MvPowerSeries σ C) : κ → MvPowerSeries σ C :=
  fun k => MvPowerSeries.subst (fun q : Fin 2 × κ => ![a, b] q.1 q.2) (F k)

def gsumK {σ ι : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (Γ : ι → κ → MvPowerSeries σ C) :
    List ι → κ → MvPowerSeries σ C
  | [] => 0
  | c :: l => addK F (Γ c) (gsumK F Γ l)


theorem pairK_const {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ q : Fin 2 × κ, MvPowerSeries.constantCoeff (![a, b] q.1 q.2) = 0 := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

theorem pairK_int {V : VF C} {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × κ, IntS V (![a, b] q.1 q.2) := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

def LgAdd (F : κ → MvPowerSeries (Fin 2 × κ) C) (lg : κ → MvPowerSeries κ C) : Prop :=
  ∀ k, MvPowerSeries.subst F (lg k) =
    MvPowerSeries.subst (fun q : κ => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) (lg k) +
      MvPowerSeries.subst (fun q : κ => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) (lg k)

theorem lg_addK {σ : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
    (lg : κ → MvPowerSeries κ C) (hadd : LgAdd F lg) (a b : κ → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (k : κ) :
    MvPowerSeries.subst (addK F a b) (lg k) = MvPowerSeries.subst a (lg k) + MvPowerSeries.subst b (lg k) := by
  have hP : MvPowerSeries.HasSubst (fun q : Fin 2 × κ => ![a, b] q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (pairK_const ha hb)
  have hF : MvPowerSeries.HasSubst F := MvPowerSeries.hasSubst_of_constantCoeff_zero hF0
  have hX0 : MvPowerSeries.HasSubst
      (fun q : κ => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hX1 : MvPowerSeries.HasSubst
      (fun q : κ => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have e := congrArg (MvPowerSeries.subst (fun q : Fin 2 × κ => ![a, b] q.1 q.2)) (hadd k)
  rw [MvPowerSeries.subst_comp_subst_apply hF hP, MvPowerSeries.subst_add hP,
    MvPowerSeries.subst_comp_subst_apply hX0 hP, MvPowerSeries.subst_comp_subst_apply hX1 hP] at e
  simp only [MvPowerSeries.subst_X hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
  exact e

section Sum

variable {F : κ → MvPowerSeries (Fin 2 × κ) C} (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
include hF0

theorem gsumK_const {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) :
    ∀ (l : List ι) j, MvPowerSeries.constantCoeff (gsumK F Γ l j) = 0
  | [], j => by
    show MvPowerSeries.constantCoeff ((0 : κ → MvPowerSeries σ C) j) = 0
    simp
  | c :: l, j => constantCoeff_subst_zero (pairK_const (hΓ c) (gsumK_const Γ hΓ l)) (hF0 j)

theorem gsumK_int {V : VF C} (hFI : ∀ k, IntS V (F k)) {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (hΓ : ∀ c j, IntS V (Γ c j)) :
    ∀ (l : List ι) j, IntS V (gsumK F Γ l j)
  | [], j => by
    intro μ
    show V.Ge 0 (MvPowerSeries.coeff μ ((0 : κ → MvPowerSeries σ C) j))
    rw [Pi.zero_apply, map_zero]
    exact VF.Ge.zero 0
  | c :: l, j => IntS.subst (pairK_const (hΓ0 c) (gsumK_const hF0 Γ hΓ0 l))
      (pairK_int (hΓ c) (gsumK_int hFI Γ hΓ0 hΓ l)) (hFI j)

theorem gsumK_lg {lg : κ → MvPowerSeries κ C} (hadd : LgAdd F lg) (hlg0 : ∀ k, MvPowerSeries.constantCoeff (lg k) = 0)
    {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (i : κ) :
    ∀ l : List ι, MvPowerSeries.subst (gsumK F Γ l) (lg i) = (l.map fun c => MvPowerSeries.subst (Γ c) (lg i)).sum
  | [] => by
    rw [List.map_nil, List.sum_nil]
    exact subst_zero_of_const _ (hlg0 i)
  | c :: l => by
    rw [List.map_cons, List.sum_cons, ← gsumK_lg hadd hlg0 Γ hΓ i l]
    exact lg_addK F hF0 lg hadd (Γ c) (gsumK F Γ l) (hΓ c) (gsumK_const hF0 Γ hΓ l) i

end Sum

section Sys1

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
  (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
  (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
  (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
  (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))

include hF0 hFI hadd hlin hexlg

theorem sysK_P {g : Fin 2} (hg : X.CartHyp V g) (S : Sys (RawChart.cart hg)) :
    ∃ P : κ → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hlg0 : ∀ k, MvPowerSeries.constantCoeff (X.lg k) = 0 := fun k => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin k 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hcur : ∀ c, ∃ γ : κ → PowerSeries C, IsCv V γ ∧ ∀ i, MvPowerSeries.subst γ (X.lg i) =
      ∑ c' : I g, X.u g c' i • tyS V.l (fun s => S.al c s c') := by
    intro c
    have hm : S.cur c ∈ X.TySet V g := (S.curve c).1
    obtain ⟨γ, lam, hγ, -, hlog, -⟩ := hm
    exact ⟨γ, hγ, hlog⟩
  choose γ hγ hlog using hcur
  have hγ0 : ∀ c, ∀ j, MvPowerSeries.constantCoeff (γ c j) = 0 := fun c j => (hγ c j).1
  have hXc : ∀ c : I g, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) :=
    fun c => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X c
  set Γ : I g → κ → MvPowerSeries (I g) C :=
    fun c j => PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (γ c j) with hΓdef
  have hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0 := fun c j =>
    constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X c) (hγ0 c j)
  have hΓI : ∀ c j, IntS V (Γ c j) := fun c j =>
    IntS.subst (fun _ => MvPowerSeries.constantCoeff_X c) (fun _ => intS_X c) (intS_ps.2 (hγ c j).2)
  have hΓlg : ∀ c i, MvPowerSeries.subst (Γ c) (X.lg i) =
      ∑ c', X.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c')) := by
    intro c i
    have e1 : MvPowerSeries.subst (Γ c) (X.lg i) =
        PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (MvPowerSeries.subst (γ c) (X.lg i)) := by
      show _ = MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) _
      rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 c)) (hXc c)]
      rfl
    rw [e1, hlog c i, ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X c)), map_sum]
    simp only [map_smul]
  set P : κ → MvPowerSeries (I g) C := gsumK F Γ Finset.univ.toList with hPdef
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := gsumK_const hF0 Γ hΓ0 _
  have hPlg : ∀ i, MvPowerSeries.subst P (X.lg i) =
      ∑ c, ∑ c', X.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C)
        (tyS V.l (fun s => S.al c s c')) := by
    intro i
    rw [gsumK_lg hF0 hadd hlg0 Γ hΓ0 i, Finset.sum_map_toList]
    exact Finset.sum_congr rfl fun c _ => hΓlg c i
  refine ⟨P, hP0, gsumK_int hF0 hFI Γ hΓ0 hΓI _, ?_, ?_⟩
  · intro j c
    have hl1 := coeff_single_subst_lin P hP0 (X.lg j) j (hlin j) c
    rw [← hl1, hPlg j, map_sum]
    simp only [map_sum, MvPowerSeries.coeff_smul, coeff_single_substX_tyS hl, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    exact congrFun (S.curve c).2.1 (Sum.inl c')
  · intro t ht j
    have ht0 := ht.1
    have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
    set Q : κ → MvPowerSeries (I g) C := fun j => MvPowerSeries.subst t (P j) with hQ
    have hQ0 : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := fun j => constantCoeff_subst_zero ht0 (hP0 j)
    have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    have hQlg : ∀ i, MvPowerSeries.subst Q (X.lg i) =
        ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
      intro i
      have e1 : MvPowerSeries.subst Q (X.lg i) = MvPowerSeries.subst t (MvPowerSeries.subst P (X.lg i)) := by
        rw [MvPowerSeries.subst_comp_subst_apply hPS hts]
      have e2 : ∀ c (A : PowerSeries C), MvPowerSeries.subst t
          (PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) A) = PowerSeries.subst (t c) A := by
        intro c A
        show MvPowerSeries.subst t (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) A) =
          MvPowerSeries.subst (fun _ : Unit => t c) A
        rw [MvPowerSeries.subst_comp_subst_apply (hXc c) hts]
        congr 1
        funext u
        rw [MvPowerSeries.subst_X hts]
      rw [e1, hPlg i, ← MvPowerSeries.coe_substAlgHom hts, map_sum]
      simp only [map_sum, map_smul, MvPowerSeries.coe_substAlgHom hts, e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.smul_sum, isT_sum S ht c']
    have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
    have hQS := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    have h := congrArg (MvPowerSeries.subst Q) (hexlg j)
    rw [MvPowerSeries.subst_comp_subst_apply hlgS hQS, MvPowerSeries.subst_X hQS] at h
    show Q j = _
    rw [← h]
    congr 1
    funext i
    exact hQlg i

private theorem v_sum_lemma {K : Type} [Field K] (w : AddValuation K (WithTop ℝ)) {ι : Type} (s : Finset ι)
    (x : ι → K) (hx : ∀ i ∈ s, (0 : WithTop ℝ) ≤ w (x i)) : (0 : WithTop ℝ) ≤ w (∑ i ∈ s, x i) :=
  Finset.sum_induction x (fun y => (0 : WithTop ℝ) ≤ w y) (fun a b ha hb => le_trans (le_min ha hb) (AddValuation.map_add w a b))
    (by
      show (0 : WithTop ℝ) ≤ w 0
      rw [AddValuation.map_zero]
      exact le_top) hx

theorem general_germ_zero
    (hsat : ∀ g, ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (H : ∀ g, X.CartHyp V g) : RawChart.IntegralGermIndependentOfSystem H := by
  intro S S₂ t t₂ hT hT₂
  choose w hw0 hw using hsat
  choose P hP0 hPI hPlin hPeq using fun g => sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S g)
  choose P₂ hP0₂ hPI₂ hPlin₂ hPeq₂ using fun g => sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S₂ g)
  refine AbstractGermZero.abstract_germ_zero V I t t₂ (fun g k => ∑ x, w g x k • P g x) (fun g k => ∑ x, w g x k • P₂ g x)
    (fun g c => (hT g).1 c) (fun g c => (hT₂ g).1 c) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g k
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
    simp [MvPowerSeries.coeff_smul, hP0]
  · intro g k μ
    show (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (∑ x, w g x k • P g x))
    rw [map_sum]
    refine v_sum_lemma X F hF0 hFI hadd hlin hexlg V.v _ _ (fun x _ => ?_)
    have h1 : (0 : WithTop ℝ) ≤ V.v (w g x k) := hw0 g x k
    have h2 : (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (P g x)) := hPI g x μ
    rw [MvPowerSeries.coeff_smul, AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro g
    have hm : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (∑ x, w g x k • P g x)) =
        (Matrix.of (S g).tan).transpose := by
      ext k c
      simp only [Matrix.of_apply, Matrix.transpose_apply, map_sum, MvPowerSeries.coeff_smul, hPlin, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hr : ∀ c' : I g, ∑ x, w g x k * (X.u g c' x * (S g).tan c c') =
          (∑ x, X.u g c' x * w g x k) * (S g).tan c c' := by
        intro c'
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      simp [hr, hw g]
    rw [hm, Matrix.det_transpose]
    exact (S g).unimod
  · intro g k
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
    simp [MvPowerSeries.coeff_smul, hP0₂]
  · intro g k μ
    show (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (∑ x, w g x k • P₂ g x))
    rw [map_sum]
    refine v_sum_lemma X F hF0 hFI hadd hlin hexlg V.v _ _ (fun x _ => ?_)
    have h1 : (0 : WithTop ℝ) ≤ V.v (w g x k) := hw0 g x k
    have h2 : (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (P₂ g x)) := hPI₂ g x μ
    rw [MvPowerSeries.coeff_smul, AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro g
    have hm : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (∑ x, w g x k • P₂ g x)) =
        (Matrix.of (S₂ g).tan).transpose := by
      ext k c
      simp only [Matrix.of_apply, Matrix.transpose_apply, map_sum, MvPowerSeries.coeff_smul, hPlin₂, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hr : ∀ c' : I g, ∑ x, w g x k * (X.u g c' x * (S₂ g).tan c c') =
          (∑ x, X.u g c' x * w g x k) * (S₂ g).tan c c' := by
        intro c'
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      simp [hr, hw g]
    rw [hm, Matrix.det_transpose]
    exact (S₂ g).unimod
  · intro g k
    have ht : MvPowerSeries.HasSubst (t g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hT g).1
    have ht₂ : MvPowerSeries.HasSubst (t₂ g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hT₂ g).1
    rw [← MvPowerSeries.coe_substAlgHom ht, ← MvPowerSeries.coe_substAlgHom ht₂]
    simp only [map_sum, map_smul]
    simp only [MvPowerSeries.coe_substAlgHom, hPeq g (t g) (hT g), hPeq₂ g (t₂ g) (hT₂ g)]

end Sys1

end GeneralGermZero

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace SelfConjugateGermZero

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem hasSubst_col (col : Fin 2) :
    MvPowerSeries.HasSubst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)

def lawS (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C :=
  MvPowerSeries.subst (fun q : Fin 2 × Fin dd =>
    (MvPowerSeries.X (q.1, (x.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (Y.B.G.F x.2)

theorem hasSubst_tau (col : Fin 2) : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
    (MvPowerSeries.X (q.1, (col, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)

theorem lawS_const (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (lawS Y x) = 0 := by
  unfold lawS
  rw [cc_subst_lemma (fun q : Fin 2 × Fin dd =>
    (MvPowerSeries.X (q.1, (x.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)]
  exact Y.B.G.const x.2

theorem lawS_int (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : IntS V (lawS Y x) := by
  unfold lawS
  rw [AbstractGermZero.intS_iff_alt]
  exact AltInv.intS_subst (v := V.v) (fun _ => by simp)
    (fun q => (AbstractGermZero.intS_iff_alt V _).mp (FormalGermZero.intS_X _)) ((AbstractGermZero.intS_iff_alt V _).mp (Y.intF x.2))

theorem uncurry_log_constantCoeff (Y : FBChart C V O dd) (j : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg j)) = 0 := by
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg j) = 0
  rw [Finsupp.mapDomain_zero, Y.lg_lin j 0 (by simp)]
  simp

private theorem prod_X_lemma {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]
    rfl
  · intro a b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]

private theorem un1_lift_lemma_2 (f : MvPowerSeries (Fin 1 × Fin dd) C) :
    MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      (un1 f) = f := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  have hμ : (μ.mapDomain Prod.snd).mapDomain (Prod.mk (0 : Fin 1)) = μ := by
    rw [← Finsupp.mapDomain_comp]
    have hc : (Prod.mk (0 : Fin 1) ∘ (Prod.snd : Fin 1 × Fin dd → Fin dd)) = id := by
      funext p
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [hc, Finsupp.mapDomain_id]
  rw [finsum_eq_single _ (μ.mapDomain Prod.snd)]
  · rw [if_pos hμ.symm, smul_eq_mul, mul_one]
    show MvPowerSeries.coeff ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x))) f = _
    rw [show (fun x : Fin dd => ((0 : Fin 1), x)) = Prod.mk (0 : Fin 1) from rfl, hμ]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h
    apply hd
    rw [h, ← Finsupp.mapDomain_comp,
      show (Prod.snd ∘ Prod.mk (0 : Fin 1) : Fin dd → Fin dd) = id from rfl, Finsupp.mapDomain_id]

private theorem ev1_lemma_3 {n : ℕ} (Q : Pt C n dd) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : PS C 1 dd) : ev ![Q] f = MvPowerSeries.subst Q (un1 f) := by
  have hA : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hB : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => (![Q] : Fin 1 → Pt C n dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨a, i⟩
      fin_cases a
      exact hQ i)
  unfold ev
  conv_lhs => rw [← un1_lift_lemma_2 f]
  rw [MvPowerSeries.subst_comp_subst_apply hA hB]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hB]
  rfl

theorem fb_add (Y : FBChart C V O dd) (j : Fin dd) :
    MvPowerSeries.subst Y.B.G.F (un1 (Y.lg j)) =
      MvPowerSeries.subst (fun q : Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun q : Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.lg j)) := by
  have hpt : ∀ k : Fin 2, ∀ i, MvPowerSeries.constantCoeff (pt C dd k i) = 0 := fun k i => by simp [pt]
  have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C dd 0) (pt C dd 1) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i)) = 0
    unfold ev
    rw [cc_subst_lemma _ (fun p => by
      rcases p with ⟨a, k⟩
      fin_cases a <;> simp [pt])]
    exact Y.B.G.const i
  have hF : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext i
    show ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i) = Y.B.G.F i
    have hX : (fun p : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) p.1 p.2) =
        MvPowerSeries.X := by
      funext p
      rcases p with ⟨a, k⟩
      fin_cases a <;> rfl
    unfold ev
    rw [hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]
    simp
  have e := Y.lg_add j
  rw [ev1_lemma_3 _ hadd, ev1_lemma_3 _ (hpt 0), ev1_lemma_3 _ (hpt 1), hF] at e
  exact e

variable {d : ℕ} {I0 : Type} [Fintype I0]

theorem lg_self (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) :
    (Y.rawSelf p).lg x = MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X (x.1, i) : MvPowerSeries (Fin 2 × Fin dd) C))
      (un1 (Y.lg x.2)) := rfl

theorem lgS_add (Y : FBChart C V O dd) (p : SelfData Y d I0) : LgAdd (lawS Y) (Y.rawSelf p).lg := by
  intro k
  have hL : MvPowerSeries.HasSubst (lawS Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero (lawS_const Y)
  have hc : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X (k.1, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := hasSubst_col k.1
  have hτ : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (k.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) := hasSubst_tau k.1
  have hF : MvPowerSeries.HasSubst Y.B.G.F := MvPowerSeries.hasSubst_of_constantCoeff_zero Y.B.G.const
  have hX0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 2 × Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)
  have hX1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 2 × Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)
  have hY0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C)) (fun _ => by simp)
  have hY1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C)) (fun _ => by simp)
  rw [lg_self Y p k, MvPowerSeries.subst_comp_subst_apply hc hL, MvPowerSeries.subst_comp_subst_apply hc hX0,
    MvPowerSeries.subst_comp_subst_apply hc hX1]
  simp only [MvPowerSeries.subst_X hL, MvPowerSeries.subst_X hX0, MvPowerSeries.subst_X hX1]
  rw [show (fun i : Fin dd => lawS Y (k.1, i)) = fun i => MvPowerSeries.subst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (k.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (Y.B.G.F i) from rfl,
    ← MvPowerSeries.subst_comp_subst_apply hF hτ, fb_add Y k.2, MvPowerSeries.subst_add hτ,
    MvPowerSeries.subst_comp_subst_apply hY0 hτ, MvPowerSeries.subst_comp_subst_apply hY1 hτ]
  simp only [MvPowerSeries.subst_X hτ]

private theorem deg_single_lemma_0 {τ : Type} (c : τ) (n : ℕ) : Finsupp.degree (Finsupp.single c n) = n := by
  first
  | exact Finsupp.degree_single c n
  | simp [Finsupp.degree_single]
  | simp [Finsupp.degree]
  | (classical
     unfold Finsupp.degree
     by_cases h : n = 0 <;> simp [h])

private theorem deg_zero_lemma_0 {τ : Type} (d : τ →₀ ℕ) (h : Finsupp.degree d = 0) : d = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff d).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h
  | simpa using h

private theorem deg_map_lemma_6 {α β : Type} (f : α → β) (μ : α →₀ ℕ) :
    Finsupp.degree (μ.mapDomain f) = Finsupp.degree μ := by
  classical
  refine Finsupp.induction μ ?_ ?_
  · simp
  · intro a b g _ _ ih
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single, deg_single_lemma_0, deg_single_lemma_0]

private theorem un1_lift_lemma_4 (h : MvPowerSeries (Fin dd) C) :
    un1 (MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      h) = h := by
  classical
  ext μ
  show MvPowerSeries.coeff (μ.mapDomain (Prod.mk (0 : Fin 1)))
    (MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) h) =
      MvPowerSeries.coeff μ h
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  rw [finsum_eq_single _ μ]
  · rw [if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h'
    exact hd (Finsupp.mapDomain_injective (Prod.mk_right_injective (0 : Fin 1)) h').symm

private theorem inner_lemma_5 (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j : Fin dd => un1 (Y.lg j)) (un1 (Y.ex i)) =
      (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  have hA : MvPowerSeries.HasSubst
      (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hU : MvPowerSeries.HasSubst (fun j : Fin dd => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (uncurry_log_constantCoeff Y)
  have hlg0 : ∀ j, MvPowerSeries.constantCoeff (Y.lg j) = 0 := fun j => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.lg_lin j 0 (by simp)]
    simp
  have e : ev (n := 1) ![Y.lg] (Y.ex i) = MvPowerSeries.X ((0 : Fin 1), i) := congrFun Y.ex_lg i
  rw [ev1_lemma_3 _ hlg0] at e
  have hL : ∀ g : MvPowerSeries (Fin dd) C,
      MvPowerSeries.subst (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C))
        (MvPowerSeries.subst (fun j : Fin dd => un1 (Y.lg j)) g) = MvPowerSeries.subst Y.lg g := fun g => by
    rw [MvPowerSeries.subst_comp_subst_apply hU hA]
    congr 1
    funext j
    exact un1_lift_lemma_2 (Y.lg j)
  rw [← un1_lift_lemma_4 (MvPowerSeries.subst (fun j : Fin dd => un1 (Y.lg j)) (un1 (Y.ex i))), hL, e,
    ← un1_lift_lemma_4 (MvPowerSeries.X i : MvPowerSeries (Fin dd) C), MvPowerSeries.subst_X hA]

theorem lgS_lin (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ)
    (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ ((Y.rawSelf p).lg x) = MvPowerSeries.coeff μ (MvPowerSeries.X x) := by
  classical
  have hdeg : μ.degree = 0 ∨ μ.degree = 1 := by omega
  rcases hdeg with h0 | h1
  · rw [deg_zero_lemma_0 μ h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lg_self Y p x, cc_subst_lemma _ (fun _ => by simp),
      uncurry_log_constantCoeff, MvPowerSeries.constantCoeff_X]
  · obtain ⟨c, rfl⟩ : ∃ c, μ = Finsupp.single c 1 := by
      have hne : μ ≠ 0 := by
        rintro rfl
        simp at h1
      obtain ⟨c, hc⟩ : ∃ c, μ c ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (Finsupp.ext h)
      refine ⟨c, ?_⟩
      have hle : Finsupp.single c 1 ≤ μ := by
        rw [Finsupp.single_le_iff]
        omega
      have hsplit : μ = Finsupp.single c 1 + (μ - Finsupp.single c 1) := (add_tsub_cancel_of_le hle).symm
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add, deg_single_lemma_0, h1] at h2
      have h3 : μ - Finsupp.single c 1 = 0 := deg_zero_lemma_0 _ (by omega)
      rw [h3, add_zero] at hsplit
      exact hsplit
    have hc : ∀ s : Fin dd, MvPowerSeries.constantCoeff
        ((MvPowerSeries.X (x.1, s) : MvPowerSeries (Fin 2 × Fin dd) C)) = 0 := fun _ => by simp
    rw [lg_self Y p x]
    refine (FormalGermZero.coeff_single_subst_lin _ hc (un1 (Y.lg x.2)) x.2 ?_ c).trans rfl
    intro μ' hμ'
    have hA : MvPowerSeries.HasSubst
        (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have hXL : (MvPowerSeries.X ((0 : Fin 1), x.2) : MvPowerSeries (Fin 1 × Fin dd) C) =
        MvPowerSeries.subst (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C))
          (MvPowerSeries.X x.2 : MvPowerSeries (Fin dd) C) := (MvPowerSeries.subst_X hA x.2).symm
    show MvPowerSeries.coeff (μ'.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg x.2) = _
    rw [Y.lg_lin x.2 _ (by rw [deg_map_lemma_6]; exact hμ'), hXL]
    exact congrArg (MvPowerSeries.coeff μ') (un1_lift_lemma_4 (MvPowerSeries.X x.2 : MvPowerSeries (Fin dd) C))

theorem exS_lg (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) :
    MvPowerSeries.subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (MvPowerSeries.X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  have hLg0 : ∀ y : Fin 2 × Fin dd, MvPowerSeries.constantCoeff ((Y.rawSelf p).lg y) = 0 := fun y => by
    rw [lg_self Y p y, cc_subst_lemma _ (fun _ => by simp)]
    exact uncurry_log_constantCoeff Y y.2
  have hLg : MvPowerSeries.HasSubst (Y.rawSelf p).lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hLg0
  have hc : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X (x.1, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := hasSubst_col x.1
  have hU : MvPowerSeries.HasSubst (fun i : Fin dd => un1 (Y.lg i)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (uncurry_log_constantCoeff Y)
  show MvPowerSeries.subst (Y.rawSelf p).lg (MvPowerSeries.subst
      (fun i : Fin dd => (MvPowerSeries.X (x.1, i) : MvPowerSeries (Fin 2 × Fin dd) C)) (un1 (Y.ex x.2))) =
    MvPowerSeries.X x
  rw [MvPowerSeries.subst_comp_subst_apply hc hLg]
  simp only [MvPowerSeries.subst_X hLg, lg_self Y p]
  rw [← MvPowerSeries.subst_comp_subst_apply hU hc, inner_lemma_5 Y x.2, MvPowerSeries.subst_X hc]

theorem gm_int (Y : FBChart C V O dd) (p : SelfData Y d I0) (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h1' := hM a r s
  simp only [Nat.cast_zero] at h1'
  have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm a r s - p.em a (M r s)) := h1'
  have h2 : (0 : WithTop ℝ) ≤ V.v (p.em a (M r s)) := p.em_int a (M r s)
  show (0 : WithTop ℝ) ≤ V.v (p.gm a r s)
  have h3 := le_trans (le_min h1 h2) (AddValuation.map_add V.v _ _)
  rwa [sub_add_cancel] at h3

theorem sat_self (Y : FBChart C V O dd) (p : SelfData Y d I0) (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  obtain ⟨w0, hw0, hsum⟩ := p.e_sat
  refine ⟨fun x c' => p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c', ?_, ?_⟩
  · intro x c'
    have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm (p.ty0 c' + p.hd) x.1 (g + 1)) := gm_int Y p _ _ _
    have h2 : (0 : WithTop ℝ) ≤ V.v (w0 x.2 c') := hw0 x.2 c'
    show (0 : WithTop ℝ) ≤ V.v (p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c')
    rw [AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro c c'
    have key : ∀ x : Fin 2 × Fin dd,
        (Y.rawSelf p).u g c x * (p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c') =
          (p.gm (p.ty0 c) x.1 g * p.gm (p.ty0 c' + p.hd) x.1 (g + 1)) * (p.e c x.2 * w0 x.2 c') := by
      intro x
      show p.gm (p.ty0 c) x.1 g * p.e c x.2 * (p.gm (p.ty0 c' + p.hd) x.1 (g + 1) * w0 x.2 c') = _
      ring
    simp only [key]
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hsum c c']
    split_ifs with hcc
    · subst hcc
      simp only [mul_one]
      have hh := p.gm_hyp (p.ty0 c) (g + 1) g
      rw [if_neg (by fin_cases g <;> decide)] at hh
      rw [← hh]
      exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
    · simp

theorem germ_zero_self_conjugate : GermZeroSelfConjugate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p H
  exact GeneralGermZero.general_germ_zero (Y.rawSelf p) (lawS Y) (fun x => lawS_const Y x) (fun x => lawS_int Y x) (lgS_add Y p)
    (fun x μ hμ => lgS_lin Y p x μ hμ) (fun x => exS_lg Y p x) (sat_self Y p) H

end SelfConjugateGermZero

end Formalism.L2.FormalSeriesBounds
end
end
