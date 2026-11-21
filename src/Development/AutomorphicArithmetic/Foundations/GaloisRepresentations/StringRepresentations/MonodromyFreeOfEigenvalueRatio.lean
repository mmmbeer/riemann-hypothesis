import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.ScalarOfCharpoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedRestriction

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.GalN

section Lin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem absSpace_disj {f : End ℂ V} {r r' : ℝ} {v : V} (h1 : v ∈ absSpace f r) (h2 : v ∈ absSpace f r') (hv : v ≠ 0) :
    r = r' := by
  by_contra hne
  have hd := (End.eigenspaces_iSupIndep f).disjoint_biSup_biSup (s := {α | ‖α‖ = r}) (t := {α | ‖α‖ = r'})
    (Set.disjoint_left.2 fun α a b => hne (a.symm.trans b))
  exact hv (Submodule.disjoint_def.1 hd v h1 h2)

theorem absSpace_smul {f : End ℂ V} {c : ℂ} (hc : c ≠ 0) {r : ℝ} {v : V} (hv : v ∈ absSpace (c • f) r) :
    v ∈ absSpace f (r / ‖c‖) := by
  refine (iSup₂_le fun α hα u hu => ?_ : absSpace (c • f) r ≤ absSpace f (r / ‖c‖)) hv
  refine Submodule.mem_iSup_of_mem (α / c) (Submodule.mem_iSup_of_mem (by rw [norm_div, hα]) ?_)
  rw [End.mem_eigenspace_iff] at hu ⊢
  rw [LinearMap.smul_apply] at hu
  rw [div_eq_inv_mul, mul_smul, ← hu, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def EV (a : WDRep h V) (χ : ↥(Ine (F := E) A) → ℂ) (v : V) : Prop := ∀ s, a.ρ (ineIncl h s) v = χ s • v

def Win (a : WDRep h V) (S : Set ℝ) : Prop :=
  ∀ χ, (∀ v, EV a χ v → a.N v = 0) → ∀ r v, EV a χ v → v ∈ absSpace (a.ρ (frob h)) r → v ≠ 0 → r ∈ S

theorem Win.iso {a : WDRep h V} {b : WDRep h V'} {S : Set ℝ} (e : a.Iso b) (hb : Win b S) : Win a S := by
  obtain ⟨e, e1, e2⟩ := e
  intro χ h0 r v hv hr hv0
  refine hb χ (fun u hu => ?_) r (e v) (fun s => by rw [← e1, hv s, map_smul])
    (map_absSpace_le e.toLinearMap (fun x => e1 _ x) r ⟨v, hr, rfl⟩) (e.map_ne_zero_iff.2 hv0)
  obtain ⟨u, rfl⟩ := e.surjective u
  rw [← e2, h0 u fun s => e.injective (by rw [e1, hu s, map_smul]), map_zero]

theorem Win.sum {a : WDRep h V} {b : WDRep h V'} {S : Set ℝ} (ha : Win a S) (hb : Win b S) : Win (a.sum b) S := by
  intro χ h0 r v hv hr hv0
  have hr' := (mem_absSpace_prodMap (a.ρ (frob h)) (b.ρ (frob h)) r v).1 hr
  by_cases h1 : v.1 = 0
  · refine hb χ (fun u hu => ?_) r v.2 (fun s => congrArg Prod.snd (hv s)) hr'.2 fun h2 => hv0 (Prod.ext h1 h2)
    exact congrArg Prod.snd (h0 (0, u) fun s => Prod.ext (by simp) (hu s))
  · refine ha χ (fun u hu => ?_) r v.1 (fun s => congrArg Prod.fst (hv s)) hr'.1 h1
    exact congrArg Prod.fst (h0 (u, 0) fun s => Prod.ext (hu s) (by simp))

theorem Win.mono {a : WDRep h V} {S T : Set ℝ} (ha : Win a S) (hS : S ⊆ T) : Win a T :=
  fun χ h0 r v hv hr hv0 => hS (ha χ h0 r v hv hr hv0)

theorem Win.tw {a : WDRep h V} {S : Set ℝ} (ha : Win a S) (s : ℝ) :
    Win (a.tw s) {r | r / ((normV w : ℕ) : ℝ) ^ s ∈ S} := by
  intro χ h0 r v hv hr hv0
  have e : ∀ u, EV (a.tw s) χ u ↔ EV a χ u := fun u => by simp [EV]
  have e2 : (a.tw s).ρ (frob h) = (qPow w s : ℂ) • a.ρ (frob h) := by simp [deg_frob]
  rw [e2] at hr
  have := ha χ (fun u hu => h0 u ((e u).2 hu)) _ v ((e v).1 hv) (absSpace_smul (qPow w s).ne_zero hr) hv0
  rwa [norm_qPow] at this

theorem abs_stable {n : ℕ} (a : WDRep h (Fin n → ℂ)) (σ : Weil h) {r : ℝ} (hr : 0 ≤ r) {v : Fin n → ℂ}
    (hv : v ∈ absSpace (a.ρ (frob h)) r) : a.ρ σ v ∈ absSpace (a.ρ (frob h)) r := by
  obtain ⟨m, hm, hc⟩ := GlobalTheory.IrrWeilAbs.exists_pow_central a (deg_frob (h := h))
  rw [← GlobalTheory.CompanionTheory.TempRes.absSpace_pow_eq (a.semisimple _) hr hm.ne', ← map_pow] at hv ⊢
  exact map_absSpace_le (a.ρ σ) (fun u => (LinearMap.congr_fun (hc σ) u).symm) _ ⟨v, hv, rfl⟩

theorem win_of_tempered {n : ℕ} {a : WDRep h (Fin n → ℂ)} (ht : a.Tempered) : Win a {1} := by
  intro χ h0 r v hv hr hv0
  have hp := ht (frob h) deg_frob
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, r = ((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2) := by
    by_contra hc
    push Not at hc
    have hd := (End.eigenspaces_iSupIndep (a.ρ (frob h))).disjoint_biSup_biSup (s := {α | ‖α‖ = r}) (t := {α | ‖α‖ = r}ᶜ)
      disjoint_compl_right
    have hle : (⨆ i : ℤ, absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2))) ≤
        ⨆ β ∈ ({α | ‖α‖ = r}ᶜ : Set ℂ), End.eigenspace (a.ρ (frob h)) β :=
      iSup_le fun i => iSup₂_le fun β hβ => le_iSup₂_of_le β (fun k => hc i (k.symm.trans hβ)) le_rfl
    rw [hp.1] at hle
    exact hv0 (Submodule.disjoint_def.1 hd v hr (hle Submodule.mem_top))
  have kill : ∀ (k : ℕ) u, EV a χ u → (a.N ^ (k + 1)) u = 0 := fun k u hu => by
    rw [pow_succ, End.mul_apply, h0 u hu, map_zero]
  have comm : ∀ (k : ℕ) (s : ↥(Ine (F := E) A)) u, a.ρ (ineIncl h s) ((a.N ^ k) u) = (a.N ^ k) (a.ρ (ineIncl h s) u) := by
    intro k s
    induction k with
    | zero => intro u; simp
    | succ k ih => intro u; rw [pow_succ', End.mul_apply, End.mul_apply, a.comm_apply, ih]; simp
  rcases i with (_ | k) | k
  · simp
  · exfalso
    obtain ⟨u, hu, e⟩ := (hp.2 (k + 1)).surjOn (show v ∈ _ from by simpa using hr)
    have hE : EV a χ u := fun s => by
      refine (hp.2 (k + 1)).injOn (abs_stable a _ (Real.rpow_nonneg (by positivity) _) hu) (Submodule.smul_mem _ _ hu) ?_
      show (a.N ^ (k + 1)) _ = (a.N ^ (k + 1)) _
      rw [← comm, map_smul, e, hv s]
    exact hv0 (e.symm.trans (kill k u hE))
  · exfalso
    refine hv0 ((hp.2 (k + 1)).injOn (show v ∈ _ from ?_) (Submodule.zero_mem _) ?_)
    · have e : ((Int.negSucc k : ℤ) : ℝ) / 2 = -((k + 1 : ℕ) : ℝ) / 2 := by rw [Int.cast_negSucc]
      rwa [e] at hr
    · show (a.N ^ (k + 1)) _ = (a.N ^ (k + 1)) _
      rw [kill k v hv, map_zero]


def Shape (y : WD h) : Prop :=
  ∃ L : List (WD h), (∀ z ∈ L, ∃ (t : WD h) (s : ℝ), t.tempered ∧ |s| < 1 / 2 ∧ z = t.lpTw s) ∧ y = sumList L

def window (w : HeightOneSpectrum (𝓞 E)) : Set ℝ :=
  Set.Ioo (((normV w : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) (((normV w : ℕ) : ℝ) ^ (1 / 2 : ℝ))

theorem Shape.win {y : WD h} (hy : Shape y) {a : WDRep h V} (e : WD.mk a = y) : Win a (window w) := by
  obtain ⟨L, hL, rfl⟩ := hy
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have key : ∀ L : List (WD h), (∀ z ∈ L, ∃ (t : WD h) (s : ℝ), t.tempered ∧ |s| < 1 / 2 ∧ z = t.lpTw s) →
      ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)), WD.mk b = sumList L ∧ Win b (window w) := by
    intro L
    induction L with
    | nil => exact fun _ => ⟨0, _, rfl, fun χ _ r v _ _ hv => absurd (Subsingleton.elim _ _) hv⟩
    | cons z L ih =>
      intro hL
      obtain ⟨n, b, eb, hb⟩ := ih fun z hz => hL z (List.mem_cons_of_mem _ hz)
      obtain ⟨t, s, ht, hs, rfl⟩ := hL z List.mem_cons_self
      obtain ⟨k, t, rfl⟩ := t.exists_rep
      obtain ⟨j, c, ec⟩ := (sumList ((WD.mk t).lpTw s :: L)).exists_rep
      refine ⟨j, c, ec, Win.iso (b := (t.tw s).sum b) (WD.mk_eq_mk.1 ?_) (Win.sum ?_ hb)⟩
      · rw [ec, ← WD.lpSum_mk, eb, ← WD.lpTw_mk]
        rfl
      · refine ((win_of_tempered ((WD.tempered_mk _).1 ht)).tw s).mono fun r hr => ?_
        have h1 : r = ((normV w : ℕ) : ℝ) ^ s := by
          have : r / ((normV w : ℕ) : ℝ) ^ s = 1 := hr
          exact (div_eq_one_iff_eq (Real.rpow_pos_of_pos (by linarith) s).ne').1 this
        rw [h1]
        exact ⟨Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).1, Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).2⟩
  obtain ⟨n, b, eb, hb⟩ := key L hL
  exact Win.iso (WD.mk_eq_mk.1 (e.trans eb.symm)) hb

theorem eig_sum (x y : WD h) (g : Weil h) : (x.lpSum y).eig g = x.eig g + y.eig g := by
  rw [WD.eig, WD.eig, WD.eig, WD.charPol_lpSum]
  exact Polynomial.roots_mul ((WD.charPol_monic x g).mul (WD.charPol_monic _ g)).ne_zero

theorem Shape.eig {y : WD h} (hy : Shape y) {φ : Weil h} (hφ : deg φ = 1) {α : ℂ} (hα : α ∈ y.eig φ) :
    ∃ (t : WD h) (s : ℝ) (β : ℂ), t.tempered ∧ |s| < 1 / 2 ∧ t.lpDim ≤ y.lpDim ∧ (y.mono0 → t.mono0) ∧ β ∈ t.eig φ ∧
      ‖α‖ = ‖β‖ * ((normV w : ℕ) : ℝ) ^ s := by
  obtain ⟨L, hL, rfl⟩ := hy
  induction L with
  | nil =>
    have := WD.card_eig (WD.lpZero h) φ
    rw [WD.lpDim_zero, Multiset.card_eq_zero] at this
    exact absurd (this ▸ hα : α ∈ (0 : Multiset ℂ)) (Multiset.notMem_zero _)
  | cons z L ih =>
    change α ∈ (z.lpSum (sumList L)).eig φ at hα
    change ∃ (t : WD h) (s : ℝ) (β : ℂ), _ ∧ _ ∧ _ ≤ (z.lpSum (sumList L)).lpDim ∧ ((z.lpSum (sumList L)).mono0 → _) ∧ _
    rw [eig_sum, Multiset.mem_add] at hα
    rw [WD.lpDim_sum, WD.monomial_sum_iff]
    rcases hα with hα | hα
    · obtain ⟨t, s, ht, hs, rfl⟩ := hL z List.mem_cons_self
      rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ] at hα
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hα
      exact ⟨t, s, β, ht, hs, by rw [WD.lpDim_tw]; omega, fun m => (WD.monomial_twist_iff _ _).1 m.1, hβ,
        by rw [norm_mul, ← coe_qPow, norm_qPow]⟩
    · obtain ⟨t, s, β, ht, hs, hd, hm, k⟩ := ih (fun z hz => hL z (List.mem_cons_of_mem _ hz)) hα
      exact ⟨t, s, β, ht, hs, by omega, fun m => hm m.2, k⟩

theorem norm_le_of_tempered {t : WD h} (ht : t.tempered) {φ : Weil h} (hφ : deg φ = 1) {β : ℂ} (hβ : β ∈ t.eig φ) :
    ((normV w : ℕ) : ℝ) ^ (-(((t.lpDim : ℝ) - 1) / 2)) ≤ ‖β‖ ∧ ‖β‖ ≤ ((normV w : ℕ) : ℝ) ^ (((t.lpDim : ℝ) - 1) / 2) ∧
      (t.mono0 → ‖β‖ = 1) := by
  induction t using WD.ind with
  | hP n b =>
    rw [WD.eig, WD.charPol_mk] at hβ
    rw [WD.tempered_mk] at ht
    rw [WD.lpDim_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    have hev : End.HasEigenvalue (b.ρ φ) β :=
      (End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr ((mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hβ)
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    have k := GlobalTheory.LocalInv.norm_le_of_isPurePair hq b.nilpotent (ht φ hφ) hev
    refine ⟨k.1, k.2, fun m => ?_⟩
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    exact absSpace_disj (Submodule.mem_iSup_of_mem β (Submodule.mem_iSup_of_mem rfl hv.1))
      (by rw [ht.norm_eq_one m hφ]; trivial) hv.2

theorem Shape.mem_window {y : WD h} (hy : Shape y) (hm : y.mono0) {φ : Weil h} (hφ : deg φ = 1) {α : ℂ}
    (hα : α ∈ y.eig φ) : ‖α‖ ∈ window w := by
  obtain ⟨t, s, β, ht, hs, -, hm', hβ, e⟩ := hy.eig hφ hα
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  rw [e, (norm_le_of_tempered ht hφ hβ).2.2 (hm' hm), one_mul]
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).1, Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).2⟩

theorem window_ratio {a b : ℝ} (ha : a ∈ window w) (hb : b ∈ window w) : a < ((normV w : ℕ) : ℝ) * b := by
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast zero_lt_one.trans (one_lt_normV w)
  refine ha.2.trans_le ?_
  have e : ((normV w : ℕ) : ℝ) ^ (1 / 2 : ℝ) = ((normV w : ℕ) : ℝ) * ((normV w : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + -(1 / 2) by norm_num, Real.rpow_add hq, Real.rpow_one]; norm_num
  rw [e]
  exact mul_le_mul_of_nonneg_left hb.1.le hq.le

theorem Shape.ratio {y : WD h} {c : ℝ} (hy : Shape (y.lpTw c)) (hm : y.mono0) {φ : Weil h} (hφ : deg φ = 1)
    {α β : ℂ} (hα : α ∈ y.eig φ) (hβ : β ∈ y.eig φ) : ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖ := by
  have k : ∀ γ ∈ y.eig φ, ‖γ‖ * ((normV w : ℕ) : ℝ) ^ c ∈ window w := fun γ hγ => by
    rw [← norm_qPow, ← norm_mul]
    refine hy.mem_window ((WD.monomial_twist_iff _ _).2 hm) hφ ?_
    rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ]
    exact Multiset.mem_map_of_mem _ hγ
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast zero_lt_one.trans (one_lt_normV w)
  have := window_ratio (k α hα) (k β hβ)
  rw [← mul_assoc] at this
  exact lt_of_mul_lt_mul_right this (Real.rpow_nonneg hq.le _)




end UpperTheory.GalN
