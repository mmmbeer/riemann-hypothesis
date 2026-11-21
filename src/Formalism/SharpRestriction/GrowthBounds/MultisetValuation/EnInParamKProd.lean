import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AuxUOfFirstTheoremPlaceBound
import Mathlib
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen

open Finset

def fac {σ : Type} (κ : σ →₀ ℕ) : ℕ := ∏ x ∈ κ.support, (κ x).factorial

def jp {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A) (f : MvPowerSeries σ K) : A :=
  ∑ κ ∈ P.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • MvPolynomial.coeff κ P

theorem jp_eq_sum {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A)
    (f : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jp P f = ∑ κ ∈ S, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • MvPolynomial.coeff κ P := by
  unfold jp
  refine Finset.sum_subset hS ?_
  intro κ _ hκ
  have h0 : MvPolynomial.coeff κ P = 0 := by simpa [MvPolynomial.mem_support_iff] using hκ
  rw [h0, smul_zero]

section Alg

variable {K Pl : Type} [CommRing K] {ι : Pl → Type}

def atP (v : Pl) (f : MvPowerSeries (ι v) K) : MvPowerSeries (Σ v, ι v) K :=
  MvPowerSeries.rename (Function.Embedding.sigmaMk v) f

variable [Fintype Pl]

abbrev eqv : ((Σ v, ι v) →₀ ℕ) ≃+ (∀ v, ι v →₀ ℕ) := Finsupp.sigmaFinsuppAddEquivPiFinsupp

variable [DecidableEq Pl]

theorem eqv_embDomain (v : Pl) (m : ι v →₀ ℕ) :
    eqv (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) = Pi.single v m := by
  funext w
  ext i
  rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
  by_cases h : w = v
  · subst h
    rw [Pi.single_eq_same]
    exact Finsupp.embDomain_apply_self (Function.Embedding.sigmaMk w) m i
  · rw [Pi.single_eq_of_ne h, Finsupp.coe_zero, Pi.zero_apply, Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩
    exact h (congrArg Sigma.fst hj).symm

theorem coeff_atP_single (v : Pl) (f : MvPowerSeries (ι v) K) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff (eqv.symm (Pi.single v m)) (atP v f) = MvPowerSeries.coeff m f := by
  have h : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  rw [h]
  exact MvPowerSeries.coeff_embDomain_rename _ _ _

theorem coeff_atP_eq_zero (v : Pl) (f : MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ)
    (h : ∀ m, n ≠ eqv.symm (Pi.single v m)) : MvPowerSeries.coeff n (atP v f) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨u, hu⟩
  refine h u ?_
  rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
  exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)

theorem coeff_prod_atP (g : ∀ v, MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPowerSeries.coeff n (∏ v, atP v (g v)) = ∏ v, MvPowerSeries.coeff (eqv n v) (g v) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  let l0 : Pl →₀ ((Σ v, ι v) →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm fun v => eqv.symm (Pi.single v (eqv n v))
  have hl0 : ∀ v, l0 v = eqv.symm (Pi.single v (eqv n v)) := fun v => rfl
  have hmem : l0 ∈ Finset.finsuppAntidiag Finset.univ n := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    calc ∑ v ∈ Finset.univ, l0 v = ∑ v, eqv.symm (Pi.single v (eqv n v)) :=
          Finset.sum_congr rfl fun v _ => hl0 v
      _ = n := by rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]
  rw [Finset.sum_eq_single_of_mem l0 hmem]
  · exact Finset.prod_congr rfl fun v _ => by rw [hl0]; exact coeff_atP_single v (g v) (eqv n v)
  · intro l hl hne
    rw [Finset.mem_finsuppAntidiag] at hl
    by_contra hprod
    apply hne
    have hall : ∀ v, ∃ m, l v = eqv.symm (Pi.single v m) := by
      intro v
      by_contra hv
      push_neg at hv
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ v) (coeff_atP_eq_zero v (g v) (l v) hv))
    choose m hm using hall
    have hn : n = eqv.symm m := by
      rw [← hl.1]
      calc ∑ v ∈ Finset.univ, l v = ∑ v, eqv.symm (Pi.single v (m v)) :=
            Finset.sum_congr rfl fun v _ => hm v
        _ = eqv.symm m := by rw [← map_sum, Finset.univ_sum_single]
    ext1 v
    rw [hm v, hl0, hn, AddEquiv.apply_symm_apply]

private theorem coe_rename_sigma_mk_eq_atP (v : Pl) (p : MvPolynomial (ι v) K) :
    ((MvPolynomial.rename (Sigma.mk v) p : MvPolynomial (Σ v, ι v) K) : MvPowerSeries (Σ v, ι v) K) =
      atP v (p : MvPowerSeries (ι v) K) := by
  ext d
  rw [MvPolynomial.coeff_coe]
  by_cases h : ∃ m, d = eqv.symm (Pi.single v m)
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_atP_single, MvPolynomial.coeff_coe]
    have h2 : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
      rw [AddEquiv.symm_apply_eq, eqv_embDomain]
    rw [h2]
    exact MvPolynomial.coeff_rename_embDomain (Function.Embedding.sigmaMk v) p m
  · push_neg at h
    rw [coeff_atP_eq_zero v _ d h]
    apply MvPolynomial.coeff_rename_eq_zero
    intro u hu
    exfalso
    refine h u ?_
    rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
    exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)

theorem coeff_prod_rename (P : ∀ v, MvPolynomial (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPolynomial.coeff n (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) =
      ∏ v, MvPolynomial.coeff (eqv n v) (P v) := by
  have h1 : ((∏ v, MvPolynomial.rename (Sigma.mk v) (P v) : MvPolynomial (Σ v, ι v) K) :
      MvPowerSeries (Σ v, ι v) K) = ∏ v, atP v (P v : MvPowerSeries (ι v) K) := by
    rw [← Finset.prod_congr rfl fun v _ => coe_rename_sigma_mk_eq_atP v (P v)]
    exact map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (R := K)) _ _
  rw [← MvPolynomial.coeff_coe, h1, coeff_prod_atP]
  simp only [MvPolynomial.coeff_coe]

theorem fac_eq [∀ v, Fintype (ι v)] (n : (Σ v, ι v) →₀ ℕ) : fac n = ∏ v, fac (eqv n v) := by
  classical
  have h1 : ∀ {τ : Type} [Fintype τ] (m : τ →₀ ℕ), fac m = ∏ x, (m x).factorial := by
    intro τ _ m
    unfold fac
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have h0 : m x = 0 := by simpa using hx
    rw [h0, Nat.factorial_zero]
  rw [h1, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [h1]
  exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]

end Alg

theorem jp_prod {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] [Fintype Pl] [DecidableEq Pl] {ι : Pl → Type}
    [∀ v, Fintype (ι v)] (P : ∀ v, MvPolynomial (ι v) A) (g : ∀ v, MvPowerSeries (ι v) K) :
    jp (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) (∏ v, atP v (g v)) = ∏ v, jp (P v) (g v) := by
  classical
  have hsub : (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)).support ⊆
      (Fintype.piFinset fun v => (P v).support).image eqv.symm := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, coeff_prod_rename] at hn
    rw [Finset.mem_image]
    refine ⟨eqv n, ?_, AddEquiv.symm_apply_apply _ _⟩
    rw [Fintype.mem_piFinset]
    intro v
    rw [MvPolynomial.mem_support_iff]
    exact fun h0 => hn (Finset.prod_eq_zero (Finset.mem_univ v) h0)
  rw [jp_eq_sum _ _ _ hsub, Finset.sum_image (fun x _ y _ h => eqv.symm.injective h)]
  unfold jp
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_prod_atP, coeff_prod_rename, fac_eq]
  simp only [AddEquiv.apply_symm_apply, Algebra.smul_def, Nat.cast_prod, map_mul, map_prod,
    Finset.prod_mul_distrib]

end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen

open Finset

section Supp

variable {R σ Pl : Type} [CommRing R]

def SuppOn (π : σ → Pl) (v : Pl) : Subring (MvPowerSeries σ R) where
  carrier := {f | ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v}
  mul_mem' := by
    classical
    intro f g hf hg m hm x hx
    rw [MvPowerSeries.coeff_mul] at hm
    obtain ⟨ab, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [← hab] at hx
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    · exact hf _ (left_ne_zero_of_mul hne) x h
    · exact hg _ (right_ne_zero_of_mul hne) x h
  one_mem' := by
    classical
    intro m hm x hx
    rw [MvPowerSeries.coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp at hx
    · exact absurd rfl hm
  add_mem' := by
    intro f g hf hg m hm x hx
    rw [map_add] at hm
    by_cases h : MvPowerSeries.coeff m f = 0
    · rw [h, zero_add] at hm; exact hg m hm x hx
    · exact hf m h x hx
  zero_mem' := by
    intro m hm
    exact absurd (map_zero _) hm
  neg_mem' := by
    intro f hf m hm x hx
    rw [map_neg, neg_ne_zero] at hm
    exact hf m hm x hx

theorem mem_SuppOn {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R} :
    f ∈ SuppOn π v ↔ ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v := Iff.rfl

theorem X_mem {π : σ → Pl} {v : Pl} {x : σ} (h : π x = v) : (MvPowerSeries.X x : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_X] at hm
  split_ifs at hm with hmx
  · subst hmx
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
    rw [hy]
    exact h
  · exact absurd rfl hm

theorem C_mem {π : σ → Pl} {v : Pl} (c : R) : (MvPowerSeries.C c : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0
    simp at hy
  · exact absurd rfl hm

theorem subst_mem {τ : Type} {π : σ → Pl} {π' : τ → Pl} {v : Pl} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {f : MvPowerSeries σ R} (hf : f ∈ SuppOn π v)
    (h : ∀ s, π s = v → a s ∈ SuppOn π' v) : MvPowerSeries.subst a f ∈ SuppOn π' v := by
  classical
  intro e he x hx
  rw [MvPowerSeries.coeff_subst ha] at he
  by_contra hxv
  apply he
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : MvPowerSeries.coeff d f = 0
  · rw [hd, zero_smul]
  · have hprod : (d.prod fun s n => a s ^ n) ∈ SuppOn π' v := by
      unfold Finsupp.prod
      exact Subring.prod_mem _ fun s hs => Subring.pow_mem _ (h s ((mem_SuppOn.mp hf) d hd s hs)) _
    have h0 : MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) = 0 := by
      by_contra hne
      exact hxv ((mem_SuppOn.mp hprod) e hne x hx)
    rw [h0, smul_zero]

theorem map_mem {R' : Type} [CommRing R'] (φ : R →+* R') {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R}
    (hf : f ∈ SuppOn π v) : MvPowerSeries.map φ f ∈ SuppOn π v := by
  intro m hm x hx
  rw [MvPowerSeries.coeff_map] at hm
  exact (mem_SuppOn.mp hf) m (fun h0 => hm (by rw [h0, map_zero])) x hx

end Supp

def resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) : MvPowerSeries (ι v) R :=
  fun m => MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f

theorem coeff_resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff m (resP v f) = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f := rfl

theorem eq_atP {R Pl : Type} [CommRing R] {ι : Pl → Type} [Fintype Pl] [DecidableEq Pl] (v : Pl)
    (f : MvPowerSeries (Σ v, ι v) R) (hf : f ∈ SuppOn (Sigma.fst : (Σ v, ι v) → Pl) v) :
    f = atP v (resP v f) := by
  classical
  ext n
  have h2 : ∀ m : ι v →₀ ℕ, (eqv (ι := ι)).symm (Pi.single v m) =
      Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    intro m
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  by_cases hn : MvPowerSeries.coeff n f = 0
  · rw [hn]
    by_cases h : ∃ m, n = eqv.symm (Pi.single v m)
    · obtain ⟨m, rfl⟩ := h
      rw [coeff_atP_single, coeff_resP, ← h2]
      exact hn.symm
    · push_neg at h
      exact (coeff_atP_eq_zero v _ n h).symm
  · have hsupp := (mem_SuppOn.mp hf) n hn
    have hn' : n = eqv.symm (Pi.single v (eqv n v)) := by
      rw [AddEquiv.eq_symm_apply]
      funext w
      ext i
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hw, Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
        by_contra hne
        exact hw (hsupp ⟨w, i⟩ (Finsupp.mem_support_iff.mpr hne))
    calc MvPowerSeries.coeff n f
        = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) (eqv n v)) f := by
          rw [← h2, ← hn']
      _ = MvPowerSeries.coeff n (atP v (resP v f)) := by
          rw [← coeff_resP, ← coeff_atP_single v (resP v f) (eqv n v), ← hn']

theorem jp_subst_expand {K A σ τ : Type} [CommRing K] [CommRing A] [Algebra K A] (Q : MvPolynomial σ A)
    (F : MvPowerSeries σ K) (a : τ → MvPowerSeries σ K) (ha : MvPowerSeries.HasSubst a) (U : MvPowerSeries τ K) :
    ∃ B : Finset (τ →₀ ℕ), jp Q (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U • jp Q (F * β.prod fun s e => a s ^ e) := by
  classical
  refine ⟨Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset, ?_⟩
  set B := Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset with hB
  have hq : ∀ κ ∈ Q.support, ∀ pq ∈ Finset.HasAntidiagonal.antidiagonal κ,
      MvPowerSeries.coeff pq.2 (MvPowerSeries.subst a U) =
        ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff pq.2 (β.prod fun s e => a s ^ e) := by
    intro κ hκ pq hpq
    rw [MvPowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset (s := B)]
    · simp only [smul_eq_mul]
    · intro β hβ
      rw [Finset.mem_coe, hB, Finset.mem_biUnion]
      exact ⟨κ, hκ, Finset.mem_biUnion.mpr ⟨pq, hpq,
        (MvPowerSeries.coeff_subst_finite ha U pq.2).mem_toFinset.mpr hβ⟩⟩
  have hκ : ∀ κ ∈ Q.support, MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e) := by
    intro κ hκ
    rw [MvPowerSeries.coeff_mul]
    simp_rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pq hpq => ?_
    rw [hq κ hκ pq hpq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  unfold jp
  have hL : ∑ κ ∈ Q.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U)) •
        MvPolynomial.coeff κ Q =
      ∑ κ ∈ Q.support, ∑ β ∈ B, (((fac κ : ℕ) : K) * (MvPowerSeries.coeff β U *
        MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e))) • MvPolynomial.coeff κ Q := by
    refine Finset.sum_congr rfl fun κ hκ' => ?_
    rw [hκ κ hκ', Finset.mul_sum, Finset.sum_smul]
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [smul_smul]
  congr 1
  ring

end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem en_p_mem : (p : Y.Kc) ∈ Y.Oc := by
  exact natCast_mem Y.Oc p

theorem en_ppow_mem (N : ℤ) (hN : 0 ≤ N) : (p : Y.Kc) ^ N ∈ Y.Oc := by
  lift N to ℕ using hN
  rw [zpow_natCast]
  exact Y.Oc.pow_mem (en_p_mem Y) _

theorem en_root (z : Y.Kc) (M : ℕ) (hM : 0 < M) (h : z ^ M ∈ Y.Oc) : z ∈ Y.Oc := by
  rcases Y.Oc_val z with hz | hz
  · exact hz
  · by_cases h0 : z = 0
    · rw [h0]
      exact Y.Oc.zero_mem
    · have e : z = z ^ M * (z⁻¹) ^ (M - 1) := by
        rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ h0), ← pow_succ']
        congr 1
        omega
      rw [e]
      exact Y.Oc.mul_mem h (Y.Oc.pow_mem hz _)

theorem en_geC_one : Y.geC 1 0 := by
  intro a b hb hab
  rw [one_pow, one_mul]
  have h' : (a : ℝ) ≤ 0 := by linarith
  have h'' : a ≤ 0 := by exact_mod_cast h'
  exact en_ppow_mem Y (-a) (by omega)

theorem en_geC_mul_rat {x y : Y.Kc} (q1 q2 : ℚ) (hx : Y.geC x q1) (hy : Y.geC y q2) :
    Y.geC (x * y) ((q1 + q2 : ℚ) : ℝ) := by
  intro a b hb hab
  have hp := pKc_ne Y
  have hM0 : 0 < q1.den * q2.den := Nat.mul_pos q1.den_pos q2.den_pos
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℤ, (a1 : ℝ) = (q1 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q1.num * q2.den * b, ?_⟩
    have hd : (q1.den : ℝ) ≠ 0 := by exact_mod_cast q1.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℤ, (a2 : ℝ) = (q2 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q2.num * q1.den * b, ?_⟩
    have hd : (q2.den : ℝ) ≠ 0 := by exact_mod_cast q2.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hx' := hx a1 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha1.le
  have hy' := hy a2 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha2.le
  have hle : a * ((q1.den * q2.den : ℕ) : ℤ) ≤ a1 + a2 := by
    have h' : ((a * ((q1.den * q2.den : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((a1 + a2 : ℤ) : ℝ) := by
      push_cast
      rw [ha1, ha2]
      push_cast at hab ⊢
      have hM' : (0 : ℝ) ≤ (q1.den : ℝ) * q2.den := by positivity
      nlinarith
    exact_mod_cast h'
  have key : ((x * y) ^ b * (p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
      (x ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a1)) * (y ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a2)) *
        (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
    have h1 : ((p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
        (p : Y.Kc) ^ (-a1) * (p : Y.Kc) ^ (-a2) * (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp, ← zpow_add₀ hp]
      congr 1
      push_cast
      ring
    rw [mul_pow, h1]
    ring
  apply en_root Y _ (q1.den * q2.den) hM0
  rw [key]
  exact Y.Oc.mul_mem (Y.Oc.mul_mem hx' hy') (en_ppow_mem Y _ (by omega))

theorem en_geC_sum {α : Type} (s : Finset α) (f : α → Y.Kc) (g : ℝ) (h : ∀ i ∈ s, Y.geC (f i) g) :
    Y.geC (∑ i ∈ s, f i) g := by
  exact Finset.sum_induction f (fun x => Y.geC x g) (fun _ _ ha hb => geC_add Y ha hb) (geC_zero Y g) h

def geP {τ : Type} (a : MvPolynomial τ Y.Kc) (g : ℝ) : Prop := ∀ n, Y.geC (MvPolynomial.coeff n a) g

theorem valuation_coeff_one_nonneg {τ : Type} : geP Y (1 : MvPolynomial τ Y.Kc) 0 := by
  classical
  intro n
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact en_geC_one Y
  · exact geC_zero Y 0

theorem valuation_coeff_ge_mul_rat {τ : Type} {a b : MvPolynomial τ Y.Kc} (q1 q2 : ℚ) (ha : geP Y a q1) (hb : geP Y b q2) :
    geP Y (a * b) ((q1 + q2 : ℚ) : ℝ) := by
  classical
  intro n
  rw [MvPolynomial.coeff_mul]
  exact en_geC_sum Y _ _ _ fun x _ => en_geC_mul_rat Y q1 q2 (ha x.1) (hb x.2)

theorem valuation_coeff_ge_prod_rat {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (q : α → ℚ)
    (h : ∀ i ∈ s, geP Y (a i) (q i)) : geP Y (∏ i ∈ s, a i) ((∑ i ∈ s, q i : ℚ) : ℝ) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using valuation_coeff_one_nonneg Y (τ := τ)
  · intro i t hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact valuation_coeff_ge_mul_rat Y _ _ (h i (Finset.mem_insert_self i t))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem valuation_coeff_ge_sum {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (g : ℝ) (h : ∀ i ∈ s, geP Y (a i) g) :
    geP Y (∑ i ∈ s, a i) g := by
  intro n
  rw [MvPolynomial.coeff_sum]
  exact en_geC_sum Y _ _ _ fun i hi => h i hi n

theorem valuation_coeff_ge_smul {τ : Type} {a : MvPolynomial τ Y.Kc} {g : ℝ} {c : Y.Kc} (hc : c ∈ Y.Oc) (h : geP Y a g) :
    geP Y (c • a) g := by
  intro n
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact geC_mul_Oc Y (h n) hc

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

namespace Gen

theorem fac_embDomain {σ τ : Type} (e : σ ↪ τ) (κ : σ →₀ ℕ) : fac (Finsupp.embDomain e κ) = fac κ := by
  classical
  unfold fac
  rw [Finsupp.support_embDomain, Finset.prod_map]
  simp [Finsupp.embDomain_apply]

theorem jp_rename {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] {ι : Pl → Type} (v : Pl)
    (P : MvPolynomial (ι v) A) (g : MvPowerSeries (ι v) K) :
    jp (MvPolynomial.rename (Sigma.mk v) P) (atP v g) = jp P g := by
  classical
  have hinj : Function.Injective (Sigma.mk v : ι v → Σ v, ι v) := sigma_mk_injective
  unfold jp atP
  rw [MvPolynomial.support_rename_of_injective hinj,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hinj h)]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have he : Finsupp.mapDomain (Sigma.mk v) κ = Finsupp.embDomain (Function.Embedding.sigmaMk v) κ :=
    by rw [Finsupp.embDomain_eq_mapDomain]; rfl
  rw [MvPolynomial.coeff_rename_mapDomain _ hinj, he, fac_embDomain, MvPowerSeries.coeff_embDomain_rename]

end Gen

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def en_mapP (Kc σ τ : Type) [Field Kc] :
    MvPolynomial σ (MvPolynomial τ ℤ) →+* MvPolynomial σ (MvPolynomial τ Kc) :=
  MvPolynomial.map (MvPolynomial.map (Int.castRingHom Kc))

theorem en_applyD_eq {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    applyD P f = Gen.jp (en_mapP Kc σ τ P) f := by
  classical
  unfold applyD Gen.jp en_mapP
  symm
  refine (Finset.sum_subset (MvPolynomial.support_map_subset _ P) ?_).trans ?_
  · intro n _ hn
    simp only [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn, smul_zero]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.coeff_map]
    unfold Gen.fac
    push_cast
    rfl

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_Ploc (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (MvPolynomial (X.FrI j) Y.Kc) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (X.FrI j) Y.Kc)) ^ (X.colExp j I i0 v s c) *
    Matrix.det (Matrix.of fun (i i' : Fin (X.colHt v (j + 1) s c)) =>
      ∑ a : Fin (NN X.G.P.m X.t j),
        MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
          MvPolynomial.X ((s, a, I v s c i'.val) :
            Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))))

theorem en_mapP_PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    en_mapP Y.Kc (X.ZA j) (X.FrI j) (PIvS X j I i0 v) =
      MvPolynomial.rename (Sigma.mk v) (en_Ploc X Y j I i0 v) := by
  unfold en_mapP PIvS en_Ploc Sys.colFac
  simp only [map_prod, map_mul, map_pow, map_natCast, RingHom.map_det, AlgHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 2
  ext i i'
  simp [Matrix.of_apply, map_sum, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section LogInv

variable (p : ℕ) [Fact p.Prime] (K1 : Type) [Field K1] [Algebra (K0 p) K1]

def en_L : PowerSeries K1 := PowerSeries.map (algebraMap (K0 p) K1) (logF p)

theorem en_logF_zero : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp [hp.ne']

theorem en_logF_one : PowerSeries.coeff 1 (logF p) = 1 := by
  rw [logF, PowerSeries.coeff_mk]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h1 : (1 : ℕ) ≠ p ^ (2 * 1) := by
    have : 1 < p ^ (2 * 1) := Nat.one_lt_pow (by norm_num) hp
    omega
  rw [if_neg h1]
  simp

theorem en_L_zero : PowerSeries.constantCoeff (en_L p K1) = 0 := by
  rw [en_L, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, en_logF_zero, map_zero]

theorem en_L_one : IsUnit (PowerSeries.coeff 1 (en_L p K1)) := by
  rw [en_L, PowerSeries.coeff_map, en_logF_one, map_one]
  exact isUnit_one

def en_E : PowerSeries K1 := (en_L p K1).substInvOfIsUnit (en_L_one p K1)

theorem en_E_zero : PowerSeries.constantCoeff (en_E p K1) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

variable {ι : Type}

def en_aL (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_L p K1)

def en_Ec (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_E p K1)

theorem en_inParamK_eq (f : MvPowerSeries ι K1) : inParamK p K1 f = MvPowerSeries.subst (en_aL p K1) f := rfl

theorem en_aL_zero (i : ι) : MvPowerSeries.constantCoeff (en_aL p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_L_zero p K1)

theorem en_Ec_zero (i : ι) : MvPowerSeries.constantCoeff (en_Ec p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_E_zero p K1)

variable [Finite ι]

theorem en_aL_hs : MvPowerSeries.HasSubst (en_aL p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_aL_zero p K1)

theorem en_Ec_hs : MvPowerSeries.HasSubst (en_Ec p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_Ec_zero p K1)

theorem en_aL_Ec (i : ι) : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) =
      PowerSeries.subst (en_aL p K1 i) (en_E p K1) := by
    unfold en_Ec PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_aL_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_aL_hs p K1)]
  rw [h1, en_aL, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_L_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_left _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_aL (i : ι) : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) =
      PowerSeries.subst (en_Ec p K1 i) (en_L p K1) := by
    unfold en_aL PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_Ec_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_Ec_hs p K1)]
  rw [h1, en_Ec, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_E_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_right _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_inParamK (U : MvPowerSeries ι K1) : MvPowerSeries.subst (en_Ec p K1) (inParamK p K1 U) = U := by
  rw [en_inParamK_eq, MvPowerSeries.subst_comp_subst_apply (en_aL_hs p K1) (en_Ec_hs p K1)]
  simp only [en_Ec_aL]
  rw [MvPowerSeries.subst_self]
  rfl

theorem en_inParamK_Ec (i : ι) : inParamK p K1 (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) :=
  en_aL_Ec p K1 i

theorem en_inParamK_mul (f g : MvPowerSeries ι K1) : inParamK p K1 (f * g) = inParamK p K1 f * inParamK p K1 g :=
  MvPowerSeries.subst_mul (en_aL_hs p K1) f g

theorem en_inParamK_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K1) :
    inParamK p K1 (∏ i ∈ s, f i) = ∏ i ∈ s, inParamK p K1 (f i) := by
  simp only [en_inParamK_eq, ← MvPowerSeries.coe_substAlgHom (en_aL_hs p K1), map_prod]

theorem en_inParamK_pow (f : MvPowerSeries ι K1) (n : ℕ) : inParamK p K1 (f ^ n) = inParamK p K1 f ^ n :=
  MvPowerSeries.subst_pow (en_aL_hs p K1) f n

theorem en_Ec_supp {Pl : Type} (π : ι → Pl) (i : ι) : en_Ec p K1 i ∈ Gen.SuppOn (R := K1) π (π i) := by
  unfold en_Ec PowerSeries.subst
  exact Gen.subst_mem (π := fun _ : Unit => π i) (PowerSeries.HasSubst.X i).const (fun _ _ _ _ => rfl)
    (fun _ _ => Gen.X_mem rfl)

end LogInv

theorem en_expS_supp {p : ℕ} [Fact p.Prime] {ι Pl : Type} (π : ι → Pl) (v : Pl) {f : MvPowerSeries ι (K0 p)}
    (hf : f ∈ Gen.SuppOn π v) : expS p f ∈ Gen.SuppOn π v := by
  intro n hn
  have e : MvPowerSeries.coeff n (expS p f) =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k) := rfl
  rw [e] at hn
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact (Subring.pow_mem _ hf k) n (right_ne_zero_of_mul hk)

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_pi (j : ℕ) : X.EA j ⊕ X.EA j → X.Pl := Sum.elim Sigma.fst Sigma.fst

theorem en_coordZA_zero (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem en_coordZA_hs (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) : MvPowerSeries.HasSubst (X.coordZA K' j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_coordZA_zero X K' j)

theorem en_coordZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    X.coordZA K' j x ∈ Gen.SuppOn (R := K') (Sigma.fst : X.ZA j → X.Pl) (en_pi X j x) := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)

theorem en_ThZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (v : X.Pl)
    {f : MvPowerSeries (X.EA j ⊕ X.EA j) K'} (hf : f ∈ Gen.SuppOn (en_pi X j) v) :
    X.ThZA K' j f ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v :=
  Gen.subst_mem (en_coordZA_hs X K' j) hf fun s hs => hs ▸ en_coordZA_supp X K' j s

theorem en_ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (en_coordZA_hs X K' j) f g

theorem en_ThZA_prod (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) {α : Type} (s : Finset α)
    (f : α → MvPowerSeries (X.EA j ⊕ X.EA j) K') : X.ThZA K' j (∏ i ∈ s, f i) = ∏ i ∈ s, X.ThZA K' j (f i) := by
  unfold Sys.ThZA
  simp only [← MvPowerSeries.coe_substAlgHom (en_coordZA_hs X K' j), map_prod]

theorem en_ThZA_pow (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f : MvPowerSeries (X.EA j ⊕ X.EA j) K')
    (n : ℕ) : X.ThZA K' j (f ^ n) = X.ThZA K' j f ^ n :=
  MvPowerSeries.subst_pow (en_coordZA_hs X K' j) f n

def en_F (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc :=
  MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))

theorem en_PhAt_supp (j : ℕ) (v : X.Pl) : Y.PhAt j v ∈ Gen.SuppOn (en_pi X j) v := by
  unfold Pend.PhAt
  refine Subring.sum_mem _ fun e _ => ?_
  unfold sub2
  refine Gen.subst_mem (π := fun _ : Fin 2 => v) MvPowerSeries.HasSubst.X_X (fun _ _ _ _ => rfl) fun s _ => ?_
  fin_cases s
  · exact Gen.X_mem rfl
  · exact Gen.X_mem rfl

theorem en_F_supp (j : ℕ) (v : X.Pl) : en_F X Y j v ∈ Gen.SuppOn (en_pi X j) v :=
  Gen.map_mem _ (en_expS_supp _ v (Subring.neg_mem _ (en_PhAt_supp X Y j v)))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
