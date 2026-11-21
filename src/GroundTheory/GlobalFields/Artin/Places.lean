import Mathlib
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.TateCohomology.DoubleCosetSum
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff

section
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

open GroundTheory.LocalField

variable {G : Type*} [Group G]

section ExtendByZero

theorem mem_conj_smul_iff (H : Subgroup G) (a g : G) :
    g ∈ (MulAut.conj a • H : Subgroup G) ↔ a⁻¹ * g * a ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]

theorem mem_conj_inv_smul_iff (H : Subgroup G) (x g : G) :
    g ∈ (MulAut.conj x⁻¹ • H : Subgroup G) ↔ x * g * x⁻¹ ∈ H := by
  rw [mem_conj_smul_iff, inv_inv]

open Classical in

def extendByZero (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  if h : g ∈ H then f ⟨g, h⟩ else 0

theorem extendByZero_of_mem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∈ H) :
    extendByZero H f g = f ⟨g, hg⟩ := by
  unfold extendByZero
  rw [dif_pos hg]

theorem extendByZero_of_notMem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∉ H) :
    extendByZero H f g = 0 := by
  unfold extendByZero
  rw [dif_neg hg]

@[simp]
theorem extendByZero_coe (H : Subgroup G) (f : H → ℂ) (h : H) : extendByZero H f h = f h :=
  extendByZero_of_mem H f h.2

theorem extendByZero_conj {H : Subgroup G} {f : H → ℂ} (hf : IsClassFun f) {h : G} (hh : h ∈ H)
    (g : G) : extendByZero H f (h * g * h⁻¹) = extendByZero H f g := by
  by_cases hg : g ∈ H
  · have hm : h * g * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh)
    rw [extendByZero_of_mem H f hm, extendByZero_of_mem H f hg, ← hf ⟨g, hg⟩ ⟨h, hh⟩]
    rfl
  · have hm : h * g * h⁻¹ ∉ H := fun hm ↦ hg (by
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hm) hh
      simpa [mul_assoc] using this)
    rw [extendByZero_of_notMem H f hm, extendByZero_of_notMem H f hg]

theorem indFun_subtype_apply [Fintype G] (H : Subgroup G) [Fintype H] (f : H → ℂ) (s : G) :
    indFun H.subtype f s = (Nat.card H : ℂ)⁻¹ * ∑ t : G, extendByZero H f (t⁻¹ * s * t) := by
  classical
  rw [indFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases hm : t⁻¹ * s * t ∈ H
  · rw [extendByZero_of_mem H f hm, Finset.sum_eq_single ⟨_, hm⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (Subtype.ext hb')
    · simp
  · rw [extendByZero_of_notMem H f hm]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [if_neg]
    intro hb'
    exact hm (hb' ▸ b.2)

end ExtendByZero

section Count

variable [Fintype G]

open Classical in

theorem sum_mul_mul_eq (H D : Subgroup G) [Fintype H] [Fintype D] (x : G) (F : G → ℂ) :
    ∑ h : H, ∑ e : D, F (h * x * e) =
      (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) *
        ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
  classical
  set E : Subgroup D := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hEdef
  have hE : ∀ c : D, c ∈ E ↔ x * c * x⁻¹ ∈ H := fun c ↦ by
    rw [hEdef, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
  have hfib : ∀ u : G, (Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u)).card =
      if DoubleCoset.mk H D u = DoubleCoset.mk H D x then Nat.card E else 0 := by
    intro u
    split_ifs with hu
    · obtain ⟨h0, hh0, e0, he0, rfl⟩ := (DoubleCoset.eq H D x u).1 hu.symm
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      refine Finset.card_bij' (fun p _ ↦ ⟨⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩, ?_⟩)
        (fun c _ ↦ (⟨h0 * (x * ((c : D) : G) * x⁻¹), H.mul_mem hh0 ((hE c).1 c.2)⟩,
          ⟨((c : D) : G)⁻¹ * e0, D.mul_mem (D.inv_mem (c : D).2) he0⟩)) ?_ ?_ ?_ ?_
      · rename_i p hp
        rw [Finset.mem_filter] at hp
        rw [hE]
        have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
          rw [← hp.2]
          group
        have : x * (e0 * (p.2 : G)⁻¹) * x⁻¹ = h0⁻¹ * p.1 := by
          rw [hp1]
          group
        rw [show ((⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩ : D) : G) =
          e0 * (p.2 : G)⁻¹ from rfl, this]
        exact H.mul_mem (H.inv_mem hh0) p.1.2
      · intro p _
        exact Finset.mem_univ _
      · intro c _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        group
      · intro p hp
        rw [Finset.mem_filter] at hp
        ext
        · change h0 * (x * (e0 * (p.2 : G)⁻¹) * x⁻¹) = p.1
          have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
            rw [← hp.2]
            group
          rw [hp1]
          group
        · change (e0 * (p.2 : G)⁻¹)⁻¹ * e0 = p.2
          group
      · intro c _
        ext
        change e0 * (((c : D) : G)⁻¹ * e0)⁻¹ = ((c : D) : G)
        group
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hp
      apply hu
      exact ((DoubleCoset.eq H D x u).2 ⟨p.1, p.1.2, p.2, p.2.2, hp.symm⟩).symm
  calc ∑ h : H, ∑ e : D, F (h * x * e)
      = ∑ p : H × D, F ((p.1 : G) * x * p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ u : G, ∑ p ∈ Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u),
          F ((p.1 : G) * x * p.2) :=
        (Finset.sum_fiberwise Finset.univ (fun p : H × D ↦ (p.1 : G) * x * p.2) _).symm
    _ = ∑ u : G, (if DoubleCoset.mk H D u = DoubleCoset.mk H D x then (Nat.card E : ℂ) else 0) *
          F u := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const,
          nsmul_eq_mul, hfib u]
        split_ifs <;> simp
    _ = (Nat.card E : ℂ) *
          ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp

end Count

section Mackey

def conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) :
    (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D → ℂ :=
  fun d ↦ f ⟨x * ((d : D) : G) * x⁻¹,
    (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩

theorem extendByZero_conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) (y : D) :
    extendByZero _ (conjFun H D x f) y = extendByZero H f (x * y * x⁻¹) := by
  by_cases hy : y ∈ (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D
  · rw [extendByZero_of_mem _ _ hy, extendByZero_of_mem H f
      ((mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 hy))]
    rfl
  · have hy' : x * (y : G) * x⁻¹ ∉ H := fun h ↦
      hy (Subgroup.mem_subgroupOf.2 ((mem_conj_inv_smul_iff H x _).2 h))
    rw [extendByZero_of_notMem _ _ hy, extendByZero_of_notMem H f hy']

variable [Fintype G]

open Classical in

theorem indFun_comp_subtype_eq_sum (H D : Subgroup G) [Fintype H] [Fintype D] {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) :
    indFun H.subtype f ∘ D.subtype =
      ∑ q, indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype
        (conjFun H D (x q) f) := by
  classical
  funext d
  rw [Function.comp_apply, Finset.sum_apply, indFun_subtype_apply]
  simp_rw [indFun_subtype_apply, extendByZero_conjFun]
  have h1 : ∑ t : G, extendByZero H f (t⁻¹ * D.subtype d * t) =
      ∑ u : G, extendByZero H f (u * d * u⁻¹) :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun t ↦ by simp)
  rw [h1, ← Finset.sum_fiberwise Finset.univ (DoubleCoset.mk H D), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have key := sum_mul_mul_eq H D (x q) (fun u ↦ extendByZero H f (u * d * u⁻¹))
  rw [hx q] at key
  set E : Subgroup D := (MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D
  have hE0 : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : ∀ (h : H) (e : D), extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      extendByZero H f (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹) := by
    intro h e
    rw [← extendByZero_conj hf h.2 (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹)]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h3 : ∑ h : H, ∑ e : D, extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹) := by
    simp_rw [h2]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv D) _ _ (fun e ↦ by simp)
  rw [h3] at key
  have hS : ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = q),
      extendByZero H f (u * d * u⁻¹) = (Nat.card E : ℂ)⁻¹ *
        (Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹)) := by
    rw [key, inv_mul_cancel_left₀ hE0]
  rw [hS, mul_left_comm, inv_mul_cancel_left₀ hH0]

end Mackey

end GroundTheory.Global.Artin
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

open GroundTheory.LocalField

section Cyclic

variable {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] {g : Γ}

theorem mul_comm_of_zpowers_eq_top {Q : Type*} [Group Q] {c : Q} (h : Subgroup.zpowers c = ⊤)
    (a b : Q) : a * b = b * a := by
  have ha : a ∈ Subgroup.zpowers c := by rw [h]; exact Subgroup.mem_top a
  have hb : b ∈ Subgroup.zpowers c := by rw [h]; exact Subgroup.mem_top b
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact zpow_mul_comm c j k

theorem zpow_inv_mul_conj_mem (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤) (a : Γ) (m : ℤ) :
    (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ N := by
  rw [← QuotientGroup.eq]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  rw [mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N)⁻¹, inv_mul_cancel_right]

theorem normal_of_le_of_zpowers_eq_top (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) : K.Normal := ⟨fun n hn a ↦ by
  have h1 : a * n * a⁻¹ * n⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N) (n : Γ ⧸ N)]
    group
  have := K.mul_mem (hNK h1) hn
  simpa using this⟩

theorem zpow_mem_iff_index_dvd [Finite Γ] (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) (m : ℤ) : g ^ m ∈ K ↔ (K.index : ℤ) ∣ m := by
  have := normal_of_le_of_zpowers_eq_top hgen hNK
  have hgenK : ∀ y : Γ ⧸ K, y ∈ Subgroup.zpowers (g : Γ ⧸ K) := by
    intro y
    induction y using QuotientGroup.induction_on with | H d => ?_
    have hd : (d : Γ ⧸ N) ∈ Subgroup.zpowers (g : Γ ⧸ N) := by rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hd
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hj
    exact hNK hj
  rw [Subgroup.index_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers hgenK,
    orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]

end Cyclic

section Frobenius

variable {G : Type*} [Group G]

def frobIndex (H D I : Subgroup G) (x : G) : ℕ :=
  (I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).relIndex D

def cosetAvg {Γ : Type*} [Group Γ] (I : Subgroup Γ) [Fintype I] (φ : Γ) (F : Γ → ℂ) (m : ℤ) :
    ℂ :=
  (Nat.card I : ℂ)⁻¹ * ∑ i : I, F (φ ^ m * i)

variable {H D I : Subgroup G}

theorem inv_mul_mul_mem_of_normal (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] {t i : G}
    (ht : t ∈ D) (hi : i ∈ I) : t⁻¹ * i * t ∈ I := by
  have := hN.conj_mem ⟨i, hID hi⟩ (Subgroup.mem_subgroupOf.2 hi) (⟨t, ht⟩⁻¹)
  simpa using Subgroup.mem_subgroupOf.1 this

theorem zpow_inv_mul_conj_mem_of_le [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (m : ℤ) : (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t) ∈ I := by
  have := zpow_inv_mul_conj_mem hgen ⟨t, ht⟩ m
  simpa using Subgroup.mem_subgroupOf.1 this

theorem zpow_inv_mul_zpow_mem [(I.subgroupOf D).Normal] {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a⁻¹ * b ∈ I) (k : ℤ) : (a ^ k)⁻¹ * b ^ k ∈ I := by
  have h : ((⟨a, ha⟩ : D) : D ⧸ I.subgroupOf D) = ((⟨b, hb⟩ : D) : D ⧸ I.subgroupOf D) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hab
  have h2 : (((⟨a, ha⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D) =
      (((⟨b, hb⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D) := by
    rw [QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, h]
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem zpow_mem_iff_relIndex_dvd [Finite G] [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {K : Subgroup G}
    (hIK : I ≤ K) (m : ℤ) : φ ^ m ∈ K ↔ (K.relIndex D : ℤ) ∣ m := by
  have h := zpow_mem_iff_index_dvd hgen (K := K.subgroupOf D)
    (fun y hy ↦ Subgroup.mem_subgroupOf.2 (hIK (Subgroup.mem_subgroupOf.1 hy))) m
  rw [Subgroup.mem_subgroupOf] at h
  simpa [Subgroup.relIndex] using h

theorem sum_conj_eq_sum_subgroupOf (H I : Subgroup G) [Fintype I] (x : G)
    [Fintype ((MulAut.conj x • I : Subgroup G).subgroupOf H)] (F : G → ℂ)
    (hF : ∀ g ∉ H, F g = 0) :
    ∑ i : I, F (x * i * x⁻¹) =
      ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, F ((j : H) : G) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun i : I ↦ x * i * x⁻¹ ∈ H)
    (fun i _ hne ↦ by
      by_contra h
      exact hne (hF _ h))]
  refine Finset.sum_bij' (fun i hi ↦ ⟨⟨x * i * x⁻¹, (Finset.mem_filter.1 hi).2⟩, ?_⟩)
    (fun j _ ↦ ⟨x⁻¹ * ((j : H) : G) * x,
      (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 j.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rename_i i hi
    rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
    change x⁻¹ * (x * (i : G) * x⁻¹) * x ∈ I
    rw [show x⁻¹ * (x * (i : G) * x⁻¹) * x = i by group]
    exact i.2
  · intro i _
    exact Finset.mem_univ _
  · intro j _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ ∈ H
    rw [show x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H) by group]
    exact (j : H).2
  · intro i _
    apply Subtype.ext
    change x⁻¹ * (x * (i : G) * x⁻¹) * x = i
    group
  · intro j _
    apply Subtype.ext
    apply Subtype.ext
    change x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H)
    group
  · intro i _
    rfl

theorem sum_conj_coset [Fintype I] (hID : I ≤ D) [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (F : G → ℂ) (m : ℤ) :
    ∑ i : I, F (t⁻¹ * (φ ^ m * i) * t) = ∑ i : I, F (φ ^ m * i) := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t) := ⟨_, rfl⟩
  have hc : c ∈ I := hcdef ▸ zpow_inv_mul_conj_mem_of_le hφ hgen ht m
  let σ : I → I := fun i ↦ ⟨c * (t⁻¹ * i * t), I.mul_mem hc (inv_mul_mul_mem_of_normal hID ht i.2)⟩
  have hσ : Function.Injective σ := by
    intro i j hij
    have h1 : c * (t⁻¹ * (i : G) * t) = c * (t⁻¹ * (j : G) * t) := congrArg Subtype.val hij
    apply Subtype.ext
    simpa using h1
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hσ) _ _ fun i ↦ ?_
  congr 1
  change t⁻¹ * (φ ^ m * i) * t = φ ^ m * (c * (t⁻¹ * i * t))
  rw [hcdef]
  group

theorem card_mul_card_eq [Finite G] (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] (x : G) :
    Nat.card D * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
      frobIndex H D I x * Nat.card I *
        Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) := by
  set I' := I.subgroupOf D with hI'
  set E := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hE
  have hK : (I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf D = I' ⊔ E := by
    rw [Subgroup.subgroupOf_sup hID inf_le_right, Subgroup.inf_subgroupOf_right]
  have hr : frobIndex H D I x = (I' ⊔ E).index := by
    rw [frobIndex, Subgroup.relIndex, hK]
  have h1 : Nat.card D = Nat.card (I' ⊔ E : Subgroup D) * (I' ⊔ E).index :=
    (Subgroup.card_mul_index _).symm
  have h2 : Nat.card (I' ⊔ E : Subgroup D) = Nat.card I' * I'.relIndex E := by
    rw [← Subgroup.relIndex_sup_left, ← Subgroup.card_mul_index (I'.subgroupOf (I' ⊔ E)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : I' ≤ I' ⊔ E)).toEquiv]
    rfl
  have h3 : Nat.card E = Nat.card (I'.subgroupOf E) * I'.relIndex E :=
    (Subgroup.card_mul_index _).symm
  have h4 : Nat.card I' = Nat.card I := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hID).toEquiv
  have hw : ∀ w : (MulAut.conj x • I : Subgroup G).subgroupOf H, x⁻¹ * ((w : H) : G) * x ∈ I :=
    fun w ↦ (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 w.2)
  have h5 : Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
      Nat.card (I'.subgroupOf E) := by
    refine Nat.card_congr
      { toFun := fun w ↦ ⟨⟨⟨x⁻¹ * ((w : H) : G) * x, hID (hw w)⟩, ?_⟩, ?_⟩
        invFun := fun z ↦ ⟨⟨x * (((z : E) : D) : G) * x⁻¹, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rename_i w
      rw [hE, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
      change x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ ∈ H
      rw [show x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H) by group]
      exact (w : H).2
    · rename_i w
      rw [Subgroup.mem_subgroupOf, hI', Subgroup.mem_subgroupOf]
      exact hw w
    · rename_i z
      exact (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 (z : E).2)
    · rename_i z
      rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
      change x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x ∈ I
      rw [show x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D) by group]
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 z.2)
    · intro w
      apply Subtype.ext
      apply Subtype.ext
      change x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H)
      group
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      change x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D)
      group
  rw [h1, h2, h3, h4, h5, hr]
  ring

end Frobenius

section Formula

variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}

open Classical in

theorem cosetAvg_indFun_conjFun [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) (f : H → ℂ) (x : G)
    (φx : H) (hφx : ∃ i ∈ (MulAut.conj x • I : Subgroup G),
      (φx : G) = x * φ ^ (frobIndex H D I x : ℤ) * x⁻¹ * i) (m : ℤ) :
    (Nat.card I : ℂ)⁻¹ * ∑ i : I,
        indFun ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D x f)
          ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩ =
      if (frobIndex H D I x : ℤ) ∣ m then
        (frobIndex H D I x : ℂ) *
          cosetAvg ((MulAut.conj x • I : Subgroup G).subgroupOf H) φx f (m / frobIndex H D I x)
      else 0 := by
  classical
  set K : Subgroup G := I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D) with hK
  have hIK : I ≤ K := le_sup_left
  have hKr : ∀ n : ℤ, φ ^ n ∈ K ↔ (frobIndex H D I x : ℤ) ∣ n :=
    zpow_mem_iff_relIndex_dvd hφ hgen hIK
  simp_rw [indFun_subtype_apply, extendByZero_conjFun]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hA : ∀ t : D, ∑ i : I, extendByZero H f (x * ((t : G)⁻¹ * (φ ^ m * i) * t) * x⁻¹) =
      ∑ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹) := fun t ↦
    sum_conj_coset hID hφ hgen t.2 (fun g ↦ extendByZero H f (x * g * x⁻¹)) m
  simp_rw [hA]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hcount := card_mul_card_eq (H := H) hID x
  have hI0 : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE0 : (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hIx0 : (Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  split_ifs with hdiv
  · obtain ⟨k, hk⟩ := hdiv
    have hr0 : (frobIndex H D I x : ℤ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hk
      have h1 : (frobIndex H D I x : ℤ) ∣ 0 := dvd_zero _
      rw [← hKr, zpow_zero] at h1
      rw [Nat.cast_eq_zero] at h0
      have := (Subgroup.card_mul_index ((I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf
        D))
      rw [← Subgroup.relIndex, ← frobIndex, h0, mul_zero] at this
      exact Nat.card_pos.ne' this.symm
    rw [hk, Int.mul_ediv_cancel_left _ hr0]
    obtain ⟨i0, hi0, hφxeq⟩ := hφx
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = x⁻¹ * (φx : G) * x := ⟨_, rfl⟩
    have hj0 : (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ ∈ I := by
      rw [show (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ = x⁻¹ * i0 * x by rw [hψ, hφxeq]; group]
      exact (mem_conj_smul_iff I x i0).1 hi0
    have hψD : ψ ∈ D := by
      have := D.mul_mem (D.zpow_mem hφ (frobIndex H D I x : ℤ)) (hID hj0)
      simpa using this
    have hi1 : (ψ ^ k)⁻¹ * φ ^ ((frobIndex H D I x : ℤ) * k) ∈ I := by
      have h1 : ψ⁻¹ * φ ^ (frobIndex H D I x : ℤ) ∈ I := by simpa using I.inv_mem hj0
      have := zpow_inv_mul_zpow_mem hψD (D.zpow_mem hφ (frobIndex H D I x : ℤ)) h1 k
      rwa [← zpow_mul] at this
    have hψk : ψ ^ k = x⁻¹ * (φx : G) ^ k * x := by
      have := conj_zpow (i := k) (a := x⁻¹) (b := (φx : G))
      rw [inv_inv] at this
      rw [hψ, this]
    have hS : ∑ i : I, extendByZero H f (x * (φ ^ ((frobIndex H D I x : ℤ) * k) * i) * x⁻¹) =
        ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹) :=
      Fintype.sum_equiv (Equiv.mulLeft (⟨_, hi1⟩ : I)) _ _ fun i ↦ by
        congr 1
        simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
        group
    have hS2 : ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹) =
        ∑ i : I, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) (x * i * x⁻¹) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only
      rw [hψk]
      congr 1
      group
    have hF : ∀ g ∉ H, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) g = 0 := fun g hg ↦
      extendByZero_of_notMem H f fun hm ↦ hg (by
        have := H.mul_mem (H.inv_mem (H.zpow_mem φx.2 k)) hm
        simpa using this)
    have hS3 : ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H,
        (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) ((j : H) : G) =
        ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j) :=
      Finset.sum_congr rfl fun j _ ↦ by
        simp only
        rw [show (φx : G) ^ k * ((j : H) : G) = ((φx ^ k * (j : H) : H) : G) by simp,
          extendByZero_coe]
    rw [hS, hS2, sum_conj_eq_sum_subgroupOf H I x _ hF, hS3, cosetAvg]
    have hc : (Nat.card D : ℂ) * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
        frobIndex H D I x * Nat.card I *
          Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) := by
      exact_mod_cast hcount
    field_simp
    linear_combination (∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j)) * hc
  · have h0 : ∀ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹) = 0 := fun i ↦
      extendByZero_of_notMem H f fun hm ↦ hdiv ((hKr m).1 (by
        have h1 : φ ^ m * i ∈ K := Subgroup.mem_sup_right (Subgroup.mem_inf.2
          ⟨(mem_conj_inv_smul_iff H x _).2 hm, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩)
        have := K.mul_mem h1 (hIK (I.inv_mem i.2))
        simpa using this))
    simp [h0]

end Formula

section Main

variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}

open Classical in

theorem cosetAvg_indFun [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) (φx : DoubleCoset.Quotient (H : Set G) D → H)
    (hφx : ∀ q, ∃ i ∈ (MulAut.conj (x q) • I : Subgroup G),
      (φx q : G) = x q * φ ^ (frobIndex H D I (x q) : ℤ) * (x q)⁻¹ * i) (m : ℤ) :
    cosetAvg I φ (indFun H.subtype f) m =
      ∑ q, if (frobIndex H D I (x q) : ℤ) ∣ m then
        (frobIndex H D I (x q) : ℂ) *
          cosetAvg ((MulAut.conj (x q) • I : Subgroup G).subgroupOf H) (φx q) f
            (m / frobIndex H D I (x q))
      else 0 := by
  classical
  have hA : ∀ i : I, indFun H.subtype f (φ ^ m * i) = ∑ q,
      indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D (x q) f)
        ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩ := by
    intro i
    have := congrFun (indFun_comp_subtype_eq_sum H D hf x hx)
      ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩
    rw [Finset.sum_apply] at this
    exact this
  rw [cosetAvg]
  simp_rw [hA]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦
    cosetAvg_indFun_conjFun hID hφ hgen f (x q) (φx q) (hφx q) m

end Main

end GroundTheory.Global.Artin
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

variable {G : Type*} [Group G] {H D I : Subgroup G}

def dxToQuot (H D I : Subgroup G) [(I.subgroupOf D).Normal] (x : G) :
    (MulAut.conj x • D : Subgroup G).subgroupOf H →* D ⧸ I.subgroupOf D :=
  (QuotientGroup.mk' (I.subgroupOf D)).comp
    { toFun := fun d ↦ ⟨x⁻¹ * ((d : H) : G) * x,
        (mem_conj_smul_iff D x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩
      map_one' := by
        apply Subtype.ext
        change x⁻¹ * (1 : G) * x = 1
        group
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        change x⁻¹ * (((a : H) : G) * ((b : H) : G)) * x =
          (x⁻¹ * ((a : H) : G) * x) * (x⁻¹ * ((b : H) : G) * x)
        group }

theorem dxToQuot_apply [(I.subgroupOf D).Normal] (x : G)
    (d : (MulAut.conj x • D : Subgroup G).subgroupOf H) :
    dxToQuot H D I x d = ((⟨x⁻¹ * ((d : H) : G) * x,
      (mem_conj_smul_iff D x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩ : D) : D ⧸ I.subgroupOf D) :=
  rfl

theorem ker_dxToQuot [(I.subgroupOf D).Normal] (x : G) :
    (dxToQuot H D I x).ker = ((MulAut.conj x • I : Subgroup G).subgroupOf H).subgroupOf
      ((MulAut.conj x • D : Subgroup G).subgroupOf H) := by
  ext d
  rw [MonoidHom.mem_ker, dxToQuot_apply, QuotientGroup.eq_one_iff]
  change x⁻¹ * ((d : H) : G) * x ∈ I ↔ _
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conj_smul_iff]

instance normal_subgroupOf_conj [(I.subgroupOf D).Normal] (x : G) :
    (((MulAut.conj x • I : Subgroup G).subgroupOf H).subgroupOf
      ((MulAut.conj x • D : Subgroup G).subgroupOf H)).Normal := by
  rw [← ker_dxToQuot (H := H) (D := D) (I := I) x]
  infer_instance

end GroundTheory.Global.Artin
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance : MulAction Gal(L/K) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := ⟨σ • w.asIdeal, Ideal.IsPrime.smul σ, fun h ↦ w.ne_bot (by
    rw [← inv_smul_smul σ w.asIdeal, h, Ideal.smul_bot])⟩
  one_smul w := HeightOneSpectrum.ext (one_smul _ w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)

@[simp]
theorem asIdeal_smul (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal :=
  rfl

end Action

section FixedField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

instance isGaloisGroup_fixedField : IsGaloisGroup H (fixedField H) L :=
  IsGaloisGroup.subgroup Gal(L/K) K L H

instance isGaloisGroup_ringOfIntegers_fixedField : IsGaloisGroup H (𝓞 (fixedField H)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 (fixedField H)) (𝓞 L) (fixedField H) L

end FixedField

section Finite

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))

def subfieldPlace (x : Gal(L/K)) : HeightOneSpectrum (𝓞 (fixedField H)) :=
  (x • w).under (𝓞 (fixedField H))

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem asIdeal_subfieldPlace (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal = (x • w.asIdeal).under (𝓞 (fixedField H)) :=
  rfl

instance liesOver_subfieldPlace (x : Gal(L/K)) :
    (x • w.asIdeal).LiesOver (subfieldPlace H w x).asIdeal :=
  ⟨rfl⟩

theorem subfieldPlace_liesOver [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.tower_bot (x • w.asIdeal) _ v.asIdeal

theorem subfieldPlace_eq_iff (x y : Gal(L/K)) :
    subfieldPlace H w x = subfieldPlace H w y ↔
      DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w.asIdeal) x =
        DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w.asIdeal) y := by
  rw [DoubleCoset.eq, HeightOneSpectrum.ext_iff, asIdeal_subfieldPlace, asIdeal_subfieldPlace]
  constructor
  · intro hxy
    have : (y • w.asIdeal).LiesOver ((x • w.asIdeal).under (𝓞 (fixedField H))) := ⟨hxy⟩
    obtain ⟨h, hh⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      ((x • w.asIdeal).under (𝓞 (fixedField H))) (x • w.asIdeal) (y • w.asIdeal) H
    have hh' : (h : Gal(L/K)) • x • w.asIdeal = y • w.asIdeal := hh
    refine ⟨h, h.2, (y⁻¹ * h * x)⁻¹, Subgroup.inv_mem _ ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hh', inv_smul_smul]
  · rintro ⟨h, hh, d, hd, rfl⟩
    rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hd,
      show h • x • w.asIdeal = (⟨h, hh⟩ : H) • (x • w.asIdeal) from rfl]
    exact (Ideal.under_smul (𝓞 (fixedField H)) (x • w.asIdeal) (⟨h, hh⟩ : H)).symm

theorem exists_subfieldPlace_eq [w.asIdeal.LiesOver v.asIdeal]
    (u : HeightOneSpectrum (𝓞 (fixedField H))) [u.asIdeal.LiesOver v.asIdeal] :
    ∃ x : Gal(L/K), subfieldPlace H w x = u := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) u.asIdeal
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q u.asIdeal v.asIdeal
  obtain ⟨x, hx⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal Q Gal(L/K)
  refine ⟨x, HeightOneSpectrum.ext ?_⟩
  rw [asIdeal_subfieldPlace, hx, ← hQ.over]

def subfieldPlaceEquiv [w.asIdeal.LiesOver v.asIdeal] :
    DoubleCoset.Quotient (H : Set Gal(L/K)) (MulAction.stabilizer Gal(L/K) w.asIdeal) ≃
      {u : HeightOneSpectrum (𝓞 (fixedField H)) // u.asIdeal.LiesOver v.asIdeal} :=
  Equiv.ofBijective
    (Quotient.lift (fun x ↦ ⟨subfieldPlace H w x, subfieldPlace_liesOver H v w x⟩)
      (fun a b hab ↦ Subtype.ext ((subfieldPlace_eq_iff H w a b).2 (Quotient.sound hab))))
    ⟨by
      rintro ⟨a⟩ ⟨b⟩ hab
      exact (subfieldPlace_eq_iff H w a b).1 (congrArg Subtype.val hab),
    by
      rintro ⟨u, hu⟩
      obtain ⟨x, hx⟩ := exists_subfieldPlace_eq H v w u
      exact ⟨DoubleCoset.mk _ _ x, Subtype.ext hx⟩⟩

@[simp]
theorem subfieldPlaceEquiv_mk [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    (subfieldPlaceEquiv H v w (DoubleCoset.mk _ _ x) : HeightOneSpectrum (𝓞 (fixedField H))) =
      subfieldPlace H w x :=
  rfl

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem stabilizer_smul_eq (x : Gal(L/K)) (P : Ideal (𝓞 L)) :
    MulAction.stabilizer H (x • P) =
      (MulAut.conj x • MulAction.stabilizer Gal(L/K) P : Subgroup Gal(L/K)).subgroupOf H := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, mul_smul, mul_smul]
  change (h : Gal(L/K)) • x • P = x • P ↔ x⁻¹ • (h : Gal(L/K)) • x • P = P
  rw [inv_smul_eq_iff]

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem inertia_smul_eq (x : Gal(L/K)) (P : Ideal (𝓞 L)) :
    (x • P).inertia H =
      (MulAut.conj x • P.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff, ← Ideal.coe_mem_inertia, mem_inertia_smul_iff]

end Finite

end GroundTheory.Global.Artin
end
end
