import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.FiniteLevel
import ReciprocityTheory.GroupCohomology.FiberFirstH0Injective
import ReciprocityTheory.GroupCohomology.ProdHolds
import ReciprocityTheory.GroupCohomology.EqZeroOfLe
import Mathlib

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section Disc

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem contAction_of_disc {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [DiscreteTopology V] (rho : Representation R G V) (h : ∀ v, Continuous fun g => rho g v) :
    ContAction rho :=
  continuous_prod_of_discrete_right.2 h

theorem orbit_cont (B : TRep R G) (v : B.V) : Continuous fun g => B.rho g v :=
  B.cont.comp (f := fun g : G => (g, v)) (continuous_id.prodMk continuous_const)

def subRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := S
  ccs := ⟨fun _ => continuous_of_discreteTopology⟩
  rho := B.rho.subrepresentation S hS
  cont := contAction_of_disc _ fun v => (orbit_cont B v.1).subtype_mk _

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (subRep B S hS).V := inferInstanceAs (DiscreteTopology S)

theorem disc_quot {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [DiscreteTopology V]
    (S : Submodule R V) : DiscreteTopology (V ⧸ S) :=
  discreteTopology_iff_forall_isOpen.2 fun _ =>
    (Submodule.isQuotientMap_mkQ S).isOpen_preimage.1 (isOpen_discrete _)

def quotRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := B.V ⧸ S
  ccs := ⟨fun _ => by have := disc_quot S; exact continuous_of_discreteTopology⟩
  rho := B.rho.quotient S hS
  cont := by
    have := disc_quot S
    refine contAction_of_disc _ fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (continuous_of_discreteTopology (f := S.mkQ)).comp (orbit_cont B v)

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (quotRep B S hS).V := disc_quot S

def quotMk (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) : Pair B (quotRep B S hS) :=
  Pair.ofMap (M' := quotRep B S hS) S.mkQ continuous_of_discreteTopology fun _ _ => rfl

theorem admissible_of_discrete_topology {A B C : TRep R G} [DiscreteTopology A.V] [DiscreteTopology B.V]
    [DiscreteTopology C.V] (i : Pair A B) (p : Pair B C) (hi : i.φ = MonoidHom.id G)
    (hp : p.φ = MonoidHom.id G) (hinj : Injective i.u) (hex : Exact i.u p.u) (hsurj : Surjective p.u) :
    admitted i p :=
  ⟨hi, hp, ⟨⟨by
      rw [DiscreteTopology.eq_bot (α := A.V)]
      symm
      apply eq_bot_of_singletons_open
      intro a
      refine ⟨{i.u a}, isOpen_discrete _, ?_⟩
      ext x
      simp [hinj.eq_iff]⟩, hinj⟩, hex,
    ⟨surjInv hsurj, continuous_of_discreteTopology, surjInv_eq hsurj⟩⟩

end Disc

section Triv

variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]

theorem alt_sum_range (m : ℕ) :
    (1 + ∑ j ∈ Finset.range (2 * m + 1), (-1 : R) ^ (j + 1)) = 0 ∧
      (1 + ∑ j ∈ Finset.range (2 * m + 2), (-1 : R) ^ (j + 1)) = 1 := by
  have key : ∀ n : ℕ, ∑ j ∈ Finset.range n, (-1 : R) ^ (j + 1) = if Even n then 0 else -1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd n with h | h
      · have h' : ¬ Even (n + 1) := by
          rw [Nat.even_add_one]
          exact not_not.mpr h
        rw [if_pos h, if_neg h', pow_succ, h.neg_one_pow]
        ring
      · have h' : Even (n + 1) := by
          rw [Nat.even_add_one]
          exact Nat.not_even_iff_odd.mpr h
        rw [if_neg (Nat.not_even_iff_odd.mpr h), if_pos h', pow_succ, h.neg_one_pow]
        ring
  refine ⟨?_, ?_⟩
  · rw [key, if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩)]
    ring
  · rw [key, if_pos ⟨m + 1, by ring⟩]
    ring

theorem alt_sum_odd (m : ℕ) : (1 + ∑ j : Fin (2 * m + 1 + 1), (-1 : R) ^ ((j : ℕ) + 1)) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1)) (2 * m + 1 + 1)]
  exact (alt_sum_range m).2

theorem dn_triv {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul R V] (rho : Representation R H V) (n : ℕ) (f : (Fin n → H) → V)
    (g : Fin (n + 1) → H) (a : Fin n → H) :
    dn rho n f g = (1 + ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1)) • f a := by
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, Module.End.one_apply,
    Subsingleton.elim (fun i => g i.succ) a, add_smul, one_smul, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Subsingleton.elim (Fin.contractNth j (· * ·) g) a]

theorem triv_odd (T : TRep R H) (m : ℕ) : Subsingleton (T.H (2 * m + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using Cx.H_ind with
  | h x hx =>
    rw [Cx.cls_eq_zero_iff]
    have h0 : ∀ g, x.1 g = 0 := fun g => by
      have := congrFun (congrArg Subtype.val hx) (fun _ => 1)
      change dn T.rho (2 * m + 1) x.1 (fun _ => 1) = 0 at this
      rw [dn_triv T.rho (2 * m + 1) _ _ g, alt_sum_odd, one_smul] at this
      exact this
    have : x = 0 := Subtype.ext (funext h0)
    rw [this]
    exact zero_mem _

theorem triv_even (T : TRep R H) (m : ℕ) : Subsingleton (T.H (2 * m + 1 + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using Cx.H_ind with
  | h x hx =>
    rw [Cx.cls_eq_zero_iff]
    refine ⟨⟨fun _ => x.1 fun _ => 1, continuous_const⟩, Subtype.ext (funext fun g => ?_)⟩
    show dn T.rho (2 * m + 1) (fun _ => x.1 fun _ => 1) g = x.1 g
    rw [dn_triv T.rho (2 * m + 1) _ g (fun _ => 1), alt_sum_odd, one_smul,
      Subsingleton.elim g (fun _ => 1)]

theorem triv_H_sub (T : TRep R H) (k : ℕ) (hk : 1 ≤ k) : Subsingleton (T.H k) := by
  obtain ⟨m, hm | hm⟩ : ∃ m, k = 2 * m + 1 ∨ k = 2 * m + 1 + 1 := by
    rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t - 1, Or.inr (by omega)⟩
    · exact ⟨t, Or.inl ht⟩
  · subst hm
    exact triv_odd T m
  · subst hm
    exact triv_even T m

end Triv

section ShiftSec

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem disc_CM {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun f => ?_
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have he : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro rfl y _ x hx; exact hx
    · intro h; ext x; exact h (f x) ⟨x, rfl⟩ rfl
  rw [he]
  exact hfin.isOpen_biInter fun y _ => ContinuousMap.isOpen_setOfPred_mapsTo
    ((isClosed_discrete _).preimage f.continuous).isCompact (isOpen_discrete _)

variable [CompactSpace G]

end ShiftSec

section ShiftC

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]

instance disc_resBot : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V :=
  inferInstanceAs (DiscreteTopology M.V)

abbrev shC : TRep R G := coindRep (⊥ : Subgroup G) (M.resSub ⊥)

instance disc_shC : DiscreteTopology (shC M).V := by
  have := disc_CM (X := G) (Y := (M.resSub (⊥ : Subgroup G)).V)
  exact inferInstanceAs (DiscreteTopology (coindSub (⊥ : Subgroup G) (M.resSub ⊥)))

def shI : M.V →ₗ[R] (shC M).V where
  toFun m := ⟨⟨fun g => M.rho g m, orbit_cont M m⟩, fun x g => by
    have hx : (x : G) = 1 := Subgroup.mem_bot.1 x.2
    show M.rho ((x : G) * g) m = M.rho (x : G) (M.rho g m)
    rw [hx, one_mul, map_one, Module.End.one_apply]⟩
  map_add' m m' := Subtype.ext (ContinuousMap.ext fun g => map_add (M.rho g) m m')
  map_smul' r m := Subtype.ext (ContinuousMap.ext fun g => map_smul (M.rho g) r m)

theorem shI_equiv (g : G) (m : M.V) : shI M (M.rho g m) = (shC M).rho g (shI M m) :=
  Subtype.ext (ContinuousMap.ext fun h => by
    show M.rho h (M.rho g m) = M.rho (h * g) m
    rw [map_mul]; rfl)

theorem shI_inj : Injective (shI M) := fun m m' h => by
  have := congrArg (fun f : (shC M).V => f.1 1) h
  change M.rho 1 m = M.rho 1 m' at this
  simpa only [map_one, Module.End.one_apply] using this

theorem shI_stable (g : G) : LinearMap.range (shI M) ≤ (LinearMap.range (shI M)).comap ((shC M).rho g) := by
  rintro v ⟨m, rfl⟩
  exact ⟨M.rho g m, shI_equiv M g m⟩

def shIP : Pair M (shC M) := Pair.ofMap (shI M) continuous_of_discreteTopology (shI_equiv M)

abbrev shQ : TRep R G := quotRep (shC M) (LinearMap.range (shI M)) (shI_stable M)

theorem shAdm : admitted (shIP M) (quotMk (shC M) _ (shI_stable M)) :=
  admissible_of_discrete_topology _ _ rfl rfl (shI_inj M)
    (LinearMap.exact_iff.2 (Submodule.ker_mkQ _)) (Submodule.mkQ_surjective _)

theorem shC_tors (hM : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∀ f : (shC M).V, ∃ k : ℕ, 0 < k ∧ k • f = 0 := by
  intro f
  choose k hk using hM
  have hfin : (Set.range f.1).Finite := (isCompact_range f.1.continuous).finite_of_discrete
  obtain ⟨s, hs⟩ : ∃ s : Finset M.V, ∀ g, f.1 g ∈ s :=
    ⟨hfin.toFinset, fun g => hfin.mem_toFinset.2 ⟨g, rfl⟩⟩
  refine ⟨∏ m ∈ s, k m, Finset.prod_pos fun m _ => (hk m).1, ?_⟩
  have key : ∀ v ∈ s, (∏ m ∈ s, k m) • v = 0 := by
    intro v hv
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem k hv
    rw [hd, mul_comm, mul_smul, (hk v).2, smul_zero]
  exact Subtype.ext (ContinuousMap.ext fun g => key _ (hs g))

theorem shQ_tors (hM : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∀ q : (shQ M).V, ∃ k : ℕ, 0 < k ∧ k • q = 0 := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H f =>
    obtain ⟨k, hk, hf⟩ := shC_tors M hM f
    refine ⟨k, hk, ?_⟩
    have := map_nsmul (LinearMap.range (shI M)).mkQ k f
    rw [hf, map_zero] at this
    exact this.symm

theorem shC_acyc (k : ℕ) (hk : 1 ≤ k) : Subsingleton ((shC M).H k) := by
  have hq := shapiro_holds R G (⊥ : Subgroup G) (M.resSub ⊥) (shC M) (coindEv _ _)
    (coindEv_isCoind _ _) ⟨fun _ => 1, continuous_const, fun x g => Subsingleton.elim _ _⟩
  have := triv_H_sub (M.resSub (⊥ : Subgroup G)) k hk
  exact (hq k).1.subsingleton

theorem shift_step (n : ℕ) (hQ : Subsingleton ((shQ M).H n)) : Subsingleton (M.H (n + 1)) := by
  obtain ⟨δ, -, hL⟩ := (lES_holds R _ _ _ _ _ (admissibility_holds R G _ _ _ _ _ (shAdm M))).1
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hC := shC_acyc M (n + 1) (by omega)
  have h0 : (shIP M).hom.H (n + 1) x = 0 := Subsingleton.elim _ _
  obtain ⟨q, rfl⟩ := (hL.exA n x).1 h0
  rw [Subsingleton.elim q 0, map_zero]

end ShiftC

end KernelCokernelKilling

end

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section KillLES

variable {R : Type u} [CommRing R] {A B C : Cx R} {i : Hom A B} {p : Hom B C}
  {δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)}

end KillLES

section KillRep

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end KillRep

end KernelCokernelKilling

open KernelCokernelKilling

theorem shift_holds : ShiftStatement.{u} := by
  intro R _ G _ _ _ _ N hN M _ hM n hn
  induction n, hn using Nat.le_induction generalizing M with
  | base => exact hN M hM
  | succ n hNn ih =>
    exact KernelCokernelKilling.shift_step M n (ih (KernelCokernelKilling.shQ M) (KernelCokernelKilling.shQ_tors M hM))

end

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open Topology
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem comm_of_dense [T2Space G] {s : G} (hs : Dense (Subgroup.zpowers s : Set G)) (a b : G) :
    a * b = b * a := by
  have hcl : IsClosed {p : G × G | p.1 * p.2 = p.2 * p.1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst)
  have hd : Dense ((Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G)) := hs.prod hs
  have hsub : (Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G) ⊆
      {p : G × G | p.1 * p.2 = p.2 * p.1} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact zpow_mul_comm s i j
  have h := hcl.closure_subset_iff.2 hsub
  rw [hd.closure_eq] at h
  exact h (Set.mem_univ (a, b))

theorem normal_of_comm (hc : ∀ a b : G, a * b = b * a) (W : Subgroup G) : W.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem finite_quot [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Finite (G ⧸ W) := by
  exact Subgroup.quotient_finite_of_isOpen W hW

theorem index_pos [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : 0 < W.index := by
  haveI := finite_quot hc hW
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

variable {s : G}

theorem mem_zpowers_quot (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} [W.Normal]
    (hW : IsOpen (W : Set G)) (x : G ⧸ W) : x ∈ Subgroup.zpowers (QuotientGroup.mk' W s) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  obtain ⟨y, hyU, hy⟩ := hs.inter_open_nonempty _ hU ⟨g, by simp [W.one_mem]⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq.mpr hyU).symm

theorem zpow_mem_iff [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (z : ℤ) :
    s ^ z ∈ W ↔ (W.index : ℤ) ∣ z := by
  haveI := normal_of_comm hc W
  haveI := finite_quot hc hW
  have hord : orderOf (QuotientGroup.mk' W s) = W.index := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_quot hs hW)]
    rfl
  rw [← QuotientGroup.eq_one_iff (N := W), ← hord, orderOf_dvd_iff_zpow_eq_one, ← map_zpow,
    QuotientGroup.mk'_apply]

theorem exists_pow [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (g : G) :
    ∃ j : ℕ, g⁻¹ * s ^ j ∈ W := by
  haveI := normal_of_comm hc W
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_quot hs hW (g : G ⧸ W))
  rw [← map_zpow, QuotientGroup.mk'_apply] at hk
  have hgk : g⁻¹ * s ^ k ∈ W := QuotientGroup.eq.mp hk.symm
  have hn : (0 : ℤ) < W.index := by exact_mod_cast index_pos hc hW
  refine ⟨(k % (W.index : ℤ)).toNat, ?_⟩
  have hj : (((k % (W.index : ℤ)).toNat : ℕ) : ℤ) = k % (W.index : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')
  have hd : s ^ (k % (W.index : ℤ) - k) ∈ W := by
    rw [zpow_mem_iff hc hs hW]
    exact ⟨-(k / (W.index : ℤ)), by rw [Int.emod_def]; ring⟩
  have heq : g⁻¹ * s ^ (k % (W.index : ℤ)).toNat =
      (g⁻¹ * s ^ k) * s ^ (k % (W.index : ℤ) - k) := by
    rw [mul_assoc, ← zpow_add, ← zpow_natCast, hj]
    congr 2
    ring
  rw [heq]
  exact W.mul_mem hgk hd

section Desc

variable {X : Type*} (n : ℕ) (T : ℕ → X)

theorem per_mul (hper : ∀ j, T (j + n) = T j) (a t : ℕ) : T (a + n * t) = T a := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]

theorem per_of_dvd (hper : ∀ j, T (j + n) = T j) (a b : ℕ) (h : (n : ℤ) ∣ (b : ℤ) - a) :
    T a = T b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have h1 : ((b : ℕ) : ℤ) = ((a + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : b = a + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]
  · rw [mul_neg] at hc
    have h1 : ((a : ℕ) : ℤ) = ((b + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : a = b + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]

end Desc

noncomputable def desc (W : Subgroup G) (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*}
    (T : ℕ → X) (g : G) : X :=
  T (Classical.choose (h g))

theorem desc_eq [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) {g : G} {j : ℕ} (hj : g⁻¹ * s ^ j ∈ W) :
    desc W h T g = T j := by
  have h0 := Classical.choose_spec (h g)
  show T (Classical.choose (h g)) = T j
  have hm : s ^ ((j : ℤ) - (Classical.choose (h g) : ℕ)) ∈ W := by
    have hw := W.mul_mem (W.inv_mem h0) hj
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    rw [zpow_sub, zpow_natCast, zpow_natCast, hc]
    exact hw
  exact per_of_dvd W.index T hper _ _ ((zpow_mem_iff hc hs hW _).mp hm)

theorem desc_continuous [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} [TopologicalSpace X] (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) : Continuous (desc W h T) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun y => g⁻¹ * y) ⁻¹' (W : Set G) := by simp [W.one_mem]
  refine (continuousAt_const : ContinuousAt (fun _ : G => desc W h T g) g).congr ?_
  filter_upwards [hU.mem_nhds hg] with y hy
  have h0 := Classical.choose_spec (h g)
  have hy' : y⁻¹ * s ^ Classical.choose (h g) ∈ W := by
    have hw := W.mul_mem (W.inv_mem hy) h0
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    exact hw
  rw [desc_eq hc hs hW h T hper hy']
  rfl

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def stab (M : TRep R G) (m : M.V) : Subgroup G where
  carrier := {a | M.rho a m = m}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem stab_isOpen (M : TRep R G) [DiscreteTopology M.V] (m : M.V) : IsOpen (stab M m : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (FiniteLevelCohomology.stab_mem_nhds M m)

theorem rho_comm (M : TRep R G) (hc : ∀ a b : G, a * b = b * a) (a b : G) (x : M.V) :
    M.rho a (M.rho b x) = M.rho b (M.rho a x) := by
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]

theorem cocycle_eq_of_apply (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hs : Dense (Subgroup.zpowers s : Set G)) (c : G → M.V) (hc : c ∈ Z1 M.rho) (m : M.V)
    (hm : c s = M.rho s m - m) (g : G) : c g = M.rho g m - m := by
  have hcont : Continuous fun a : G => M.rho a m :=
    M.cont.comp (f := fun a : G => (a, m)) (continuous_id.prodMk continuous_const)
  have hcl : IsClosed {a : G | c a = M.rho a m - m} :=
    isClosed_eq hc.1 (hcont.sub continuous_const)
  have step : ∀ a : G, c (a * s) - (M.rho (a * s) m - m) = c a - (M.rho a m - m) := by
    intro a
    rw [hc.2, hm, map_mul, Module.End.mul_apply]
    simp only [map_sub]; abel
  have hz : ∀ i : ℤ, c (s ^ i) = M.rho (s ^ i) m - m := by
    have h0 : c (s ^ (0 : ℤ)) - (M.rho (s ^ (0 : ℤ)) m - m) = 0 := by
      have e := hc.2 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at e
      simp only [zpow_zero, map_one, Module.End.one_apply, sub_self, sub_zero]
      exact (add_eq_left.1 e.symm)
    intro i
    have : c (s ^ i) - (M.rho (s ^ i) m - m) = 0 := by
      induction i using Int.induction_on with
      | zero => exact h0
      | succ i ih => rw [zpow_add_one, step, ih]
      | pred i ih => rw [← ih, ← step, zpow_sub_one, inv_mul_cancel_right]
    exact sub_eq_zero.1 this
  have hsub : (Subgroup.zpowers s : Set G) ⊆ {a : G | c a = M.rho a m - m} := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact hz i
  have h := hcl.closure_subset_iff.2 hsub
  rw [hs.closure_eq] at h
  exact h (Set.mem_univ g)

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def psum (M : TRep R G) (s : G) (m : M.V) (j : ℕ) : M.V :=
  ∑ i ∈ Finset.range j, M.rho (s ^ i) m

theorem psum_add (M : TRep R G) (s : G) (m : M.V) (i j : ℕ) :
    psum M s m (i + j) = psum M s m i + M.rho (s ^ i) (psum M s m j) := by
  simp only [psum, Finset.sum_range_add, map_sum, pow_add, map_mul, Module.End.mul_apply]

theorem exists_cocycle [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (m : M.V) (hk : ∃ k : ℕ, 0 < k ∧ k • m = 0) : ∃ c ∈ Z1 M.rho, c s = m := by
  obtain ⟨k, hk0, hkm⟩ := hk
  set V := stab M m
  have hVo := stab_isOpen M m
  set a := V.index
  have ha : 0 < a := index_pos hc hVo
  have hsa : s ^ a ∈ V := by
    have := (zpow_mem_iff hc hs hVo (a : ℤ)).2 dvd_rfl
    simpa using this
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (a * k) (Nat.mul_pos ha hk0)
  set W := V ⊓ W0
  have hWo : IsOpen (W : Set G) := hVo.inter hW0o
  have hWV : W ≤ V := inf_le_left
  have hdvd : a * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right

  have hfixV : ∀ v ∈ V, ∀ j, M.rho v (psum M s m j) = psum M s m j := by
    intro v hv j
    simp only [psum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rho_comm M hc]
    rw [show M.rho v m = m from hv]
  have hmul : ∀ t, psum M s m (a * t) = t • psum M s m a := by
    intro t
    induction t with
    | zero => simp [psum]
    | succ t ih =>
      rw [Nat.mul_succ, psum_add, ih, hfixV _ (by rw [pow_mul]; exact V.pow_mem hsa t), succ_nsmul]
  have hN : psum M s m (a * k) = 0 := by
    rw [hmul, psum, Finset.smul_sum]
    simp only [← map_nsmul, hkm, map_zero, Finset.sum_const_zero]
  have hperN : ∀ j, psum M s m (j + a * k) = psum M s m j := by
    intro j; rw [psum_add, hN, map_zero, add_zero]
  have hper : ∀ j, psum M s m (j + W.index) = psum M s m j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]; exact per_mul _ _ hperN j t
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex (psum M s m), ⟨desc_continuous hc hs hWo hex _ hper, fun g h => ?_⟩, ?_⟩
  · have hg := Classical.choose_spec (hex g)
    have hh := Classical.choose_spec (hex h)
    set i := Classical.choose (hex g)
    set j := Classical.choose (hex h)
    have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
      have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
        calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
              rw [mul_inv_rev, pow_add]; group
          _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
      rw [e]; exact W.mul_mem hg hh
    have e1 : desc W hex (psum M s m) (g * h) = psum M s m (i + j) := desc_eq hc hs hWo hex _ hper hgh
    have e2 : desc W hex (psum M s m) g = psum M s m i := rfl
    have e3 : desc W hex (psum M s m) h = psum M s m j := rfl
    rw [e1, e2, e3, psum_add]
    congr 1
    have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
    conv_rhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixV _ (hWV (W.inv_mem hg))]
  · have : desc W hex (psum M s m) s = psum M s m 1 :=
      desc_eq hc hs hWo hex _ hper (by simp)
    rw [this]; simp [psum]

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem model_comparison_degree_zero_bijective [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
      ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := by
  set P := LinearMap.range (M.rho s - LinearMap.id)
  let f : Z1 M.rho →ₗ[R] M.V ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 M.rho).subtype)
  have hf : ∀ c : Z1 M.rho, f c = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hker : (B1 M.rho).comap (Z1 M.rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ := ((B1 M.rho).comap (Z1 M.rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 M.rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) :=
    fun c => rfl
  have hinj : Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨m, cocycle_eq_of_apply M hs c.1 c.2 m ?_⟩
    rw [← hm]; simp
  have hsurj : Surjective φ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, hcZ, hcs⟩ := exists_cocycle M hc hs hidx m (htor m)
    exact ⟨Submodule.Quotient.mk ⟨c, hcZ⟩, by rw [hφ]; simp [hcs]⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun c => hφ c⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def tr (M : TRep R G) (f : G × G → M.V) (s : G) : ℕ → M.V
  | 0 => f (1, 1)
  | j + 1 => tr M f s j - f (s ^ j, s)

theorem tr_key (M : TRep R G) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) (s : G) (i j : ℕ) :
    f (s ^ i, s ^ j) = M.rho (s ^ i) (tr M f s j) - tr M f s (i + j) + tr M f s i := by
  have hc := hf.2
  induction j with
  | zero =>
    have e := hc (s ^ i) 1 1
    simp only [mul_one] at e
    rw [sub_add_cancel, sub_eq_zero] at e
    simp only [pow_zero, add_zero]
    rw [sub_add_cancel]
    exact e.symm
  | succ j ih =>
    have e := hc (s ^ i) (s ^ j) s
    rw [← pow_add, ← pow_succ, ih] at e
    have e2 : tr M f s (j + 1) = tr M f s j - f (s ^ j, s) := rfl
    have e3 : tr M f s (i + (j + 1)) = tr M f s (i + j) - f (s ^ (i + j), s) := rfl
    rw [e2, e3, map_sub, ← sub_eq_zero, ← e]
    abel

theorem tr_add (M : TRep R G) (f : G × G → M.V) (s : G) (j t : ℕ) :
    tr M f s (j + t) = tr M f s j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : tr M f s (j + (t + 1)) = tr M f s (j + t) - f (s ^ (j + t), s) := rfl
    rw [e, ih, Finset.sum_range_succ]
    abel

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_coboundaries_of_cocycle_procyclic [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) :
    f ∈ B2 M.rho := by
  obtain ⟨N, -, hNo, hconst, hfix⟩ := FiniteLevelCohomology.exists_open_normal M (n := 2)
    (fun v : Fin 2 → G => f (v 0, v 1))
    (hf.1.comp ((continuous_apply 0).prodMk (continuous_apply 1)))
  have hbi : ∀ g h w w', w ∈ N → w' ∈ N → f (g * w, h * w') = f (g, h) := by
    intro g h w w' hw hw'
    have := hconst ![g, h] ![w, w'] (fun i => by fin_cases i <;> simpa)
    simpa using this
  have hfixf : ∀ g h, ∀ a ∈ N, M.rho a (f (g, h)) = f (g, h) := by
    intro g h a ha
    simpa using hfix ![g, h] a ha
  set T := tr M f s
  set n := N.index
  have hsn : s ^ n ∈ N := by simpa using (zpow_mem_iff hc hs hNo (n : ℤ)).2 dvd_rfl

  set a := ∑ i ∈ Finset.range n, f (s ^ i, s)
  have hwin : ∀ j, ∑ i ∈ Finset.range n, f (s ^ (j + i), s) = a := by
    intro j
    induction j with
    | zero => simp [a]
    | succ j ih =>
      have h1 : ∑ i ∈ Finset.range (n + 1), f (s ^ (j + i), s) =
          ∑ i ∈ Finset.range n, f (s ^ (j + 1 + i), s) + f (s ^ (j + 0), s) := by
        rw [Finset.sum_range_succ']
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show j + (i + 1) = j + 1 + i by omega]
      have h2 := Finset.sum_range_succ (fun i => f (s ^ (j + i), s)) n
      have hp : f (s ^ (j + n), s) = f (s ^ (j + 0), s) := by
        rw [pow_add, add_zero]
        simpa using hbi (s ^ j) s (s ^ n) 1 hsn N.one_mem
      rw [← ih]
      rw [hp] at h2
      exact add_right_cancel (h1.symm.trans h2)
  have hTn : ∀ j t, T (j + n * t) = T j - t • a := by
    intro j t
    induction t with
    | zero => simp
    | succ t ih =>
      have htadd : ∀ j t, T (j + t) = T j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) :=
        tr_add M f s
      rw [Nat.mul_succ, ← add_assoc, htadd, ih, hwin, succ_nsmul]; abel
  obtain ⟨k, hk0, hka⟩ := htor a
  have hn0 : 0 < n := index_pos hc hNo
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (n * k) (Nat.mul_pos hn0 hk0)
  set W := N ⊓ W0
  have hWo : IsOpen (W : Set G) := hNo.inter hW0o
  have hWN : W ≤ N := inf_le_left
  have hdvd : n * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right
  have hper : ∀ j, T (j + W.index) = T j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]
    refine per_mul _ _ (fun j => ?_) j t
    rw [hTn, hka, sub_zero]
  have hfixT : ∀ w ∈ N, ∀ j, M.rho w (T j) = T j := by
    intro w hw j
    induction j with
    | zero => exact hfixf 1 1 w hw
    | succ j ih =>
      show M.rho w (T j - f (s ^ j, s)) = T j - f (s ^ j, s)
      rw [map_sub, ih, hfixf _ _ w hw]
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex T, desc_continuous hc hs hWo hex T hper, ?_⟩
  funext ⟨g, h⟩
  have hg := Classical.choose_spec (hex g)
  have hh := Classical.choose_spec (hex h)
  set i := Classical.choose (hex g)
  set j := Classical.choose (hex h)
  have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
    have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
      calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
            rw [mul_inv_rev, pow_add]; group
        _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
    rw [e]; exact W.mul_mem hg hh
  have e1 : desc W hex T (g * h) = T (i + j) := desc_eq hc hs hWo hex _ hper hgh
  have e2 : desc W hex T g = T i := rfl
  have e3 : desc W hex T h = T j := rfl
  have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
  have hheq : h = s ^ j * (h⁻¹ * s ^ j)⁻¹ := by group
  rw [d1_apply, e1, e2, e3]
  have hr : M.rho g (T j) = M.rho (s ^ i) (T j) := by
    conv_lhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixT _ (hWN (W.inv_mem hg))]
  have hfv : f (g, h) = f (s ^ i, s ^ j) := by
    conv_lhs => rw [hgeq, hheq]
    exact hbi _ _ _ _ (hWN (W.inv_mem hg)) (hWN (W.inv_mem hh))
  rw [hr, hfv, tr_key M f hf s i j]

theorem subsingleton_H2_of_procyclic_of_torsion [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) : Subsingleton (H2 M.rho) := by
  have hz : ∀ z : H2 M.rho, z = 0 := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_coboundaries_of_cocycle_procyclic M hc hs hidx htor z.1 z.2)
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Function

universe u

namespace ProcyclicCohomology

theorem length_ker_eq_coker {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    (f : V →ₗ[R] V) (h : IsFiniteLength R V) :
    Module.length R (LinearMap.ker f) = Module.length R (V ⧸ LinearMap.range f) := by
  have h1 : Module.length R V = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.injective_subtype _)
      f.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R V = Module.length R (LinearMap.range f) + Module.length R (V ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.injective_subtype _) (LinearMap.range f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  have hVt : Module.length R V ≠ ⊤ := Module.length_ne_top_iff.2 h
  have hL : Module.length R (LinearMap.range f) ≠ ⊤ := fun h' => hVt (by rw [h1, h', add_top])
  rw [h1, add_comm (Module.length R (LinearMap.range f))] at h2
  exact (WithTop.add_right_cancel hL h2)

end ProcyclicCohomology

theorem zHat_holds : ZHatStatement.{u} := by
  intro R _ G _ _ _ _ _ _ s hG M _ htor
  have hs := hG.1
  have hidx := hG.2
  have hc := ProcyclicCohomology.comm_of_dense hs
  have hA := ProcyclicCohomology.model_comparison_degree_zero_bijective M hc hs hidx htor
  have hH2 : ∀ (M' : TRep R G) [DiscreteTopology M'.V], (∀ m : M'.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) →
      Subsingleton (M'.H 2) := by
    intro M' _ ht
    obtain ⟨-, -, -, e2, -⟩ := low_holds R G M'
    have := ProcyclicCohomology.subsingleton_H2_of_procyclic_of_torsion M' hc hs hidx ht
    exact e2.toEquiv.subsingleton
  have hB : ∀ n, 1 < n → Subsingleton (M.H n) := fun n hn =>
    shift_holds R G 2 hH2 M htor n hn
  refine ⟨hA, hB, fun hM => ?_⟩
  obtain ⟨-, ⟨e0, -⟩, ⟨e1, -⟩, -⟩ := low_holds R G M
  obtain ⟨eA, -⟩ := hA
  set f := M.rho s - LinearMap.id
  have hH0 : H0 M.rho = LinearMap.ker f := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, LinearMap.mem_ker]
    constructor
    · intro h; simp [f, h s]
    · intro h g
      have h' : M.rho s m = m := by
        have := h
        simp only [f, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
        exact this
      have := ProcyclicCohomology.cocycle_eq_of_apply M hs 0 (Z1 M.rho).zero_mem m (by simp [h']) g
      rw [Pi.zero_apply, eq_comm, sub_eq_zero] at this
      exact this
  have fl0 : IsFiniteLength R (M.H 0) :=
    (hM.of_injective (Submodule.injective_subtype (H0 M.rho))).of_injective e0.injective
  have fl1 : IsFiniteLength R (M.H 1) :=
    (hM.of_surjective (Submodule.mkQ_surjective (LinearMap.range f))).of_injective
      (e1.trans eA).injective
  have hfl : ∀ n, IsFiniteLength R (M.H n) := by
    intro n
    rcases n with _ | _ | n
    · exact fl0
    · exact fl1
    · have := hB (n + 2) (by omega); exact .of_subsingleton
  refine ⟨⟨hfl, hB⟩, ?_⟩
  have l0 : Module.length R (M.H 0) = Module.length R (LinearMap.ker f) := by
    rw [e0.length_eq, hH0]
  have l1 : Module.length R (M.H 1) = Module.length R (M.V ⧸ LinearMap.range f) :=
    (e1.trans eA).length_eq
  have l01 : Module.length R (M.H 0) = Module.length R (M.H 1) := by
    rw [l0, l1, ProcyclicCohomology.length_ker_eq_coker f hM]
  simp only [Cx.chi, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, one_mul,
    neg_one_mul, zero_add]
  rw [show Module.length R (M.coch.H 0) = Module.length R (M.coch.H 1) from l01]
  ring

end ReciprocityTheory.Coh
end
