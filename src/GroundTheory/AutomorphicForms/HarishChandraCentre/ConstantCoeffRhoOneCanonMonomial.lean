import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.MemCenterOfCommuteE
import GroundTheory.AutomorphicForms.HarishChandraCentre.RepBase

section
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

def Closed (P : Fin n × Fin n → Prop) : Prop := ∀ a b, P a → P b → a.2 = b.1 → P (a.1, b.2)

def IsLower (a : Fin n × Fin n) : Prop := a.2 < a.1

def IsDiag (a : Fin n × Fin n) : Prop := a.1 = a.2

def IsUpper (a : Fin n × Fin n) : Prop := a.1 < a.2

theorem closed_lower : Closed (IsLower (n := n)) := fun a b ha hb h => by
  simp only [IsLower] at *; rw [h] at ha; exact lt_trans hb ha

theorem closed_upper : Closed (IsUpper (n := n)) := fun a b ha hb h => by
  simp only [IsUpper] at *; rw [h] at ha; exact lt_trans ha hb


theorem closed_true : Closed (fun _ : Fin n × Fin n => True) := fun _ _ _ _ _ => trivial

def wordSpan (P : Fin n × Fin n → Prop) (k : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ w : List (Fin n × Fin n), (∀ a ∈ w, P a) ∧ w.length = k ∧ word w = u}

theorem word_mem_wordSpan {P : Fin n × Fin n → Prop} {w : List (Fin n × Fin n)}
    (hw : ∀ a ∈ w, P a) : word w ∈ wordSpan P w.length :=
  Submodule.subset_span ⟨w, hw, rfl, rfl⟩

theorem e_mul_mem_wordSpan {P : Fin n × Fin n → Prop} {a : Fin n × Fin n} (ha : P a) {k : ℕ}
    {u : U n} (hu : u ∈ wordSpan P k) : e a * u ∈ wordSpan P (k + 1) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl, rfl⟩ := hx
    rw [← word_cons]
    refine word_mem_wordSpan (w := a :: w) ?_
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact hw b hb
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx


theorem commutator_mul_mem_wordSpan {P : Fin n × Fin n → Prop} (hP : Closed P)
    {a b : Fin n × Fin n} (ha : P a) (hb : P b) {l : List (Fin n × Fin n)} (hl : ∀ c ∈ l, P c) :
    (e a * e b - e b * e a) * word l ∈ wordSpan P (l.length + 1) := by
  rw [e_mul_sub_mul, sub_mul]
  refine Submodule.sub_mem _ ?_ ?_
  · split_ifs with h
    · rw [← word_cons]
      refine word_mem_wordSpan (w := (a.1, b.2) :: l) ?_
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hP a b ha hb h
      · exact hl c hc
    · simp
  · split_ifs with h
    · rw [← word_cons]
      refine word_mem_wordSpan (w := (b.1, a.2) :: l) ?_
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hP b a hb ha h
      · exact hl c hc
    · simp

theorem word_sub_word_mem_of_perm {P : Fin n × Fin n → Prop} (hP : Closed P)
    {w w' : List (Fin n × Fin n)} (h : w.Perm w') (hw : ∀ a ∈ w, P a) :
    word w - word w' ∈ wordSpan P (w.length - 1) := by
  induction h with
  | nil => simp
  | cons x h ih =>
    rename_i l₁ l₂
    rcases l₁ with _ | ⟨y, l₁⟩
    · rw [List.nil_perm.1 h]; simp
    · rw [show word (x :: y :: l₁) - word (x :: l₂) = e x * (word (y :: l₁) - word l₂) by
        rw [word_cons x, word_cons x, mul_sub], List.length_cons, Nat.add_sub_cancel]
      have := ih fun a ha => hw a (List.mem_cons_of_mem _ ha)
      simp only [List.length_cons, Nat.add_sub_cancel] at this
      exact e_mul_mem_wordSpan (hw x (List.mem_cons_self ..)) this
  | swap x y l =>
    rw [word_cons, word_cons, word_cons, word_cons, ← mul_assoc, ← mul_assoc, ← sub_mul]
    simp only [List.length_cons, Nat.add_sub_cancel]
    exact commutator_mul_mem_wordSpan hP (hw y (by simp)) (hw x (by simp))
      (fun c hc => hw c (by simp [hc]))
  | trans h₁ h₂ ih₁ ih₂ =>
    rw [← sub_add_sub_cancel]
    refine Submodule.add_mem _ (ih₁ hw) ?_
    rw [h₁.length_eq]
    exact ih₂ fun a ha => hw a (h₁.symm.subset ha)

def letters (n : ℕ) : List (Fin n × Fin n) :=
  let all := (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)
  all.filter (fun a => decide (a.2 < a.1)) ++ all.filter (fun a => decide (a.1 = a.2)) ++
    all.filter (fun a => decide (a.1 < a.2))

theorem mem_letters (a : Fin n × Fin n) : a ∈ letters n := by
  simp only [letters, List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and, decide_eq_true_eq]
  have hall : ∃ i, ∃ j, (i, j) = a := ⟨a.1, a.2, rfl⟩
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact Or.inr ⟨hall, h⟩
  · exact Or.inl (Or.inr ⟨hall, h⟩)
  · exact Or.inl (Or.inl ⟨hall, h⟩)

theorem nodup_letters : (letters n).Nodup := by
  have hall : ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => (List.nodup_finRange n).map fun j j' h => by simpa using h, ?_⟩
    refine (List.nodup_finRange n).pairwise_of_forall_ne ?_
    intro i _ i' _ hii'
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨j, rfl⟩ ⟨j', h⟩
    exact hii' (congrArg Prod.fst h).symm
  simp only [letters]
  refine List.Nodup.append (List.Nodup.append (hall.filter _) (hall.filter _) ?_) (hall.filter _) ?_
  · simp only [List.disjoint_left, List.mem_filter, decide_eq_true_eq]
    rintro a ⟨_, h⟩ ⟨_, h'⟩
    exact absurd h (by rw [h']; exact lt_irrefl _)
  · simp only [List.disjoint_left, List.mem_append, List.mem_filter, decide_eq_true_eq]
    rintro a (⟨_, h⟩ | ⟨_, h⟩) ⟨_, h'⟩
    · exact lt_asymm h h'
    · exact absurd h' (by rw [h]; exact lt_irrefl _)

def expand (m : Fin n × Fin n →₀ ℕ) : List (Fin n × Fin n) :=
  (letters n).flatMap fun a => List.replicate (m a) a

noncomputable def canon (m : Fin n × Fin n →₀ ℕ) : U n := word (expand m)

theorem word_flatMap_replicate (l : List (Fin n × Fin n)) (m : Fin n × Fin n → ℕ) :
    word (l.flatMap fun a => List.replicate (m a) a) = (l.map fun a => e a ^ m a).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, word_append, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [word, List.map_replicate, List.prod_replicate]

theorem canon_eq_prod (m : Fin n × Fin n →₀ ℕ) :
    canon m = ((letters n).map fun a => e a ^ m a).prod :=
  word_flatMap_replicate _ _

theorem count_expand (m : Fin n × Fin n →₀ ℕ) (a : Fin n × Fin n) :
    Multiset.count a ((expand m : List _) : Multiset _) = m a := by
  have key : ∀ l : List (Fin n × Fin n), l.Nodup →
      Multiset.count a ((l.flatMap fun b => List.replicate (m b) b : List _) : Multiset _) =
        if a ∈ l then m a else 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.flatMap_cons, ← Multiset.coe_add, Multiset.count_add, ih (List.nodup_cons.1 hl).2,
        Multiset.coe_replicate, Multiset.count_replicate]
      by_cases hb : b = a
      · subst hb; simp [(List.nodup_cons.1 hl).1]
      · simp [hb, Ne.symm hb]
  rw [expand, key _ nodup_letters, if_pos (mem_letters a)]

theorem toFinsupp_expand (m : Fin n × Fin n →₀ ℕ) :
    Multiset.toFinsupp ((expand m : List _) : Multiset _) = m := by
  ext a
  rw [Multiset.toFinsupp_apply, count_expand]

theorem perm_expand (w : List (Fin n × Fin n)) :
    w.Perm (expand (Multiset.toFinsupp (w : Multiset _))) := by
  refine Multiset.coe_eq_coe.1 ?_
  ext a
  rw [count_expand, Multiset.toFinsupp_apply]

theorem length_expand (m : Fin n × Fin n →₀ ℕ) : (expand m).length = m.degree := by
  rw [Finsupp.degree_eq_sum, expand, List.length_flatMap]
  simp only [List.length_replicate]
  have : (letters n).toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun a => List.mem_toFinset.2 (mem_letters a)
  rw [← this, List.sum_toFinset _ nodup_letters]

theorem degree_toFinsupp (w : List (Fin n × Fin n)) :
    Finsupp.degree (Multiset.toFinsupp (w : Multiset (Fin n × Fin n))) = w.length := by
  rw [← length_expand]
  exact (perm_expand w).length_eq.symm

theorem mem_of_mem_support_toFinsupp {w : List (Fin n × Fin n)} {a : Fin n × Fin n}
    (ha : a ∈ (Multiset.toFinsupp (w : Multiset _)).support) : a ∈ w := by
  rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at ha
  exact Multiset.mem_coe.1 ha

theorem mem_support_of_mem_expand {m : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n}
    (ha : a ∈ expand m) : a ∈ m.support := by
  rw [Finsupp.mem_support_iff, ← count_expand]
  exact (Multiset.count_pos.2 (Multiset.mem_coe.2 ha)).ne'
@[simp] theorem expand_zero : expand (0 : Fin n × Fin n →₀ ℕ) = [] := by
  simp [expand]

@[simp] theorem canon_zero : canon (0 : Fin n × Fin n →₀ ℕ) = 1 := by
  simp [canon]

def canonSpan (P : Fin n × Fin n → Prop) (lo hi : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ m : Fin n × Fin n →₀ ℕ, (∀ a ∈ m.support, P a) ∧ lo ≤ m.degree ∧
    m.degree ≤ hi ∧ canon m = u}

theorem canonSpan_mono {P : Fin n × Fin n → Prop} {lo lo' hi hi' : ℕ} (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : canonSpan P lo hi ≤ canonSpan P lo' hi' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, h1, h2, rfl⟩
  exact ⟨m, hm, hlo.trans h1, h2.trans hhi, rfl⟩

theorem canon_mem_canonSpan {P : Fin n × Fin n → Prop} {m : Fin n × Fin n →₀ ℕ}
    (hm : ∀ a ∈ m.support, P a) : canon m ∈ canonSpan P m.degree m.degree :=
  Submodule.subset_span ⟨m, hm, le_rfl, le_rfl, rfl⟩

theorem word_mem_canonSpan {P : Fin n × Fin n → Prop} (hP : Closed P) :
    ∀ (w : List (Fin n × Fin n)), (∀ a ∈ w, P a) →
      word w ∈ canonSpan P (min 1 w.length) w.length := by
  intro w
  induction hk : w.length using Nat.strong_induction_on generalizing w with
  | _ k ih =>
  intro hw
  set m := Multiset.toFinsupp (w : Multiset (Fin n × Fin n))
  have hmP : ∀ a ∈ m.support, P a := fun a ha => hw a (mem_of_mem_support_toFinsupp ha)
  have hmdeg : m.degree = k := by rw [degree_toFinsupp, hk]
  have hcanon : canon m ∈ canonSpan P (min 1 k) k := by
    have := canon_mem_canonSpan hmP
    rw [hmdeg] at this
    exact canonSpan_mono (min_le_right _ _) le_rfl this
  rw [← sub_add_cancel (word w) (canon m)]
  refine Submodule.add_mem _ ?_ hcanon
  have hperm := word_sub_word_mem_of_perm hP (perm_expand w) hw
  rw [hk] at hperm
  change word w - word (expand m) ∈ _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    have hw' : w = expand m := by
      rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
      · simp [m]
      · have h := perm_expand [a]
        exact (List.perm_singleton.1 h.symm).symm
      · simp at hk; omega
    rw [← hw', sub_self]
    exact Submodule.zero_mem _
  · refine (Submodule.span_le.2 ?_) hperm
    rintro _ ⟨v, hv, hvl, rfl⟩
    have := ih (k - 1) (by omega) v hvl hv
    rw [show min 1 (k - 1) = 1 by omega] at this
    exact canonSpan_mono (by omega) (by omega) this

theorem span_canon_eq_top : Submodule.span ℂ (Set.range (canon (n := n))) = ⊤ := by
  have hword : ∀ w : List (Fin n × Fin n), word w ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    intro w
    have := word_mem_canonSpan closed_true w (fun _ _ => trivial)
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨m, -, -, -, rfl⟩
    exact Submodule.subset_span ⟨m, rfl⟩
  set S := Submodule.span ℂ (Set.range (canon (n := n)))
  have hS : Submodule.span ℂ (Set.range (word (n := n))) ≤ S :=
    Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact hword w)
  have hall : ∀ u : U n, u ∈ Submodule.span ℂ (Set.range (word (n := n))) := by
    intro u
    induction u using U.induction with
    | halg r =>
      rw [Algebra.algebraMap_eq_smul_one, ← word_nil]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
    | hι X =>
      rw [ι_eq_sum_e]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
      rw [← word_singleton]
      exact Submodule.subset_span ⟨[a], rfl⟩
    | hmul a b ha hb =>
      have : Submodule.span ℂ (Set.range (word (n := n))) *
          Submodule.span ℂ (Set.range (word (n := n))) ≤
            Submodule.span ℂ (Set.range (word (n := n))) := by
        rw [Submodule.span_mul_span]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨v ++ w, word_append v w⟩
      exact this (Submodule.mul_mem_mul ha hb)
    | hadd a b ha hb => exact Submodule.add_mem _ ha hb
  exact eq_top_iff.2 fun u _ => hS (hall u)

def filt (d : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ w : List (Fin n × Fin n), w.length ≤ d ∧ word w = u}

theorem word_mem_filt {w : List (Fin n × Fin n)} {d : ℕ} (h : w.length ≤ d) : word w ∈ filt (n := n) d :=
  Submodule.subset_span ⟨w, h, rfl⟩

theorem wordSpan_le_filt (P : Fin n × Fin n → Prop) (k : ℕ) : wordSpan (n := n) P k ≤ filt k :=
  Submodule.span_le.2 fun _ ⟨w, _, hw, hu⟩ => Submodule.subset_span ⟨w, hw.le, hu⟩

theorem filt_le_canonSpan (d : ℕ) : filt (n := n) d ≤ canonSpan (fun _ => True) 0 d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, hw, rfl⟩
  exact canonSpan_mono (Nat.zero_le _) hw (word_mem_canonSpan closed_true w fun _ _ => trivial)

theorem word_sub_canon_mem_filt (w : List (Fin n × Fin n)) :
    word w - canon (Multiset.toFinsupp (w : Multiset _)) ∈ filt (n := n) (w.length - 1) :=
  wordSpan_le_filt _ _ (word_sub_word_mem_of_perm closed_true (perm_expand w) fun _ _ => trivial)

def rootAt (a : Fin n × Fin n) (k : Fin n) : ℤ :=
  (if k = a.1 then 1 else 0) - (if k = a.2 then 1 else 0)

def wt (m : Fin n × Fin n →₀ ℕ) (k : Fin n) : ℤ := m.sum fun a c => (c : ℤ) * rootAt a k

theorem e_diag_mul_sub (k : Fin n) (a : Fin n × Fin n) :
    e (k, k) * e a - e a * e (k, k) = (rootAt a k : ℂ) • e a := by
  rw [e_mul_sub_mul]
  obtain ⟨i, j⟩ := a
  simp only [rootAt]
  by_cases hi : k = i <;> by_cases hj : k = j
  · subst hi; subst hj; simp
  · subst hi; simp [hj, Ne.symm hj]
  · subst hj; simp [hi]
  · simp [hi, hj, Ne.symm hj]

theorem e_diag_mul_word_sub (k : Fin n) (w : List (Fin n × Fin n)) :
    e (k, k) * word w - word w * e (k, k) = (((w.map fun a => rootAt a k).sum : ℤ) : ℂ) • word w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [word_cons, List.map_cons, List.sum_cons]
    have h1 := e_diag_mul_sub k a
    calc e (k, k) * (e a * word w) - e a * word w * e (k, k)
        = (e (k, k) * e a - e a * e (k, k)) * word w + e a * (e (k, k) * word w - word w * e (k, k)) := by
          noncomm_ring
      _ = _ := by
          rw [h1, ih, smul_mul_assoc, mul_smul_comm, ← add_smul]
          push_cast; ring_nf

theorem sum_rootAt_expand (m : Fin n × Fin n →₀ ℕ) (k : Fin n) :
    ((expand m).map fun a => rootAt a k).sum = wt m k := by
  have hw : ∀ w : List (Fin n × Fin n), (w.map fun a => rootAt a k).sum =
      wt (Multiset.toFinsupp (w : Multiset _)) k := by
    intro w
    induction w with
    | nil => simp [wt]
    | cons a w ih =>
      rw [List.map_cons, List.sum_cons, ih,
        show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset _) by simp,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, wt, wt,
        Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring),
        Finsupp.sum_single_index (by simp)]
      push_cast; ring
  rw [hw, toFinsupp_expand]

theorem e_diag_mul_canon_sub (k : Fin n) (m : Fin n × Fin n →₀ ℕ) :
    e (k, k) * canon m - canon m * e (k, k) = (wt m k : ℂ) • canon m := by
  rw [canon, e_diag_mul_word_sub, sum_rootAt_expand]

end GroundTheory.Automorphic.HarishChandra
end

section
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable def rhoDeriv (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) :
    Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ fun a => ∑ i, C (M i a.1) * (X (i, a.2) + C (c i a.2))

theorem rhoDeriv_X (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) (a : Fin n × Fin n) :
    rhoDeriv c M (X a) = ∑ i, C (M i a.1) * (X (i, a.2) + C (c i a.2)) :=
  mkDerivation_X ℂ _ a

theorem rhoDeriv_add (c : Matrix (Fin n) (Fin n) ℂ) (M N : gl n) :
    rhoDeriv c (M + N) = rhoDeriv c M + rhoDeriv c N := by
  apply derivation_ext
  intro a
  simp only [rhoDeriv_X, Derivation.add_apply, Matrix.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

theorem rhoDeriv_smul (c : Matrix (Fin n) (Fin n) ℂ) (r : ℂ) (M : gl n) :
    rhoDeriv c (r • M) = r • rhoDeriv c M := by
  apply derivation_ext
  intro a
  simp only [rhoDeriv_X, Derivation.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Finset.smul_sum, smul_eq_C_mul, mul_assoc]

theorem rhoDeriv_rhoDeriv_X (c : Matrix (Fin n) (Fin n) ℂ) (P Q : gl n) (a : Fin n × Fin n) :
    rhoDeriv c P (rhoDeriv c Q (X a)) =
      ∑ k, C ((P * Q) k a.1) * (X (k, a.2) + C (c k a.2)) := by
  rw [rhoDeriv_X, map_sum]
  simp only [Derivation.leibniz, Derivation.map_add, derivation_C, smul_zero, add_zero,
    smul_eq_mul, mul_zero, rhoDeriv_X, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul]
  ring

theorem rhoDeriv_lie (c : Matrix (Fin n) (Fin n) ℂ) (M N : gl n) :
    rhoDeriv c ⁅M, N⁆ = ⁅rhoDeriv c M, rhoDeriv c N⁆ := by
  apply derivation_ext
  intro a
  rw [Derivation.commutator_apply, rhoDeriv_rhoDeriv_X, rhoDeriv_rhoDeriv_X, rhoDeriv_X,
    LieRing.of_associative_ring_bracket]
  simp only [Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

noncomputable def rhoLie (c : Matrix (Fin n) (Fin n) ℂ) : gl n →ₗ⁅ℂ⁆ Module.End ℂ (Poly n) where
  toFun M := (rhoDeriv c M : Poly n →ₗ[ℂ] Poly n)
  map_add' M N := by rw [rhoDeriv_add]; rfl
  map_smul' r M := by rw [rhoDeriv_smul]; rfl
  map_lie' {M N} := by
    rw [rhoDeriv_lie, Derivation.commutator_coe_linear_map]

noncomputable def rho (c : Matrix (Fin n) (Fin n) ℂ) : U n →ₐ[ℂ] Module.End ℂ (Poly n) :=
  UniversalEnvelopingAlgebra.lift ℂ (rhoLie c)

theorem rho_ι_apply (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) (f : Poly n) :
    rho c (UniversalEnvelopingAlgebra.ι ℂ M) f = rhoDeriv c M f := by
  simp [rho, rhoLie]

theorem rho_e_apply (c : Matrix (Fin n) (Fin n) ℂ) (a : Fin n × Fin n) (f : Poly n) :
    rho c (e a) f = rhoDeriv c (E a) f :=
  rho_ι_apply c (E a) f

theorem rhoDeriv_E_X (c : Matrix (Fin n) (Fin n) ℂ) (i j a b : Fin n) :
    rhoDeriv c (E (i, j)) (X (a, b)) = if a = j then X (i, b) + C (c i b) else 0 := by
  rw [rhoDeriv_X, Finset.sum_eq_single i]
  · by_cases h : a = j
    · subst h; simp [E]
    · simp [E, Matrix.single_apply, Ne.symm h, h]
  · intro k _ hk
    simp [E, Matrix.single_apply, Ne.symm hk]
  · simp

noncomputable def rowDeriv (i j : Fin n) : Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ fun a => if a.1 = j then X (i, a.2) else 0

theorem rowDeriv_apply (i j : Fin n) (f : Poly n) : rowDeriv i j f = rowOp i j f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [rowDeriv, rowOp_apply, derivation_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p a hp =>
    rw [Derivation.leibniz, hp, rowOp_apply, rowOp_apply, smul_eq_mul, smul_eq_mul]
    have h1 : rowDeriv i j (X a) = ∑ k, X (i, k) * pderiv (j, k) (X a) := by
      obtain ⟨a1, a2⟩ := a
      simp only [rowDeriv, mkDerivation_X, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      rw [Finset.sum_eq_single a2]
      · by_cases h : a1 = j <;> simp [h]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    rw [h1]
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring

theorem rhoDeriv_zero_E (i j : Fin n) : rhoDeriv 0 (E (i, j)) = rowDeriv i j := by
  apply derivation_ext
  rintro ⟨a, b⟩
  rw [rhoDeriv_E_X]
  simp [rowDeriv, mkDerivation_X]

theorem rho_zero_e (i j : Fin n) : rho 0 (e (i, j)) = rowOp i j := by
  refine LinearMap.ext fun f => ?_
  rw [rho_e_apply, rhoDeriv_zero_E, rowDeriv_apply]

theorem rho_one_e_apply (i j : Fin n) (f : Poly n) :
    rho 1 (e (i, j)) f = pderiv (j, i) f + rowOp i j f := by
  rw [rho_e_apply, ← rowDeriv_apply, ← Derivation.add_apply]
  congr 1
  apply derivation_ext
  rintro ⟨a, b⟩
  rw [rhoDeriv_E_X, Derivation.add_apply, pderiv_X]
  simp only [rowDeriv, mkDerivation_X, Matrix.one_apply, Pi.single_apply, Prod.mk.injEq]
  by_cases h : a = j
  · subst h
    by_cases h' : b = i
    · subst h'; simp [add_comm]
    · simp [h'] <;> exact fun hh => h' hh.symm
  · simp [h]

noncomputable def shift : Poly n ≃ₐ[ℂ] Poly n :=
  AlgEquiv.ofAlgHom (aeval fun a => X a + C (if a.1 = a.2 then 1 else 0))
    (aeval fun a => X a - C (if a.1 = a.2 then 1 else 0))
    (by ext a : 1; simp) (by ext a : 1; simp)

theorem shift_X (a : Fin n × Fin n) : shift (X a : Poly n) = X a + C (if a.1 = a.2 then 1 else 0) := by
  simp [shift]

theorem shift_C (r : ℂ) : shift (C r : Poly n) = C r :=
  (shift : Poly n ≃ₐ[ℂ] Poly n).commutes r

theorem rhoDeriv_one_shift (M : gl n) (f : Poly n) :
    rhoDeriv 1 M (shift f) = shift (rhoDeriv 0 M f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    have : shift (C r : Poly n) = C r := (shift : Poly n ≃ₐ[ℂ] Poly n).commutes r
    rw [this, derivation_C, derivation_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p a hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    congr 2
    rw [shift_X, Derivation.map_add, derivation_C, add_zero, rhoDeriv_X, rhoDeriv_X, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [shift_X, shift_C, Matrix.one_apply]

theorem rho_one_shift (u : U n) (f : Poly n) : rho 1 u (shift f) = shift (rho 0 u f) := by
  induction u using U.induction generalizing f with
  | halg r => simp [AlgHom.commutes, Module.algebraMap_end_apply]
  | hι M => rw [rho_ι_apply, rho_ι_apply, rhoDeriv_one_shift]
  | hmul a b ha hb => rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
  | hadd a b ha hb => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb,
      map_add]

theorem rho_one_eq_zero_of_rho_zero_eq_zero (u : U n) (h : rho 0 u = 0) : rho 1 u = 0 := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨g, rfl⟩ := (shift : Poly n ≃ₐ[ℂ] Poly n).surjective f
  rw [rho_one_shift, h, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

def geDeg (t : ℕ) : Submodule ℂ (Poly n) where
  carrier := {f | ∀ s : Fin n × Fin n →₀ ℕ, s.degree < t → coeff s f = 0}
  add_mem' {f g} hf hg s hs := by rw [coeff_add, hf s hs, hg s hs, add_zero]
  zero_mem' s _ := coeff_zero s
  smul_mem' r f hf s hs := by rw [coeff_smul, hf s hs, smul_zero]

theorem geDeg_anti {t t' : ℕ} (h : t' ≤ t) : (geDeg t : Submodule ℂ (Poly n)) ≤ geDeg t' :=
  fun _ hf s hs => hf s (lt_of_lt_of_le hs h)

theorem monomial_mem_geDeg {t : ℕ} (s : Fin n × Fin n →₀ ℕ) (c : ℂ) (h : t ≤ s.degree) :
    (monomial s c : Poly n) ∈ geDeg t := by
  intro s' hs'
  rw [coeff_monomial, if_neg]
  rintro rfl
  omega

theorem constantCoeff_eq_zero_of_mem_geDeg {f : Poly n} (hf : f ∈ geDeg 1) :
    constantCoeff f = 0 := by
  have h0 : constantCoeff f = coeff 0 f := by rw [constantCoeff_eq]
  rw [h0]
  exact hf 0 (by simp)

theorem mem_geDeg_of_isHomogeneous {f : Poly n} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ geDeg d := by
  intro s hs
  by_contra h
  have h2 : s.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hf h
  omega

theorem map_mem_of_monomial (L : Poly n →ₗ[ℂ] Poly n) (P : Submodule ℂ (Poly n))
    (Q : (Fin n × Fin n →₀ ℕ) → Prop) {f : Poly n} (hf : ∀ s, coeff s f ≠ 0 → Q s)
    (h : ∀ s (c : ℂ), Q s → L (monomial s c) ∈ P) : L f ∈ P := by
  rw [f.as_sum, map_sum]
  exact Submodule.sum_mem _ fun s hs => h s _ (hf s (mem_support_iff.1 hs))

theorem degree_sub_single {s : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n} (h : s a ≠ 0) :
    (s - Finsupp.single a 1).degree + 1 = s.degree := by
  have hle : Finsupp.single a 1 ≤ s := by
    rw [Finsupp.single_le_iff]; omega
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

theorem pderiv_monomial_mem_geDeg {t : ℕ} (a : Fin n × Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : pderiv a (monomial s c : Poly n) ∈ geDeg (t - 1) := by
  rw [pderiv_monomial]
  by_cases hs : s a = 0
  · rw [hs, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
  · apply monomial_mem_geDeg
    have := degree_sub_single hs
    omega

theorem pderiv_mem_geDeg {t : ℕ} (a : Fin n × Fin n) {f : Poly n} (hf : f ∈ geDeg t) :
    pderiv a f ∈ geDeg (t - 1) := by
  refine map_mem_of_monomial (pderiv a : Derivation ℂ (Poly n) (Poly n)).toLinearMap _
    (fun s => t ≤ s.degree) (fun s hs => ?_) (fun s c hs => pderiv_monomial_mem_geDeg a s c hs)
  by_contra hlt
  exact hs (hf s (not_le.1 hlt))

theorem rowOp_monomial (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i j (monomial s c) =
      ∑ k, monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)) (c * s (j, k)) := by
  rw [rowOp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]

theorem rowOp_monomial_term_mem {i j k : Fin n} {s : Fin n × Fin n →₀ ℕ} (c : ℂ)
    (P : Submodule ℂ (Poly n))
    (h : s (j, k) ≠ 0 → (monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1))
        (c * s (j, k)) : Poly n) ∈ P) :
    (monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)) (c * s (j, k)) : Poly n)
      ∈ P := by
  by_cases hs : s (j, k) = 0
  · rw [hs, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
  · exact h hs

theorem degree_rowOp_term {i j k : Fin n} {s : Fin n × Fin n →₀ ℕ} (hs : s (j, k) ≠ 0) :
    (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)).degree = s.degree := by
  rw [map_add, Finsupp.degree_single, ← degree_sub_single hs]
  ring

theorem rowOp_monomial_mem_geDeg {t : ℕ} (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : rowOp i j (monomial s c) ∈ geDeg t := by
  rw [rowOp_monomial]
  refine Submodule.sum_mem _ fun k _ => rowOp_monomial_term_mem c _ fun hs => ?_
  apply monomial_mem_geDeg
  rw [degree_rowOp_term hs]; exact h

theorem rowOp_mem_geDeg {t : ℕ} (i j : Fin n) {f : Poly n} (hf : f ∈ geDeg t) :
    rowOp i j f ∈ geDeg t := by
  refine map_mem_of_monomial (rowOp i j) _ (fun s => t ≤ s.degree) (fun s hs => ?_)
    (fun s c hs => rowOp_monomial_mem_geDeg i j s c hs)
  by_contra hlt
  exact hs (hf s (not_le.1 hlt))

noncomputable def iterPd (w : List (Fin n × Fin n)) (f : Poly n) : Poly n :=
  w.foldr (fun a g => pderiv (a.2, a.1) g) f

@[simp] theorem iterPd_nil (f : Poly n) : iterPd [] f = f := rfl

@[simp] theorem iterPd_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) (f : Poly n) :
    iterPd (a :: w) f = pderiv (a.2, a.1) (iterPd w f) := rfl

theorem iterPd_mem_geDeg (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n} (hf : f ∈ geDeg t) :
    iterPd w f ∈ geDeg (t - w.length) := by
  induction w with
  | nil => simpa using hf
  | cons a w ih =>
    rw [iterPd_cons, List.length_cons, ← Nat.sub_sub]
    exact pderiv_mem_geDeg _ ih

theorem rho_one_word_sub_iterPd (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n}
    (hw : w.length ≤ t) (hf : f ∈ geDeg t) :
    rho 1 (word w) f - iterPd w f ∈ geDeg (t - w.length + 1) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.length_cons] at hw ⊢
    have ih := ih (by omega)
    rw [word_cons, map_mul, Module.End.mul_apply, iterPd_cons]
    obtain ⟨i, j⟩ := a
    rw [rho_one_e_apply]
    set g := rho 1 (word w) f
    have e1 : pderiv (j, i) g + rowOp i j g - pderiv (j, i) (iterPd w f) =
        pderiv (j, i) (g - iterPd w f) + rowOp i j (g - iterPd w f) + rowOp i j (iterPd w f) := by
      rw [map_sub, map_sub]; abel
    rw [e1]
    have ht : t - (w.length + 1) + 1 = t - w.length := by omega
    rw [ht]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · have := pderiv_mem_geDeg (j, i) ih
      rwa [Nat.add_sub_cancel] at this
    · exact geDeg_anti (by omega) (rowOp_mem_geDeg i j ih)
    · exact rowOp_mem_geDeg i j (iterPd_mem_geDeg w hf)

theorem constantCoeff_rho_one_word_of_lt (w : List (Fin n × Fin n)) (f : Poly n) (d : ℕ)
    (hf : f.IsHomogeneous d) (h : w.length < d) :
    constantCoeff (rho 1 (word w) f) = 0 := by
  have hf' := mem_geDeg_of_isHomogeneous hf
  have h1 := rho_one_word_sub_iterPd w h.le hf'
  have h2 := iterPd_mem_geDeg w hf'
  rw [← sub_add_cancel (rho 1 (word w) f) (iterPd w f), map_add,
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h1),
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h2), add_zero]

theorem toFinsupp_map_swap_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Multiset.toFinsupp (((a :: w).map Prod.swap : List _) : Multiset (Fin n × Fin n)) =
      Finsupp.single (a.2, a.1) 1 +
        Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) := by
  rw [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton]
  rfl

theorem iterPd_monomial (w : List (Fin n × Fin n)) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    ∃ κ : ℂ, iterPd w (monomial s c) =
        monomial (s - Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _)) (c * κ) ∧
      (κ ≠ 0 ↔ Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) ≤ s) := by
  induction w with
  | nil => exact ⟨1, by simp, by simp⟩
  | cons a w ih =>
    obtain ⟨κ, h1, h2⟩ := ih
    rw [toFinsupp_map_swap_cons]
    generalize Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) = T
      at h1 h2 ⊢
    refine ⟨κ * ((s - T) (a.2, a.1) : ℕ), ?_, ?_⟩
    · rw [iterPd_cons, h1, pderiv_monomial, tsub_tsub, add_comm T, mul_assoc]
    · rw [mul_ne_zero_iff, h2, Nat.cast_ne_zero, Finsupp.tsub_apply]
      constructor
      · rintro ⟨hT, hb⟩ x
        rw [Finsupp.add_apply, Finsupp.single_apply]
        have := hT x
        split_ifs with hx
        · subst hx; omega
        · omega
      · intro h
        have hx : ∀ x, T x ≤ s x := fun x => le_trans (by simp) (h x)
        refine ⟨hx, ?_⟩
        have := h (a.2, a.1)
        rw [Finsupp.add_apply, Finsupp.single_eq_same] at this
        omega

theorem constantCoeff_rho_one_word_monomial (w : List (Fin n × Fin n))
    (s : Fin n × Fin n →₀ ℕ) (h : w.length = s.degree) :
    constantCoeff (rho 1 (word w) (monomial s 1)) ≠ 0 ↔
      Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) = s := by
  have hf' : (monomial s (1 : ℂ) : Poly n) ∈ geDeg s.degree := monomial_mem_geDeg s 1 le_rfl
  have h1 := rho_one_word_sub_iterPd w h.le hf'
  rw [← sub_add_cancel (rho 1 (word w) (monomial s 1)) (iterPd w (monomial s 1)), map_add,
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h1), zero_add]
  obtain ⟨κ, hκ, hiff⟩ := iterPd_monomial w s 1
  rw [hκ, constantCoeff_monomial, one_mul]
  set T := Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n))
  constructor
  · intro hne
    split_ifs at hne with h0
    · exact le_antisymm (hiff.1 hne) (tsub_eq_zero_iff_le.1 h0)
    · exact absurd rfl hne
  · rintro rfl
    rw [tsub_self, if_pos rfl]
    exact hiff.2 le_rfl

end GroundTheory.Automorphic.HarishChandra
end

section
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable def transposeExp (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.mapDomain Prod.swap m

theorem transposeExp_injective : Function.Injective (transposeExp (n := n)) :=
  Finsupp.mapDomain_injective Prod.swap_injective

theorem toFinsupp_map_swap (w : List (Fin n × Fin n)) :
    Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) =
      transposeExp (Multiset.toFinsupp (w : Multiset (Fin n × Fin n))) := by
  induction w with
  | nil => simp [transposeExp]
  | cons a w ih =>
    rw [List.map_cons,
      show ((Prod.swap a :: w.map Prod.swap : List _) : Multiset _) =
        {Prod.swap a} + ((w.map Prod.swap : List _) : Multiset _) by simp,
      show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset _) by simp,
      Multiset.toFinsupp_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      Multiset.toFinsupp_singleton, ih, transposeExp, transposeExp, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single]

theorem degree_transposeExp (m : Fin n × Fin n →₀ ℕ) :
    (transposeExp m).degree = m.degree := by
  have h1 := degree_toFinsupp ((expand m).map Prod.swap)
  rw [toFinsupp_map_swap, toFinsupp_expand, List.length_map, length_expand] at h1
  exact h1

theorem constantCoeff_rho_one_canon_monomial (m s : Fin n × Fin n →₀ ℕ) (h : m.degree = s.degree) :
    constantCoeff (rho 1 (canon m) (monomial s 1)) ≠ 0 ↔ transposeExp m = s := by
  rw [canon, constantCoeff_rho_one_word_monomial _ _ (by rw [length_expand, h]),
    toFinsupp_map_swap, toFinsupp_expand]

theorem coeff_eq_zero_of_rho_one (s : Finset (Fin n × Fin n →₀ ℕ)) (c : (Fin n × Fin n →₀ ℕ) → ℂ)
    (h : rho 1 (∑ m ∈ s, c m • canon m) = 0) : ∀ m ∈ s, c m = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨m, hms, hm⟩ := hne
  set s' := s.filter fun m => c m ≠ 0
  have hne' : s'.Nonempty := ⟨m, Finset.mem_filter.2 ⟨hms, hm⟩⟩
  obtain ⟨m₀, hm₀, hmax⟩ := s'.exists_max_image Finsupp.degree hne'
  rw [Finset.mem_filter] at hm₀
  set N := transposeExp m₀
  have hN : N.degree = m₀.degree := degree_transposeExp m₀
  have hhom : (monomial N (1 : ℂ)).IsHomogeneous m₀.degree := by
    rw [← hN]; exact isHomogeneous_monomial _ rfl
  have key : ∀ m ∈ s, m ≠ m₀ → c m * constantCoeff (rho 1 (canon m) (monomial N 1)) = 0 := by
    intro m hm hne
    by_cases hc : c m = 0
    · rw [hc, zero_mul]
    have hdeg : m.degree ≤ m₀.degree := hmax m (Finset.mem_filter.2 ⟨hm, hc⟩)
    rcases hdeg.lt_or_eq with hlt | heq
    · rw [canon, constantCoeff_rho_one_word_of_lt _ _ _ hhom (by rw [length_expand]; exact hlt),
        mul_zero]
    · have : ¬ constantCoeff (rho 1 (canon m) (monomial N 1)) ≠ 0 := by
        rw [constantCoeff_rho_one_canon_monomial _ _ (by rw [heq, hN])]
        exact fun h' => hne (transposeExp_injective h')
      rw [not_not.1 this, mul_zero]
  have hsum := congrArg (fun T : Module.End ℂ (Poly n) => constantCoeff (T (monomial N 1))) h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C] at hsum
  rw [Finset.sum_eq_single m₀ (fun m hm hne => key m hm hne) (fun h' => absurd hm₀.1 h')] at hsum
  have h0 : constantCoeff (rho 1 (canon m₀) (monomial N 1)) ≠ 0 :=
    (constantCoeff_rho_one_canon_monomial _ _ hN.symm).2 rfl
  exact hm₀.2 ((mul_eq_zero.1 hsum).resolve_right h0)

theorem linearIndependent_canon : LinearIndependent ℂ (canon (n := n)) := by
  rw [linearIndependent_iff']
  intro s c hs
  exact coeff_eq_zero_of_rho_one s c (by rw [hs, map_zero])

noncomputable def pbw : Module.Basis (Fin n × Fin n →₀ ℕ) ℂ (U n) :=
  Module.Basis.mk linearIndependent_canon span_canon_eq_top.ge

@[simp] theorem pbw_apply (m : Fin n × Fin n →₀ ℕ) : pbw (n := n) m = canon m :=
  Module.Basis.mk_apply _ _ _

theorem sum_repr_canon (u : U n) :
    ∑ m ∈ (pbw.repr u).support, pbw.repr u m • canon m = u := by
  conv_rhs => rw [← pbw.linearCombination_repr u]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp

theorem eq_zero_of_rho_one_eq_zero {u : U n} (h : rho 1 u = 0) : u = 0 := by
  rw [← sum_repr_canon u] at h ⊢
  have := coeff_eq_zero_of_rho_one _ _ h
  exact Finset.sum_eq_zero fun m hm => by rw [this m hm, zero_smul]

theorem eq_zero_of_rho_zero_eq_zero {u : U n} (h : rho 0 u = 0) : u = 0 :=
  eq_zero_of_rho_one_eq_zero (rho_one_eq_zero_of_rho_zero_eq_zero u h)

end GroundTheory.Automorphic.HarishChandra
end
