import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
import Formalism.GradedWeylDivisibility.StatementD
import Lemmata.GeneralBFactSecondTer.Imports
import Formalism.GradedWeylDivisibility.FinalD

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qa_nu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin n → ℕ := fun t => (mu t - mu (lastIdx n)).toNat

def qa_row {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) : Fin (colH mu c) → Fin n :=
  fun p => (I c).1.orderEmbOfFin (I c).2 p

lemma qa_row_strictMono {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    StrictMono (qa_row I c) := ((I c).1.orderEmbOfFin (I c).2).strictMono

def qa_exp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : Fin n × Fin n →₀ ℕ :=
  ∑ c : ↥(TCols mu), ∑ p : Fin (colH mu c), Finsupp.single (qa_row I c p, Fin.castLE (colH_le mu c) p) 1

lemma qa_lower_iff {n : ℕ} (Q : Fin n → Prop) [DecidablePred Q] (hQ : ∀ q q', q' ≤ q → Q q → Q q') (p : Fin n) :
    Q p ↔ p.val < (univ.filter Q).card := by
  first | exact Bl.general_b_fact_second_ter.goal1 .. | (apply Bl.general_b_fact_second_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter.goal1 <;> assumption)

lemma qa_lt_colH {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (p : Fin n) :
    p.val < colH mu c ↔ c ≤ mu p :=
  (qa_lower_iff (fun m => c ≤ mu m) (fun _ _ hqq hq => hq.trans (hmu hqq)) p).symm

lemma qa_emb_le_iff {n h : ℕ} (J : Finset (Fin n)) (hJ : J.card = h) (p : Fin h) (a : Fin n) :
    J.orderEmbOfFin hJ p ≤ a ↔ p.val < (J.filter (· ≤ a)).card := by
  have h1 : (J.filter (· ≤ a)).card = (univ.filter fun q : Fin h => J.orderEmbOfFin hJ q ≤ a).card := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J hJ]
    rw [Finset.filter_map, Finset.card_map]
    rfl
  rw [h1]
  exact qa_lower_iff (fun q : Fin h => J.orderEmbOfFin hJ q ≤ a)
    (fun q q' hqq hq => ((J.orderEmbOfFin hJ).monotone hqq).trans hq) p

lemma qa_seg (L U : ℤ) (Q : ℤ → Prop) [DecidablePred Q] (hQ : ∀ c, L < c → c + 1 ≤ U → Q (c + 1) → Q c)
    (c : ℤ) (hc : c ∈ Finset.Ioc L U) : Q c ↔ c - L ≤ ((Finset.Ioc L U).filter Q).card := by
  rw [Finset.mem_Ioc] at hc
  have hdown : ∀ k : ℕ, ∀ d, L < d → d + k ≤ U → Q (d + k) → Q d := by
    intro k
    induction k with
    | zero => intro d _ _ h; simpa using h
    | succ k ih =>
      intro d hd hU h
      apply ih d hd (by push_cast at hU; omega)
      apply hQ _ (by omega) (by push_cast at hU; omega)
      have : d + (k : ℤ) + 1 = d + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact h
  have hdown' : ∀ d e, L < d → d ≤ e → e ≤ U → Q e → Q d := by
    intro d e hd hde he h
    have := hdown (e - d).toNat d hd (by omega)
    apply this
    have h3 : d + ((e - d).toNat : ℤ) = e := by omega
    rw [h3]; exact h
  constructor
  · intro h
    have : Finset.Ioc L c ⊆ (Finset.Ioc L U).filter Q := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hd.1, hd.2.trans hc.2⟩, hdown' d c hd.1 hd.2 hc.2 h⟩
    have h2 := Finset.card_le_card this
    rw [Int.card_Ioc] at h2
    omega
  · intro h
    by_contra hn
    have : (Finset.Ioc L U).filter Q ⊆ Finset.Ioo L c := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ioc] at hd
      rw [Finset.mem_Ioo]
      refine ⟨hd.1.1, ?_⟩
      by_contra hle
      exact hn (hdown' c d hc.1 (not_lt.mp hle) hd.1.2 hd.2)
    have h2 := Finset.card_le_card this
    rw [Int.card_Ioo] at h2
    omega

def qa_cnt {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (a : Fin n) : ℕ :=
  ((I c).1.filter (· ≤ a)).card

lemma qa_cnt_le {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (a : Fin n) :
    qa_cnt I c a ≤ colH mu c := (card_filter_le _ _).trans (I c).2.le

lemma qa_row_le_iff {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (q : Fin (colH mu c))
    (a : Fin n) : qa_row I c q ≤ a ↔ q.val < qa_cnt I c a := qa_emb_le_iff (I c).1 (I c).2 q a

lemma qa_exp_apply {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (b p : Fin n) :
    qa_exp I (b, p) = ∑ c : ↥(TCols mu), ∑ q : Fin (colH mu c),
      if qa_row I c q = b ∧ q.val = p.val then 1 else 0 := by
  simp only [qa_exp, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq, Fin.ext_iff,
    Fin.val_castLE]

lemma qa_cum {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (a p : Fin n) :
    ∑ b : Fin n with b ≤ a, qa_exp I (b, p) =
      (univ.filter fun c : ↥(TCols mu) => p.val < qa_cnt I c a).card := by
  simp only [qa_exp_apply]
  rw [Finset.sum_comm, Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have h1 : ∀ q : Fin (colH mu c),
      (∑ b : Fin n with b ≤ a, if qa_row I c q = b ∧ q.val = p.val then 1 else 0) =
        if (q.val = p.val ∧ q.val < qa_cnt I c a) then 1 else 0 := by
    intro q
    rw [Finset.sum_filter, Finset.sum_eq_single (qa_row I c q)]
    · have := qa_row_le_iff I c q a
      by_cases h : qa_row I c q ≤ a
      · simp [h, this.mp h]
      · have h' : ¬ q.val < qa_cnt I c a := fun hh => h (this.mpr hh)
        simp [h, h']
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simp only [h1]
  split_ifs with hp
  · have hq : p.val < colH mu c := hp.trans_le (qa_cnt_le I c a)
    rw [Finset.sum_eq_single ⟨p.val, hq⟩]
    · simp [hp]
    · intro q _ hq'
      rw [if_neg]
      rintro ⟨h2, _⟩
      exact hq' (Fin.ext h2)
    · simp
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h2, h3⟩
    exact hp (h2 ▸ h3)

lemma qa_card_sub {T : Finset ℤ} (P : ↥T → Prop) [DecidablePred P]
    [DecidablePred fun d => ∃ h : d ∈ T, P ⟨d, h⟩] :
    (univ.filter P).card = (T.filter fun d => ∃ h : d ∈ T, P ⟨d, h⟩).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext d
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨h, h, hp⟩
  · rintro ⟨_, h, hp⟩; exact ⟨h, hp⟩

lemma qa_std_iff {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (hI : StdT I) (c : ↥(TCols mu))
    (a p : Fin n) :
    p.val < qa_cnt I c a ↔
      (c : ℤ) - mu (lastIdx n) ≤ ((∑ b : Fin n with b ≤ a, qa_exp I (b, p) : ℕ) : ℤ) := by
  classical
  rw [qa_cum, qa_card_sub]
  have := qa_seg (mu (lastIdx n)) (mu 0) (fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) ?_ c c.2
  · rw [← TCols] at this
    rw [← this]
    exact ⟨fun h => ⟨c.2, h⟩, fun ⟨_, h⟩ => h⟩
  · rintro d hd hU ⟨h, hp⟩
    have hd' : d ∈ TCols mu := Finset.mem_Ioc.mpr ⟨hd, by omega⟩
    exact ⟨hd', hp.trans_le (hI ⟨d, hd'⟩ h a)⟩

theorem qa_exp_inj {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I J : TIdx mu) (hI : StdT I) (hJ : StdT J)
    (h : qa_exp I = qa_exp J) : I = J := by
  funext c
  apply Subtype.ext
  have hrow : ∀ q, qa_row I c q = qa_row J c q := by
    intro q
    have hq : q.val < n := q.2.trans_le (colH_le mu c)
    have key : ∀ a, qa_row I c q ≤ a ↔ qa_row J c q ≤ a := by
      intro a
      rw [qa_row_le_iff, qa_row_le_iff]
      have h1 := qa_std_iff I hI c a ⟨q.val, hq⟩
      have h2 := qa_std_iff J hJ c a ⟨q.val, hq⟩
      rw [h] at h1
      exact h1.trans h2.symm
    exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)
  rw [← Finset.map_orderEmbOfFin_univ (I c).1 (I c).2, ← Finset.map_orderEmbOfFin_univ (J c).1 (J c).2]
  ext x
  simp only [mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, (hrow q).symm⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, hrow q⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qa_S {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : ℕ := ∑ b : Fin n with b ≤ a, m (b, p)

lemma qa_S_mono {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (p : Fin n) {a a' : Fin n} (h : a ≤ a') :
    qa_S m a p ≤ qa_S m a' p := by
  unfold qa_S
  apply Finset.sum_le_sum_of_subset
  intro b hb
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact hb.trans h

lemma qa_S_le {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : qa_S m a p ≤ ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma qa_S_last {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (p : Fin n) :
    qa_S m (lastIdx n) p = ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  congr 1
  ext b
  simp only [mem_filter, mem_univ, true_and, iff_true]
  rw [Fin.le_def]
  have := b.2
  simp only [lastIdx]
  omega

lemma qa_Slt {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) :
    (∑ b : Fin n with b < a, m (b, p)) = 0 ∨ ∃ b, b < a ∧ (∑ b : Fin n with b < a, m (b, p)) = qa_S m b p := by
  obtain ⟨a, ha⟩ := a
  cases a with
  | zero =>
    left
    apply Finset.sum_eq_zero
    intro b hb
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hb
    omega
  | succ k =>
    right
    refine ⟨⟨k, by omega⟩, by simp [Fin.lt_def], ?_⟩
    unfold qa_S
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def, Fin.le_def]
    omega

lemma qa_of_cum {n : ℕ} (m m' : Fin n × Fin n →₀ ℕ) (h : ∀ a p, qa_S m a p = qa_S m' a p) : m = m' := by
  ext ⟨a, p⟩
  have hsplit : ∀ (m : Fin n × Fin n →₀ ℕ), qa_S m a p = m (a, p) + ∑ b : Fin n with b < a, m (b, p) := by
    intro m
    unfold qa_S
    have : (univ.filter fun b : Fin n => b ≤ a) = insert a (univ.filter fun b : Fin n => b < a) := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      exact le_iff_eq_or_lt
    rw [this, Finset.sum_insert (by simp)]
  have h1 := h a p
  rw [hsplit m, hsplit m'] at h1
  rcases qa_Slt m a p with h0 | ⟨b, hb, h2⟩
  · rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · omega
    ·
      have h3 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b' p
      omega
  · have h3 : qa_S m' b p ≤ ∑ b : Fin n with b < a, m' (b, p) := by
      unfold qa_S
      apply Finset.sum_le_sum_of_subset
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact lt_of_le_of_lt hx hb
    rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · have := h b p
      omega
    · have h4 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b p
      have := h b' p
      omega

def qa_g {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n) : Fin n :=
  if h : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n then
    ⟨(univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card, h⟩ else lastIdx n

lemma qa_g_le_iff {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n)
    (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ)) (a : Fin n) : qa_g m k p ≤ a ↔ k ≤ qa_S m a p := by
  have hl := qa_lower_iff (fun a : Fin n => (qa_S m a p : ℤ) < k)
    (fun q q' hqq hq => lt_of_le_of_lt (by exact_mod_cast qa_S_mono m p hqq) hq)
  have hn : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n := by
    have h1 := hl (lastIdx n)
    rw [qa_S_last] at h1
    have h2 : ¬ (lastIdx n).val < (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card :=
      fun hh => absurd (h1.mpr hh) (not_lt.mpr hk)
    have h3 : (lastIdx n).val = n - 1 := rfl
    have := NeZero.pos n
    omega
  unfold qa_g
  rw [dif_pos hn, Fin.le_def]
  have h1 := hl a
  constructor
  · intro h
    by_contra hc
    have := h1.mp (not_le.mp hc)
    simp only at h
    omega
  · intro h
    by_contra hc
    have := h1.mpr (not_le.mp hc)
    omega

lemma qa_last_le {n : ℕ} [NeZero n] (p : Fin n) : p ≤ lastIdx n := by
  rw [Fin.le_def]
  have := p.2
  simp only [lastIdx]
  omega

lemma qa_nu_cast {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (p : Fin n) :
    (qa_nu mu p : ℤ) = mu p - mu (lastIdx n) := by
  unfold qa_nu
  have : mu (lastIdx n) ≤ mu p := hmu (qa_last_le p)
  omega

lemma qa_nu_antitone {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) : Antitone (qa_nu mu) := by
  intro p p' h
  have := hmu h
  unfold qa_nu
  omega

lemma qa_g_step {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (k : ℤ) (hk1 : 1 ≤ k)
    (p p' : Fin n) (hpp : p'.val = p.val + 1) (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ))
    (hk' : k ≤ (∑ b : Fin n, m (b, p') : ℕ)) : qa_g m k p < qa_g m k p' := by
  have h1 : k ≤ qa_S m (qa_g m k p') p' := (qa_g_le_iff m k p' hk' _).mp le_rfl
  have h2 : qa_S m (qa_g m k p') p' ≤ 0 + ∑ b : Fin n with b < qa_g m k p', m (b, p) :=
    hint p p' hpp (qa_g m k p')
  by_contra hc
  rcases qa_Slt m (qa_g m k p') p with h0 | ⟨b, hb, h3⟩
  · omega
  · have h4 : ¬ qa_g m k p ≤ b := fun hh => hc (lt_of_le_of_lt hh hb)
    rw [qa_g_le_iff m k p hk] at h4
    omega

lemma qa_g_lt {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (ν : Fin n → ℕ)
    (hν : Antitone ν) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = ν t) (k : ℤ) (hk1 : 1 ≤ k) :
    ∀ (d : ℕ) (p p' : Fin n), p'.val = p.val + d + 1 → k ≤ ν p' → qa_g m k p < qa_g m k p' := by
  intro d
  induction d with
  | zero =>
    intro p p' hpp hk
    have h1 : ν p' ≤ ν p := hν (by rw [Fin.le_def]; omega)
    exact qa_g_step m hint k hk1 p p' (by omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)
  | succ d ih =>
    intro p p' hpp hk
    have hlt : p.val + d + 1 < n := by have := p'.2; omega
    have h1 : ν p' ≤ ν ⟨p.val + d + 1, hlt⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    refine (ih p ⟨p.val + d + 1, hlt⟩ rfl (by omega)).trans ?_
    exact qa_g_step m hint k hk1 _ p' (by simp only; omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)

lemma qa_fill_exists {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hint : Formalism.GradedWeylDivisibility.Interlaced m) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) :
    ∃ I : TIdx mu, ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
  have hf : ∀ c : ↥(TCols mu), StrictMono fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
    intro c q q' hqq
    have hc := Finset.mem_Ioc.mp c.2
    rw [Fin.lt_def] at hqq
    refine qa_g_lt m hint (qa_nu mu) (qa_nu_antitone hmu) hcol _ (by omega) (q'.val - q.val - 1) _ _ ?_ ?_
    · simp only [Fin.val_castLE]; omega
    · rw [qa_nu_cast hmu]
      have := (qa_lt_colH hmu c (Fin.castLE (colH_le mu c) q')).mp q'.2
      omega
  refine ⟨fun c => ⟨univ.map ⟨_, (hf c).injective⟩, by simp⟩, fun c q => ?_⟩
  have := Finset.orderEmbOfFin_unique (s := univ.map ⟨_, (hf c).injective⟩) (by simp) (f := fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) (by simp) (hf c)
  exact (congrFun this q).symm

lemma qa_fill_cnt {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q))
    (c : ↥(TCols mu)) (a p : Fin n) :
    p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p := by
  have hc := Finset.mem_Ioc.mp c.2
  have key : ∀ hp : p.val < colH mu c, (p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p) := by
    intro hp
    have h1 := qa_row_le_iff I c ⟨p.val, hp⟩ a
    rw [hI] at h1
    have h2 : Fin.castLE (colH_le mu c) ⟨p.val, hp⟩ = p := Fin.ext rfl
    rw [h2, qa_g_le_iff] at h1
    · exact h1.symm
    · rw [hcol, qa_nu_cast hmu]
      have := (qa_lt_colH hmu c p).mp hp
      omega
  constructor
  · intro h
    exact (key (h.trans_le (qa_cnt_le I c a))).mp h
  · intro h
    have h1 := qa_S_le m a p
    rw [hcol] at h1
    have h2 := qa_nu_cast hmu p
    have hp : p.val < colH mu c := (qa_lt_colH hmu c p).mpr (by omega)
    exact (key hp).mpr h

lemma qa_fill_std {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) : StdT I := by
  intro c hc a
  change qa_cnt I ⟨(c : ℤ) + 1, hc⟩ a ≤ qa_cnt I c a
  by_contra hlt
  have hlt := not_le.mp hlt
  have hn : qa_cnt I c a < n := hlt.trans_le ((qa_cnt_le I _ a).trans (colH_le mu _))
  have h1 := (qa_fill_cnt hmu m hcol I hI ⟨(c : ℤ) + 1, hc⟩ a ⟨qa_cnt I c a, hn⟩).mp hlt
  have h2 := (qa_fill_cnt hmu m hcol I hI c a ⟨qa_cnt I c a, hn⟩).mpr (by simp only at h1; omega)
  exact lt_irrefl _ h2

lemma qa_fill_exp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) :
    qa_exp I = m := by
  classical
  apply qa_of_cum
  intro a p
  change ∑ b : Fin n with b ≤ a, qa_exp I (b, p) = qa_S m a p
  rw [qa_cum, qa_card_sub]
  have h1 := qa_S_le m a p
  rw [hcol] at h1
  have h2 := qa_nu_cast hmu p
  have h3 : mu p ≤ mu 0 := hmu (Fin.zero_le p)
  have : ((TCols mu).filter fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) =
      Finset.Ioc (mu (lastIdx n)) (mu (lastIdx n) + qa_S m a p) := by
    ext d
    simp only [mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, h, hp⟩
      have := (qa_fill_cnt hmu m hcol I hI ⟨d, h⟩ a p).mp hp
      have hd' := Finset.mem_Ioc.mp hd
      simp only at this
      omega
    · rintro ⟨hd1, hd2⟩
      have hd : d ∈ TCols mu := Finset.mem_Ioc.mpr ⟨hd1, by omega⟩
      exact ⟨hd, hd, (qa_fill_cnt hmu m hcol I hI ⟨d, hd⟩ a p).mpr (by simp only; omega)⟩
  rw [this, Int.card_Ioc]
  simp

theorem qa_exp_surj {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hm : m ∈ Formalism.GradedWeylDivisibility.ssIdx n n (qa_nu mu)) : ∃ I : TIdx mu, StdT I ∧ qa_exp I = m := by
  obtain ⟨I, hI⟩ := qa_fill_exists hmu m hm.1 hm.2
  exact ⟨I, qa_fill_std hmu m hm.2 I hI, qa_fill_exp hmu m hm.2 I hI⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qa_P (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    MvPolynomial (Fin n × Fin n) R :=
  ∏ c : ↥(TCols mu), initMinor R (qa_row I c) (colH_le mu c)

def qa_e {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin (Fintype.card ↥(TCols mu)) ≃ ↥(TCols mu) :=
  (Fintype.equivFin ↥(TCols mu)).symm

lemma tableauBideterminant_eq_bideterminant (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I = bideterminant R (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_P bideterminant
  exact (Fintype.prod_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

lemma qa_exp_eq_bidetExp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_exp I = bidetExp (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_exp bidetExp
  exact (Fintype.sum_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

private theorem lt_colH_iff_le {n : ℕ} {mu : Fin n → ℤ} (hmu : Antitone mu) (c : ℤ) (t : Fin n) :
    (t : ℕ) < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (Finset.univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      omega
    exact absurd (lt_of_lt_of_le h ((Finset.card_le_card hsub).trans (Fin.card_Iio t).le)) (lt_irrefl _)
  · intro h
    have hsub : Finset.Iic t ⊆ (Finset.univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hmu hm)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((Fin.card_Iic t).symm.le.trans (Finset.card_le_card hsub))

lemma qa_shape {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    shapeDeg (n := n) (fun k => colH mu (qa_e mu k)) = qa_nu mu := by
  have hmu' : Antitone mu := hmu
  funext t
  unfold shapeDeg qa_nu
  have h1 : (Finset.univ.filter fun k => (t : ℕ) < colH mu ↑(qa_e mu k)).card =
      (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card :=
    Finset.card_equiv (qa_e mu) (by simp)
  have h2 : (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card =
      ((TCols mu).filter fun c => (t : ℕ) < colH mu c).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort (TCols mu) (fun c => if (t : ℕ) < colH mu c then 1 else 0)
  have h3 : ((TCols mu).filter fun c => (t : ℕ) < colH mu c) = Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    have h0 : mu t ≤ mu 0 := hmu' (by simp [Fin.le_iff_val_le_val])
    simp only [TCols, Finset.mem_filter, Finset.mem_Ioc, lt_colH_iff_le hmu']
    constructor <;> intro h <;> omega
  exact h1.trans (h2.trans (by rw [h3, Int.card_Ioc]))

lemma tableauBideterminant_degree_leadingCoeff (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    (colLex n n).degree (qa_P R I) = qa_exp I ∧ (colLex n n).leadingCoeff (qa_P R I) = 1 := by
  rw [tableauBideterminant_eq_bideterminant, qa_exp_eq_bidetExp]
  exact column_lex_bideterminant R n n _ _ _ _ fun k => qa_row_strictMono I _

lemma tableauBideterminant_mem_dualWeyl (R : Type) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_P R I ∈ dualWeyl R n n (qa_nu mu) := by
  rw [tableauBideterminant_eq_bideterminant, ← qa_shape hmu]
  exact bidetMem R n n _ _ _ _

lemma tableauBideterminant_ne_zero (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I ≠ 0 := by
  intro h
  have := (tableauBideterminant_degree_leadingCoeff R I).2
  rw [h] at this
  simp at this

lemma map_tableauBideterminant {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (I : TIdx mu) : MvPolynomial.map φ (qa_P R I) = qa_P S I := by
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

lemma qa_exp_mem {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_exp I ∈ ssIdx n n (qa_nu mu) := by
  have h1 := leadInterlaced ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) (tableauBideterminant_ne_zero ℤ I)
  have h2 := colSums ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) _
    (((colLex n n).degree_mem_support_iff _).mpr (tableauBideterminant_ne_zero ℤ I))
  rw [(tableauBideterminant_degree_leadingCoeff ℤ I).1] at h1 h2
  exact ⟨h1, h2⟩

theorem linearIndependent_standard_tableauBideterminant (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    LinearIndependent R (fun I : {I : TIdx mu // StdT I} => qa_P R I.1) := by
  refine ldbasis_linearIndependent (colLex n n) _ ?_ fun I => (tableauBideterminant_degree_leadingCoeff R I.1).2
  intro I J h
  simp only [(tableauBideterminant_degree_leadingCoeff R _).1] at h
  exact Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 h)

theorem dualWeyl_eq_span_standard_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) =
      Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) := by
  apply le_antisymm
  · suffices key : ∀ d : (colLex n n).syn, ∀ f ∈ dualWeyl B n n (qa_nu mu),
        (colLex n n).toSyn ((colLex n n).degree f) = d →
          f ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) by
      intro f hf
      exact key _ f hf rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      have hint : Interlaced ((colLex n n).degree f) := leadInterlaced B n n _ f hf hf0
      have hcol := colSums B n n _ f hf _ (((colLex n n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu _ ⟨hint, hcol⟩
      have hbS : qa_P B I ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) :=
        Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩
      have hdecomp : f = (f - (colLex n n).leadingCoeff f • qa_P B I) + (colLex n n).leadingCoeff f • qa_P B I := by
        abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
      by_cases h0 : f - (colLex n n).leadingCoeff f • qa_P B I = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex n n) (f := f) (g := qa_P B I) ((tableauBideterminant_degree_leadingCoeff B I).1.trans he)
        (tableauBideterminant_degree_leadingCoeff B I).2 h0
      exact ih _ (hd ▸ hlt) _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl B hmu I))) rfl
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I.1

theorem dualWeyl_eq_span_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) = Submodule.span B (Set.range fun I : TIdx mu => qa_P B I) := by
  apply le_antisymm
  · rw [dualWeyl_eq_span_standard_tableauBideterminant B hmu]
    apply Submodule.span_mono
    rintro _ ⟨I, rfl⟩
    exact ⟨I.1, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qa_can_emb {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2
    (f := fun a : Fin (colH mu c) => Fin.castLE (colH_le mu c) a) (by intro x; simp [canT])
    (Fin.strictMono_castLE _)
  exact (congrFun this a).symm

lemma qa_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (initMinor R (qa_row I c) (colH_le mu c)) := by
  conv_rhs => rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [Matrix.transpose_apply, genMat, qa_row, qa_can_emb]

lemma qa_prod_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (qa_P R I) := by
  unfold qa_P
  rw [map_prod]
  exact Finset.prod_congr rfl fun c _ => qa_minor R I c

theorem qa_brk_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap (qa_P ℤ I)) := by
  unfold brk TMat minorC
  rw [← qa_prod_minor, map_prod]

theorem qa_brkPol_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brkPol mu I = (genMat ℤ n).det ^ (mu (lastIdx n)).toNat * rename Prod.swap (qa_P ℤ I) := by
  unfold brkPol
  rw [qa_prod_minor]

lemma qa_det_ne (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) R

lemma qa_algebraMap_inj (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) :=
  IsLocalization.injective (GLCoord R n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (qa_det_ne R n))

def qa_Phi (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
  (LinearMap.mulLeft R u) ∘ₗ (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap ∘ₗ
    (rename (R := R) (Prod.swap : Fin n × Fin n → Fin n × Fin n)).toLinearMap

lemma qa_Phi_apply (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) (f : MvPolynomial (Fin n × Fin n) R) :
    qa_Phi R n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (rename Prod.swap f) := rfl

lemma qa_Phi_inj (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) (u : GLCoord R n) (hu : IsUnit u) :
    Function.Injective (qa_Phi R n u) := by
  intro f g h
  rw [qa_Phi_apply, qa_Phi_apply] at h
  exact rename_injective _ Prod.swap_injective (qa_algebraMap_inj R n (hu.mul_left_cancel h))

def qa_intLin {M N : Type*} [AddCommGroup M] {i1 : Module ℤ M} [AddCommGroup N] {i2 : Module ℤ N}
    (f : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 i2) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) ⟨f, f.map_add⟩
    (fun z x => (f.map_smul z x).trans (int_smul_eq_zsmul i2 z (f x)))

def qa_PhiZ (n : ℕ) (u : GLCoord ℤ n) := qa_intLin (qa_Phi ℤ n u)

lemma qa_PhiZ_apply (n : ℕ) (u : GLCoord ℤ n) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    qa_PhiZ n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap f) := rfl

lemma qa_PhiZ_inj (n : ℕ) (u : GLCoord ℤ n) (hu : IsUnit u) : Function.Injective (qa_PhiZ n u) :=
  qa_Phi_inj ℤ n u hu

lemma qa_mapCoord_algebraMap {n : ℕ} (F : Type) [CommRing F] (f : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) f) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) f) := by
  unfold mapCoord
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem qa_mapCoord_brk {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (F : Type) [CommRing F] (I : TIdx mu) :
    mapCoord (n := n) F (brk mu I) =
      qa_Phi F n (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) (qa_P F I) := by
  rw [qa_brk_eq, map_mul, qa_mapCoord_algebraMap, qa_Phi_apply, MvPolynomial.map_rename, map_tableauBideterminant]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
