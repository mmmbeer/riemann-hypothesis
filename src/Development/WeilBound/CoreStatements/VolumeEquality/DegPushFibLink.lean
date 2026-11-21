import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs

section
noncomputable section

namespace SheetDecomposition

open GlobalTheory.CompanionTheory.Ar

section

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem mem_flagStep_iff (f : Fin r → V) (n : ℕ) (x : V) :
    x ∈ flagStep Ω f n ↔ ∃ B : Fin r → Ω, (∀ m : Fin r, n ≤ (m : ℕ) → B m = 0) ∧ x = ∑ m, B m • f m := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨Pi.single k 1, fun m hm => ?_, ?_⟩
      · have : m ≠ k := by rintro rfl; exact absurd hk (not_lt.2 hm)
        simp [this]
      · simp [Pi.single_apply]
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨B, hB, rfl⟩ := hx
      obtain ⟨C, hC, rfl⟩ := hy
      exact ⟨B + C, fun m hm => by simp [hB m hm, hC m hm], by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul a x _ hx =>
      obtain ⟨B, hB, rfl⟩ := hx
      exact ⟨a • B, fun m hm => by simp [hB m hm], by simp [Finset.smul_sum, mul_smul]⟩
  · rintro ⟨B, hB, rfl⟩
    refine Submodule.sum_mem _ fun m _ => ?_
    by_cases h : (m : ℕ) < n
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, h, rfl⟩)
    · simp [hB m (not_lt.1 h)]

theorem coeff_zero_of_mem {f : Fin r → V} (hf : LinearIndependent Ω f) {n : ℕ} {a : Fin r → Ω}
    (h : ∑ m, a m • f m ∈ flagStep Ω f n) (m : Fin r) (hm : n ≤ (m : ℕ)) : a m = 0 := by
  obtain ⟨B, hB, e⟩ := (mem_flagStep_iff f n _).1 h
  have := Fintype.linearIndependent_iff.1 hf (a - B) (by simp [sub_smul, Finset.sum_sub_distrib, e]) m
  simpa [hB m hm] using this

theorem smul_mem_flagStep {f : Fin r → V} (hf : LinearIndependent Ω f) {m : Fin r} {t : Ω}
    (h : t • f m ∈ flagStep Ω f m) : t = 0 := by
  classical
  have := coeff_zero_of_mem hf (a := Pi.single m t) (n := m) (by simpa [Pi.single_apply] using h) m le_rfl
  simpa using this

theorem sum_sub_mem (f : Fin r → V) (m : Fin r) {B : Fin r → Ω} (hB : ∀ m' : Fin r, (m : ℕ) + 1 ≤ (m' : ℕ) → B m' = 0) :
    ∑ m', B m' • f m' - B m • f m ∈ flagStep Ω f m := by
  classical
  refine (mem_flagStep_iff f m _).2 ⟨B - Pi.single m (B m), fun m' hm' => ?_, ?_⟩
  · by_cases e : m' = m
    · simp [e]
    · have : (m' : ℕ) ≠ m := fun h => e (Fin.ext h)
      simp [e, hB m' (by omega)]
  · simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply]

theorem self_mem_flagStep (f : Fin r → V) (m : Fin r) : f m ∈ flagStep Ω f (m + 1) :=
  Submodule.subset_span ⟨m, Nat.lt_succ_self _, rfl⟩

theorem flagStep_mono (f : Fin r → V) {n n' : ℕ} (h : n ≤ n') : flagStep Ω f n ≤ flagStep Ω f n' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem gr_span {b₀ bb : Fin r → V} (h₀ : LinearIndependent Ω b₀) (hb : LinearIndependent Ω bb)
    (hf : ∀ n, flagStep Ω bb n = flagStep Ω b₀ n) (R : Subring Ω) (m : Fin r) {t : Ω}
    (ht : bb m - t • b₀ m ∈ flagStep Ω b₀ m) :
    t ≠ 0 ∧ Submodule.span R {t' : Ω | ∃ e ∈ Submodule.span R (Set.range bb), e - t' • b₀ m ∈ flagStep Ω b₀ m} =
      Submodule.span R {t} := by
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro rfl
    have : (1 : Ω) • bb m ∈ flagStep Ω bb m := by simpa [hf] using ht
    exact one_ne_zero (smul_mem_flagStep hb this)
  · rintro t' ⟨e, he, h⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    have e1 : ∑ l, a l • bb l = ∑ l, (a l : Ω) • bb l := rfl
    rw [e1] at h
    have h1 : ∑ l, (a l : Ω) • bb l ∈ flagStep Ω bb (m + 1) := by
      rw [hf]
      have := Submodule.add_mem _ (flagStep_mono b₀ (Nat.le_succ _) h)
        (Submodule.smul_mem _ t' (self_mem_flagStep (Ω := Ω) b₀ m))
      simpa using this
    have h2 := sum_sub_mem bb m (B := fun l => (a l : Ω)) (coeff_zero_of_mem hb h1)
    rw [hf] at h2
    have h3 : (t' - a m * t) • b₀ m ∈ flagStep Ω b₀ m := by
      have := Submodule.sub_mem _ (Submodule.add_mem _ h2 (Submodule.smul_mem _ (a m : Ω) ht)) h
      convert this using 1
      simp only [sub_smul, smul_sub, mul_smul]
      abel
    have h4 := smul_mem_flagStep h₀ h3
    exact Submodule.mem_span_singleton.2 ⟨a m, by
      show (a m : Ω) * t = t'
      linear_combination -h4⟩
  · rintro _ rfl
    exact Submodule.subset_span ⟨bb m, Submodule.subset_span ⟨m, rfl⟩, ht⟩

end

section

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃)

theorem det_mul_rows {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) :
    (H * G).det = ∑ I : Fin n → Fin r, (∏ a, H a (I a)) * (Matrix.of fun a b => G (I a) b).det := by
  have e : (H * G : Matrix (Fin n) (Fin n) Ω₃) = fun a => ∑ l, H a l • G l := by
    funext a b
    simp [Matrix.mul_apply]
  have h := (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap.map_sum (fun a l => H a l • G l)
  have h' : (H * G).det = (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap (fun a => ∑ l, H a l • G l) := by
    rw [e]; rfl
  rw [h', h]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem sup_minor_eq_one {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) (hH : ∀ a l, H a l ∈ O)
    (hG : ∀ l b, G l b ∈ O) (h : H * G = 1) :
    (Finset.univ.sup fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) = 1 := by
  refine le_antisymm (Finset.sup_le fun I _ => (O.valuation_le_one_iff _).2 ?_) ?_
  · rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => hG _ _)
  · have e := det_mul_rows H G
    rw [h, Matrix.det_one] at e
    rw [← O.valuation.map_one, e]
    refine Valuation.map_sum_le _ fun I _ => ?_
    rw [map_mul]
    refine (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (prod_mem fun a _ => hH _ _))).trans ?_
    exact Finset.le_sup (f := fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) (Finset.mem_univ I)

theorem val_le_of_mem_span {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {S : Set Ω}
    {γ : O.ValueGroup} (hS : ∀ s ∈ S, O.valuation (i s) ≤ γ) {x : Ω} (hx : x ∈ Submodule.span R S) :
    O.valuation (i x) ≤ γ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    show O.valuation (i ((a : Ω) * x)) ≤ γ
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (hR _ a.2))).trans hx

theorem val_eq_of_span_eq {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {x y : Ω}
    (h : Submodule.span R {x} = Submodule.span R {y}) : O.valuation (i x) = O.valuation (i y) :=
  le_antisymm (val_le_of_mem_span O i R hR (S := {y}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self x))
    (val_le_of_mem_span O i R hR (S := {x}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self y))

end

end SheetDecomposition
end
end

section
noncomputable section

namespace SheetDecomposition

open GlobalTheory.CompanionTheory.Ar Matrix

variable {Ω₀ Ω Ω₃ V : Type} [Field Ω₀] [Field Ω] [Field Ω₃] [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem coords_of_mem_span (fn : Ω₀ →+* Ω) (c : Fin r → V) (R : Subring Ω) (A : Set (Fin r → Ω₀)) (P : (Fin r → Ω) → Prop)
    (h0 : P 0) (hadd : ∀ g g', P g → P g' → P (g + g')) (hsm : ∀ a ∈ R, ∀ g, P g → P (a • g))
    (hA : ∀ a ∈ A, P fun l => fn (a l)) {x : V}
    (hx : x ∈ Submodule.span R {w | ∃ a ∈ A, w = ∑ m, fn (a m) • c m}) : ∃ g, P g ∧ x = ∑ l, g l • c l := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨fun l => fn (a l), hA a ha, rfl⟩
  | zero => exact ⟨0, h0, by simp⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨g, hg, rfl⟩ := ihy
    obtain ⟨g', hg', rfl⟩ := ihz
    exact ⟨g + g', hadd g g' hg hg', by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a y _ ih =>
    obtain ⟨g, hg, rfl⟩ := ih
    refine ⟨(a : Ω) • g, hsm a a.2 g hg, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Subring.smul_def, smul_smul]
    rfl

theorem coords_unique {c : Fin r → V} (hc : LinearIndependent Ω c) {g g' : Fin r → Ω} (h : ∑ l, g l • c l = ∑ l, g' l • c l) :
    g = g' := by
  have h' : ∑ l, (g - g') l • c l = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := Fintype.linearIndependent_iff.1 hc (g - g') h'
  funext l
  exact sub_eq_zero.1 (this l)

theorem sum_mulVec (c bb : Fin r → V) (G : Matrix (Fin r) (Fin r) Ω) (hG : ∀ m, bb m = ∑ l, G l m • c l) (v : Fin r → Ω) :
    ∑ m, v m • bb m = ∑ l, (G *ᵥ v) l • c l := by
  simp only [hG, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm]

private theorem exists_triangular_of_flags_eq (X Y : Fin r → V) (h : ∀ n, flagStep Ω X n = flagStep Ω Y n) :
    ∃ S : Matrix (Fin r) (Fin r) Ω, S.BlockTriangular id ∧ ∀ k, X k = ∑ j, S j k • Y j := by
  have key : ∀ k : Fin r, ∃ l : Fin r →₀ Ω, (∀ j : Fin r, (k : ℕ) < j → l j = 0) ∧ X k = ∑ j, l j • Y j := by
    intro k
    have hk : X k ∈ flagStep Ω Y ((k : ℕ) + 1) := by
      rw [← h]
      exact Submodule.subset_span ⟨k, by simp, rfl⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 hk
    refine ⟨l, fun j hj => ?_, ?_⟩
    · rw [Finsupp.mem_supported'] at hl
      exact hl j (by simp; omega)
    · rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i
      simp
  choose l hl1 hl2 using key
  refine ⟨Matrix.of fun j k => l k j, ?_, fun k => by simpa using hl2 k⟩
  intro j k hjk
  exact hl1 k j hjk

private theorem sub_diag_smul_mem_flag_of_triangular (X Y : Fin r → V) (S : Matrix (Fin r) (Fin r) Ω) (hS : S.BlockTriangular id)
    (hX : ∀ k, X k = ∑ j, S j k • Y j) (m : Fin r) : X m - S m m • Y m ∈ flagStep Ω Y m := by
  rw [hX m, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), add_sub_cancel_left]
  apply Submodule.sum_mem
  intro j hj
  by_cases hjm : j < m
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hjm, rfl⟩)
  · have hmj : m < j := lt_of_le_of_ne (not_lt.1 hjm) (Ne.symm (Finset.ne_of_mem_erase hj))
    rw [hS hmj, zero_smul]
    exact zero_mem _

private theorem prod_Iic_eq_prod_castLE' {M : Type} [CommMonoid M] (m : Fin r) (f : Fin r → M) :
    ∏ x ∈ Finset.Iic m, f x = ∏ b : Fin ((m : ℕ) + 1), f (Fin.castLE m.2 b) := by
  have himg : Finset.Iic m = Finset.univ.image (Fin.castLE m.2) := by
    ext x
    simp only [Finset.mem_Iic, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨⟨x, by rw [Fin.le_def] at hx; omega⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩
      rw [Fin.le_def, Fin.coe_castLE]
      omega
  rw [himg, Finset.prod_image]
  intro a _ b _ hab
  exact Fin.castLE_injective _ hab

private theorem det_submatrix_mul_triangular_eq (u W : Matrix (Fin r) (Fin r) Ω) (hW : W.BlockTriangular id) (m : Fin r)
    (I : Fin ((m : ℕ) + 1) → Fin r) :
    (Matrix.of fun a b : Fin ((m : ℕ) + 1) => (u * W) (I a) (Fin.castLE m.2 b)).det =
      (Matrix.of fun a b : Fin ((m : ℕ) + 1) => u (I a) (Fin.castLE m.2 b)).det *
        ∏ b : Fin ((m : ℕ) + 1), W (Fin.castLE m.2 b) (Fin.castLE m.2 b) := by
  have hmat : (Matrix.of fun a b : Fin ((m : ℕ) + 1) => (u * W) (I a) (Fin.castLE m.2 b)) =
      (Matrix.of fun a c : Fin ((m : ℕ) + 1) => u (I a) (Fin.castLE m.2 c)) *
        (Matrix.of fun c b : Fin ((m : ℕ) + 1) => W (Fin.castLE m.2 c) (Fin.castLE m.2 b)) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [(Finset.sum_image (s := Finset.univ) (g := Fin.castLE m.2)
      (f := fun j => u (I a) j * W j (Fin.castLE m.2 b)) fun x _ y _ h => Fin.castLE_injective _ h).symm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    have hjm : (m : ℕ) < j := by
      by_contra hc
      exact hj (Finset.mem_image.2 ⟨⟨j, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    have hlt : Fin.castLE m.2 b < j := by
      rw [Fin.lt_def, Fin.coe_castLE]
      omega
    exact mul_eq_zero_of_right _ (hW hlt)
  rw [hmat, Matrix.det_mul,
    Matrix.det_of_upperTriangular (M := Matrix.of fun c b : Fin ((m : ℕ) + 1) => W (Fin.castLE m.2 c) (Fin.castLE m.2 b))]
  · simp only [Matrix.of_apply]
  · intro c b hbc
    simp only [Matrix.of_apply]
    apply hW
    show Fin.castLE m.2 b < Fin.castLE m.2 c
    rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
    exact hbc

private theorem exists_integral_change_of_basis_of_span_eq (fn : Ω₀ →+* Ω) (i : Ω →+* Ω₃) (c bb : Fin r → V) (hc : LinearIndependent Ω c)
    (O : ValuationSubring Ω₃) (R : Subring Ω) (A : Set (Fin r → Ω₀))
    (hR : ∀ a ∈ R, i a ∈ O) (hfn : ∀ a, i (fn a) ∈ O) (hbb : LinearIndependent Ω bb)
    (hspan : Submodule.span R (Set.range bb) = Submodule.span R {w | ∃ a ∈ A, w = ∑ m, fn (a m) • c m}) :
    ∃ G Hinv : Matrix (Fin r) (Fin r) Ω, (∀ l k, i (G l k) ∈ O) ∧ (∀ l k, i (Hinv l k) ∈ O) ∧
      G * Hinv = 1 ∧ ∀ k, bb k = ∑ l, G l k • c l := by
  have hG0 : ∀ k, ∃ g : Fin r → Ω, ((∀ l, i (g l) ∈ O) ∧ ∀ φ : Fin r → Ω₀,
      (∀ a ∈ A, ∑ l, φ l * a l = 0) → ∑ l, fn (φ l) * g l = 0) ∧ bb k = ∑ l, g l • c l := by
    intro k
    have hk : bb k ∈ Submodule.span R {w | ∃ a ∈ A, w = ∑ m, fn (a m) • c m} :=
      hspan ▸ Submodule.subset_span ⟨k, rfl⟩
    refine coords_of_mem_span fn c R A _ ?_ ?_ ?_ ?_ hk
    · exact ⟨fun l => by simp, fun φ _ => by simp⟩
    · rintro g g' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
      refine ⟨fun l => by simpa using add_mem (hg1 l) (hg1' l), fun φ hφ => ?_⟩
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hg2 φ hφ, hg2' φ hφ, add_zero]
    · rintro a ha g ⟨hg1, hg2⟩
      refine ⟨fun l => by simpa using mul_mem (hR a ha) (hg1 l), fun φ hφ => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show ∑ l, fn (φ l) * (a * g l) = a * ∑ l, fn (φ l) * g l by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring, hg2 φ hφ, mul_zero]
    · intro a ha
      refine ⟨fun l => hfn _, fun φ hφ => ?_⟩
      rw [← map_zero fn, ← hφ a ha, map_sum]
      simp [map_mul]
  choose g hg1 hgeq using hG0
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin r) (Fin r) Ω, G = Matrix.of fun l k => g k l := ⟨_, rfl⟩
  have hGk : ∀ k, bb k = ∑ l, G l k • c l := fun k => by rw [hGdef]; exact hgeq k
  have hGunit : IsUnit G := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    apply coords_unique hbb
    rw [sum_mulVec c bb G hGk v, sum_mulVec c bb G hGk w, hvw]
  have hφ0 : ∀ φ : Fin r → Ω₀, (∀ a ∈ A, ∑ l, φ l * a l = 0) → φ = 0 := by
    intro φ hφ
    have hv : (fun l => fn (φ l)) ᵥ* G = 0 := by
      funext k
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, hGdef, Matrix.of_apply]
      exact (hg1 k).2 φ hφ
    have := (Matrix.vecMul_injective_iff_isUnit.2 hGunit) (hv.trans (Matrix.zero_vecMul G).symm)
    funext l
    apply fn.injective
    rw [Pi.zero_apply, map_zero]
    exact congrFun this l
  have hspanA : ∀ j : Fin r, Pi.single j (1 : Ω₀) ∈ Submodule.span Ω₀ A := by
    intro j
    by_contra hj
    obtain ⟨f, hfj, hfA⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hj inferInstance
    have hφ := hφ0 (fun l => f fun j => if l = j then 1 else 0) (fun a ha => by
      have hfa : f a = 0 := by
        have : f a ∈ (Submodule.span Ω₀ A).map f := Submodule.mem_map_of_mem (Submodule.subset_span ha)
        rw [hfA] at this
        exact (Submodule.mem_bot _).1 this
      rw [LinearMap.pi_apply_eq_sum_univ f a] at hfa
      simpa [mul_comm] using hfa)
    apply hfj
    have h1 : (Pi.single j (1 : Ω₀) : Fin r → Ω₀) = fun k => if j = k then 1 else 0 := by
      ext k
      simp [Pi.single_apply, eq_comm]
    rw [h1]
    exact congrFun hφ j
  have hcoord : ∀ x ∈ Submodule.span Ω₀ A, ∃ h : Fin r → Ω, (∀ m, i (h m) ∈ O) ∧
      (fun l => fn (x l)) = G *ᵥ h := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      have hmem : ∑ m, fn (a m) • c m ∈ Submodule.span R (Set.range bb) :=
        hspan ▸ Submodule.subset_span ⟨a, ha, rfl⟩
      have hrange : Set.range bb = {w | ∃ e ∈ Set.range (fun k : Fin r => (Pi.single k (1 : Ω) : Fin r → Ω)),
          w = ∑ m, (RingHom.id Ω) (e m) • bb m} := by
        ext w
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨_, ⟨k, rfl⟩, by simp [Pi.single_apply]⟩
        · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, by simp [Pi.single_apply]⟩
      rw [hrange] at hmem
      obtain ⟨h, hh, heq⟩ := coords_of_mem_span (RingHom.id Ω) bb R _ (fun h => ∀ m, i (h m) ∈ O)
        (fun m => by simp) (fun g g' hg hg' m => by simpa using add_mem (hg m) (hg' m))
        (fun a ha g hg m => by simpa using mul_mem (hR a ha) (hg m))
        (by
          rintro _ ⟨k, rfl⟩ m
          by_cases hmk : m = k
          · subst hmk
            simp
          · simp [Pi.single_apply, hmk]) hmem
      refine ⟨h, hh, coords_unique hc ?_⟩
      rw [← sum_mulVec c bb G hGk h, ← heq]
    | zero => exact ⟨0, fun m => by simp, by funext l; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨h, hh, he⟩ := hx
      obtain ⟨h', hh', he'⟩ := hy
      refine ⟨h + h', fun m => by simpa using add_mem (hh m) (hh' m), ?_⟩
      rw [Matrix.mulVec_add, ← he, ← he']
      funext l
      simp
    | smul a x _ hx =>
      obtain ⟨h, hh, he⟩ := hx
      refine ⟨fn a • h, fun m => by simpa using mul_mem (hfn a) (hh m), ?_⟩
      rw [Matrix.mulVec_smul, ← he]
      funext l
      simp
  have hj : ∀ j, ∃ h : Fin r → Ω, (∀ m, i (h m) ∈ O) ∧ Pi.single j 1 = G *ᵥ h := by
    intro j
    obtain ⟨h, hh, he⟩ := hcoord _ (hspanA j)
    refine ⟨h, hh, ?_⟩
    rw [← he]
    funext l
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [Pi.single_apply, hlj]
  choose h hh1 hh2 using hj
  refine ⟨G, Matrix.of fun m j => h j m, fun l k => by rw [hGdef]; exact (hg1 k).1 l,
    fun l k => hh1 k l, ?_, hGk⟩
  ext l j
  have := congrFun (hh2 j) l
  simp only [Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← this, Pi.single_apply]

theorem flag_val (fn : Ω₀ →+* Ω) (i : Ω →+* Ω₃) (c b₀ : Fin r → V) (u : Matrix (Fin r) (Fin r) Ω) (hc : LinearIndependent Ω c)
    (h₀ : LinearIndependent Ω b₀) (hf : ∀ n, flagStep Ω b₀ n = flagStep Ω (fun m' => ∑ l, u l m' • c l) n) :
    ∃ β : Fin r → Ω, (∀ m, β m ≠ 0) ∧ ∀ (O : ValuationSubring Ω₃) (R : Subring Ω) (A : Set (Fin r → Ω₀)) (bb : Fin r → V),
      (∀ a ∈ R, i a ∈ O) → (∀ a, i (fn a) ∈ O) → LinearIndependent Ω bb → (∀ n, flagStep Ω bb n = flagStep Ω b₀ n) →
      Submodule.span R (Set.range bb) = Submodule.span R {w | ∃ a ∈ A, w = ∑ m, fn (a m) • c m} →
      ∃ t : Fin r → Ω, (∀ m : Fin r, bb m - t m • b₀ m ∈ flagStep Ω b₀ m) ∧ ∀ m : Fin r,
        (∏ m' ∈ Finset.Iic m, O.valuation (i (t m'))) * (Finset.univ.sup fun I : Fin (m + 1) → Fin r =>
          O.valuation (Matrix.of fun a b : Fin (m + 1) => u.map i (I a) (Fin.castLE m.2 b)).det) =
        O.valuation (i (∏ m' ∈ Finset.Iic m, β m')) := by
  obtain ⟨T', hT'tri, hT'⟩ := exists_triangular_of_flags_eq b₀ (fun m' => ∑ l, u l m' • c l) hf
  obtain ⟨T, hTtri, hT⟩ := exists_triangular_of_flags_eq (fun m' => ∑ l, u l m' • c l) b₀ (fun n => (hf n).symm)
  have hTT : T * T' = 1 := by
    ext a k
    have h1 : ∑ j, T' j k • (fun m' => ∑ l, u l m' • c l) j = ∑ l, (T *ᵥ fun j => T' j k) l • b₀ l :=
      sum_mulVec b₀ _ T hT _
    have h2 : b₀ k = ∑ l, (1 : Matrix (Fin r) (Fin r) Ω) l k • b₀ l := by
      simp [Matrix.one_apply]
    have e := coords_unique h₀ (h2.symm.trans ((hT' k).trans h1))
    have e2 := congrFun e a
    simp only [Matrix.mulVec, dotProduct] at e2
    rw [Matrix.mul_apply, ← e2]
  have hdet : T'.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hTT
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdiag : ∀ k, T' k k ≠ 0 := by
    intro k
    rw [Matrix.det_of_upperTriangular hT'tri] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet k (Finset.mem_univ k)
  refine ⟨fun k => (T' k k)⁻¹, fun k => inv_ne_zero (hdiag k), ?_⟩
  intro O R A bb hR hfn hbb hbbf hspan
  obtain ⟨S, hStri, hS⟩ := exists_triangular_of_flags_eq bb b₀ hbbf
  obtain ⟨G, Hinv, hG, hH, hGH, hGk⟩ := exists_integral_change_of_basis_of_span_eq fn i c bb hc O R A hR hfn hbb hspan
  refine ⟨fun k => S k k, sub_diag_smul_mem_flag_of_triangular bb b₀ S hStri hS, ?_⟩
  have hb0 : ∀ k, b₀ k = ∑ l, (u * T') l k • c l := by
    intro k
    rw [hT' k, sum_mulVec c _ u (fun m => rfl)]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hGeq : G = u * (T' * S) := by
    rw [← Matrix.mul_assoc]
    ext l k
    have e := coords_unique hc ((hGk k).symm.trans ((hS k).trans (sum_mulVec c b₀ (u * T') hb0 _)))
    have e2 := congrFun e l
    simp only [Matrix.mulVec, dotProduct] at e2
    rw [e2, Matrix.mul_apply]
  have hW : (T' * S).BlockTriangular id := hT'tri.mul hStri
  have hWdiag : ∀ k, (T' * S) k k = T' k k * S k k := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [hT'tri h, zero_mul]
      · rw [hStri h, mul_zero]
    · simp
  have hHG : Hinv.map i * G.map i = 1 := by
    rw [← Matrix.map_mul, mul_eq_one_comm.1 hGH, Matrix.map_one _ (map_zero i) (map_one i)]
  intro m
  have hsup := sup_minor_eq_one O (Matrix.of fun a l => i (Hinv (Fin.castLE m.2 a) l))
    (Matrix.of fun l b => i (G l (Fin.castLE m.2 b))) (fun a l => hH _ _) (fun l b => hG _ _) (by
      ext a b
      have e := congrFun (congrFun hHG (Fin.castLE m.2 a)) (Fin.castLE m.2 b)
      rw [Matrix.mul_apply] at e ⊢
      simp only [Matrix.map_apply, Matrix.of_apply] at e ⊢
      rw [e, Matrix.one_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · have : Fin.castLE m.2 a ≠ Fin.castLE m.2 b := fun h => hab (Fin.castLE_injective _ h)
        simp [hab, this])
  simp only [Matrix.of_apply] at hsup
  have hfun : (fun I : Fin ((m : ℕ) + 1) → Fin r =>
      O.valuation (Matrix.of fun a b : Fin ((m : ℕ) + 1) => i (G (I a) (Fin.castLE m.2 b))).det) =
      fun I => O.valuation (Matrix.of fun a b : Fin ((m : ℕ) + 1) => u.map i (I a) (Fin.castLE m.2 b)).det *
        O.valuation (i (∏ b : Fin ((m : ℕ) + 1), (T' * S) (Fin.castLE m.2 b) (Fin.castLE m.2 b))) := by
    funext I
    have hdG : (Matrix.of fun a b : Fin ((m : ℕ) + 1) => i (G (I a) (Fin.castLE m.2 b))).det =
        i (Matrix.of fun a b : Fin ((m : ℕ) + 1) => G (I a) (Fin.castLE m.2 b)).det := by
      rw [RingHom.map_det]
      rfl
    have hdU : (Matrix.of fun a b : Fin ((m : ℕ) + 1) => u.map i (I a) (Fin.castLE m.2 b)).det =
        i (Matrix.of fun a b : Fin ((m : ℕ) + 1) => u (I a) (Fin.castLE m.2 b)).det := by
      rw [RingHom.map_det]
      rfl
    rw [hdG, hdU, hGeq, det_submatrix_mul_triangular_eq u _ hW m I, map_mul, map_mul]
  rw [hfun] at hsup
  have hpull : ∀ (κ : O.ValueGroup) (f : (Fin ((m : ℕ) + 1) → Fin r) → O.ValueGroup),
      (Finset.univ.sup fun I => f I * κ) = (Finset.univ.sup f) * κ := by
    intro κ f
    have := Finset.comp_sup_eq_sup_comp (s := Finset.univ) (f := f) (fun x => x * κ)
      (fun x y => Monotone.map_sup (fun a b (h : a ≤ b) => mul_le_mul_left h κ) x y) (by simp [bot_eq_zero])
    rw [this]
    rfl
  rw [hpull] at hsup
  have e1 := prod_Iic_eq_prod_castLE' m (fun x => O.valuation (i (S x x)))
  have e2 := prod_Iic_eq_prod_castLE' m (fun x => (T' x x)⁻¹)
  simp only at e1 e2 ⊢
  rw [e1, e2]
  simp only [hWdiag, map_prod, map_mul, Finset.prod_mul_distrib, map_inv₀, Finset.prod_inv_distrib] at hsup ⊢
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hsup]
  ac_rfl

end SheetDecomposition
end
end

section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem exists_root {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (s : CMType H ⊕ CMType H)
    (m : Fin (labelRk D s)) : ∃ ρ : CMType H × Fin (D.p + D.q), HodgeCpt.rootIdx D ρ = ⟨s, m⟩ ∧
      HodgeCpt.rootSgn D ρ * HodgeCpt.rootSgn D ρ = 1 ∧
      ∀ (K : Type) (x : CMType H × Fin (D.p + D.q) → K → ℤ), grDeg x s m = HodgeCpt.rootSgn D ρ • x ρ := by
  rcases s with τ | τ
  · have hm : (m : ℕ) < D.p := m.2
    refine ⟨(τ, ⟨m, by omega⟩), ?_, ?_, fun K x => ?_⟩
    · simp only [HodgeCpt.rootIdx, hm, dif_pos]
    · simp [HodgeCpt.rootSgn, hm]
    · simp [HodgeCpt.rootSgn, hm, grDeg]
  · have hm : (m : ℕ) < D.q := m.2
    have h : ¬ D.p + D.q - 1 - m < D.p := by omega
    refine ⟨(τ, ⟨D.p + D.q - 1 - m, by omega⟩), ?_, ?_, fun K x => ?_⟩
    · simp only [HodgeCpt.rootIdx, h, dif_neg, not_false_eq_true]
      congr 1
      exact Fin.ext (by show D.p + D.q - 1 - (D.p + D.q - 1 - m) = m; omega)
    · simp [HodgeCpt.rootSgn, h]
    · simp [HodgeCpt.rootSgn, h, grDeg]

theorem val_tens {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) {ξ : Sp Ω ⟶ X}
    (q : Cpt ξ) (hR : ∀ a ∈ regAt ξ q, i a ∈ O) (Λ : Lat ξ Ω) {t M : Ω} (ε : ℤ) (ht : Λ.IsGenAt q t)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q = Submodule.span (regAt ξ q) {M}) :
    O.valuation (i M) = O.valuation (i t) ^ ε := by
  refine le_antisymm (val_le_of_mem_span O i _ hR (S := {t | ∃ s : Unit → Ω, (∀ j, Λ.IsGenAt q (s j)) ∧ t = ∏ j, s j ^ ε}) ?_
    (show M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q from h ▸ Submodule.mem_span_singleton_self M)) ?_
  · rintro _ ⟨s, hs, rfl⟩
    simp [val_eq_of_span_eq O i _ hR ((hs ()).2.symm.trans ht.2)]
  · have : t ^ ε ∈ Submodule.span (regAt ξ q) {M} :=
      h ▸ Submodule.subset_span ⟨fun _ => t, fun _ => ht, by simp⟩
    simpa using val_le_of_mem_span O i _ hR (S := {M}) (γ := O.valuation (i M)) (by rintro _ rfl; rfl) this

theorem val_step {Ω Ω₃ K : Type} [Field Ω] [Field Ω₃] [Fintype K] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (w : K → Ω)
    (x : K → ℤ) {ε : ℤ} (hε : ε * ε = 1) {e t : Ω} (he : e ≠ 0)
    (h : O.valuation (i ((∏ a, w a ^ x a) • e)) = O.valuation (i t) ^ ε) :
    O.valuation (i (∏ a, w a ^ (ε • x) a)) = O.valuation (i t) * O.valuation (i (e ^ ε)⁻¹) := by
  have h3 := congrArg (· ^ ε) h
  simp only [← zpow_mul, hε, zpow_one] at h3
  have h4 : O.valuation (i e) ≠ 0 := by simpa using he
  rw [← h3, smul_eq_mul, map_mul, map_mul, mul_zpow, map_inv₀, map_inv₀, map_zpow₀, map_zpow₀,
    mul_inv_cancel_right₀ (zpow_ne_zero _ h4), ← map_zpow₀, ← map_zpow₀, ← Finset.prod_zpow]
  simp only [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem rootLat_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag)
    (ρ : CMType H × Fin (D.p + D.q)) (s : CMType H ⊕ CMType H) (m : Fin (labelRk D s)) (h : HodgeCpt.rootIdx D ρ = ⟨s, m⟩) :
    Fl.rootLat ρ = Lat.tens (fun _ : Unit => (𝔐.V s).gr (Fl.b s) m) fun _ => HodgeCpt.rootSgn D ρ := by
  unfold HodgeCpt.Flag.rootLat
  generalize HodgeCpt.rootIdx D ρ = z at h
  subst h
  rfl

theorem fibLink : ChartVal → Centre → CoordLat → FibLink := by
  intro hCV hC hL E _ _ _ H D l Xo c Y S' Ω' _ K' _ J' _ y' 𝔐 Fl x e b u k _ _ Ω₃ _ _ i hRL hb _ _ hfl hk s m
  classical
  obtain ⟨A, hA, hind, -⟩ := hL E H D l Xo c Y S' Ω' K' J' y' 𝔐 Fl b hb
  have h₀ : LinearIndependent Ω' (Fl.b s) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h s
  obtain ⟨β, hβ, hV⟩ := flag_val 𝔐.fn i (fun m => Fl.j (b s m)) (Fl.b s) (u s) (hind s).1 h₀ (hfl s)
  choose ρ hρ hε hx using exists_root D s
  refine ⟨i ((∏ m' ∈ Finset.Iic m, β m') * ∏ m' ∈ Finset.Iic m, (e (ρ m') ^ HodgeCpt.rootSgn D (ρ m'))⁻¹),
    (map_ne_zero i).2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun m' _ => hβ m')
      (Finset.prod_ne_zero_iff.2 fun m' _ => inv_ne_zero (zpow_ne_zero _ (hRL _).1))), fun O hO => ?_⟩
  obtain ⟨q, -, hq, -, -⟩ := hC E H D l Xo c Y S' S' Ω' Ω' Ω₃ K' K' J' J' y' y' 𝔐 𝔐 i i O rfl
  have hch : ∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q := fun p hp hn => by
    have : CharZero Ω₃ := charZero_of_injective_algebraMap (algebraMap k Ω₃).injective
    have : CharZero Ω' := i.charZero
    have h0 : (p : Ω') ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    refine hn ⟨h0, natCast_mem _ _, hq.2 _ (natCast_mem _ _) h0 ?_⟩
    simpa using hO (p : k)⁻¹
  obtain ⟨ch, hc⟩ := 𝔐.tie.cover q
  have hy : ∀ a, y' ⟨a, ch a⟩ ≠ 0 := fun a => Finset.prod_ne_zero_iff.1 hc.1 a (Finset.mem_univ a)
  obtain ⟨U, hU, bb, hbf, hbq⟩ := Fl.sub s q trivial
  obtain ⟨hbi, hbs⟩ := hbq q trivial hU
  obtain ⟨t, ht, hv⟩ := hV O (regAt 𝔐.ξ q) (A s (𝔐.f q.1)) bb hq.1 (fun a => by
    obtain ⟨z, hz⟩ := hk a
    exact hz ▸ hO z) hbi hbf (hbs.symm.trans (hA q hch s))
  have hgen : ∀ m', ((𝔐.V s).gr (Fl.b s) m').IsGenAt q (t m') := fun m' => by
    have := gr_span h₀ hbi hbf (regAt 𝔐.ξ q) m' (ht m')
    rw [← hbs] at this
    exact this
  have hstep : ∀ m', O.valuation (i (∏ a, y' ⟨a, ch a⟩ ^ grDeg x s m' a)) =
      O.valuation (i (t m')) * O.valuation (i (e (ρ m') ^ HodgeCpt.rootSgn D (ρ m'))⁻¹) := fun m' => by
    have h1 := (hRL (ρ m')).2 q trivial ch hc
    have h2 : Fl.rootLat (ρ m') = Lat.tens (fun _ : Unit => (𝔐.V s).gr (Fl.b s) m') fun _ => HodgeCpt.rootSgn D (ρ m') :=
      rootLat_eq Fl (ρ m') s m' (hρ m')
    rw [h2] at h1
    rw [hx]
    exact val_step O i _ _ (hε m') (hRL _).1 (val_tens O i q hq.1 _ _ (hgen m') h1)
  have hm : (∏ a, y' ⟨a, ch a⟩ ^ stepDeg x s m a) = ∏ m' ∈ Finset.Iic m, ∏ a, y' ⟨a, ch a⟩ ^ grDeg x s m' a := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [stepDeg, Finset.sum_apply]
    induction Finset.Iic m using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ (hy a), ih]
  have hpl : vdeg O (plPt fun s => (u s).map i) (plDeg ⟨s, m⟩) = (Finset.univ.sup fun I : Fin (m + 1) → Fin (labelRk D s) =>
      O.valuation (Matrix.of fun a b : Fin (m + 1) => (u s).map i (I a) (Fin.castLE m.2 b)).det)⁻¹ := by
    rw [vdeg, Finset.prod_eq_single (⟨s, m⟩ : Σ s, Fin (labelRk D s)) (fun z _ hz => by simp [plDeg, hz]) (by simp)]
    simp only [plDeg, if_pos, zpow_neg, zpow_one]
    rfl
  have h5 := hv m
  have h6 : O.valuation (i (∏ m' ∈ Finset.Iic m, β m')) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun m' _ => hβ m'))
  rw [hCV _ _ _ O i 𝔐.ξ q K' J' y' ch _ hq hc, hm, hpl, map_mul, map_mul, ← h5, mul_right_comm,
    mul_inv_cancel_right₀ (right_ne_zero_of_mul (h5 ▸ h6)), map_prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m' _ => hstep m'

end SheetDecomposition
end
end
