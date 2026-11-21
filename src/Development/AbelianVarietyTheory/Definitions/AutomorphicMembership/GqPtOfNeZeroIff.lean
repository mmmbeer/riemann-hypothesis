import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndepOfGqNeZero
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMassConst

section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Tri

variable {m : ℕ} {u v : Matrix (Fin m) (Fin m) E}

theorem up_tri (h : IsUp u) : u.BlockTriangular id := fun i j hij => (h i j).1 hij

theorem mul_diag (hu : u.BlockTriangular id) (hv : v.BlockTriangular id) (i : Fin m) :
    (u * v) i i = u i i * v i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i _ (by simp)]
  intro k _ hk
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hu h, zero_mul]
  · rw [hv h, mul_zero]

theorem up_one : IsUp (1 : Matrix (Fin m) (Fin m) E) :=
  fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

theorem up_mul (hu : IsUp u) (hv : IsUp v) : IsUp (u * v) := fun i j =>
  ⟨fun h => (up_tri hu).mul (up_tri hv) h, fun h => by
    subst h; rw [mul_diag (up_tri hu) (up_tri hv), (hu i i).2 rfl, (hv i i).2 rfl, one_mul]⟩

theorem up_det (hu : IsUp u) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (up_tri hu)]
  exact Finset.prod_eq_one fun i _ => (hu i i).2 rfl

theorem up_mul_inv (hu : IsUp u) : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by simp [up_det hu])

theorem up_inv_mul (hu : IsUp u) : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ (by simp [up_det hu])

theorem up_inv (hu : IsUp u) : IsUp u⁻¹ := by
  letI := u.invertibleOfIsUnitDet (by simp [up_det hu])
  have h := Matrix.blockTriangular_inv_of_blockTriangular (up_tri hu)
  refine fun i j => ⟨fun hij => h hij, fun e => ?_⟩
  subst e
  have := mul_diag (up_tri hu) h i
  rw [up_mul_inv hu, (hu i i).2 rfl, one_mul, Matrix.one_apply_eq] at this
  exact this.symm

theorem lo_cT (σ : E →+* E) (hu : IsUp u) : IsLo (cT σ u) := fun i j =>
  ⟨fun h => by simp [cT, (hu j i).1 h], fun h => by simp [cT, (hu j i).2 h.symm]⟩

theorem lo_mul (hu : IsLo u) (hv : IsLo v) : IsLo (u * v) := by
  have t {w : Matrix (Fin m) (Fin m) E} (h : IsLo w) : IsUp wᵀ :=
    fun i j => ⟨(h j i).1, fun e => (h j i).2 e.symm⟩
  have := up_mul (t hv) (t hu)
  rw [← Matrix.transpose_mul] at this
  exact fun i j => ⟨(this j i).1, fun e => (this j i).2 e.symm⟩

theorem lo_det (hu : IsLo u) : u.det = 1 := by
  rw [← Matrix.det_transpose]
  exact up_det fun i j => ⟨(hu j i).1, fun e => (hu j i).2 e.symm⟩

theorem lead_block_mul (Z : Matrix (Fin m) (Fin m) E) (hu : IsUp u) {l : ℕ} (hl : l ≤ m) :
    (Z * u).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * u.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hl) (Fin.castLE_injective hl).injOn (by simp) ?_ (by simp)
  intro k _ hk
  have : Fin.castLE hl j < k := by
    by_contra h
    exact hk ⟨⟨k, by have := j.2; simp [Fin.lt_def] at h; omega⟩, by simp, rfl⟩
  rw [(hu k _).1 this, mul_zero]

theorem lead_mul_up (Z : Matrix (Fin m) (Fin m) E) (hu : IsUp u) (l : ℕ) (hl : l ≤ m) :
    SgAlg.lead (Z * u) l hl = SgAlg.lead Z l hl := by
  rw [SgAlg.lead, lead_block_mul Z hu, Matrix.det_mul,
    up_det (u := u.submatrix (Fin.castLE hl) (Fin.castLE hl)) fun i j => ⟨fun h => (hu _ _).1 h, fun h => (hu _ _).2 (congrArg _ h)⟩, mul_one,
    SgAlg.lead]

theorem lead_lo_mul (Z : Matrix (Fin m) (Fin m) E) (hu : IsLo u) (l : ℕ) (hl : l ≤ m) :
    SgAlg.lead (u * Z) l hl = SgAlg.lead Z l hl := by
  have t (W : Matrix (Fin m) (Fin m) E) : SgAlg.lead Wᵀ l hl = SgAlg.lead W l hl := by
    rw [SgAlg.lead, SgAlg.lead, ← Matrix.det_transpose]; rfl
  rw [← t, Matrix.transpose_mul, lead_mul_up (u := uᵀ) _ (fun i j => ⟨(hu j i).1, fun e => (hu j i).2 e.symm⟩), t]

def IsStrict (A : Matrix (Fin m) (Fin m) E) : Prop := ∀ i j, j ≤ i → A i j = 0

def simpleSum {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := ∑ a : Fin r, A a.castSucc a.succ

theorem strict_conj {r : ℕ} {u v A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hu : IsUp u) (hv : IsUp v)
    (hA : IsStrict A) : IsStrict (v * A * u) ∧ simpleSum (v * A * u) = simpleSum A := by
  have h1 : IsStrict (v * A) := fun i j h => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(hv i k).1 hk, zero_mul]
    · rw [hA k j (h.trans hk), mul_zero]
  have h2 (a : Fin r) : (v * A) a.castSucc a.succ = A a.castSucc a.succ := by
    rw [Matrix.mul_apply, Finset.sum_eq_single a.castSucc _ (by simp), (hv _ _).2 rfl, one_mul]
    intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hv _ k).1 h, zero_mul]
    · rw [hA k _ (Fin.castSucc_lt_iff_succ_le.1 h), mul_zero]
  refine ⟨fun i j h => ?_, Finset.sum_congr rfl fun a _ => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge j k with hk | hk
    · rw [(hu k j).1 hk, mul_zero]
    · rw [h1 i k (hk.trans h), zero_mul]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a.succ _ (by simp), (hu _ _).2 rfl, mul_one, h2]
    intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [h1 _ k (Fin.le_castSucc_iff.2 h), zero_mul]
    · rw [(hu k _).1 h, mul_zero]

end Tri

section Frames

variable {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem cT_mul {a b c : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b c E) :
    cT σ (A * B) = cT σ B * cT σ A := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem pairM_isom (hs : IsUn σ J s) : pairM σ J (s * P') (s * P) = pairM σ J P' P := by
  rw [pairM, pairM, cT_mul]
  conv_rhs => rw [← hs]
  simp only [Matrix.mul_assoc]

theorem pairM_mul (u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    pairM σ J (P' * u) (P * v) = cT σ v * pairM σ J P' P * u := by
  rw [pairM, pairM, cT_mul]
  simp only [Matrix.mul_assoc]

theorem eOf_mul (hu : IsUp u) : eOf (P * u) = eOf P * u.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [eOf, Matrix.submatrix_apply, Matrix.mul_apply, id, Fin.sum_univ_castSucc]
  rw [(hu _ _).1 (Fin.castSucc_lt_last j), mul_zero, add_zero]


theorem spanX_mul (hu : IsUp u) : spanX (P * u) = spanX P := by
  have k {Q : Matrix (Fin n) (Fin (r + 1)) E} {w : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hw : IsUp w) :
      spanX (Q * w) ≤ spanX Q := by
    rintro _ ⟨c, rfl⟩
    exact ⟨w.submatrix Fin.castSucc Fin.castSucc *ᵥ c, by simp [eOf_mul hw]⟩
  refine le_antisymm (k hu) ?_
  simpa [Matrix.mul_assoc, up_mul_inv hu] using k (Q := P * u) (up_inv hu)

theorem perpX_mul (hu : IsUp u) : perpX σ J (P * u) = perpX σ J P := by
  have k {Q : Matrix (Fin n) (Fin (r + 1)) E} {w : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hw : IsUp w) :
      perpX σ J Q ≤ perpX σ J (Q * w) := by
    intro x hx
    rw [mem_perpX] at hx ⊢
    rw [eOf_mul hw, cT_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  refine le_antisymm ?_ (k hu)
  simpa [Matrix.mul_assoc, up_mul_inv hu] using k (Q := P * u) (up_inv hu)

theorem mulVec_mem_spanX {x : Fin n → E} (hx : x ∈ spanX P) : s *ᵥ x ∈ spanX (s * P) := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c, (Matrix.mulVec_mulVec c s (eOf P)).symm⟩

theorem isFrame_mul {T : E} (h : IsFrame σ J T P) (hu : IsUp u) : IsFrame σ J T (P * u) := by
  obtain ⟨⟨L, hL⟩, h2⟩ := h
  refine ⟨⟨u⁻¹ * L, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, up_inv_mul hu]⟩, ?_⟩
  rw [pairM_mul, h2]
  ext a b
  have e (c : Fin (r + 1)) : u (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
    split_ifs with h
    · exact (hu _ _).2 h.symm
    · exact (hu _ _).1 (Fin.lt_last_iff_ne_last.2 h)
  simp only [TF, Matrix.mul_apply, Matrix.diagonal_apply, cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r) (fun k _ hk => by simp [hk]) (by simp)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, e]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb, eq_comm]

theorem isFrame_isom (hJ : IsUnit J.det) {T : E} (h : IsFrame σ J T P) (hs : IsUn σ J s) :
    IsFrame σ J T (s * P) := by
  obtain ⟨⟨L, hL⟩, h2⟩ := h
  refine ⟨⟨L * s⁻¹, ?_⟩, by rw [pairM_isom hs, h2]⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc s⁻¹, Matrix.nonsing_inv_mul _ (isUnit_det_of_isUn hJ hs),
    Matrix.one_mul, hL]

theorem isUn_inv (hJ : IsUnit J.det) (hs : IsUn σ J s) : IsUn σ J s⁻¹ :=
  isUn_of_mul_eq_one hs (Matrix.mul_nonsing_inv _ (isUnit_det_of_isUn hJ hs))

theorem inS_iff : InS σ J P s ↔ IsUn σ J s ∧
    ∃ a : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUp a ∧ s * P = P * a := Iff.rfl

theorem inN_iff : InN σ J P s ↔ IsUn σ J s ∧ (∃ a : Matrix (Fin r) (Fin r) E, IsUp a ∧ s * eOf P = eOf P * a) ∧
    ∀ x ∈ perpX σ J P, ∃ c, s *ᵥ x - x = eOf P *ᵥ c := Iff.rfl

theorem inS_one : InS σ J P 1 := inS_iff.2 ⟨isUn_one, 1, up_one, by simp⟩

theorem inS_mul {t : Matrix (Fin n) (Fin n) E} (hs : InS σ J P s) (ht : InS σ J P t) : InS σ J P (s * t) := by
  obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
  obtain ⟨h2, b, hb, f⟩ := inS_iff.1 ht
  exact inS_iff.2 ⟨isUn_mul h1 h2, a * b, up_mul ha hb, by
    rw [Matrix.mul_assoc, f, ← Matrix.mul_assoc, e, Matrix.mul_assoc]⟩

theorem inS_inv (hJ : IsUnit J.det) (hs : InS σ J P s) : InS σ J P s⁻¹ := by
  obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
  refine inS_iff.2 ⟨isUn_inv hJ h1, a⁻¹, up_inv ha, ?_⟩
  have : P = s * (P * a⁻¹) := by rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, up_mul_inv ha, Matrix.mul_one]
  conv_lhs => rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_isUn hJ h1), Matrix.one_mul]

theorem inS_of_inN {T : E} (hP : IsFrame σ J T P) (hs : InN σ J P s) : InS σ J P s := by
  obtain ⟨h1, ⟨a, ha, e⟩, h3⟩ := inN_iff.1 hs
  obtain ⟨c, hc⟩ := h3 _ (zOf_mem_perpX hP)
  refine inS_iff.2 ⟨h1, Matrix.of fun i j => Fin.lastCases (motive := fun _ => E)
    (Fin.lastCases (motive := fun _ => E) 1 c i)
    (fun j => Fin.lastCases (motive := fun _ => E) 0 (fun i => a i j) i) j, fun i j => ?_, ?_⟩
  · induction j using Fin.lastCases <;> induction i using Fin.lastCases
    · simp
    · simp [(Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).le]
    · simp [(Fin.castSucc_lt_last _).ne']
    · simpa using ha _ _
  · ext i j
    induction j using Fin.lastCases
    · have := congrFun hc i
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, zOf, eOf, Matrix.submatrix_apply, id] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Fin.lastCases_last, Fin.sum_univ_castSucc,
        Fin.lastCases_castSucc, mul_one]
      rw [← this]; ring
    · have := congrFun (congrFun e i) ‹_›
      simpa [Matrix.mul_apply, Fin.sum_univ_castSucc, eOf] using this

theorem inN_one : InN σ J P 1 := inN_iff.2 ⟨isUn_one, ⟨1, up_one, by simp⟩, fun v _ => ⟨0, by simp⟩⟩

theorem inN_perp (hs : InN σ J P s) (x : Fin n → E) : s *ᵥ x ∈ perpX σ J P ↔ x ∈ perpX σ J P := by
  obtain ⟨h1, ⟨a, ha, e⟩, -⟩ := inN_iff.1 hs
  rw [← mulVec_mem_perpX h1 P x, mem_perpX, mem_perpX, show eOf (s * P) = s * eOf P from rfl, e, cT_mul,
    Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (cT σ a)]
  have hu : IsUnit (cT σ a) := (Matrix.isUnit_iff_isUnit_det _).2 (by simp [lo_det (lo_cT σ ha)])
  exact ⟨fun h => by rw [h, Matrix.mulVec_zero],
    fun h => Matrix.mulVec_injective_iff_isUnit.2 hu (h.trans (Matrix.mulVec_zero _).symm)⟩

theorem inN_mul {t : Matrix (Fin n) (Fin n) E} (hs : InN σ J P s) (ht : InN σ J P t) : InN σ J P (s * t) := by
  have k := inN_perp ht
  obtain ⟨h1, ⟨a, ha, e⟩, h3⟩ := inN_iff.1 hs
  obtain ⟨h2, ⟨b, hb, f⟩, h4⟩ := inN_iff.1 ht
  refine inN_iff.2 ⟨isUn_mul h1 h2, ⟨a * b, up_mul ha hb, by
    rw [Matrix.mul_assoc, f, ← Matrix.mul_assoc, e, Matrix.mul_assoc]⟩, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := h3 _ ((k x).2 hx)
  obtain ⟨d, hd⟩ := h4 _ hx
  exact ⟨c + d, by rw [Matrix.mulVec_add, ← hc, ← hd, Matrix.mulVec_mulVec]; abel⟩

theorem inN_inv (hJ : IsUnit J.det) (hs : InN σ J P s) : InN σ J P s⁻¹ := by
  have k := inN_perp hs
  obtain ⟨h1, ⟨a, ha, e⟩, h3⟩ := inN_iff.1 hs
  have hu := isUnit_det_of_isUn hJ h1
  refine inN_iff.2 ⟨isUn_inv hJ h1, ⟨a⁻¹, up_inv ha, ?_⟩, fun x hx => ?_⟩
  · have : eOf P = s * (eOf P * a⁻¹) := by
      rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, up_mul_inv ha, Matrix.mul_one]
    conv_lhs => rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  · have e1 : s *ᵥ (s⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    obtain ⟨c, hc⟩ := h3 _ ((k (s⁻¹ *ᵥ x)).1 (by rwa [e1]))
    exact ⟨-c, by rw [Matrix.mulVec_neg, ← hc, e1]; abel⟩

end Frames

section Lattices

variable [NumberField E] {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ M : Submodule (𝓞 E) (Fin n → E)}

def triRing (E : Type) [Field E] [NumberField E] (r : ℕ) : Subring (Matrix (Fin (r + 1)) (Fin (r + 1)) E) where
  carrier := {u | ∀ a b : Fin (r + 1), (b < a → u a b = 0) ∧ u a b ∈ dInv E ((b : ℕ) - a)}
  one_mem' := fun a b => ⟨(one_mem_UO.1 a b).1, UO.entry_mem one_mem_UO a b⟩
  zero_mem' := fun _ _ => ⟨fun _ => rfl, FractionalIdeal.zero_mem _⟩
  add_mem' := fun hu hv a b => ⟨fun h => by simp [(hu a b).1 h, (hv a b).1 h],
    Submodule.add_mem (dInv E _ : Submodule (𝓞 E) E) (hu a b).2 (hv a b).2⟩
  neg_mem' := fun hu a b => ⟨fun h => by simp [(hu a b).1 h],
    Submodule.neg_mem (dInv E _ : Submodule (𝓞 E) E) (hu a b).2⟩
  mul_mem' := fun {u v} hu hv a b => ⟨fun h =>
    Matrix.BlockTriangular.mul (b := id) (fun i j k => (hu i j).1 k) (fun i j k => (hv i j).1 k) h, by
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem (dInv E _ : Submodule (𝓞 E) E) fun k _ => ?_
    rcases lt_or_ge k a with h1 | h1
    · rw [(hu a k).1 h1, zero_mul]; exact Submodule.zero_mem _
    rcases lt_or_ge b k with h2 | h2
    · rw [(hv k b).1 h2, mul_zero]; exact Submodule.zero_mem _
    have h3 : (a : ℕ) ≤ k := h1
    have h4 : (k : ℕ) ≤ b := h2
    rw [show (b : ℕ) - a = ((k : ℕ) - a) + ((b : ℕ) - k) by omega]
    exact mul_mem_dInv (hu a k).2 (hv k b).2⟩

theorem mem_UO_iff : u ∈ UO E r ↔ IsUp u ∧ u ∈ triRing E r :=
  ⟨fun h => ⟨h.1, fun a b => ⟨(h.1 a b).1, UO.entry_mem h a b⟩⟩, fun h => ⟨h.1, fun a b _ => (h.2 a b).2⟩⟩

theorem UO_mul (hu : u ∈ UO E r) (hv : v ∈ UO E r) : u * v ∈ UO E r :=
  mem_UO_iff.2 ⟨up_mul hu.1 hv.1, mul_mem (mem_UO_iff.1 hu).2 (mem_UO_iff.1 hv).2⟩

theorem UO_inv (hu : u ∈ UO E r) : u⁻¹ ∈ UO E r := by
  refine mem_UO_iff.2 ⟨up_inv hu.1, ?_⟩
  have h := Matrix.aeval_self_charpoly (1 - u)
  rw [Matrix.charpoly_of_upperTriangular _ ((up_tri up_one).sub (up_tri hu.1))] at h
  have e (i : Fin (r + 1)) : (1 - u) i i = 0 := by simp [(hu.1 i i).2 rfl]
  simp only [e, map_zero, sub_zero, Finset.prod_const, map_pow, Polynomial.aeval_X] at h
  have k := mul_neg_geom_sum (1 - u) (Finset.univ : Finset (Fin (r + 1))).card
  rw [h, sub_sub_cancel, sub_zero] at k
  rw [Matrix.inv_eq_right_inv k]
  exact sum_mem fun i _ => pow_mem (sub_mem (one_mem _) (mem_UO_iff.1 hu).2) i

theorem frameLat_mul (hu : u ∈ UO E r) : frameLat (P * u) = frameLat P :=
  le_antisymm (frameLat_mul_le P hu) (by
    simpa [Matrix.mul_assoc, up_mul_inv hu.1] using frameLat_mul_le (P * u) (UO_inv hu))

theorem mem_UO_of_le (hP : Free P) (hu : IsUp u) (h : frameLat (P * u) ≤ frameLat P) : u ∈ UO E r := by
  obtain ⟨L, hL⟩ := hP
  refine ⟨hu, fun a b hab => ?_⟩
  have h1 : (a : ℕ) < b := hab
  have h2 := b.2
  have hne (j : ℕ) : dInv E j ≠ 0 := fun e => by
    simpa [e] using Iota.one_mem_dInv (E := E) j
  have hI : dInv E ((b : ℕ) - a) = dInv E (r - a) / dInv E (r - b) := by
    rw [eq_div_iff (hne _), dInv, dInv, dInv, ← pow_add]
    congr 1; omega
  rw [hI, FractionalIdeal.mem_div_iff_of_ne_zero (hne _)]
  intro t ht
  obtain ⟨c, hc, e⟩ := (Iota.mem_frameLat _ _).1 (h ((Iota.mem_frameLat _ _).2 ⟨Pi.single b t, fun k => by
    rcases eq_or_ne k b with rfl | hk
    · simpa using ht
    · simp [hk, FractionalIdeal.zero_mem], rfl⟩))
  have e2 := congrArg (L *ᵥ ·) e
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.one_mulVec] at e2
  have := hc a
  rw [e2] at this
  simpa [mul_comm] using this

theorem frameLat_isom (s : Matrix (Fin n) (Fin n) E) : frameLat (s * P) = latMap s (frameLat P) := by
  ext x
  simp only [mem_latMap, Iota.mem_frameLat]
  exact ⟨fun ⟨a, ha, e⟩ => ⟨_, ⟨a, ha, rfl⟩, by rw [Matrix.mulVec_mulVec, e]⟩,
    fun ⟨_, ⟨a, ha, rfl⟩, e⟩ => ⟨a, ha, by rw [← e, Matrix.mulVec_mulVec]⟩⟩

omit [NumberField E] in

theorem mulVec_mem_latMap (hs : IsUnit s.det) (x : Fin n → E) : s *ᵥ x ∈ latMap s M ↔ x ∈ M :=
  ⟨fun ⟨w, hw, e⟩ => Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hs) e ▸ hw,
    fun h => ⟨x, h, rfl⟩⟩

omit [NumberField E] in

theorem mulVec_mem_span (hs : IsUnit s.det) (x : Fin n → E) :
    s *ᵥ x ∈ Submodule.span E (latMap s M : Set (Fin n → E)) ↔ x ∈ Submodule.span E (M : Set (Fin n → E)) := by
  have e : Submodule.span E (latMap s M : Set (Fin n → E)) =
      (Submodule.span E (M : Set (Fin n → E))).map s.mulVecLin := by
    rw [Submodule.map_span]; rfl
  rw [e]
  exact ⟨fun ⟨w, hw, e⟩ => Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hs) e ▸ hw,
    fun h => ⟨x, h, rfl⟩⟩

omit [NumberField E] in

theorem primIn_latMap (hs : IsUnit s.det) : PrimIn (latMap s M) (latMap s Λ) ↔ PrimIn M Λ := by
  have hsur := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hs)
  simp only [PrimIn, SetLike.le_def]
  refine and_congr (hsur.forall.trans ?_) (hsur.forall.trans ?_) <;>
    simp only [mulVec_mem_latMap hs, mulVec_mem_span hs]

omit [NumberField E] in

theorem selfDual_latMap (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : SelfDual σ J Λ) :
    SelfDual σ J (latMap s Λ) := by
  have hu := isUnit_det_of_isUn hJ hs
  have hsur := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu)
  refine ⟨h.1.map _, hsur.forall.2 fun x => ?_⟩
  rw [hsur.forall]
  simp only [mulVec_mem_latMap hu, form_mulVec hs]
  exact h.2 x

end Lattices

end GlobalTheory.IntTerm
end
end

section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Defs

def LieN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Y : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  cT σ Y * J + J * Y = 0 ∧ IsStrict A ∧ Y * P = P * A ∧ ∀ x ∈ perpX σ J P, Y *ᵥ x ∈ spanX P

def Relevant (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∀ Y A A', LieN σ J P Y A → LieN σ J P' Y A' →
    (simpleSum A - simpleSum A') + σ (simpleSum A - simpleSum A') = 0

def Unip {n r : ℕ} (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ a : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUp a ∧ P' = P * a

def SameFlag {n r : ℕ} (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ b : Matrix (Fin (r + 1)) (Fin (r + 1)) E, b.BlockTriangular id ∧ IsUnit b.det ∧ P' = P * b

def LiesAt {r : ℕ} (w : Formalism.MainNotions.S.Point E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ l u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLo l ∧ IsUp u ∧ Z * eps E r = l * Formalism.MainNotions.S.ptMat w * u

def onePt (E : Type) [Field E] (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) := ⟨[(1, r + 1)], by simp, by simp⟩

open scoped Classical in

def ptOfMat {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Formalism.MainNotions.S.Point E (r + 1) :=
  if h : ∃ w, LiesAt w Z then h.choose else onePt E r

variable [NumberField E]

def IntFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IsFrame σ J T P ∧ PrimIn (frameLat P) Λ

def Cong {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  frameLat ((g : E)⁻¹ • (P' - P)) ≤ Λ

def admitted (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T' : E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IntFrame σ J T' Λ P' ∧ ∃ u ∈ UO E r, Cong g Λ (P * u) P'

def defLat {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Λ ⊓ (frameLat P ⊔ frameLat P').comap ((g : 𝓞 E) • LinearMap.id)

def satLat {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  latIn Λ (Submodule.span E (M : Set (Fin n → E)))

abbrev Defect {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Type :=
  satLat M Λ ⧸ M.submoduleOf (satLat M Λ)

def DefectAt (F : Type) [Field F] [Algebra F E] {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E))
    (p : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ x : Defect M Λ, ∀ a : 𝓞 F, a ∉ p.asIdeal → algebraMap (𝓞 F) (𝓞 E) a • x ≠ 0

def NO (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {s | InN σ J P s ∧ latMap s Λ = Λ}

def Move (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P A B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s ∈ NO σ J Λ P, ∃ u ∈ UO E r, B = s * A * u

def Transp (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin (r + 1)) E)
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s, InS σ J P s ∧ latMap s Λ = Λ' ∧ ∃ u ∈ UO E r, B = s * A * u

end Defs

section Field

variable {σ : E →+* E} {n r : ℕ} {J s Y : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v A Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem LieN.of_mul (hu : IsUp u) (h : LieN σ J (P * u) Y A) : LieN σ J P Y (u * A * u⁻¹) := by
  refine ⟨h.1, (strict_conj (up_inv hu) hu h.2.1).1, ?_, by simpa [perpX_mul hu, spanX_mul hu] using h.2.2.2⟩
  have := congrArg (· * u⁻¹) h.2.2.1
  simpa only [Matrix.mul_assoc, up_mul_inv hu, Matrix.mul_one] using this

theorem LieN.of_isom (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : LieN σ J (s * P) Y A) :
    LieN σ J P (s⁻¹ * Y * s) A := by
  have hu := isUnit_det_of_isUn hJ hs
  have l := Matrix.nonsing_inv_mul s hu
  have e1 : J * s⁻¹ = cT σ s * J := by
    conv_lhs => rw [← hs, Matrix.mul_assoc, Matrix.mul_nonsing_inv s hu, Matrix.mul_one]
  have e2 : cT σ s⁻¹ * J = J * s := by
    conv_rhs => rw [← isUn_inv hJ hs, Matrix.mul_assoc, l, Matrix.mul_one]
  refine ⟨?_, h.2.1, ?_, fun x hx => ?_⟩
  · have := congrArg (fun W => cT σ s * W * s) h.1
    rw [cT_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, ← Matrix.mul_assoc J, ← Matrix.mul_assoc J, e1]
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul] using this
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, h.2.2.1, Matrix.mul_assoc, ← Matrix.mul_assoc, l, Matrix.one_mul]
  · have := mulVec_mem_spanX (s := s⁻¹) (h.2.2.2 _ ((mulVec_mem_perpX hs P x).2 hx))
    rwa [← Matrix.mul_assoc, l, Matrix.one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this

theorem Relevant.mul (h : Relevant σ J P P') (hu : IsUp u) (hv : IsUp v) : Relevant σ J (P * u) (P' * v) := by
  intro Y A A' h1 h2
  have := h _ _ _ (h1.of_mul hu) (h2.of_mul hv)
  rwa [(strict_conj (up_inv hu) hu h1.2.1).2, (strict_conj (up_inv hv) hv h2.2.1).2] at this

theorem Relevant.isom (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : Relevant σ J P P') :
    Relevant σ J (s * P) (s * P') := fun _ _ _ h1 h2 => h _ _ _ (h1.of_isom hJ hs) (h2.of_isom hJ hs)

theorem relevant_self (hP : Free P) : Relevant σ J P P := by
  intro Y A A' h1 h2
  obtain ⟨L, hL⟩ := hP
  have := congrArg (L * ·) (h1.2.2.1.symm.trans h2.2.2.1)
  simp only [← Matrix.mul_assoc, hL, Matrix.one_mul] at this
  simp [this]

theorem eps_mul_eps : eps E r * eps E r = 1 := by
  rw [eps, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext b
  rw [← mul_pow]; simp

theorem LiesAt.mul {w : Formalism.MainNotions.S.Point E (r + 1)} (h : LiesAt w Z) (hv : IsLo v) (hu : IsUp u) :
    LiesAt w (v * Z * u) := by
  obtain ⟨l, a, hl, ha, e⟩ := h
  refine ⟨v * l, a * (eps E r * u * eps E r), lo_mul hv hl, up_mul ha fun i j => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · simp [eps, (hu i j).1 h]
  · subst h; simp [eps, (hu i i).2 rfl, ← mul_pow]
  · calc v * Z * u * eps E r = v * (Z * eps E r) * (eps E r * u * eps E r) := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (eps E r) (eps E r), eps_mul_eps, Matrix.one_mul]
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]

theorem liesAt_ptOfMat (h : ∃ w, LiesAt w Z) : LiesAt (ptOfMat Z) Z := by
  rw [ptOfMat, dif_pos h]; exact h.choose_spec

theorem Gq_mul (T T' : E) (hv : IsLo v) (hu : IsUp u) : Gq σ T T' (v * Z * u) = Gq σ T T' Z := by
  simp only [Gq, Matrix.det_mul, lo_det hv, up_det hu, one_mul, mul_one, lead_mul_up _ hu, lead_lo_mul _ hv]


theorem Gq_TF {T : E} (hT : σ T = T) : Gq σ T T (TF r T) = 0 := by
  have h1 : (TF r T).det = 0 ^ r * -T := by
    simp [TF, Fin.prod_univ_castSucc, (Fin.castSucc_lt_last _).ne]
  have h2 : SgAlg.lead (TF r T) r (Nat.le_succ r) = 0 ^ r := by
    rw [SgAlg.lead, TF, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    refine (Finset.prod_congr rfl (g := fun _ => (0 : E)) fun i _ => ?_).trans (by simp)
    exact if_neg (Fin.castSucc_lt_last i).ne
  rw [Gq, h1, h2, map_mul, map_neg, hT]; ring

theorem Unip.norm_eq {T T' : E} (h : Unip P P') (hP : IsFrame σ J T P) (hP' : IsFrame σ J T' P') : T' = T := by
  obtain ⟨a, ha, rfl⟩ := h
  simpa [TF] using congrFun (congrFun (hP'.2.symm.trans (isFrame_mul hP ha).2) (Fin.last r)) (Fin.last r)

end Field

section Lattice

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' A B C : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ Λ' Λ'' M : Submodule (𝓞 E) (Fin n → E)} {T T' : E}

theorem mem_defLat (x : Fin n → E) :
    x ∈ defLat g Λ P P' ↔ x ∈ Λ ∧ (g : E) • x ∈ frameLat P ⊔ frameLat P' := by
  simp only [defLat, Submodule.mem_inf, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
    Nat.cast_smul_eq_nsmul]

theorem defLat_eq_pairLat (hg : g ≠ 0) (hP : PrimIn (frameLat P) Λ) (hu : u ∈ UO E r)
    (h : Cong g Λ (P * u) P') : defLat g Λ P P' = pairLat g (P * u) P' := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  rw [defLat, ← frameLat_mul (P := P) hu, ← defLat]
  rw [← frameLat_mul (P := P) hu] at hP
  generalize P * u = Q at *
  refine le_antisymm (fun x hx => ?_) (sup_le (fun x hx => ?_) fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := (mem_defLat x).1 hx
    obtain ⟨y, hy, y', hy', e⟩ := Submodule.mem_sup.1 h2
    obtain ⟨a, ha, rfl⟩ := (Iota.mem_frameLat _ _).1 hy
    obtain ⟨a', ha', rfl⟩ := (Iota.mem_frameLat _ _).1 hy'
    have k : ((g : E)⁻¹ • (P' - Q)) *ᵥ a' ∈ frameLat ((g : E)⁻¹ • (P' - Q)) :=
      (Iota.mem_frameLat _ _).2 ⟨a', ha', rfl⟩
    have e2 : x - ((g : E)⁻¹ • (P' - Q)) *ᵥ a' = Q *ᵥ ((g : E)⁻¹ • (a + a')) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.mulVec_add,
        ← inv_smul_smul₀ hg' x, ← e, ← smul_sub]
      congr 1; abel
    rw [← sub_add_cancel x (((g : E)⁻¹ • (P' - Q)) *ᵥ a')]
    exact add_mem (Submodule.mem_sup_left (hP.2 _ (sub_mem h1 (h k))
      ((Iota.mem_span_frameLat _ _).2 ⟨_, e2.symm⟩))) (Submodule.mem_sup_right k)
  · exact (mem_defLat x).2 ⟨hP.1 hx, Submodule.mem_sup_left (by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx g)⟩
  · refine (mem_defLat x).2 ⟨h hx, ?_⟩
    obtain ⟨a, ha, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
    rw [Matrix.smul_mulVec, smul_inv_smul₀ hg', Matrix.sub_mulVec]
    exact sub_mem (Submodule.mem_sup_right ((Iota.mem_frameLat _ _).2 ⟨a, ha, rfl⟩))
      (Submodule.mem_sup_left ((Iota.mem_frameLat _ _).2 ⟨a, ha, rfl⟩))

theorem defectAt_iff (F : Type) [Field F] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) :
    DefectAt F M Λ p ↔ ∃ x ∈ Λ, x ∈ Submodule.span E (M : Set (Fin n → E)) ∧
      ∀ a : 𝓞 F, a ∉ p.asIdeal → algebraMap (𝓞 F) (𝓞 E) a • x ∉ M := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨x, x.2.1, x.2.2, fun a ha h => hx a ha ((Submodule.Quotient.mk_eq_zero _).2 h)⟩
  · rintro ⟨x, h1, h2, h3⟩
    exact ⟨Submodule.Quotient.mk ⟨x, h1, h2⟩, fun a ha h => h3 a ha
      ((Submodule.Quotient.mk_eq_zero (M.submoduleOf (satLat M Λ))).1 h)⟩




theorem exists_UO (hP : Free P) (h : PrimIn (frameLat P) Λ) (h' : PrimIn (frameLat P) (latMap s Λ))
    (hs : InS σ J P s) : ∃ a ∈ UO E r, s * P = P * a := by
  obtain ⟨-, a, ha, e⟩ := inS_iff.1 hs
  refine ⟨a, mem_UO_of_le hP ha fun x hx => h'.2 x ?_ ?_, e⟩
  · rw [← e, frameLat_isom] at hx
    exact Submodule.map_mono h.1 hx
  · obtain ⟨c, -, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
    exact (Iota.mem_span_frameLat _ _).2 ⟨_, Matrix.mulVec_mulVec _ _ _⟩

theorem Unip.exists_UO (h : Unip P P') (hP : IntFrame σ J T Λ P) (hP' : frameLat P' ≤ Λ) :
    ∃ a ∈ UO E r, P' = P * a := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨a, mem_UO_of_le hP.1.1 ha fun x hx => hP.2.2 x (hP' hx) ?_, rfl⟩
  obtain ⟨c, -, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
  exact (Iota.mem_span_frameLat _ _).2 ⟨_, Matrix.mulVec_mulVec _ _ _⟩

theorem tower_admissible_self (h : IntFrame σ J T Λ P) : admitted σ J T g Λ P P :=
  ⟨h, 1, one_mem_UO, fun x hx => by
    obtain ⟨a, -, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
    simp⟩

theorem Transp.refl : Transp σ J P Λ A Λ A := ⟨1, inS_one, latMap_one _, 1, one_mem_UO, by simp⟩

theorem Transp.symm (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) : Transp σ J P Λ' B Λ A := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  have l := Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1)
  refine ⟨s⁻¹, inS_inv hJ hs, by rw [← latMap_mul, l, latMap_one], u⁻¹, UO_inv hu, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, up_mul_inv hu.1, Matrix.mul_one, ← Matrix.mul_assoc, l, Matrix.one_mul]

theorem Transp.trans (h : Transp σ J P Λ A Λ' B) (k : Transp σ J P Λ' B Λ'' C) : Transp σ J P Λ A Λ'' C := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨t, ht, rfl, v, hv, rfl⟩ := k
  exact ⟨t * s, inS_mul ht hs, latMap_mul _ _ _, u * v, UO_mul hu hv, by simp only [Matrix.mul_assoc]⟩

theorem move_equivalence (hJ : IsUnit J.det) : Equivalence (Move σ J Λ P) := by
  refine ⟨fun A => ⟨1, ⟨inN_one, latMap_one _⟩, 1, one_mem_UO, by simp⟩, ?_, ?_⟩
  · rintro A _ ⟨s, ⟨hs, e⟩, u, hu, rfl⟩
    have l := Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1)
    refine ⟨s⁻¹, ⟨inN_inv hJ hs, by conv_lhs => rw [← e, ← latMap_mul, l, latMap_one]⟩, u⁻¹, UO_inv hu, ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, up_mul_inv hu.1, Matrix.mul_one, ← Matrix.mul_assoc, l,
      Matrix.one_mul]
  · rintro A _ _ ⟨s, ⟨hs, e⟩, u, hu, rfl⟩ ⟨t, ⟨ht, f⟩, v, hv, rfl⟩
    exact ⟨t * s, ⟨inN_mul ht hs, by rw [latMap_mul, e, f]⟩, u * v, UO_mul hu hv, by
      simp only [Matrix.mul_assoc]⟩

theorem Move.transp (hP : IsFrame σ J T P) (h : Move σ J Λ P A B) : Transp σ J P Λ A Λ B := by
  obtain ⟨s, hs, u, hu, e⟩ := h
  exact ⟨s, inS_of_inN hP hs.1, hs.2, u, hu, e⟩

theorem Transp.pairM_eq (h : Transp σ J P Λ A Λ' B) :
    ∃ l u, IsLo l ∧ IsUp u ∧ pairM σ J B P = l * pairM σ J A P * u := by
  obtain ⟨s, hs, -, u, hu, rfl⟩ := h
  obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
  refine ⟨cT σ a⁻¹, u, lo_cT σ (up_inv ha), hu.1, ?_⟩
  rw [← pairM_isom (P' := A) h1, ← pairM_mul, e, Matrix.mul_assoc P, up_mul_inv ha, Matrix.mul_one]

theorem Transp.Gq_eq (h : Transp σ J P Λ A Λ' B) (T T' : E) :
    Gq σ T T' (pairM σ J B P) = Gq σ T T' (pairM σ J A P) := by
  obtain ⟨l, u, hl, hu, e⟩ := h.pairM_eq
  rw [e, Gq_mul T T' hl hu]

theorem Transp.lead_eq (h : Transp σ J P Λ A Λ' B) (l : ℕ) (hl : l ≤ r + 1) :
    SgAlg.lead (pairM σ J B P) l hl = SgAlg.lead (pairM σ J A P) l hl := by
  obtain ⟨a, u, ha, hu, e⟩ := h.pairM_eq
  rw [e, lead_mul_up _ hu, lead_lo_mul _ ha]

theorem Transp.liesAt_iff (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) (w : Formalism.MainNotions.S.Point E (r + 1)) :
    LiesAt w (pairM σ J B P) ↔ LiesAt w (pairM σ J A P) := by
  obtain ⟨a, u, ha, hu, e⟩ := h.pairM_eq
  obtain ⟨b, v, hb, hv, f⟩ := (h.symm hJ).pairM_eq
  exact ⟨fun k => f ▸ k.mul hb hv, fun k => e ▸ k.mul ha hu⟩

theorem Transp.unip_iff (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) : Unip P B ↔ Unip P A := by
  have k {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {A B : Matrix (Fin n) (Fin (r + 1)) E}
      (h : Transp σ J P Λ A Λ' B) (hA : Unip P A) : Unip P B := by
    obtain ⟨s, hs, -, u, hu, rfl⟩ := h
    obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
    obtain ⟨b, hb, rfl⟩ := hA
    exact ⟨a * b * u, up_mul (up_mul ha hb) hu.1, by rw [← Matrix.mul_assoc s, e]; simp only [Matrix.mul_assoc]⟩
  exact ⟨k (h.symm hJ), k h⟩

theorem Transp.adm (hJ : IsUnit J.det) (hP : Free P) (h1 : PrimIn (frameLat P) Λ) (h2 : PrimIn (frameLat P) Λ')
    (h : Transp σ J P Λ A Λ' B) (hA : admitted σ J T' g Λ P A) : admitted σ J T' g Λ' P B := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨a, ha, e⟩ := exists_UO hP h1 h2 hs
  obtain ⟨⟨k1, k2⟩, w, hw, k3⟩ := hA
  refine ⟨⟨isFrame_mul (isFrame_isom hJ k1 hs.1) hu.1, ?_⟩, a * w * u, UO_mul (UO_mul ha hw) hu, ?_⟩
  · rwa [frameLat_mul hu, frameLat_isom, primIn_latMap (isUnit_det_of_isUn hJ hs.1)]
  · have : (g : E)⁻¹ • (s * A * u - P * (a * w * u)) = s * ((g : E)⁻¹ • (A - P * w)) * u := by
      rw [← Matrix.mul_assoc P, ← Matrix.mul_assoc P, ← e]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [Cong, this, frameLat_mul hu, frameLat_isom]
    exact Submodule.map_mono k3

theorem Transp.defLat_eq (hJ : IsUnit J.det) (hP : Free P) (h1 : PrimIn (frameLat P) Λ)
    (h2 : PrimIn (frameLat P) Λ') (h : Transp σ J P Λ A Λ' B) :
    ∃ s, IsUnit s.det ∧ latMap s Λ = Λ' ∧ latMap s (defLat g Λ P A) = defLat g Λ' P B := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨a, ha, e⟩ := exists_UO hP h1 h2 hs
  have hd := isUnit_det_of_isUn hJ hs.1
  have hsur := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hd)
  refine ⟨s, hd, rfl, Submodule.ext (hsur.forall.2 fun x => ?_)⟩
  have k : frameLat P ⊔ frameLat (s * A * u) = latMap s (frameLat P ⊔ frameLat A) := by
    rw [frameLat_mul hu, frameLat_isom, latMap, latMap, Submodule.map_sup, ← latMap, ← latMap,
      ← frameLat_isom (P := P), e, frameLat_mul ha]
  rw [mulVec_mem_latMap hd, mem_defLat, mem_defLat, k, ← Matrix.mulVec_smul, mulVec_mem_latMap hd,
    mulVec_mem_latMap hd]

end Lattice

end GlobalTheory.IntTerm
end
end

section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P

def normOf (P : Matrix (Fin n) (Fin (r + 1)) E) : E := -pairM σ J P P (Fin.last r) (Fin.last r)

open scoped Classical in

def nullPt (T T' : E) (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) :=
  if h : ∃ w : Formalism.MainNotions.S.Point E (r + 1), Gq σ T T' (Formalism.MainNotions.S.ptMat w) = 0 then h.choose else onePt E r

open scoped Classical in

def ptOrNull (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Formalism.MainNotions.S.Point E (r + 1) :=
  if ∃ w, LiesAt w Z then ptOfMat Z else nullPt σ T T' r

variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

def mk (c : Col σ J P) (A : Matrix (Fin n) (Fin (r + 1)) E) (h : admitted σ J T' g c.lat P A) : Term σ J T' g P :=
  ⟨c, Quot.mk _ ⟨A, h⟩⟩

variable (t : Term σ J T' g P)

def col : Col σ J P := t.1

def lat : Submodule (𝓞 E) (Fin n → E) := t.col.lat

def fr : Matrix (Fin n) (Fin (r + 1)) E := (Quot.out t.2).1

def Zhat : Matrix (Fin (r + 1)) (Fin (r + 1)) E := pairM σ J t.fr P

def minor (l : ℕ) (hl : l ≤ r + 1) : E := SgAlg.lead t.Zhat l hl

def G : E := Gq σ (normOf σ J P) T' t.Zhat

def GF (F : Type) [Field F] [Algebra F E] : F := Function.invFun (algebraMap F E) t.G

def isId : Prop := ∃ h : admitted σ J T' g t.col.lat P P, t = mk t.col P h

def inS : Prop := Unip P t.fr

def FeqF : Prop := Move σ J t.lat P P t.fr

def sameFlag : Prop := SameFlag P t.fr

def relevant : Prop := Relevant σ J P t.fr

def M : Submodule (𝓞 E) (Fin n → E) := defLat g t.lat P t.fr

abbrev BB : Type := Defect t.M t.lat

def BBne (F : Type) [Field F] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) : Prop := DefectAt F t.M t.lat p

def prim : Prop := PrimIn t.M t.lat

def generic : Prop := t.G ≠ 0 ∧ PrimIn t.M t.lat

def At (w : Formalism.MainNotions.S.Point E (r + 1)) : Prop := LiesAt w t.Zhat

def ptOf : Formalism.MainNotions.S.Point E (r + 1) := ptOrNull σ (normOf σ J P) T' t.Zhat

def Carries {P₀ : Matrix (Fin n) (Fin (r + 1)) E} (c' : Col σ J P₀) (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J γ ∧ latMap γ c'.lat = t.lat ∧ Move σ J t.lat P (γ * P₀) t.fr

def Rep (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  Transp σ J P t.lat t.fr Λ A

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}

omit [NumberField E] in

theorem normOf_eq (hP : IsFrame σ J T P) : normOf σ J P = T := by
  rw [normOf, hP.2]; simp [TF]

omit [NumberField E] in

theorem ptEntry_replicate (ζ : E) : ∀ (m i j : ℕ), Formalism.MainNotions.S.ptEntry (List.replicate m ((1 : E), 1) ++ [(ζ, 1)]) i j =
    if i = j then (if i < m then 1 else if i = m then ζ else 0) else 0
  | 0, i, j => by
    simp only [List.replicate_zero, List.nil_append, Formalism.MainNotions.S.ptEntry]
    split_ifs <;> first | rfl | omega
  | m + 1, i, j => by
    rw [List.replicate_succ, List.cons_append, Formalism.MainNotions.S.ptEntry, ptEntry_replicate ζ m]
    split_ifs <;> first | rfl | omega

omit [NumberField E] in

theorem Gq_nullPt {ζ : E} (hζ : ζ ≠ 0) (h : ζ * σ ζ = T * T') :
    Gq σ T T' (Formalism.MainNotions.S.ptMat (nullPt σ T T' r)) = 0 := by
  have k : ∃ w : Formalism.MainNotions.S.Point E (r + 1), Gq σ T T' (Formalism.MainNotions.S.ptMat w) = 0 := by
    let w : Formalism.MainNotions.S.Point E (r + 1) := ⟨List.replicate r ((1 : E), 1) ++ [(ζ, 1)], fun b hb => by
      rcases List.mem_append.1 hb with hb | hb
      · rw [List.eq_of_mem_replicate hb]; simp
      · rw [List.mem_singleton.1 hb]; simpa using hζ, by simp⟩
    have e : Formalism.MainNotions.S.ptMat w = Matrix.diagonal fun a => if a = Fin.last r then ζ else 1 := by
      ext a b
      have := a.2
      rw [Formalism.MainNotions.S.ptMat, ptEntry_replicate, Matrix.diagonal_apply]
      simp only [Fin.ext_iff, Fin.val_last]
      split_ifs <;> first | rfl | omega
    have h1 : (Formalism.MainNotions.S.ptMat w).det = ζ := by
      simp [e, Fin.prod_univ_castSucc, (Fin.castSucc_lt_last _).ne]
    have h2 : SgAlg.lead (Formalism.MainNotions.S.ptMat w) r (Nat.le_succ r) = 1 := by
      rw [SgAlg.lead, e, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
      exact Finset.prod_eq_one fun i _ => if_neg (Fin.castSucc_lt_last i).ne
    exact ⟨w, by rw [Gq, h1, h2, h, map_one]; ring⟩
  rw [nullPt, dif_pos k]; exact k.choose_spec

omit [NumberField E] in

theorem Gq_mul_eps (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Gq σ T T' (Z * eps E r) = Gq σ T T' Z := by
  have k (l : ℕ) (hl : l ≤ r + 1) : SgAlg.lead (Z * eps E r) l hl * σ (SgAlg.lead (Z * eps E r) l hl) =
      SgAlg.lead Z l hl * σ (SgAlg.lead Z l hl) := by
    have e : (Z * eps E r).submatrix (Fin.castLE hl) (Fin.castLE hl) = Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal fun b : Fin l => (-1 : E) ^ (r - (b : ℕ)) := by
      ext a b; simp [eps]
    have s : (∏ b : Fin l, (-1 : E) ^ (r - (b : ℕ))) * σ (∏ b : Fin l, (-1 : E) ^ (r - (b : ℕ))) = 1 := by
      simp [← Finset.prod_mul_distrib, ← mul_pow]
    rw [SgAlg.lead, e, Matrix.det_mul, Matrix.det_diagonal, map_mul, mul_mul_mul_comm, s, mul_one, SgAlg.lead]
  have k1 : (Z * eps E r).det * σ (Z * eps E r).det = Z.det * σ Z.det := k (r + 1) le_rfl
  rw [Gq, Gq, k, k1]

omit [NumberField E] in

theorem LiesAt.Gq_eq {w : Formalism.MainNotions.S.Point E (r + 1)} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : LiesAt w Z)
    (T T' : E) : Gq σ T T' (Formalism.MainNotions.S.ptMat w) = Gq σ T T' Z := by
  obtain ⟨l, u, hl, hu, e⟩ := h
  rw [← Gq_mul_eps T T' Z, e, Gq_mul T T' hl hu]

theorem Col.lat_mem (c : Col σ J P) : c.lat ∈ FrameLats σ J P := (Quot.out c).2

theorem Col.existsUnique (hJ : IsUnit J.det) (h : Λ ∈ FrameLats σ J P) :
    ∃! c : Col σ J P, ∃ s, InS σ J P s ∧ latMap s Λ = c.lat := by
  have hre : Equivalence fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1 :=
    ⟨fun _ => ⟨1, inS_one, latMap_one _⟩, fun ⟨s, hs, e⟩ => ⟨s⁻¹, inS_inv hJ hs, by
      rw [← e, ← latMap_mul, Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1), latMap_one]⟩,
      fun ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨t * s, inS_mul ht hs, by rw [latMap_mul, e, f]⟩⟩
  refine ⟨Quot.mk _ ⟨Λ, h⟩,
    hre.eqvGen_iff.1 (Quot.eq.1 (Quot.out_eq (Quot.mk _ (⟨Λ, h⟩ : FrameLats σ J P))).symm), fun c hc => ?_⟩
  exact (Quot.out_eq c).symm.trans (Quot.sound (a := (⟨Λ, h⟩ : FrameLats σ J P)) hc).symm

namespace Term

variable (t : Term σ J T' g P)

theorem lat_mem : t.lat ∈ FrameLats σ J P := t.col.lat_mem

theorem adm : admitted σ J T' g t.lat P t.fr := (Quot.out t.2).2

theorem mk_fr : mk t.col t.fr t.adm = t := by
  obtain ⟨c, q⟩ := t
  exact congrArg (Sigma.mk c) (Quot.out_eq q)

theorem mk_eq_mk (hJ : IsUnit J.det) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) (hB : admitted σ J T' g c.lat P B) :
    mk c A hA = mk c B hB ↔ Move σ J c.lat P A B := by
  have hre : Equivalence fun A B : {A // admitted σ J T' g c.lat P A} => Move σ J c.lat P A.1 B.1 :=
    (move_equivalence hJ).comap Subtype.val
  exact ⟨fun h => hre.eqvGen_iff.1 (Quot.eq.1 (eq_of_heq (Sigma.mk.inj h).2)),
    fun h => congrArg (Sigma.mk c) (Quot.sound h)⟩

theorem move_fr_mk (hJ : IsUnit J.det) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) :
    Move σ J c.lat P (mk c A hA).fr A :=
  (mk_eq_mk hJ c (mk c A hA).adm hA).1 (mk c A hA).mk_fr

theorem rep_mk (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) :
    (mk c A hA).Rep c.lat A := (move_fr_mk hJ c hA).transp hP

theorem exists_rep (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (h : Λ ∈ FrameLats σ J P)
    (hA : admitted σ J T' g Λ P A) : ∃ t : Term σ J T' g P, t.Rep Λ A := by
  obtain ⟨c, ⟨s, hs, e⟩, -⟩ := Col.existsUnique hJ h
  have k : Transp σ J P Λ A c.lat (s * A) := ⟨s, hs, e, 1, one_mem_UO, (Matrix.mul_one _).symm⟩
  exact ⟨_, (rep_mk hJ hP c (k.adm hJ hP.1 h.2 c.lat_mem.2 hA)).trans (k.symm hJ)⟩

variable {t}


theorem Rep.G_eq (h : t.Rep Λ A) (hP : IsFrame σ J T P) : t.G = Gq σ T T' (pairM σ J A P) := by
  rw [Term.G, normOf_eq hP]; exact (Transp.Gq_eq h T T').symm

theorem Rep.inS_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) : t.inS ↔ Unip P A := (Transp.unip_iff hJ h).symm

theorem Rep.generic_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (hΛ : Λ ∈ FrameLats σ J P) :
    t.generic ↔ Gq σ T T' (pairM σ J A P) ≠ 0 ∧ PrimIn (defLat g Λ P A) Λ := by
  obtain ⟨s, hs, e1, e2⟩ := Transp.defLat_eq (g := g) hJ hP.1 t.lat_mem.2 hΛ.2 h
  rw [← e2, ← h.G_eq hP]
  conv_rhs => enter [2, 2]; rw [← e1]
  exact and_congr_right fun _ => (primIn_latMap hs).symm

variable (t)



theorem M_eq (hg : g ≠ 0) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hu : u ∈ UO E r)
    (h : Cong g t.lat (P * u) t.fr) : t.M = pairLat g (P * u) t.fr :=
  defLat_eq_pairLat hg t.lat_mem.2 hu h

theorem M_le : t.M ≤ t.lat := inf_le_left



theorem generic_iff : t.generic ↔ t.G ≠ 0 ∧ t.prim := Iff.rfl




theorem at_ptOf (h : ∃ w, t.At w) : t.At t.ptOf := by
  rw [Term.ptOf, ptOrNull, if_pos (show ∃ w, LiesAt w t.Zhat from h)]; exact liesAt_ptOfMat h

theorem At.Gq_eq {t : Term σ J T' g P} {w : Formalism.MainNotions.S.Point E (r + 1)} (h : t.At w) (hP : IsFrame σ J T P) :
    Gq σ T T' (Formalism.MainNotions.S.ptMat w) = t.G := by
  rw [Term.G, normOf_eq hP]; exact LiesAt.Gq_eq h T T'






theorem inS.props {t : Term σ J T' g P} (h : t.inS) (hP : IsFrame σ J T P) (hT : σ T = T) :
    t.sameFlag ∧ t.relevant ∧ t.G = 0 ∧ T' = T := by
  obtain rfl := Unip.norm_eq h hP t.adm.1.1
  obtain ⟨a, ha, e⟩ := h
  refine ⟨⟨a, up_tri ha, by simp [up_det ha], e⟩, ?_, ?_, rfl⟩
  · simpa [Term.relevant, e] using (relevant_self (σ := σ) (J := J) hP.1).mul up_one ha
  · have k := pairM_mul (σ := σ) (J := J) (P := P) (P' := P) a 1
    rw [Matrix.mul_one, ← e, hP.2] at k
    rw [Term.G, normOf_eq hP, Term.Zhat, k, Gq_mul _ _ (lo_cT σ up_one) ha, Gq_TF hT]

theorem inS.prim {t : Term σ J T' g P} (h : t.inS) (hP : IsFrame σ J T P) : t.prim := by
  obtain ⟨a, ha, e⟩ := Unip.exists_UO h ⟨hP, t.lat_mem.2⟩ t.adm.1.2.1
  refine ⟨t.M_le, fun v hv k => (mem_defLat v).2 ⟨hv, Submodule.mem_sup_left ?_⟩⟩
  rw [Nat.cast_smul_eq_nsmul]
  by_cases hg : g = 0
  · simp [hg]
  refine nsmul_mem (t.lat_mem.2.2 v hv (Submodule.span_le.2 (fun x hx => ?_) k)) g
  have := ((mem_defLat x).1 hx).2
  rw [e, frameLat_mul ha, sup_idem] at this
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hg)).1 (Submodule.subset_span this)


theorem exists_generic (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermU σ J) (hg : g ≠ 0)
    {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : ((Λ, P, A) : Tri E n r) ∈ GenConf σ J T T' g Z)
    (hG : Gq σ T T' Z ≠ 0) : ∃ t : Term σ J T' g P, t.Rep Λ A ∧ t.generic ∧ t.G = Gq σ T T' Z := by
  obtain ⟨h1, ⟨h2, h3, h4⟩, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h4
  obtain ⟨k1, k2⟩ := Iota.primIn_frameLat (Nat.cast_ne_zero.2 hg) h5
    (Iota.indep_of_Gq_ne_zero hσ hJ.1 ⟨h2, h3, rfl⟩ hG)
  have hc : Cong g Λ (P * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) A := by
    rw [Matrix.mul_one]; exact le_sup_right.trans h5.1
  obtain ⟨t, ht⟩ := exists_rep hJ.2 h2 ⟨h1, k1⟩ ⟨⟨h3, k2⟩, 1, one_mem_UO, hc⟩
  refine ⟨t, ht, (ht.generic_iff hJ.2 h2 ⟨h1, k1⟩).2 ⟨hG, ?_⟩, ht.G_eq h2⟩
  rwa [defLat_eq_pairLat hg k1 one_mem_UO hc, Matrix.mul_one]

end Term

end Basic

section Examples

variable {E : Type} [Field E] [NumberField E]



example : LiesAt (onePt E 1) !![0, 1; -1, 0] :=
  ⟨1, 1, fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne, fun h => h ▸ Matrix.one_apply_eq _⟩, up_one, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [eps, onePt, Formalism.MainNotions.S.ptMat, Formalism.MainNotions.S.ptEntry]⟩

example (σ : E →+* E) :
    ¬ Relevant (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1] !![1, 0; 0, 0; 0, 1] !![-1, 0; 0, 0; 0, 1] := by
  intro h
  have k (c : E) (hc : c * c = 1) (hs : σ c = c) : LieN (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1]
      !![c, 0; 0, 0; 0, 1] !![0, 0, 1; 0, 0, 0; 0, 1, 0] !![0, c; 0, 0] := by
    refine ⟨?_, fun i j hij => ?_, ?_, fun x hx => ⟨![c * x 2], ?_⟩⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [cT, Matrix.mul_apply, Fin.sum_univ_three]
    · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hc]
    · have h1 : x 1 = 0 := by
        have := (mem_perpX_iff_form _ _).1 hx 0
        have hc0 : c ≠ 0 := fun e => by simp [e] at hc
        simpa [form, dotProduct, Matrix.mulVec, Fin.sum_univ_three, hs, hc0] using this
      ext i
      fin_cases i <;> simp [eOf, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, ← mul_assoc, hc]
  have := h _ _ _ (k 1 (by simp) (by simp)) (k (-1) (by simp) (by simp))
  simp [simpleSum] at this

end Examples

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coMat (V : HSpace E) {a : Type} (x : a → V.V) : Matrix (Fin V.rank) a E :=
  Matrix.of fun i b => V.frame.repr (x b) i

theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

theorem pairM_coMat (V : HSpace E) {a b : Type} (x : a → V.V) (y : b → V.V) (i : a) (j : b) :
    pairM (starRingEnd E) V.gram (coMat V y) (coMat V x) i j = V.hD (y j) (x i) := by
  rw [HSpace.hD, hT_eq_sum]; rfl


def spFrame (S : Spaces R F E) (c : E) : Matrix (Fin (S.Y 0).rank) (Fin (R.rS + 1)) E :=
  coMat (S.Y 0) (Fin.snoc (α := fun _ => (S.Y 0).V) S.hypE (c • S.zm))

theorem isFrame_spFrame (S : Spaces R F E) {c : E} (hc : c ≠ 0) :
    IsFrame (starRingEnd E) (S.Y 0).gram (c * star c * S.T) (spFrame S c) := by
  have hT : (S.T : E) ≠ 0 := Nat.cast_ne_zero.2 S.T_prime.ne_zero
  have sw {x y : (S.Y 0).V} {a : E} (h : (S.Y 0).hT x y = a) : (S.Y 0).hT y x = star a := by
    rw [← h]; exact ((S.Y 0).herm.eq x y).symm
  refine ⟨⟨cT (starRingEnd E) (coMat (S.Y 0) (Fin.snoc (α := fun _ => (S.Y 0).V) S.hypF
    ((-(star c * S.T)⁻¹) • S.zm))) * (S.Y 0).gram, ?_⟩, ?_⟩
  · ext a b
    refine (pairM_coMat _ _ _ a b).trans ?_
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · simp [HSpace.hD, S.zm_norm, starRingEnd_apply]
      field_simp
    · simp [HSpace.hD, (S.hyp_orthz _).1, (Fin.castSucc_lt_last _).ne']
    · simp [HSpace.hD, sw (S.hyp_orthz _).2, (Fin.castSucc_lt_last _).ne]
    · simp [HSpace.hD, sw (S.hyp_ef _ _), Matrix.one_apply, eq_comm, apply_ite star]
  · ext a b
    refine (pairM_coMat _ _ _ a b).trans ?_
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · simp [HSpace.hD, S.zm_norm, TF, starRingEnd_apply]
      ring
    · simp [HSpace.hD, (S.hyp_orthz _).1, TF, (Fin.castSucc_lt_last _).ne']
    · simp [HSpace.hD, sw (S.hyp_orthz _).1, TF, (Fin.castSucc_lt_last _).ne]
    · simp [HSpace.hD, S.hyp_ee, TF, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne]

end Spaces

section Record

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def recFrame (u : D.what₂.Word) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.R.rS + 1)) D.host.E :=
  spFrame D.sp (D.cOf u)⁻¹

abbrev RecTerm (u u' : D.what₂.Word) : Type :=
  Term (starRingEnd D.host.E) (D.sp.Y 0).gram (((D.mem u').A.T : ℕ) : D.host.E) (D.host.g 0 * D.host.g 1)
    (recFrame D u)


theorem isFrame_recFrame (u : D.what₂.Word) :
    IsFrame (starRingEnd D.host.E) (D.sp.Y 0).gram (((D.mem u).A.T : ℕ) : D.host.E) (recFrame D u) := by
  have h := isFrame_spFrame D.sp (inv_ne_zero (D.cOf_ne u))
  have hc := D.cOf_ne u
  have hs : star (D.cOf u) ≠ 0 := star_ne_zero.2 hc
  have e : D.cOf u * star (D.cOf u) * ((D.mem u).A.T : D.host.E) = ((D.mem D.u₀).A.T : D.host.E) := by
    rw [bridge_star_holds D.R D.host]; exact D.cOf_eq u
  rwa [D.sp_T, ← e, star_inv₀, show (D.cOf u)⁻¹ * (star (D.cOf u))⁻¹ *
    (D.cOf u * star (D.cOf u) * ((D.mem u).A.T : D.host.E)) = ((D.mem u).A.T : D.host.E) by field_simp] at h

variable {D} {u u' : D.what₂.Word}




theorem exists_norm_eq (u u' : D.what₂.Word) : ∃ ζ : D.host.E, ζ ≠ 0 ∧
    ζ * starRingEnd D.host.E ζ = ((D.mem u).A.T : D.host.E) * ((D.mem u').A.T : D.host.E) := by
  have k (u : D.what₂.Word) : ∃ π : D.host.E, π ≠ 0 ∧ π * star π = ((D.mem u).A.T : D.host.E) := by
    obtain ⟨π, -, h, -⟩ := D.T_norm u
    refine ⟨π, fun e => ?_, by rw [bridge_star_holds D.R D.host]; exact h⟩
    have h2 := D.cOf_eq u
    rw [← h, e, zero_mul, mul_zero, ← D.sp_T] at h2
    exact D.sp.T_prime.ne_zero (Nat.cast_eq_zero.1 h2.symm)
  obtain ⟨a, ha, e⟩ := k u
  obtain ⟨b, hb, f⟩ := k u'
  exact ⟨a * b, mul_ne_zero ha hb, by rw [← e, ← f, starRingEnd_apply, star_mul]; ring⟩



end Record

end GlobalTheory.IntTerm
end
end
