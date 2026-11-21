import Formalism.SharpRestriction.GrowthBounds.ObjPol

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

open Classical in

def vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = true then al v else 0

open Classical in

def covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = false then al v else 0

structure flt_Fil (B : Type*) [CommRing B] where
  F : ℤ → AddSubgroup B
  mul_mem : ∀ {t u : ℤ} {a b : B}, a ∈ F t → b ∈ F u → a * b ∈ F (t + u)
  one_mem : (1 : B) ∈ F 0
  anti : ∀ {t u : ℤ}, t ≤ u → F u ≤ F t

def flt_L (A : Type*) [CommRing A] (e : ℤ) : flt_Fil (LaurentPolynomial A) where
  F t :=
    { carrier := {f | ∀ k : ℤ, f.coeff k ≠ 0 → t ≤ e * k}
      zero_mem' := by intro k hk; simp at hk
      add_mem' := by
        intro a b ha hb k hk
        by_cases h : a.coeff k = 0
        · apply hb k
          intro h'
          apply hk
          simp [AddMonoidAlgebra.coeff_add, h, h']
        · exact ha k h
      neg_mem' := by
        intro a ha k hk
        apply ha k
        intro h
        apply hk
        simp [AddMonoidAlgebra.coeff_neg, h] }
  mul_mem := by
    classical
    intro t u a b ha hb k hk
    have hk' : k ∈ (a * b).coeff.support := Finsupp.mem_support_iff.2 hk
    have := AddMonoidAlgebra.support_coeff_mul_subset a b hk'
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 this
    have h1 := ha x (Finsupp.mem_support_iff.1 hx)
    have h2 := hb y (Finsupp.mem_support_iff.1 hy)
    rw [mul_add]
    exact add_le_add h1 h2
  one_mem := by
    intro k hk
    have : k = 0 := by
      by_contra h
      apply hk
      rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply, if_neg (Ne.symm h)]
    simp [this]
  anti := by
    intro t u h f hf k hk
    exact h.trans (hf k hk)

theorem flt_L_mem {A : Type*} [CommRing A] {e t : ℤ} {f : LaurentPolynomial A} :
    f ∈ (flt_L A e).F t ↔ ∀ k : ℤ, f.coeff k ≠ 0 → t ≤ e * k := Iff.rfl

theorem flt_L_C {A : Type*} [CommRing A] (e : ℤ) (a : A) : LaurentPolynomial.C a ∈ (flt_L A e).F 0 := by
  rw [flt_L_mem]
  intro k hk
  by_cases h : k = 0
  · simp [h]
  · exfalso
    apply hk
    rw [← LaurentPolynomial.single_eq_C]
    simp [Finsupp.single_apply, Ne.symm h]
    intro h'
    exact absurd h' h

theorem T_mem_laurentFiltration {A : Type*} [CommRing A] (e k : ℤ) : (LaurentPolynomial.T k : LaurentPolynomial A) ∈ (flt_L A e).F (e * k) := by
  rw [flt_L_mem]
  intro k' hk
  rw [LaurentPolynomial.T_apply] at hk
  split_ifs at hk with h
  · rw [h]
  · exact absurd rfl hk

def flt_lift {B : Type*} [CommRing B] {σ : Type*} (Fl : flt_Fil B) (wt : (σ →₀ ℕ) →+ ℤ) :
    flt_Fil (MvPolynomial σ B) where
  F t :=
    { carrier := {P | ∀ m, coeff m P ∈ Fl.F (t - wt m)}
      zero_mem' := by intro m; simp
      add_mem' := by
        intro a b ha hb m
        rw [coeff_add]
        exact (Fl.F _).add_mem (ha m) (hb m)
      neg_mem' := by
        intro a ha m
        rw [coeff_neg]
        exact (Fl.F _).neg_mem (ha m) }
  mul_mem := by
    classical
    intro t u a b ha hb m
    rw [coeff_mul]
    refine (Fl.F _).sum_mem fun x hx => ?_
    have hx' : x.1 + x.2 = m := by simpa using hx
    have := Fl.mul_mem (ha x.1) (hb x.2)
    have e1 : t - wt x.1 + (u - wt x.2) = t + u - wt m := by
      rw [← hx', map_add]; ring
    rwa [e1] at this
  one_mem := by
    classical
    intro m
    rw [coeff_one]
    split_ifs with h
    · subst h
      simpa using Fl.one_mem
    · exact (Fl.F _).zero_mem
  anti := by
    intro t u h P hP m
    exact Fl.anti (by linarith) (hP m)

theorem flt_lift_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {P : MvPolynomial σ B} : P ∈ (flt_lift Fl wt).F t ↔ ∀ m, coeff m P ∈ Fl.F (t - wt m) := Iff.rfl

theorem flt_monomial_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {m : σ →₀ ℕ} {a : B} (ha : a ∈ Fl.F (t - wt m)) : monomial m a ∈ (flt_lift Fl wt).F t := by
  classical
  rw [flt_lift_mem]
  intro m'
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact ha
  · exact (Fl.F _).zero_mem

theorem flt_C_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {a : B} (ha : a ∈ Fl.F t) : (C a : MvPolynomial σ B) ∈ (flt_lift Fl wt).F t := by
  have := flt_monomial_mem (wt := wt) (m := 0) (a := a) (t := t) (by simpa using ha)
  rwa [← C_apply] at this

theorem flt_pow_mem {B : Type*} [CommRing B] (Fl : flt_Fil B) {t : ℤ} {a : B} (ha : a ∈ Fl.F t) (k : ℕ) :
    a ^ k ∈ Fl.F (k * t) := by
  induction k with
  | zero => simpa using Fl.one_mem
  | succ k ih =>
    rw [pow_succ]
    have := Fl.mul_mem ih ha
    have e : ((k : ℤ) * t + t) = ((k + 1 : ℕ) : ℤ) * t := by push_cast; ring
    rwa [e] at this

theorem flt_hom_monomial {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) (m : σ →₀ ℕ) :
    φ (monomial m 1) ∈ Fl'.F (wt m) := by
  classical
  refine Finsupp.induction m ?_ ?_
  · simpa using Fl'.one_mem
  · intro a b f _ _ ih
    have e : monomial (Finsupp.single a b + f) (1 : B₀) = monomial (Finsupp.single a b) 1 * monomial f 1 := by
      rw [monomial_mul, one_mul]
    rw [e, ← X_pow_eq_monomial, map_mul, map_pow, map_add]
    refine Fl'.mul_mem ?_ ih
    have hp := flt_pow_mem Fl' (hX a) b
    have e2 : Finsupp.single a b = b • Finsupp.single a 1 := by simp
    rw [e2, map_nsmul, nsmul_eq_mul]
    exact hp

theorem flt_hom_mem {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl : flt_Fil B₀) (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hC : ∀ (t : ℤ) (b : B₀), b ∈ Fl.F t → φ (C b) ∈ Fl'.F t)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) {t : ℤ} {P : MvPolynomial σ B₀}
    (hP : P ∈ (flt_lift Fl wt).F t) : φ P ∈ Fl'.F t := by
  classical
  rw [P.as_sum, map_sum]
  refine (Fl'.F t).sum_mem fun m _ => ?_
  have e : monomial m (coeff m P) = C (coeff m P) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [e, map_mul]
  have := Fl'.mul_mem (hC _ _ ((flt_lift_mem.1 hP) m)) (flt_hom_monomial Fl' φ wt hX m)
  rwa [sub_add_cancel] at this

abbrev laurentCoeffFiltration (R : Type*) [CommRing R] (n : ℕ) (σ : Type*) (e : ℤ) : flt_Fil (MvPolynomial σ (GLLaurent R n)) :=
  flt_lift (flt_L (GLCoord R n) e) 0

theorem flt_mem_sDegs {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∈ sDegs LL S j G ↔ ∃ m, ((twistSub LL S j G).coeff m).coeff k ≠ 0 := by
  classical
  unfold sDegs
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨m, -, hk⟩
    exact ⟨m, Finsupp.mem_support_iff.1 hk⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h]
    rfl

theorem flt_le_valS {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (t : ℤ) :
    (t : WithTop ℤ) ≤ valS LL S G ↔ twistSub LL S (lastIdx n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F t := by
  unfold valS
  rw [Finset.le_inf_iff, flt_lift_mem]
  constructor
  · intro h m
    rw [flt_L_mem]
    intro k hk
    have := h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩)
    simp only [AddMonoidHom.zero_apply, sub_zero, one_mul]
    exact WithTop.coe_le_coe.1 this
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    have := (flt_L_mem.1 (h m)) k hm
    simp only [AddMonoidHom.zero_apply, sub_zero, one_mul] at this
    exact WithTop.coe_le_coe.2 this

theorem flt_lam1S_le {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (M : ℤ) :
    lam1S LL S G ≤ (M : WithBot ℤ) ↔ twistSub LL S (0 : Fin n) G ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-M) := by
  unfold lam1S
  rw [Finset.sup_le_iff, flt_lift_mem]
  constructor
  · intro h m
    rw [flt_L_mem]
    intro k hk
    have := WithBot.coe_le_coe.1 (h k ((flt_mem_sDegs LL S _ G k).2 ⟨m, hk⟩))
    simp only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff]
    exact this
  · intro h k hk
    obtain ⟨m, hm⟩ := (flt_mem_sDegs LL S _ G k).1 hk
    have := (flt_L_mem.1 (h m)) k hm
    simp only [AddMonoidHom.zero_apply, sub_zero, neg_one_mul, neg_le_neg_iff] at this
    exact WithBot.coe_le_coe.2 this

theorem flt_withTop_le {a b : WithTop ℤ} {N : ℤ}
    (h : ∀ t : ℤ, (t : WithTop ℤ) ≤ a → ((t - N : ℤ) : WithTop ℤ) ≤ b) : a ≤ b + (N : WithTop ℤ) := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe c =>
      exfalso
      have := WithTop.coe_le_coe.1 (h (c + N + 1) le_top)
      linarith
  | coe x =>
    have h1 := h x le_rfl
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe c =>
      have := WithTop.coe_le_coe.1 h1
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      linarith

theorem flt_withTop_add_le {a b c : WithTop ℤ}
    (h : ∀ t u : ℤ, (t : WithTop ℤ) ≤ a → (u : WithTop ℤ) ≤ b → ((t + u : ℤ) : WithTop ℤ) ≤ c) : a + b ≤ c := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction c using WithTop.recTopCoe with
    | top => exact le_top
    | coe z =>
      exfalso
      induction b using WithTop.recTopCoe with
      | top =>
        have := WithTop.coe_le_coe.1 (h (z + 1) 0 le_top le_top)
        linarith
      | coe y =>
        have := WithTop.coe_le_coe.1 (h (z - y + 1) y le_top le_rfl)
        linarith
  | coe x =>
    induction b using WithTop.recTopCoe with
    | top =>
      induction c using WithTop.recTopCoe with
      | top => exact le_top
      | coe z =>
        exfalso
        have := WithTop.coe_le_coe.1 (h x (z - x + 1) le_rfl le_top)
        linarith
    | coe y =>
      rw [← WithTop.coe_add]
      exact h x y le_rfl le_rfl

theorem flt_valS_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) := by
  have key := flt_withTop_le (a := min (valS LL S F) (valS LL S G)) (b := valS LL S (F + G)) (N := 0) ?_
  · simpa using key
  intro t ht
  obtain ⟨h1, h2⟩ := le_min_iff.1 ht
  simp only [sub_zero]
  rw [flt_le_valS] at h1 h2 ⊢
  rw [map_add]
  exact AddSubgroup.add_mem _ h1 h2

theorem flt_valS_mul_ge {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S F + valS LL S G ≤ valS LL S (F * G) := by
  apply flt_withTop_add_le
  intro t u ht hu
  rw [flt_le_valS] at ht hu ⊢
  rw [map_mul]
  exact (laurentCoeffFiltration R n (ι × Fin n) 1).mul_mem ht hu

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

theorem flt_twistMat_mem (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k e t : ℤ) (h0 : t ≤ 0) (hk : t ≤ e * k)
    (b c : Fin n) : twistMat R n j k b c ∈ (flt_L (GLCoord R n) e).F t := by
  unfold twistMat
  rw [Matrix.mul_apply]
  refine sum_mem fun a _ => ?_
  rw [Matrix.mul_diagonal]
  have hg : gL R n b a ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gL, Matrix.map_apply]
    exact flt_L_C e _
  have hgi : gLinv R n a c ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gLinv, Matrix.map_apply]
    exact flt_L_C e _
  have hd : (if a = j then LaurentPolynomial.T k else 1) ∈ (flt_L (GLCoord R n) e).F t := by
    split_ifs
    · exact (flt_L (GLCoord R n) e).anti hk (T_mem_laurentFiltration e k)
    · exact (flt_L (GLCoord R n) e).anti h0 (flt_L (GLCoord R n) e).one_mem
  have hm := (flt_L (GLCoord R n) e).mul_mem ((flt_L (GLCoord R n) e).mul_mem hg hd) hgi
  rwa [zero_add, add_zero] at hm

open Classical in

def flt_cost {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Finsupp.liftAddHom fun v => if v.1 ∈ S ∧ LL.vec v.1 = b then Nat.castAddMonoidHom ℤ else 0

open Classical in
theorem flt_cost_single {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) (v : ι × Fin n) (k : ℕ) :
    flt_cost LL S b (Finsupp.single v k) = if v.1 ∈ S ∧ LL.vec v.1 = b then (k : ℤ) else 0 := by
  unfold flt_cost
  rw [Finsupp.liftAddHom_apply_single]
  split_ifs
  · rfl
  · rfl

def flt_compat (e : ℤ) (bm : Bool) : Prop := (e = 1 ∧ bm = false) ∨ (e = -1 ∧ bm = true)

theorem flt_twistX_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (v : ι × Fin n) :
    twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F ((-flt_cost LL S bm) (Finsupp.single v 1)) := by
  classical
  have hX : ∀ w : ι × Fin n,
      (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 := by
    intro w
    rw [laurentCoeffFiltration, flt_lift_mem]
    intro m
    rw [AddMonoidHom.zero_apply, sub_zero, MvPolynomial.coeff_X]
    split_ifs
    · exact (flt_L (GLCoord R n) e).one_mem
    · exact zero_mem _
  have hterm : ∀ (a : GLLaurent R n) (w : ι × Fin n) (t : ℤ), a ∈ (flt_L (GLCoord R n) e).F t →
      MvPolynomial.C a * X w ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t := by
    intro a w t ha
    have hm := (laurentCoeffFiltration R n (ι × Fin n) e).mul_mem (flt_C_mem ha) (hX w)
    rwa [add_zero] at hm
  unfold twistSub
  rw [MvPolynomial.eval₂Hom_X', AddMonoidHom.neg_apply, flt_cost_single]
  by_cases hS : v.1 ∈ S
  · rw [if_pos hS]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases hb : LL.vec v.1 <;> simp only [hS, true_and] <;>
      norm_num <;>
      exact sum_mem fun b _ => hterm _ _ _ (flt_twistMat_mem R n j _ _ _ (by norm_num) (by norm_num) _ _)
  · rw [if_neg hS, if_neg (fun h' => hS h'.1), neg_zero]
    exact hX v

theorem flt_twist_monomial_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (al : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al (1 : R)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (-flt_cost LL S bm al) :=
  flt_hom_monomial (laurentCoeffFiltration R n (ι × Fin n) e) (twistSub LL S j) (-flt_cost LL S bm)
    (fun w => flt_twistX_mem LL S j h w) al

theorem flt_gL_mul_gLinv (R : Type*) [CommRing R] (n : ℕ) : gL R n * gLinv R n = 1 := by
  ext i k
  have hu : algebraMap _ (GLCoord R n) (genMat R n).det *
      IsLocalization.Away.invSelf (genMat R n).det = 1 :=
    IsLocalization.Away.mul_invSelf _
  have e : ∑ j, algebraMap _ (GLCoord R n) (genMat R n i j) *
      (IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n).adjugate j k)) =
      IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n * (genMat R n).adjugate) i k) := by
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  rw [Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at e
  simp only [Matrix.mul_apply, gL, gLinv, Matrix.map_apply, ← map_mul, ← map_sum, e,
    Matrix.one_apply]
  split_ifs
  · rw [mul_one, mul_comm, hu, map_one]
  · rw [mul_zero, map_zero, mul_zero, map_zero]

theorem flt_gLinv_mul_gL (R : Type*) [CommRing R] (n : ℕ) : gLinv R n * gL R n = 1 :=
  mul_eq_one_comm.1 (flt_gL_mul_gLinv R n)

theorem flt_twistMat_mul (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    twistMat R n j k * twistMat R n j (-k) = 1 := by
  have hd : Matrix.diagonal (fun a => if a = j then (LaurentPolynomial.T k : GLLaurent R n) else 1) *
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-k) else 1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs
    · rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
    · rw [one_mul]
  unfold twistMat
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gLinv R n) (gL R n), flt_gLinv_mul_gL, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hd, Matrix.one_mul, flt_gL_mul_gLinv]

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

def flt_tay (R : Type*) [CommRing R] (σ : Type*) : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R) :=
  eval₂Hom (C.comp C) (fun v => C (X v) + X v)

def flt_g (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) : MvPolynomial σ R :=
  monomial (m - be) (((be.prod fun k j => (m k).choose j : ℕ)) : R)

open Classical in
theorem flt_g_pascal (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) (a : σ) :
    flt_g R (m + Finsupp.single a 1) be =
      flt_g R m be * X a + (if a ∈ be.support then flt_g R m (be - Finsupp.single a 1) else 0) := by
  unfold flt_g
  rw [X, monomial_mul, mul_one]
  by_cases ha : a ∈ be.support
  · rw [if_pos ha]
    have hba : be a ≠ 0 := Finsupp.mem_support_iff.1 ha
    have hsub : (be - Finsupp.single a 1).support ⊆ be.support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [Finsupp.tsub_apply] at hk
      omega
    rw [Finsupp.prod_of_support_subset _ hsub _ (fun k _ => Nat.choose_zero_right _)]
    simp only [Finsupp.prod]
    rw [← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ ha]
    have hrest1 : ∏ k ∈ be.support.erase a, ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose (be k) =
        ∏ k ∈ be.support.erase a, (m k).choose (be k) :=
      Finset.prod_congr rfl fun k hk => by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hk).symm, add_zero]
    have hrest2 : ∏ k ∈ be.support.erase a, (m k).choose ((be - Finsupp.single a 1 : σ →₀ ℕ) k) =
        ∏ k ∈ be.support.erase a, (m k).choose (be k) :=
      Finset.prod_congr rfl fun k hk => by
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hk).symm, tsub_zero]
    rw [hrest1, hrest2]
    obtain ⟨b, hb⟩ : ∃ b, be a = b + 1 := ⟨be a - 1, by omega⟩
    have hA : (m + Finsupp.single a 1 : σ →₀ ℕ) a = m a + 1 := by simp
    have hB : (be - Finsupp.single a 1 : σ →₀ ℕ) a = b := by rw [Finsupp.tsub_apply, hb]; simp
    rw [hA, hB, hb, Nat.choose_succ_succ]
    rcases Nat.lt_or_ge (m a) b with hlt | hge
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega : m a < b + 1)]
      simp
    · have e3 : m - (be - Finsupp.single a 1) = m + Finsupp.single a 1 - be := by
        ext k
        by_cases hk : k = a
        · subst hk
          simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hb]
          omega
        · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
          omega
      rcases Nat.lt_or_ge (m a) (b + 1) with hlt2 | hge2
      · rw [Nat.choose_eq_zero_of_lt hlt2, e3]
        simp
      · have e2 : m - be + Finsupp.single a 1 = m + Finsupp.single a 1 - be := by
          ext k
          by_cases hk : k = a
          · subst hk
            simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hb]
            omega
          · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
            omega
        rw [e2, e3, ← map_add]
        congr 1
        push_cast
        ring
  · rw [if_neg ha, add_zero]
    have hba : be a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    have e2 : m - be + Finsupp.single a 1 = m + Finsupp.single a 1 - be := by
      ext k
      by_cases hk : k = a
      · subst hk
        simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hba]
        omega
      · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
        omega
    have hc : (be.prod fun k j => ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose j) = be.prod fun k j => (m k).choose j := by
      simp only [Finsupp.prod]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hka : a ≠ k := fun h => ha (h ▸ hk)
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hka, add_zero]
    rw [e2, hc]

theorem flt_tay_monomial (R : Type*) [CommRing R] {σ : Type*} (m : σ →₀ ℕ) :
    ∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be := by
  classical
  have htx : ∀ a, flt_tay R σ (X a) = C (X a) + X a := fun a => by simp [flt_tay]
  have step : ∀ m : σ →₀ ℕ, (∀ be, coeff be (flt_tay R σ (monomial m 1)) = flt_g R m be) →
      ∀ a be, coeff be (flt_tay R σ (monomial (m + Finsupp.single a 1) 1)) =
        flt_g R (m + Finsupp.single a 1) be := by
    intro m hm a be
    rw [flt_g_pascal, monomial_add_single, pow_one, map_mul, htx, mul_add, coeff_add,
      mul_comm _ (C (X a)), coeff_C_mul, coeff_mul_X', hm, mul_comm (X a)]
    by_cases ha : a ∈ be.support
    · simp [ha, hm]
    · simp [ha]
  induction m using Finsupp.induction with
  | zero =>
    intro be
    by_cases hbe : be = 0
    · subst hbe
      simp [flt_g]
    · obtain ⟨k, hk⟩ : ∃ k, be k ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hbe (Finsupp.ext hc)
      have hz : (be.prod fun k j => ((Nat.choose 0 j : ℕ) : R)) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hk)
          (by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
      simp [flt_g, hz, coeff_one, Ne.symm hbe]
  | single_add a b f _ hb ih =>
    clear hb
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      have e : Finsupp.single a (b + 1) + f = (Finsupp.single a b + f) + Finsupp.single a 1 := by
        rw [Finsupp.single_add, add_right_comm]
      rw [e]
      exact step _ ihb a

theorem flt_tay_coeff (R : Type*) [CommRing R] {σ : Type*} (F : MvPolynomial σ R) (be : σ →₀ ℕ) :
    coeff be (flt_tay R σ F) = divDer be F := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum, divDer]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show monomial m (coeff m F) = C (coeff m F) * monomial m 1 by rw [C_mul_monomial, mul_one], map_mul]
  have hC : flt_tay R σ (C (coeff m F)) = C (C (coeff m F)) := by simp [flt_tay]
  rw [hC, coeff_C_mul, flt_tay_monomial, flt_g, C_mul_monomial]
  split_ifs with hle
  · rfl
  · have hz : (be.prod fun k j => (m k).choose j) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, m k < be k := by
        by_contra hcon
        push_neg at hcon
        exact hle fun k => hcon k
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk)
    rw [hz, Nat.cast_zero, mul_zero, monomial_zero]

open Classical in

def flt_Th {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    MvPolynomial (ι × Fin n) (GLLaurent R n) →+*
      MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n)) :=
  eval₂Hom (C.comp C) fun w => C (X w) +
    (if w.1 ∈ S then
      (if LL.vec w.1 then ∑ c : Fin n, C (C (twistMat R n j (-1) c w.2)) * X (w.1, c)
       else ∑ c : Fin n, C (C (twistMat R n j 1 w.2 c)) * X (w.1, c))
     else X w)

theorem sum_C_C_mul_sum_of_mul_eq_one {B : Type*} [CommRing B] {σ' σ'' : Type*} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) B)
    (h : Q * P = 1) (Y : Fin n → MvPolynomial σ' (MvPolynomial σ'' B)) (d : Fin n) :
    ∑ b, C (C (P b d)) * ∑ c, C (C (Q c b)) * Y c = Y d := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  have hcd : ∀ c, ∑ b, P b d * Q c b = (1 : Matrix (Fin n) (Fin n) B) c d := fun c => by
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp_rw [hcd, Matrix.one_apply]
  simp

theorem flt_Th_twist {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    (MvPolynomial.map (twistSub (R := R) LL S j)).comp (flt_tay R (ι × Fin n)) =
      (flt_Th LL S j).comp (twistSub (R := R) LL S j) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [flt_tay, flt_Th, twistSub]
  · intro v
    have hY1 := sum_C_C_mul_sum_of_mul_eq_one (σ' := ι × Fin n) (σ'' := ι × Fin n) (twistMat R n j 1) (twistMat R n j (-1))
      (by simpa using flt_twistMat_mul R n j (-1)) (fun c => X (v.1, c)) v.2
    have hM : twistMat R n j (-1) * twistMat R n j 1 = 1 := by simpa using flt_twistMat_mul R n j (-1)
    have hY2 := sum_C_C_mul_sum_of_mul_eq_one (σ' := ι × Fin n) (σ'' := ι × Fin n) (Matrix.transpose (twistMat R n j (-1)))
      (Matrix.transpose (twistMat R n j 1))
      (by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]) (fun c => X (v.1, c)) v.2
    simp only [Matrix.transpose_apply] at hY2
    by_cases hS : v.1 ∈ S
    · by_cases hv : LL.vec v.1 = true
      · simp [flt_tay, flt_Th, twistSub, hS, hv, mul_add, Finset.sum_add_distrib, hY1]
      · simp [flt_tay, flt_Th, twistSub, hS, hv, mul_add, Finset.sum_add_distrib, hY2]
    · simp [flt_tay, flt_Th, twistSub, hS]

theorem flt_Th_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {P : MvPolynomial (ι × Fin n) (GLLaurent R n)}
    (hP : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) :
    flt_Th LL S j P ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by
  have hone : ∀ s : ℤ, s = 0 → (1 : GLLaurent R n) ∈ (flt_L (GLCoord R n) e).F s := by
    rintro s rfl
    exact (flt_L (GLCoord R n) e).one_mem
  have hX : ∀ w, flt_Th LL S j (X w) ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F
      ((0 : (ι × Fin n →₀ ℕ) →+ ℤ) (Finsupp.single w 1)) := by
    intro w
    rw [AddMonoidHom.zero_apply]
    have hXw : (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 :=
      flt_monomial_mem (hone _ (by simp))
    simp only [flt_Th, eval₂Hom_X']
    refine AddSubgroup.add_mem _ (flt_C_mem hXw) ?_
    split_ifs with hS hv
    · refine AddSubgroup.sum_mem _ fun c _ => ?_
      rw [show (C (C (twistMat R n j (-1) c w.2)) * X (w.1, c) :
          MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n))) =
          monomial (Finsupp.single (w.1, c) 1) (C (twistMat R n j (-1) c w.2)) by
        rw [X, C_mul_monomial, mul_one]]
      refine flt_monomial_mem (flt_C_mem (flt_twistMat_mem R n j _ _ _ ?_ ?_ _ _)) <;>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [flt_cost, hS, hv]
    · refine AddSubgroup.sum_mem _ fun c _ => ?_
      rw [show (C (C (twistMat R n j 1 w.2 c)) * X (w.1, c) :
          MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n))) =
          monomial (Finsupp.single (w.1, c) 1) (C (twistMat R n j 1 w.2 c)) by
        rw [X, C_mul_monomial, mul_one]]
      refine flt_monomial_mem (flt_C_mem (flt_twistMat_mem R n j _ _ _ ?_ ?_ _ _)) <;>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [flt_cost, hS, hv]
    · have h1 : (1 : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F
          (0 - flt_cost LL S (!bm) (Finsupp.single w 1)) := by
        have h0 : flt_cost LL S (!bm) (Finsupp.single w 1) = 0 := by simp [flt_cost, hS]
        rw [h0, sub_zero]
        exact (laurentCoeffFiltration R n (ι × Fin n) e).one_mem
      exact flt_monomial_mem h1
  rw [P.as_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun m _ => ?_
  rw [show monomial m (coeff m P) = C (coeff m P) * monomial m 1 by rw [C_mul_monomial, mul_one], map_mul]
  have hc : coeff m P ∈ (flt_L (GLCoord R n) e).F t := by
    have h3 := (flt_lift_mem.1 hP) m
    simpa using h3
  have h1 : flt_Th LL S j (C (coeff m P)) ∈
      (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by
    simp only [flt_Th, eval₂Hom_C, RingHom.comp_apply]
    exact flt_C_mem (flt_C_mem hc)
  have h2 := flt_hom_monomial _ (flt_Th LL S j) 0 hX m
  rw [AddMonoidHom.zero_apply] at h2
  have h4 := (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).mul_mem h1 h2
  rwa [add_zero] at h4

theorem flt_divDer_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (t - flt_cost LL S (!bm) be) := by
  have h1 := flt_lift_mem.1 (flt_Th_mem LL S j h hF) be
  have e1 : twistSub LL S j (divDer be F) = coeff be (flt_Th LL S j (twistSub LL S j F)) := by
    have h2 := congrArg (fun φ => coeff be (φ F)) (flt_Th_twist (R := R) LL S j)
    simp only [RingHom.comp_apply, coeff_map] at h2
    rw [← h2, flt_tay_coeff]
  rw [e1]
  exact h1

theorem flt_op_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (al be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al 1 * divDer be F) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F (t - (flt_cost LL S bm al + flt_cost LL S (!bm) be)) := by
  rw [map_mul]
  have h1 := flt_twist_monomial_mem (R := R) LL S j h al
  have h2 := flt_divDer_mem LL S j h hF be
  have h3 := (laurentCoeffFiltration R n (ι × Fin n) e).mul_mem h1 h2
  rwa [show -flt_cost LL S bm al + (t - flt_cost LL S (!bm) be) =
    t - (flt_cost LL S bm al + flt_cost LL S (!bm) be) by ring] at h3

private theorem flt_cost_false_eq_covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S false al = (covDeg LL S al : ℤ) := by
  simp only [flt_cost, Finsupp.liftAddHom_apply, covDeg, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

private theorem flt_cost_true_eq_vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S true al = (vecDeg LL S al : ℤ) := by
  simp only [flt_cost, Finsupp.liftAddHom_apply, vecDeg, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem flt_op_mem_val {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {t : ℤ} (ht : (t : WithTop ℤ) ≤ valS LL S F) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    twistSub LL S (lastIdx n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F (t - N) := by
  have hF := (flt_le_valS LL S F t).1 ht
  have hm := flt_op_mem LL S (lastIdx n) (Or.inl ⟨rfl, rfl⟩ : flt_compat 1 false) hF al be
  refine (laurentCoeffFiltration R n (ι × Fin n) 1).anti ?_ hm
  simp only [Bool.not_false, flt_cost_false_eq_covDeg, flt_cost_true_eq_vecDeg]
  have hN' : ((covDeg LL S al + vecDeg LL S be : ℕ) : ℤ) ≤ N := by exact_mod_cast hN
  push_cast at hN'
  linarith

theorem flt_op_mem_lam {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {M : ℤ} (hM : lam1S LL S F ≤ (M : WithBot ℤ)) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    twistSub LL S (0 : Fin n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) (-1)).F (-(M + N)) := by
  have hF := (flt_lam1S_le LL S F M).1 hM
  have hm := flt_op_mem LL S (0 : Fin n) (Or.inr ⟨rfl, rfl⟩ : flt_compat (-1) true) hF al be
  refine (laurentCoeffFiltration R n (ι × Fin n) (-1)).anti ?_ hm
  simp only [Bool.not_true, flt_cost_false_eq_covDeg, flt_cost_true_eq_vecDeg]
  have hN' : ((vecDeg LL S al + covDeg LL S be : ℕ) : ℤ) ≤ N := by exact_mod_cast hN
  push_cast at hN'
  linarith

theorem flt_op_valS {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + ((N : ℤ) : WithTop ℤ) := by
  by_contra hcon
  push_neg at hcon
  cases hv : valS LL S (monomial al 1 * divDer be F) with
  | top =>
    rw [hv] at hcon
    simp at hcon
  | coe w =>
    rw [hv] at hcon
    have ht : ((w + N + 1 : ℤ) : WithTop ℤ) ≤ valS LL S F := by
      cases hF : valS LL S F with
      | top => exact le_top
      | coe x =>
        rw [hF] at hcon
        norm_cast at hcon ⊢ <;> omega
    have hm := flt_op_mem_val LL S ht al be N hN
    rw [← flt_le_valS, hv] at hm
    norm_cast at hm <;> omega

theorem flt_op_lam1S {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    lam1S LL S (monomial al 1 * divDer be F) ≤ lam1S LL S F + ((N : ℤ) : WithBot ℤ) := by
  by_contra hcon
  push_neg at hcon
  cases hv : lam1S LL S (monomial al 1 * divDer be F) with
  | bot =>
    rw [hv] at hcon
    simp at hcon
  | coe w =>
    rw [hv] at hcon
    have hM : lam1S LL S F ≤ ((w - N - 1 : ℤ) : WithBot ℤ) := by
      cases hF : lam1S LL S F with
      | bot => exact bot_le
      | coe x =>
        rw [hF] at hcon
        norm_cast at hcon ⊢ <;> omega
    have hm := flt_op_mem_lam LL S hM al be N hN
    rw [← flt_lam1S_le, hv] at hm
    norm_cast at hm <;> omega

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

theorem coeff_divDer (be μ : ι × Fin n →₀ ℕ) (F : MvPolynomial (ι × Fin n) R) :
    coeff μ (divDer be F) = coeff (μ + be) F * ((be.prod fun k j => ((μ + be) k).choose j : ℕ) : R) := by
  classical
  rw [divDer, coeff_sum]
  rw [Finset.sum_congr rfl (g := fun m => if m = μ + be then
      coeff m F * ((be.prod fun k j => (m k).choose j : ℕ) : R) else 0)]
  · rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, zero_mul]
  · intro m _
    by_cases h1 : be ≤ m
    · rw [if_pos h1, coeff_monomial]
      by_cases h2 : m = μ + be
      · subst h2
        rw [if_pos (add_tsub_cancel_right μ be), if_pos rfl]
      · rw [if_neg h2, if_neg]
        intro h3
        apply h2
        rw [← h3, tsub_add_cancel_of_le h1]
    · rw [if_neg h1, coeff_zero, if_neg]
      rintro rfl
      exact h1 le_add_self

theorem divDer_zero' (F : MvPolynomial (ι × Fin n) R) : divDer 0 F = F := by
  ext μ
  rw [coeff_divDer]
  simp

theorem divDer_single_one (v : ι × Fin n) (F : MvPolynomial (ι × Fin n) R) :
    divDer (Finsupp.single v 1) F = pderiv v F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    ext μ
    rw [coeff_divDer, pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = μ + Finsupp.single v 1
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_right μ _)]
      simp [Finsupp.prod_single_index, Nat.choose_one_right]
    · rw [if_neg h, zero_mul]
      split_ifs with h2
      · have hv : u v = 0 := by
          by_contra hv
          have hle : Finsupp.single v 1 ≤ u :=
            Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          apply h
          rw [← h2, tsub_add_cancel_of_le hle]
        rw [hv, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq]
    ext μ
    rw [coeff_add, coeff_divDer, coeff_divDer, coeff_divDer, coeff_add, add_mul]

theorem vecDeg_zero' (S : Set ι) : vecDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [vecDeg]

theorem covDeg_zero' (S : Set ι) : covDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [covDeg]

theorem vecDeg_single_le (S : Set ι) (v : ι × Fin n) : vecDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

theorem covDeg_single_le (S : Set ι) (v : ι × Fin n) : covDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

theorem vecDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    vecDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

theorem covDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    covDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

theorem X_eq_monomial' (v : ι × Fin n) : (X v : MvPolynomial (ι × Fin n) R) = monomial (Finsupp.single v 1) 1 := rfl

theorem twistSub_X_out (j : Fin n) (v : ι × Fin n) (h : v.1 ∉ S) :
    twistSub (R := R) LL S j (X v) = X v := by
  simp [twistSub, h]

theorem mem_of_X_mul_mem {e t : ℤ} (v : ι × Fin n) (P : MvPolynomial (ι × Fin n) (GLLaurent R n))
    (h : X v * P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t := by
  rw [laurentCoeffFiltration, flt_lift_mem] at h ⊢
  intro m
  have hm := h (Finsupp.single v 1 + m)
  rw [coeff_X_mul] at hm
  simpa using hm

theorem valS_X_mul_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    valS LL S F ≤ valS LL S (X v * F) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 0
    (by rw [covDeg_single_of LL S v h, vecDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithTop.coe_zero, add_zero] at hv
  exact hv

theorem valS_X_mul (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (X v * F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 1
    (by rw [vecDeg_zero', add_zero]; exact covDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

theorem valS_pderiv_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    valS LL S F ≤ valS LL S (pderiv v F) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 0
    (by rw [covDeg_zero', vecDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithTop.coe_zero, add_zero] at hv
  exact hv

theorem valS_pderiv (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (pderiv v F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 1
    (by rw [covDeg_zero', zero_add]; exact vecDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv



theorem maxTwistDegree_X_mul_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    lam1S LL S (X v * F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 0
    (by rw [vecDeg_single_of LL S v h, covDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithBot.coe_zero, add_zero] at hv
  exact hv

theorem maxTwistDegree_X_mul_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (X v * F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 1
    (by rw [covDeg_zero', add_zero]; exact vecDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

theorem maxTwistDegree_pderiv_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 0
    (by rw [vecDeg_zero', covDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithBot.coe_zero, add_zero] at hv
  exact hv

theorem maxTwistDegree_pderiv_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 1
    (by rw [vecDeg_zero', zero_add]; exact covDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv



end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
end
end
