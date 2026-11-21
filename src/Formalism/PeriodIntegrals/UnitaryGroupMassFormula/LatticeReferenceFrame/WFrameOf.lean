import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.ThetaA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WBasis

section
noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open Matrix

namespace PI.ScRefExists.WF

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_def (x y : Fin I.n → I.E) : hG I x y = ∑ i, ∑ j, star (x i) * I.J i j * y j := rfl

theorem hG_add_left (x y z : Fin I.n → I.E) : hG I (x + y) z = hG I x z + hG I y z := by
  simp only [hG_def, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem hG_add_right (x y z : Fin I.n → I.E) : hG I x (y + z) = hG I x y + hG I x z := by
  simp only [hG_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hG_smul_left (c : I.E) (x y : Fin I.n → I.E) : hG I (c • x) y = star c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_zero_left (y : Fin I.n → I.E) : hG I 0 y = 0 := by
  simp [hG_def]

theorem hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by
  simp [hG_def]

theorem hG_neg_left (x y : Fin I.n → I.E) : hG I (-x) y = - hG I x y := by
  simp only [hG_def, Pi.neg_apply, star_neg, neg_mul, Finset.sum_neg_distrib]

theorem hG_neg_right (x y : Fin I.n → I.E) : hG I x (-y) = - hG I x y := by
  simp only [hG_def, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hG_sub_left (x y z : Fin I.n → I.E) : hG I (x - y) z = hG I x z - hG I y z := by
  rw [sub_eq_add_neg, hG_add_left, hG_neg_left, ← sub_eq_add_neg]

theorem hG_sub_right (x y z : Fin I.n → I.E) : hG I x (y - z) = hG I x y - hG I x z := by
  rw [sub_eq_add_neg, hG_add_right, hG_neg_right, ← sub_eq_add_neg]

theorem hG_sum_right {ι : Type*} (s : Finset ι) (x : Fin I.n → I.E) (y : ι → Fin I.n → I.E) :
    hG I x (∑ t ∈ s, y t) = ∑ t ∈ s, hG I x (y t) := by
  exact map_sum (AddMonoidHom.mk' (hG I x) (hG_add_right I x)) y s


theorem J_entry (i j : Fin I.n) : star (I.J j i) = I.J i j := by
  have h : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
  have h2 := congrFun (congrFun h i) j
  simpa [Formalism.UG.cT, starRingEnd_apply] using h2

theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  simp only [hG_def, star_sum, star_mul', star_star]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [J_entry I a b]
  ring

theorem hG_single (i : Fin I.n) (v : Fin I.n → I.E) :
    hG I (Pi.single i 1) v = (I.J *ᵥ v) i := by
  rw [hG_def, Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem hG_nondeg (v : Fin I.n → I.E) (h : ∀ x, hG I x v = 0) : v = 0 := by
  have h1 : I.J *ᵥ v = 0 := funext fun i => by
    rw [← hG_single I i v]
    exact h _
  exact Matrix.eq_zero_of_mulVec_eq_zero I.J_det h1

variable {I}

theorem mem_Ap {p : ℕ} {x : I.E} :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) := Iff.rfl

theorem inv_mem_Ap {p s : ℕ} (hp : p.Prime) (hs : Nat.Coprime s p) : ((s : I.E))⁻¹ ∈ Ap I p := by
  have hs0 : (s : I.E) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr ?_
    rintro rfl
    rw [Nat.coprime_zero_left] at hs
    exact hp.one_lt.ne' hs
  exact mem_Ap.mpr ⟨s, hs, 1, by rw [mul_inv_cancel₀ hs0]; simp⟩

theorem star_mem_Ap {p : ℕ} {x : I.E} (hx : x ∈ Ap I p) : star x ∈ Ap I p := by
  obtain ⟨s, hs, a, ha⟩ := mem_Ap.mp hx
  have hint : IsIntegral ℤ (star (a : I.E)) := by
    have := map_isIntegral_int (starRingEnd I.E) (RingOfIntegers.isIntegral_coe a)
    simpa [starRingEnd_apply] using this
  refine mem_Ap.mpr ⟨s, hs, ⟨star (a : I.E), hint⟩, ?_⟩
  show (s : I.E) * star x = star (a : I.E)
  rw [← ha, star_mul', star_natCast]

end PI.ScRefExists.WF
end
end

section
noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WF

variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

theorem ap_smul (a : Ap I p) (v : Fin I.n → I.E) : a • v = (a : I.E) • v := rfl

theorem osmul (o : 𝓞 I.E) (v : Fin I.n → I.E) : o • v = (o : I.E) • v :=
  (algebraMap_smul I.E o v).symm

theorem hG_L {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    hG I x y ∈ (algebraMap (𝓞 I.E) I.E).range := by
  unfold hG
  exact (I.L_dual y).mp hy x hx

theorem natsmul_mem_L {s : ℕ} {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  have h1 : ((s : 𝓞 I.E) : I.E) = (s : I.E) := by simp
  rw [← h1, ← osmul]
  exact I.L.smul_mem _ hx

theorem mem_LA_iff (hp : p.Prime) {x : Fin I.n → I.E} :
    x ∈ LA I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • x ∈ I.L := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
    | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
      have : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
        push_cast; module
      rw [this]
      exact I.L.add_mem (natsmul_mem_L hsx) (natsmul_mem_L hty)
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨s0, hs0, a0, ha0⟩ := a.2
      refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, ?_⟩
      have : ((s0 * s : ℕ) : I.E) • (a • x) = a0 • ((s : I.E) • x) := by
        rw [ap_smul, osmul, ← ha0]; push_cast; module
      rw [this]
      exact I.L.smul_mem _ hsx
  · rintro ⟨s, hs, hsx⟩
    have hsA : ((s : I.E))⁻¹ ∈ Ap I p := inv_mem_Ap hp hs
    have hs0 : (s : I.E) ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs)
      exact_mod_cast this
    have : x = (⟨_, hsA⟩ : Ap I p) • ((s : I.E) • x) := by
      rw [ap_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

theorem L_le_LA {x : Fin I.n → I.E} (hx : x ∈ I.L) : x ∈ LA I p := Submodule.subset_span hx

theorem hG_LA (hp : p.Prime) {x y : Fin I.n → I.E} (hx : x ∈ LA I p) (hy : y ∈ LA I p) :
    hG I x y ∈ Ap I p := by
  obtain ⟨s, hs, hsx⟩ := (mem_LA_iff hp).1 hx
  obtain ⟨t, ht, hty⟩ := (mem_LA_iff hp).1 hy
  obtain ⟨o, ho⟩ := hG_L hsx hty
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, o, ?_⟩
  rw [hG_smul_left, hG_smul_right, star_natCast] at ho
  rw [show ((o : 𝓞 I.E) : I.E) = algebraMap (𝓞 I.E) I.E o from rfl, ho]; push_cast; ring

theorem dual_LA (hp : p.Prime) {x : Fin I.n → I.E} (hx : ∀ y ∈ I.L, hG I y x ∈ Ap I p) : x ∈ LA I p := by
  classical
  obtain ⟨T, hT⟩ := I.L_fg
  have hden : ∀ t ∈ T, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * hG I t x = (a : I.E) := by
    intro t ht
    exact hx t (hT ▸ Submodule.subset_span ht)
  choose! s hs a ha using hden
  let S : ℕ := ∏ t ∈ T, s t
  have hS : Nat.Coprime S p := Nat.Coprime.prod_left fun t ht => hs t ht
  have key : ∀ y ∈ I.L, hG I y ((S : I.E) • x) ∈ (algebraMap (𝓞 I.E) I.E).range := by
    intro y hy
    rw [← hT] at hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      have hdvd : s t ∣ S := Finset.dvd_prod_of_mem s ht
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : 𝓞 I.E) * a t, ?_⟩
      rw [hG_smul_right, hc]; push_cast
      rw [mul_comm ((s t : ℕ) : I.E), mul_assoc, ha t ht]
    | zero => exact ⟨0, by simp [hG_zero_left]⟩
    | add y z _ _ hy hz =>
      obtain ⟨o1, h1⟩ := hy; obtain ⟨o2, h2⟩ := hz
      exact ⟨o1 + o2, by rw [hG_add_left, ← h1, ← h2]; simp⟩
    | smul o y _ hy =>
      obtain ⟨o1, h1⟩ := hy
      refine ⟨PI.ScRefExists.TH.sg I o * o1, ?_⟩
      rw [osmul, hG_smul_left, ← h1]; simp [PI.ScRefExists.TH.sg_coe]
  have hSx : (S : I.E) • x ∈ I.L := (I.L_dual _).2 key
  exact (mem_LA_iff hp).2 ⟨S, hS, hSx⟩

theorem mem_LA_of_nsmul (hp : p.Prime) {M : ℕ} (hM : Nat.Coprime M p) {x : Fin I.n → I.E}
    (hx : M • x ∈ I.L) : x ∈ LA I p := by
  refine (mem_LA_iff hp).2 ⟨M, hM, ?_⟩
  rwa [← Nat.cast_smul_eq_nsmul I.E] at hx

def proj {r : ℕ} (e f : Fin r → Fin I.n → I.E) (y : Fin I.n → I.E) : Fin I.n → I.E :=
  ∑ a, (hG I (f a) y • e a + hG I (e a) y • f a)

theorem hG_e_proj {r : ℕ} {e f : Fin r → Fin I.n → I.E} (he : ∀ a b, hG I (e a) (e b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (e b) (proj e f y) = hG I (e b) y := by
  have hr : ∀ (x : Fin I.n → I.E) (c : Fin r → I.E) (w : Fin r → Fin I.n → I.E),
      hG I x (∑ a, c a • w a) = ∑ a, c a * hG I x (w a) := by
    intro x c w
    unfold hG Formalism.UG.hform
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hadd2 : ∀ x u w : Fin I.n → I.E, hG I x (u + w) = hG I x u + hG I x w := by
    intro x u w
    unfold hG Formalism.UG.hform
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  unfold proj
  rw [Finset.sum_add_distrib, hadd2, hr, hr]
  simp only [he, hef]
  simp

theorem hG_f_proj {r : ℕ} {e f : Fin r → Fin I.n → I.E} (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (f b) (proj e f y) = hG I (f b) y := by
  have hr : ∀ (x : Fin I.n → I.E) (c : Fin r → I.E) (w : Fin r → Fin I.n → I.E),
      hG I x (∑ a, c a • w a) = ∑ a, c a * hG I x (w a) := by
    intro x c w
    unfold hG Formalism.UG.hform
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hadd2 : ∀ x u w : Fin I.n → I.E, hG I x (u + w) = hG I x u + hG I x w := by
    intro x u w
    unfold hG Formalism.UG.hform
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i := by
    intro i j
    have := congrFun (congrFun I.J_herm j) i
    simpa [Formalism.UG.cT] using this
  have hsym : ∀ x y, hG I y x = starRingEnd I.E (hG I x y) := by
    intro x y
    unfold hG Formalism.UG.hform
    simp only [map_sum, map_mul, starRingEnd_self_apply, hJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 : ∀ a, hG I (f b) (e a) = if a = b then 1 else 0 := by
    intro a
    rw [hsym (e a) (f b), hef]
    split_ifs <;> simp
  unfold proj
  rw [Finset.sum_add_distrib, hadd2, hr, hr]
  simp only [hf, h1]
  simp

theorem proj_mem (hp : p.Prime) {r : ℕ} {e f : Fin r → Fin I.n → I.E}
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p) :
    proj e f y ∈ LA I p := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p) (heA a)
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p) (hfA a)
    rwa [ap_smul] at h1

theorem proj_span {r : ℕ} (e f : Fin r → Fin I.n → I.E) (hp : p.Prime)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p)
    (S : Set (Fin I.n → I.E)) (hS : Set.range e ∪ Set.range f ⊆ S) :
    proj e f y ∈ Submodule.span (Ap I p) S := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inl ⟨a, rfl⟩)))
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inr ⟨a, rfl⟩)))
    rwa [ap_smul] at h1

end PI.ScRefExists.WF
end
end

section
noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WF

variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

section Frame

variable {r k : ℕ} {e f : Fin r → Fin I.n → I.E} {w : Fin (k + 1) → Fin I.n → I.E}

def fam (e f : Fin r → Fin I.n → I.E) (w : Fin (k + 1) → Fin I.n → I.E) :
    Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → Fin I.n → I.E :=
  Sum.elim e (Sum.elim f w)

theorem fam_li (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (hw : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0) (hli : LinearIndependent I.E w) :
    LinearIndependent I.E (fam e f w) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [fam, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hg
  have hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hG_symm I (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hb : ∀ a, g (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have hw1 : ∀ i, hG I (e a) (w i) = 0 := fun i => (hw i a).1
    have h1 := congrArg (hG I (e a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, he, hef, hw1, hG_zero_right] using h1
  have ha : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    have hw2 : ∀ i, hG I (f a) (w i) = 0 := fun i => (hw i a).2
    have h1 := congrArg (hG I (f a)) hg
    simpa [hG_add_right, hG_sum_right, hG_smul_right, hf, hfe, hw2, hG_zero_right] using h1
  simp only [ha, hb, zero_smul, Finset.sum_const_zero, zero_add] at hg
  have hc := Fintype.linearIndependent_iff.1 hli (fun i => g (Sum.inr (Sum.inr i))) hg
  intro i
  rcases i with a | a | i
  · exact ha a
  · exact hb a
  · exact hc i

theorem fam_sp (hp : p.Prime) (he : ∀ a b, hG I (e a) (e b) = 0) (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p)
    (hW : ∀ x ∈ LA I p, (∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0) →
        x ∈ Submodule.span (Ap I p) (Set.range w)) :
    ⊤ ≤ Submodule.span I.E (Set.range (fam e f w)) := by
  rw [← I.L_span, Submodule.span_le]
  intro y hy
  have hyA : y ∈ LA I p := L_le_LA hy
  have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
    apply hW _ (sub_mem hyA (proj_mem hp heA hfA hyA))
    intro a
    rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
    exact ⟨rfl, rfl⟩
  have key : ∀ z ∈ Submodule.span (Ap I p) (Set.range w),
      z ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ (c : I.E) hx
  have hp' : proj e f y ∈ Submodule.span I.E (Set.range (fam e f w)) := by
    unfold proj
    refine Submodule.sum_mem _ fun a _ => add_mem ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl a), rfl⟩)
  have := add_mem hp' (key _ hz)
  simpa using this

end Frame

theorem wFrame_of (hPID : ApPID) (hWB : WBasis) : WFrame := by
  intro I p r k e f M hp hn he hf hef hM heM
  obtain ⟨w, hw1, hwli, hwsp⟩ := hWB I p r k e f M hp (hPID I p hp) hn he hf hef hM heM
  have heA : ∀ a, e a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).1
  have hfA : ∀ a, f a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).2
  have hwA : ∀ i, w i ∈ LA I p := fun i => (hw1 i).1
  have hwo : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 := fun i a => (hw1 i).2 a
  have hli := fam_li he hf hef hwo hwli
  have hsp := fam_sp hp he hf hef heA hfA hwsp
  have hT0 : ∀ u, (∀ j, hG I (fam e f w j) u = 0) → u = 0 := by
    intro u hu
    apply hG_nondeg
    intro x
    have hx : x ∈ Submodule.span I.E (Set.range (fam e f w)) := hsp Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hu j
    | zero => exact hG_zero_left I u
    | add x y _ _ hx hy => rw [hG_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [hG_smul_left, hx, mul_zero]
  let T : (Fin I.n → I.E) →ₗ[I.E] (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) :=
    { toFun := fun d j => hG I (fam e f w j) d
      map_add' := fun x y => by
        ext j
        simp [hG_add_right]
      map_smul' := fun c x => by
        ext j
        simp [hG_smul_right] }
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact hT0 u (fun j => congrFun hu j)
  have hdim : Module.finrank I.E (Fin I.n → I.E) =
      Module.finrank I.E (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hn]
    ring
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hTi
  have hex : ∀ i : Fin (k + 1), ∃ d : Fin I.n → I.E, ∀ j,
      hG I (fam e f w j) d = if j = Sum.inr (Sum.inr i) then 1 else 0 := by
    intro i
    obtain ⟨d, hd⟩ := hTs (fun j => if j = Sum.inr (Sum.inr i) then 1 else 0)
    exact ⟨d, fun j => congrFun hd j⟩
  choose wd hwd using hex
  have hewd : ∀ a i, hG I (e a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inl a)
  have hfwd : ∀ a i, hG I (f a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inl a))
  have hwwd : ∀ j i, hG I (w j) (wd i) = if j = i then 1 else 0 := fun j i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inr j))
  have hdual : ∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [hG_symm I (w j) (wd i), hwwd j i]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hyS : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
      apply hwsp _ (sub_mem hyA (proj_mem hp heA hfA hyA))
      intro a
      rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
      exact ⟨rfl, rfl⟩
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range w)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) :=
      Submodule.span_mono Set.subset_union_right hz
    have := add_mem h1 h2
    simpa using this
  have hwdAp : ∀ i, ∀ y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w),
      hG I (wd i) y ∈ Ap I p := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨j, rfl⟩
      · rw [hG_symm I (e a) (wd i), hewd a i, star_zero]
        exact zero_mem _
      · rw [hG_symm I (f a) (wd i), hfwd a i, star_zero]
        exact zero_mem _
      · rw [hdual i j]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    | zero => rw [hG_zero_right]; exact zero_mem _
    | add x y _ _ hx hy => rw [hG_add_right]; exact add_mem hx hy
    | smul c x _ hx =>
      show hG I (wd i) ((c : I.E) • x) ∈ Ap I p
      rw [hG_smul_right]
      exact mul_mem c.2 hx
  have hwdA : ∀ i, wd i ∈ LA I p := fun i => dual_LA hp fun y hy => by
    rw [hG_symm I (wd i) y]
    exact star_mem_Ap (hwdAp i y (hyS y hy))
  have hyS' : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hzA : y - proj e f y ∈ LA I p := sub_mem hyA (proj_mem hp heA hfA hyA)
    have hze : ∀ a, hG I (e a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_e_proj he hef, sub_self]
    have hzf : ∀ a, hG I (f a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_f_proj hf hef, sub_self]
    have hzeq : y - proj e f y = ∑ i, hG I (w i) (y - proj e f y) • wd i := by
      rw [← sub_eq_zero]
      apply hT0
      intro j
      rw [hG_sub_right, hG_sum_right]
      simp only [hG_smul_right]
      rcases j with a | a | j
      · simp [fam, hze a, hewd]
      · simp [fam, hzf a, hfwd]
      · simp [fam, hwwd]
    have hz' : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range wd) := by
      rw [hzeq]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem _ (⟨_, hG_LA hp (hwA i) hzA⟩ : Ap I p)
        (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range wd)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) :=
      Submodule.span_mono Set.subset_union_right hz'
    have := add_mem h1 h2
    simpa using this
  exact ⟨w, wd, fun i => ⟨hwA i, hwdA i⟩,
    fun a i => ⟨(hwo i a).1, (hwo i a).2, hewd a i, hfwd a i⟩, hdual,
    fun y hy => ⟨hyS y hy, hyS' y hy⟩⟩

end PI.ScRefExists.WF
end
end
