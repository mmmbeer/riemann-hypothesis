import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.ThetaA

section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_add_left (x x' y : Fin I.n → I.E) : hG I (x + x') y = hG I x y + hG I x' y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem hG_add_right (x y y' : Fin I.n → I.E) : hG I x (y + y') = hG I x y + hG I x y' := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hG_smul_left (c : I.E) (x y : Fin I.n → I.E) : hG I (c • x) y = star c * hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_neg_left (x y : Fin I.n → I.E) : hG I (-x) y = -hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.neg_apply, star_neg, neg_mul, Finset.sum_neg_distrib]

theorem hG_neg_right (x y : Fin I.n → I.E) : hG I x (-y) = -hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hG_sub_left (x x' y : Fin I.n → I.E) : hG I (x - x') y = hG I x y - hG I x' y := by
  rw [sub_eq_add_neg, hG_add_left, hG_neg_left, ← sub_eq_add_neg]

theorem hG_sub_right (x y y' : Fin I.n → I.E) : hG I x (y - y') = hG I x y - hG I x y' := by
  rw [sub_eq_add_neg, hG_add_right, hG_neg_right, ← sub_eq_add_neg]

theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  have hJ : ∀ a b, star (I.J b a) = I.J a b := by
    intro a b
    have h : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
    have h2 := congrFun (congrFun h a) b
    simpa [Formalism.UG.cT, starRingEnd_apply] using h2
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, star_sum, star_mul', star_star]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ a b]
  ring

private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl

theorem int_mem_Ap (p : ℕ) (a : 𝓞 I.E) : (a : I.E) ∈ Ap I p := (mem_Ap_lemma I p _).mpr ⟨1, Nat.coprime_one_left p, a, by simp⟩

theorem natCast_smul_mem_L (s : ℕ) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx s

theorem oE_smul (a : 𝓞 I.E) (x : Fin I.n → I.E) : a • x = (a : I.E) • x := by
  ext i; simp [Algebra.smul_def]

theorem natE_smul (t : ℕ) (x : Fin I.n → I.E) : (t : I.E) • x = (t : 𝓞 I.E) • x := by
  rw [oE_smul]
  simp

theorem intE_smul_mem_L (a : 𝓞 I.E) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (a : I.E) • x ∈ I.L := by
  rw [← oE_smul]
  exact I.L.smul_mem a hx

theorem LA_clear (p : ℕ) {v : Fin I.n → I.E} (hv : v ∈ LA I p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by
  have hv' : v ∈ Submodule.span (Ap I p) (I.L : Set (Fin I.n → I.E)) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul hs ht, ?_⟩
    have e : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
      simp only [Nat.cast_mul, smul_add, smul_smul, mul_comm (t : I.E) (s : I.E)]
    rw [e]
    exact add_mem (natCast_smul_mem_L I t hsx) (natCast_smul_mem_L I s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨s0, hs0, a, ha⟩ := (mem_Ap_lemma I p (c : I.E)).mp c.2
    refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, ?_⟩
    have hc : c • x = (c : I.E) • x := rfl
    have e : ((s0 * s : ℕ) : I.E) • (c • x) = (a : I.E) • ((s : I.E) • x) := by
      rw [hc, smul_smul, smul_smul, ← ha]
      push_cast
      congr 1
      ring
    rw [e]
    exact intE_smul_mem_L I a hsx

theorem hG_mem_Ap (p : ℕ) {v v' : Fin I.n → I.E} (hv : v ∈ LA I p) (hv' : v' ∈ LA I p) :
    hG I v v' ∈ Ap I p := by
  obtain ⟨s, hs, hsv⟩ := LA_clear I p hv
  obtain ⟨t, ht, htv⟩ := LA_clear I p hv'
  obtain ⟨a, ha⟩ := RingHom.mem_range.mp ((I.L_dual _).mp htv _ hsv)
  have e : hG I ((s : I.E) • v) ((t : I.E) • v') = (s : I.E) * t * hG I v v' := by
    rw [hG_smul_left, hG_smul_right, star_natCast]
    ring
  refine (mem_Ap_lemma I p _).mpr ⟨s * t, Nat.Coprime.mul hs ht, a, ?_⟩
  rw [Nat.cast_mul, ← e]
  exact ha.symm

theorem span_clear (p : ℕ) (S : Set (Fin I.n → I.E)) {y : Fin I.n → I.E}
    (hy : y ∈ Submodule.span (Ap I p) S) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • y ∈ Submodule.span (𝓞 I.E) S := by
  have key : ∀ (a : 𝓞 I.E) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (a : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun a z hz => by
    rw [← oE_smul]
    exact Submodule.smul_mem _ a hz
  have keyN : ∀ (t : ℕ) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (t : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun t z hz => by
    rw [natE_smul]
    exact Submodule.smul_mem _ _ hz
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using Submodule.subset_span hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul hs ht, ?_⟩
    have e : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
      simp only [Nat.cast_mul, smul_add, smul_smul, mul_comm (t : I.E) (s : I.E)]
    rw [e]
    exact add_mem (keyN t hsx) (keyN s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨s0, hs0, a, ha⟩ := (mem_Ap_lemma I p (c : I.E)).mp c.2
    refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, ?_⟩
    have hc : c • x = (c : I.E) • x := rfl
    have e : ((s0 * s : ℕ) : I.E) • (c • x) = (a : I.E) • ((s : I.E) • x) := by
      rw [hc, smul_smul, smul_smul, ← ha]
      push_cast
      congr 1
      ring
    rw [e]
    exact key a hsx

def QA (p q : ℕ) (x : I.E) : Prop := ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (q : I.E) * a

theorem QA_of_GE (p q : ℕ) {x : I.E} (h : GE I q x) : QA I p q x := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨1, Nat.coprime_one_left p, t, by simp⟩

theorem QA_add (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x + y) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨t, ht, b, hb⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
  push_cast at ha hb ⊢
  linear_combination (t : I.E) * ha + (s : I.E) * hb

theorem QA_neg (p q : ℕ) {x : I.E} (hx : QA I p q x) : QA I p q (-x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  refine ⟨s, hs, -a, ?_⟩
  push_cast
  linear_combination -ha

theorem QA_sub (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x - y) := by
  rw [sub_eq_add_neg]
  exact QA_add I p q hx (QA_neg I p q hy)

theorem QA_mul (p q : ℕ) {c x : I.E} (hc : c ∈ Ap I p) (hx : QA I p q x) : QA I p q (c * x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨s0, hs0, a0, ha0⟩ := (mem_Ap_lemma I p c).mp hc
  refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, a0 * a, ?_⟩
  push_cast
  linear_combination ((s : I.E) * x) * ha0 + (a0 : I.E) * ha

theorem GE_of_QA (p m : ℕ) {x : I.E} (hint : ∃ a : 𝓞 I.E, (a : I.E) = x) (h : QA I p (p ^ m) x) :
    GE I (p ^ m) x := by
  obtain ⟨b, rfl⟩ := hint
  obtain ⟨s, hs, a, ha⟩ := h
  have hcop : Nat.Coprime s (p ^ m) := Nat.Coprime.pow_right m hs
  have hz : (s : ℤ) * Nat.gcdA s (p ^ m) + ((p ^ m : ℕ) : ℤ) * Nat.gcdB s (p ^ m) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop]
    norm_num
  have hzE := congrArg (Int.cast : ℤ → I.E) hz
  push_cast at hzE ha
  refine ⟨(Nat.gcdA s (p ^ m) : 𝓞 I.E) * a + (Nat.gcdB s (p ^ m) : 𝓞 I.E) * b, ?_⟩
  have hA : (((Nat.gcdA s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdA s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  have hB : (((Nat.gcdB s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdB s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  push_cast
  linear_combination ((Nat.gcdA s (p ^ m) : ℤ) : I.E) * ha - (b : I.E) * hzE -
    (p : I.E) ^ m * (a : I.E) * hA - (b : I.E) * (p : I.E) ^ m * hB

end PI.ScRefExists.PPA
end
end

section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

variable (I : Formalism.MainNotions.S.AutInst)

theorem GE_star (g : ℕ) {x : I.E} (h : GE I g x) : GE I g (star x) := by
  obtain ⟨t, ht⟩ := h
  have hint : IsIntegral ℤ (starRingEnd I.E (t : I.E)) := by
    first
    | exact (RingOfIntegers.isIntegral_coe t).map (starRingEnd I.E).toIntAlgHom
    | exact (t.2).map (starRingEnd I.E).toIntAlgHom
  refine ⟨⟨starRingEnd I.E (t : I.E), hint⟩, ?_⟩
  rw [ht]
  first
  | (rw [star_mul', star_natCast]; rfl)
  | simp [star_mul']

theorem span_part (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M T : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E)
    (hM : Nat.Coprime M p) (hM0 : (M : I.E) ≠ 0) (hT : Nat.Coprime T p) (hT0 : (T : I.E) ≠ 0)
    (hθ1 : GE I (p ^ m) ((θ : I.E) * θ - θ)) (hθ2 : GE I (p ^ m) ((θ : I.E) * star (θ : I.E)))
    (hθ3 : GE I (p ^ m) (1 - (θ : I.E) - star (θ : I.E)))
    (hw : ∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p)
    (hspan : ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd))
    (Sset : Set (Fin I.n → I.E))
    (hSe : ∀ a, M • e a ∈ Sset) (hSf : ∀ a, M • f a ∈ Sset)
    (hSz : (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) ∈ Sset)
    (hSb : ∀ i : Fin k, (θ : I.E) • ((T : I.E) • w i.castSucc) ∈ Sset)
    (hSbd : ∀ i : Fin k, star (θ : I.E) • ((T : I.E) • wd i.castSucc) ∈ Sset) :
    ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) := by
  classical
  set N : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) with hN
  have hsm : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), c • v = (c : I.E) • v := fun c v => rfl
  have hS : ∀ v ∈ Sset, v ∈ N := fun v hv => Submodule.mem_sup_left (Submodule.subset_span hv)
  have hE : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), v ∈ N → (c : I.E) • v ∈ N := fun c v hv => by
    rw [← hsm]
    exact N.smul_mem c hv
  have hnat : ∀ (s : ℕ) (v : Fin I.n → I.E), v ∈ N → (s : I.E) • v ∈ N := fun s v hv => by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv s
  have hgl : ∀ x ∈ I.L, ∀ t : 𝓞 I.E, (((p ^ m : ℕ) : I.E) * (t : I.E)) • x ∈ N := by
    intro x hx t
    have h1 : ((p ^ m : ℕ) : I.E) • x ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [mul_comm, mul_smul]
    exact hE t _ h1
  have hbez : ∀ z ∈ I.L, ∀ s : ℕ, Nat.Coprime s p → (s : I.E) • z ∈ N → z ∈ N := by
    intro z hz s hs hsz
    have hcop : IsCoprime (s : ℤ) ((p ^ m : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right m hs)
    obtain ⟨u, v, huv⟩ := hcop
    have hpz : ((p ^ m : ℕ) : I.E) • z ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩)
    have hc : (u : I.E) * (s : I.E) + (v : I.E) * ((p ^ m : ℕ) : I.E) = 1 := by
      have h := congrArg (Int.cast : ℤ → I.E) huv
      push_cast at h ⊢
      linear_combination h
    have e : z = u • ((s : I.E) • z) + v • (((p ^ m : ℕ) : I.E) • z) := by
      rw [← Int.cast_smul_eq_zsmul I.E u, ← Int.cast_smul_eq_zsmul I.E v, smul_smul, smul_smul,
        ← add_smul, hc, one_smul]
    rw [e]
    exact N.add_mem (zsmul_mem hsz u) (zsmul_mem hpz v)
  have hclr : ∀ v ∈ LA I p, ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by
    intro v hv
    obtain ⟨s, hs, h⟩ := span_clear I p (I.L : Set (Fin I.n → I.E)) hv
    exact ⟨s, hs, by rwa [Submodule.span_eq] at h⟩
  have gen : ∀ (φ φ' : 𝓞 I.E) (u u' : Fin (k + 1) → Fin I.n → I.E),
      (∀ i, u i ∈ LA I p) → (∀ i, u' i ∈ LA I p) →
      (∀ i : Fin k, (φ : I.E) • ((T : I.E) • u i.castSucc) ∈ Sset) →
      (T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)) ∈ N →
      GE I (p ^ m) ((φ : I.E) * φ - φ) → GE I (p ^ m) ((φ : I.E) * φ') →
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range u) →
        (φ : I.E) • y ∈ N := by
    intro φ φ' u u' hu hu' hSu hz h1 h2 y hy hyA
    obtain ⟨s2, hs2, hs2L⟩ := hclr _ (hu (Fin.last k))
    obtain ⟨s3, hs3, hs3L⟩ := hclr _ (hu' (Fin.last k))
    obtain ⟨t1, ht1⟩ := h1
    obtain ⟨t2, ht2⟩ := h2
    obtain ⟨s1, hs1, hs1y⟩ := span_clear I p _ hyA
    have key : ∀ v ∈ Submodule.span (𝓞 I.E) (Set.range e ∪ Set.range f ∪ Set.range u),
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • v) ∈ N := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        rcases hv with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨i, rfl⟩
        · have h := hS _ (hSe a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • e a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • e a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · have h := hS _ (hSf a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • f a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • f a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · cases i using Fin.lastCases with
          | last =>
            have hA : ((M * s2 * s3 : ℕ) : I.E) •
                ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) ∈ N :=
              hnat _ _ (hE φ _ hz)
            have hB : ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                ((s2 : I.E) • u (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs2L t1)
            have hC : ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                ((s3 : I.E) • u' (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs3L t2)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u (Fin.last k)) =
                ((M * s2 * s3 : ℕ) : I.E) •
                  ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) -
                ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                  ((s2 : I.E) • u (Fin.last k))) +
                ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                  ((s3 : I.E) • u' (Fin.last k))) := by
              rw [← ht1, ← ht2]
              funext i
              simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              push_cast
              ring
            rw [e1]
            exact N.add_mem (N.sub_mem hA hB) hC
          | cast j =>
            have h := hS _ (hSu j)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u j.castSucc) =
                ((M * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((T : I.E) • u j.castSucc)) := by
              simp only [smul_smul]
              congr 1
              push_cast
              ring
            rw [e1]
            exact hnat _ _ h
      | zero => simp
      | add v w _ _ hv hw =>
        rw [smul_add, smul_add]
        exact N.add_mem hv hw
      | smul c v _ hv =>
        rw [hsm, smul_comm (φ : I.E) (c : I.E) v, smul_comm ((M * T * s2 * s3 : ℕ) : I.E) (c : I.E)]
        exact hE c _ hv
    have hk := key _ hs1y
    have hφy : (φ : I.E) • y ∈ I.L := by
      rw [← hsm]
      exact I.L.smul_mem φ hy
    refine hbez _ hφy (M * T * s2 * s3 * s1)
      (Nat.Coprime.mul (Nat.Coprime.mul (Nat.Coprime.mul (Nat.Coprime.mul hM hT) hs2) hs3) hs1) ?_
    have e2 : ((M * T * s2 * s3 * s1 : ℕ) : I.E) • ((φ : I.E) • y) =
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((s1 : I.E) • y)) := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e2]
    exact hk
  obtain ⟨θb, hθb⟩ : ∃ θb : 𝓞 I.E, (θb : I.E) = star (θ : I.E) := by
    have hint : IsIntegral ℤ (starRingEnd I.E (θ : I.E)) := by
      first
      | exact (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
      | exact (θ.2).map (starRingEnd I.E).toIntAlgHom
    exact ⟨⟨starRingEnd I.E (θ : I.E), hint⟩, rfl⟩
  intro y hy
  have hyN1 : (θ : I.E) • y ∈ N :=
    gen θ θb w wd (fun i => (hw i).1) (fun i => (hw i).2) hSb (by rw [hθb]; exact hS _ hSz) hθ1
      (by rw [hθb]; exact hθ2) y hy (hspan y hy).1
  have hz2 : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) ∈ N := by
    have e : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) =
        -((T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k))) := by
      rw [hθb, ← smul_neg, neg_sub]
    rw [e]
    exact N.neg_mem (hS _ hSz)
  have h1' : GE I (p ^ m) ((θb : I.E) * θb - θb) := by
    have h := GE_star I (p ^ m) hθ1
    rwa [star_sub, star_mul', ← hθb] at h
  have h2' : GE I (p ^ m) ((θb : I.E) * θ) := by
    rw [hθb, mul_comm]
    exact hθ2
  have hyN2 : (θb : I.E) • y ∈ N :=
    gen θb θ wd w (fun i => (hw i).2) (fun i => (hw i).1) (fun i => by rw [hθb]; exact hSbd i) hz2 h1' h2'
      y hy (hspan y hy).2
  obtain ⟨t3, ht3⟩ := hθ3
  have h3 : ((1 : I.E) - θ - star (θ : I.E)) • y ∈ N := by
    rw [ht3]
    exact hgl y hy t3
  have e : y = (θ : I.E) • y + (θb : I.E) • y + ((1 : I.E) - θ - star (θ : I.E)) • y := by
    rw [hθb, ← add_smul, ← add_smul,
      show (θ : I.E) + star (θ : I.E) + (1 - θ - star (θ : I.E)) = 1 by ring, one_smul]
  rw [e]
  exact N.add_mem (N.add_mem hyN1 hyN2) h3

end PI.ScRefExists.PPA
end
end

section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

def IsInt (I : Formalism.MainNotions.S.AutInst) (x : I.E) : Prop := ∃ a : 𝓞 I.E, (a : I.E) = x

section Int

variable (I : Formalism.MainNotions.S.AutInst)

theorem isInt_coe (a : 𝓞 I.E) : IsInt I (a : I.E) := ⟨a, rfl⟩

theorem isInt_mul {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by push_cast; rfl⟩

theorem isInt_sub {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; rfl⟩

theorem isInt_add {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isInt_one : IsInt I (1 : I.E) := ⟨1, by simp⟩

theorem isInt_hG {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) : IsInt I (hG I x y) := by
  obtain ⟨a, ha⟩ := (I.L_dual y).1 hy x hx
  exact ⟨a, ha⟩

theorem isInt_star (θ : 𝓞 I.E) : IsInt I (star (θ : I.E)) :=
  ⟨⟨star (θ : I.E), (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩

theorem natCast_mem_Ap (p s : ℕ) : (s : I.E) ∈ Ap I p := by
  refine ⟨1, Nat.coprime_one_left p, (s : 𝓞 I.E), ?_⟩
  simp

end Int

theorem local_assembly_principal : PPAssemble := by
  unfold PPAssemble
  intro I p m r k θ e f M w wd hp hm hH hw hew hwd hspan
  obtain ⟨-, -, hθ, -, -, -, -, hMc, -⟩ := hH
  obtain ⟨hθ1, hθ2, hθ3⟩ := hθ
  have hm0 : m ≠ 0 := by omega
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hMp : Nat.Coprime M p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p hm0) hMc
  have hM0 : (M : I.E) ≠ 0 := by
    have hM : M ≠ 0 := by
      rintro rfl
      exact hp1 ((Nat.coprime_zero_left _).1 hMp)
    exact_mod_cast hM

  choose sw hsw using fun i => LA_clear (I := I) p (hw i).1
  choose sd hsd using fun i => LA_clear (I := I) p (hw i).2
  have hT0p : Nat.Coprime ((∏ i, sw i) * ∏ i, sd i) p :=
    Nat.Coprime.mul (Nat.Coprime.prod_left fun i _ => (hsw i).1)
      (Nat.Coprime.prod_left fun i _ => (hsd i).1)
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = ((∏ i, sw i) * ∏ i, sd i) ^ Nat.totient (p ^ m) := ⟨_, rfl⟩
  have hTp : Nat.Coprime T p := hTdef ▸ Nat.Coprime.pow_left _ hT0p
  have hT0dvd : ((∏ i, sw i) * ∏ i, sd i) ∣ T :=
    hTdef ▸ dvd_pow_self _ (Nat.totient_pos.2 (pow_pos hp.pos m)).ne'
  have hTne : T ≠ 0 := by
    rintro h0
    rw [h0] at hTp
    exact hp1 ((Nat.coprime_zero_left _).1 hTp)
  have hTE : (T : I.E) ≠ 0 := by exact_mod_cast hTne
  have hTmod : T ≡ 1 [MOD p ^ m] := hTdef ▸ Nat.ModEq.pow_totient (Nat.Coprime.pow_right m hT0p)
  obtain ⟨c, hc⟩ : ∃ c, T = 1 + p ^ m * c := by
    have h1 : 1 ≤ T := Nat.one_le_iff_ne_zero.2 hTne
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).1 hTmod.symm
    refine ⟨c, ?_⟩
    generalize p ^ m * c = q at hc ⊢
    omega
  have hT1 : QA I p (p ^ m) (1 - (T : I.E) ^ 2) := by
    apply QA_of_GE (I := I)
    refine ⟨-((c : 𝓞 I.E) + c + (p : 𝓞 I.E) ^ m * c * c), ?_⟩
    rw [hc]
    push_cast
    ring
  have hTA : (T : I.E) ^ 2 ∈ Ap I p := pow_mem (natCast_mem_Ap I p T) 2
  have hTw : ∀ i, (T : I.E) • w i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sw i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sw (Finset.mem_univ i))
      (dvd_mul_right _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsw i).2
  have hTwd : ∀ i, (T : I.E) • wd i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sd i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sd (Finset.mem_univ i))
      (dvd_mul_left _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsd i).2

  have hθ1s : GE I (p ^ m) (star (θ : I.E) * star (θ : I.E) - star (θ : I.E)) := by
    obtain ⟨t, ht⟩ := hθ1
    obtain ⟨ts, hts⟩ := isInt_star I t
    refine ⟨ts, ?_⟩
    have h := congrArg star ht
    simp only [star_sub, star_mul, star_natCast] at h
    rw [h, hts]
    ring
  obtain ⟨θs, hθs⟩ := isInt_star I θ
  obtain ⟨z, hzdef⟩ : ∃ z : Fin I.n → I.E,
      z = (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) := ⟨_, rfl⟩
  have hz : z ∈ I.L := by
    rw [hzdef, smul_sub, smul_comm (T : I.E) (θ : I.E), smul_comm (T : I.E) (star (θ : I.E)), ← hθs]
    exact I.L.sub_mem (I.L.smul_mem θ (hTw _)) (I.L.smul_mem θs (hTwd _))
  have hl1 : hG I (wd (Fin.last k)) (w (Fin.last k)) = 1 := by
    simpa using hwd (Fin.last k) (Fin.last k)
  have hl2 : hG I (w (Fin.last k)) (wd (Fin.last k)) = 1 := by
    rw [hG_symm (I := I) (wd (Fin.last k)) (w (Fin.last k)), hl1, star_one]
  have hl3 : ∀ i : Fin k, hG I (wd (Fin.last k)) (w i.castSucc) = 0 := by
    intro i
    rw [hwd, if_neg (Fin.castSucc_ne_last i).symm]
  have hl4 : ∀ i : Fin k, hG I (w (Fin.last k)) (wd i.castSucc) = 0 := by
    intro i
    rw [hG_symm (I := I) (wd i.castSucc) (w (Fin.last k)), hwd, if_neg (Fin.castSucc_ne_last i), star_zero]
  unfold Concl
  refine ⟨z, fun i => (T : I.E) • w i.castSucc, fun i => (T : I.E) • wd i.castSucc, hz,
    fun i => ⟨hTw _, hTwd _⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hzdef]
    refine ⟨?_, ?_⟩ <;> rw [hG_smul_right, hG_sub_right, hG_smul_right, hG_smul_right]
    · rw [(hew a _).1, (hew a _).2.2.1]
      ring
    · rw [(hew a _).2.1, (hew a _).2.2.2]
      ring
  · intro a i
    simp [hG_smul_right, hew]
  ·
    apply GE_of_QA (I := I) p m (isInt_add I (isInt_hG I hz hz) (isInt_one I))
    have hzz : hG I z z + 1 =
        ((T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k))))
          * ((θ : I.E) * star (θ : I.E))
        - (T : I.E) ^ 2 * ((θ : I.E) * θ - θ)
        - (T : I.E) ^ 2 * (star (θ : I.E) * star (θ : I.E) - star (θ : I.E))
        + (T : I.E) ^ 2 * (1 - (θ : I.E) - star (θ : I.E))
        + (1 - (T : I.E) ^ 2) := by
      rw [hzdef]
      simp only [hG_smul_left, hG_smul_right, hG_sub_left, hG_sub_right, star_natCast, star_star, star_sub,
        star_smul]
      rw [hl1, hl2]
      ring
    rw [hzz]
    have hAD : (T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k)))
        ∈ Ap I p :=
      mul_mem hTA (add_mem (hG_mem_Ap (I := I) p (hw _).1 (hw _).1) (hG_mem_Ap (I := I) p (hw _).2 (hw _).2))
    refine QA_add (I := I) p _ (QA_add (I := I) p _ (QA_sub (I := I) p _ (QA_sub (I := I) p _
      (QA_mul (I := I) p _ hAD (QA_of_GE (I := I) p _ hθ2))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1s)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ3))) hT1
  · intro i
    constructor
    · apply GE_of_QA (I := I) p m (isInt_mul I (isInt_coe I θ) (isInt_hG I hz (hTw _)))
      have h : (θ : I.E) * hG I z ((T : I.E) • w i.castSucc) =
          ((T : I.E) ^ 2 * hG I (w (Fin.last k)) (w i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl3]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).1 (hw _).1))
        (QA_of_GE (I := I) p _ hθ2)
    · apply GE_of_QA (I := I) p m
        (isInt_mul I (by rw [← hθs]; exact isInt_coe I θs) (isInt_hG I hz (hTwd _)))
      have h : star (θ : I.E) * hG I z ((T : I.E) • wd i.castSucc) =
          -((T : I.E) ^ 2 * hG I (wd (Fin.last k)) (wd i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl4]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (neg_mem (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).2 (hw _).2)))
        (QA_of_GE (I := I) p _ hθ2)
  · intro i j
    have h : hG I ((T : I.E) • wd i.castSucc) ((T : I.E) • w j.castSucc) =
        (T : I.E) ^ 2 * (if i = j then 1 else 0) := by
      rw [hG_smul_left, hG_smul_right, hwd, star_natCast]
      simp only [Fin.castSucc_inj]
      ring
    rw [h]
    by_cases hij : i = j
    · rw [if_pos hij, mul_one]
      apply GE_of_QA (I := I) p m
        (isInt_mul I (isInt_coe I θ) (isInt_sub I ⟨(T : 𝓞 I.E) ^ 2, by push_cast; rfl⟩ (isInt_one I)))
      have h2 : (θ : I.E) * ((T : I.E) ^ 2 - 1) = -(θ : I.E) * (1 - (T : I.E) ^ 2) := by ring
      rw [h2]
      exact QA_mul (I := I) p _ (neg_mem (int_mem_Ap (I := I) p θ)) hT1
    · rw [if_neg hij]
      exact ⟨0, by simp⟩
  · exact span_part (I := I) p m r k θ e f M T w wd hMp hM0 hTp hTE hθ1 hθ2 hθ3 hw hspan _
      (fun a => Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩))))
      (fun a => Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))))
      (Or.inl (Or.inl (Or.inr hzdef.symm)))
      (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
      (fun i => Or.inr ⟨i, rfl⟩)

end PI.ScRefExists.PPA
end
end
