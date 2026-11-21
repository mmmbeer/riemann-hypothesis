import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen

section
noncomputable section
open NumberField Matrix

namespace PI.SqPairW

open Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

def lam (L' L'' : Submodule (𝓞 E) (Fin N → E)) : Subring (Matrix (Fin N) (Fin N) E) where
  carrier := {e | (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'')}
  mul_mem' {a b} ha hb := ⟨fun y hy => by rw [← mulVec_mulVec]; exact ha.1 _ (hb.1 y hy),
    fun y hy => by rw [← mulVec_mulVec]; exact ha.2 _ (hb.2 y hy)⟩
  one_mem' := ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
  add_mem' {a b} ha hb := ⟨fun y hy => by rw [add_mulVec]; exact L'.add_mem (ha.1 y hy) (hb.1 y hy),
    fun y hy => by rw [add_mulVec]; exact L''.add_mem (ha.2 y hy) (hb.2 y hy)⟩
  zero_mem' := ⟨fun y _ => by simp, fun y _ => by simp⟩
  neg_mem' {a} ha := ⟨fun y hy => by rw [neg_mulVec]; exact L'.neg_mem (ha.1 y hy),
    fun y hy => by rw [neg_mulVec]; exact L''.neg_mem (ha.2 y hy)⟩

theorem stdHG_eq_dot (x y : Fin N → E) : stdHG E N x y = star x ⬝ᵥ y := rfl

theorem conjTranspose_pres {L : Submodule (𝓞 E) (Fin N → E)} (hL : IsSDG E N L)
    {e : Matrix (Fin N) (Fin N) E} (he : ∀ y ∈ L, e *ᵥ y ∈ L) : ∀ y ∈ L, eᴴ *ᵥ y ∈ L := by
  intro y hy
  refine (hL.2.2 _).2 (fun x hx => ?_)
  have hy' := (hL.2.2 y).1 hy (e *ᵥ x) (he x hx)
  rw [stdHG_eq_dot] at hy' ⊢
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  exact hy'

theorem conjTranspose_mem_lam {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hL' : IsSDG E N L')
    (hL'' : IsSDG E N L'') {e : Matrix (Fin N) (Fin N) E} (he : e ∈ lam L' L'') :
    eᴴ ∈ lam L' L'' := ⟨conjTranspose_pres hL' he.1, conjTranspose_pres hL'' he.2⟩

def mset (e : Matrix (Fin N) (Fin N) E) : Set (Matrix (Fin N) (Fin N) E) :=
  {e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)}

theorem mset_sub {R : Subring (Matrix (Fin N) (Fin N) E)} (hstar : ∀ x ∈ R, xᴴ ∈ R)
    {e : Matrix (Fin N) (Fin N) E} (he : e ∈ R) : ∀ M ∈ mset e, M ∈ R := by
  have h1e : 1 - e ∈ R := R.sub_mem R.one_mem he
  rintro M (rfl | rfl | rfl)
  · exact R.sub_mem (R.mul_mem he he) he
  · exact R.mul_mem (hstar e he) he
  · exact R.mul_mem (hstar _ h1e) h1e

theorem star_cong (b d : Matrix (Fin N) (Fin N) E) (P : ℤ) :
    (b + P • d)ᴴ * (b + P • d) = bᴴ * b + P • (bᴴ * d + dᴴ * b + P • (dᴴ * d)) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_zsmul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  abel

theorem sq_cong (b d : Matrix (Fin N) (Fin N) E) (P : ℤ) :
    (b + P • d) * (b + P • d) - (b + P • d) = (b * b - b) + P • (b * d + d * b + P • (d * d) - d) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub,
    smul_smul]
  abel

theorem mset_cong {R : Subring (Matrix (Fin N) (Fin N) E)} (hstar : ∀ x ∈ R, xᴴ ∈ R)
    {a d : Matrix (Fin N) (Fin N) E} (ha : a ∈ R) (hd : d ∈ R) (P : ℤ) :
    ∀ M ∈ mset (a + P • d), ∃ M' ∈ mset a, ∃ r ∈ R, M = M' + P • r := by
  rintro M (rfl | rfl | rfl)
  · refine ⟨a * a - a, Or.inl rfl, a * d + d * a + P • (d * d) - d, ?_, sq_cong a d P⟩
    exact R.sub_mem (R.add_mem (R.add_mem (R.mul_mem ha hd) (R.mul_mem hd ha))
      (zsmul_mem (R.mul_mem hd hd) P)) hd
  · refine ⟨aᴴ * a, Or.inr (Or.inl rfl), aᴴ * d + dᴴ * a + P • (dᴴ * d), ?_, star_cong a d P⟩
    exact R.add_mem (R.add_mem (R.mul_mem (hstar a ha) hd) (R.mul_mem (hstar d hd) ha))
      (zsmul_mem (R.mul_mem (hstar d hd) hd) P)
  · have e1 : 1 - (a + P • d) = (1 - a) + P • (-d) := by
      rw [smul_neg]
      abel
    have h1a : 1 - a ∈ R := R.sub_mem R.one_mem ha
    have hnd : -d ∈ R := R.neg_mem hd
    refine ⟨(1 - a)ᴴ * (1 - a), Or.inr (Or.inr rfl),
      (1 - a)ᴴ * (-d) + (-d)ᴴ * (1 - a) + P • ((-d)ᴴ * (-d)), ?_, ?_⟩
    · exact R.add_mem (R.add_mem (R.mul_mem (hstar _ h1a) hnd) (R.mul_mem (hstar _ hnd) h1a))
        (zsmul_mem (R.mul_mem (hstar _ hnd) hnd) P)
    · rw [e1]
      exact star_cong (1 - a) (-d) P

def yg (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) : AddSubgroup (Fin N → E) where
  carrier := {x | ∃ m, m ∈ L' ∧ m ∈ L'' ∧ x = (n : E) • m}
  add_mem' := by
    rintro _ _ ⟨m1, h1, h1', rfl⟩ ⟨m2, h2, h2', rfl⟩
    exact ⟨m1 + m2, L'.add_mem h1 h2, L''.add_mem h1' h2', (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, L'.zero_mem, L''.zero_mem, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨m, h, h', rfl⟩
    exact ⟨-m, L'.neg_mem h, L''.neg_mem h', (smul_neg _ _).symm⟩


theorem mem_of_local {V : Type*} [AddCommGroup V] (Y : AddSubgroup V) (x : V)
    (h : ∀ p : ℕ, p.Prime → ∃ t : ℤ, ¬ (p : ℤ) ∣ t ∧ t • x ∈ Y) : x ∈ Y := by
  classical
  let I : Ideal ℤ :=
    { carrier := {t | t • x ∈ Y}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • x ∈ Y
        rw [add_smul]
        exact Y.add_mem ha hb
      zero_mem' := by
        show (0 : ℤ) • x ∈ Y
        rw [zero_smul]
        exact Y.zero_mem
      smul_mem' := fun c {t} ht => by
        show (c • t) • x ∈ Y
        rw [smul_eq_mul, mul_smul]
        exact Y.zsmul_mem ht c }
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmem : ∀ t : ℤ, t • x ∈ Y ↔ n ∣ t := by
    intro t
    have e : t ∈ I ↔ t ∈ Submodule.span ℤ {n} := by rw [hn]
    exact e.trans Ideal.mem_span_singleton
  have h1 : n ∣ 1 := by
    by_contra hn1
    have hna : n.natAbs ≠ 1 := by
      intro e
      apply hn1
      rw [← Int.natAbs_dvd, e]
      exact one_dvd _
    have hp := Nat.minFac_prime hna
    obtain ⟨t, ht, htY⟩ := h _ hp
    apply ht
    have hpn : ((n.natAbs.minFac : ℕ) : ℤ) ∣ n := Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
    exact hpn.trans ((hmem t).1 htY)
  have := (hmem 1).2 h1
  rwa [one_smul] at this

theorem exists_nat_mul_int (c : E) : ∃ k : ℕ, 0 < k ∧ ∃ β : 𝓞 E, (β : E) = (k : E) * c := by
  have halg : IsAlgebraic ℤ c := by
    rw [IsFractionRing.isAlgebraic_iff ℤ ℚ E]
    exact Algebra.IsAlgebraic.isAlgebraic c
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨β, hβ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  have e1 : algebraMap (𝓞 E) E β = (y : E) * c := by rw [hβ, zsmul_eq_mul]
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · refine ⟨β, ?_⟩
    change algebraMap (𝓞 E) E β = _
    have hk : (y : E) = ((y.natAbs : ℤ) : E) := by exact_mod_cast h
    rw [e1, hk, Int.cast_natCast]
  · refine ⟨-β, ?_⟩
    change algebraMap (𝓞 E) E (-β) = _
    have hk : (y : E) = -((y.natAbs : ℤ) : E) := by exact_mod_cast h
    rw [map_neg, e1, hk, Int.cast_natCast]
    ring

end PI.SqPairW
end
end

section
noncomputable section
open NumberField Matrix

namespace PI.SqPairW

open Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem ringInt_smul (β : 𝓞 E) (w : Fin N → E) : β • w = (β : E) • w := by
  ext i
  rfl

theorem exists_nat_smul_mem {L : Submodule (𝓞 E) (Fin N → E)}
    (hL : Submodule.span E (L : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ k : ℕ, 0 < k ∧ (k : ℤ) • v ∈ L := by
  let T : Submodule E (Fin N → E) :=
    { carrier := {v | ∃ k : ℕ, 0 < k ∧ (k : ℤ) • v ∈ L}
      add_mem' := by
        rintro a b ⟨k1, hk1, ha⟩ ⟨k2, hk2, hb⟩
        refine ⟨k1 * k2, Nat.mul_pos hk1 hk2, ?_⟩
        have e1 : ((k1 * k2 : ℕ) : ℤ) • (a + b) = (k2 : ℤ) • ((k1 : ℤ) • a) + (k1 : ℤ) • ((k2 : ℤ) • b) := by
          push_cast
          module
        rw [e1]
        exact L.add_mem (L.toAddSubgroup.zsmul_mem ha _) (L.toAddSubgroup.zsmul_mem hb _)
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c v ⟨k2, hk2, hv⟩
        obtain ⟨k1, hk1, β, hβ⟩ := exists_nat_mul_int c
        refine ⟨k1 * k2, Nat.mul_pos hk1 hk2, ?_⟩
        have e1 : ((k1 * k2 : ℕ) : ℤ) • (c • v) = β • ((k2 : ℤ) • v) := by
          rw [ringInt_smul, hβ, ← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul,
            smul_smul]
          push_cast
          congr 1
          ring
        rw [e1]
        exact L.smul_mem β hv }
  have hLT : L ≤ T.restrictScalars (𝓞 E) := fun v hv => ⟨1, one_pos, by simpa using hv⟩
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hL, Submodule.span_le]
    exact fun v hv => hLT hv
  have hv : v ∈ T := hT ▸ Submodule.mem_top
  exact hv

theorem exists_den_le {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hfg : L'.FG)
    (hspan : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) :
    ∃ D : ℕ, 0 < D ∧ ∀ w ∈ L', (D : ℤ) • w ∈ L'' := by
  obtain ⟨s, rfl⟩ := hfg
  have hk : ∀ x : s, ∃ k : ℕ, 0 < k ∧ (k : ℤ) • (x : Fin N → E) ∈ L'' :=
    fun x => exists_nat_smul_mem hspan x
  choose k hk0 hkL using hk
  refine ⟨∏ x, k x, Finset.prod_pos (fun x _ => hk0 x), ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ : k ⟨x, hx⟩ ∣ ∏ y, k y := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    rw [hm, Nat.cast_mul, mul_comm, mul_smul]
    exact zsmul_mem (hkL ⟨x, hx⟩) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_comm]
    exact L''.smul_mem c hx

theorem exists_den {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hL' : IsSDG E N L') (hL'' : IsSDG E N L'')
    {n : 𝓞 E} (hn : n ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ ∀ w, (w ∈ L' ∨ w ∈ L'') → (D : ℤ) • w ∈ yg L' L'' n := by
  obtain ⟨D1, hD1, h1⟩ := exists_den_le hL'.1 hL''.2.1
  obtain ⟨D2, hD2, h2⟩ := exists_den_le hL''.1 hL'.2.1
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
  obtain ⟨k, hk, β, hβ⟩ := exists_nat_mul_int (n : E)⁻¹
  have hkY : ∀ u, u ∈ L' → u ∈ L'' → (k : ℤ) • u ∈ yg L' L'' n := by
    intro u hu hu'
    refine ⟨β • u, L'.smul_mem β hu, L''.smul_mem β hu', ?_⟩
    rw [ringInt_smul, smul_smul, hβ, ← Int.cast_smul_eq_zsmul E]
    congr 1
    field_simp
    push_cast
    ring
  refine ⟨k * D1 * D2, Nat.mul_pos (Nat.mul_pos hk hD1) hD2, ?_⟩
  rintro w (hw | hw)
  · have hu : (D1 : ℤ) • w ∈ L'' := h1 w hw
    have hu' : (D1 : ℤ) • w ∈ L' := L'.toAddSubgroup.zsmul_mem hw _
    have e1 : ((k * D1 * D2 : ℕ) : ℤ) • w = (k : ℤ) • ((D2 : ℤ) • ((D1 : ℤ) • w)) := by
      push_cast
      module
    rw [e1]
    exact hkY _ (L'.toAddSubgroup.zsmul_mem hu' _) (L''.toAddSubgroup.zsmul_mem hu _)
  · have hu : (D2 : ℤ) • w ∈ L' := h2 w hw
    have hu' : (D2 : ℤ) • w ∈ L'' := L''.toAddSubgroup.zsmul_mem hw _
    have e1 : ((k * D1 * D2 : ℕ) : ℤ) • w = (k : ℤ) • ((D1 : ℤ) • ((D2 : ℤ) • w)) := by
      push_cast
      module
    rw [e1]
    exact hkY _ (L'.toAddSubgroup.zsmul_mem hu _) (L''.toAddSubgroup.zsmul_mem hu' _)

end PI.SqPairW
end
end
