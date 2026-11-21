import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsSumPadicValIntWindowEq
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem lift_le (l : ℕ) [Fact l.Prime] (hl : 11 ≤ l) (h η H M : ℕ) (h1 : 1 ≤ h) (hη : 20 * η ≤ h)
    (hH : H ≤ h + η) (hM : M ≤ h) (jumps : Finset ℤ)
    (hj : ∀ u ∈ jumps, -(M : ℤ) ≤ u ∧ u ≤ h) :
    let J : Finset ℤ :=
      ((jumps ×ˢ Finset.Icc (1 : ℤ) M).image (fun p : ℤ × ℤ => p.1 + p.2)).filter (fun j => j ≠ 0) ∪
        Finset.Icc (1 : ℤ) M
    let aS : ℕ := M / (l - 1) + 1
    let eW : ℕ := ⌊(H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1)⌋₊
    let eU : ℕ := (∑ j ∈ J, padicValInt l j) + aS + padicValNat l aS.factorial
    ((2 * eW + eU : ℕ) : ℝ) ≤ 71 / 10 * (h : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * (h : ℝ)) := by
  intro J aS eW eU
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) < l := by linarith
  have hxm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hxi0 : 0 ≤ (l : ℝ)⁻¹ := by positivity
  have hyi0 : 0 ≤ ((l : ℝ) - 1)⁻¹ := inv_nonneg.2 hxm.le
  have hyi10 : ((l : ℝ) - 1)⁻¹ ≤ 1 / 10 := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le hl'
  have hyix : ((l : ℝ) - 1)⁻¹ ≤ 11 / 10 * (l : ℝ)⁻¹ := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le_u hl'
  have hsq : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 121 / 100 * (l : ℝ)⁻¹ := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.q_le hl'
  have hsq0 : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2 := by positivity
  have hH1 : H + 1 ≤ 2 * h := by omega
  have hHr : (H : ℝ) ≤ h + η := by exact_mod_cast hH
  have hMr : (M : ℝ) ≤ h := by exact_mod_cast hM
  have hηr : (20 : ℝ) * η ≤ h := by exact_mod_cast hη
  have hH1r : (H : ℝ) + 1 ≤ 2 * (h : ℝ) := by exact_mod_cast hH1
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hlogH0 : 0 ≤ Real.logb l ((H : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlogH : Real.logb l ((H : ℝ) + 1) ≤ Real.logb l (2 * (h : ℝ)) :=
    Real.logb_le_logb_of_le hl1 (by linarith) hH1r
  have hW : (eW : ℝ) ≤ (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) + 3 + Real.logb l ((H : ℝ) + 1) := by
    have h0 : 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1) := by
      have : 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by positivity
      linarith
    calc (eW : ℝ) ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1) :=
          Nat.floor_le h0
      _ = (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) + 3 + Real.logb l ((H : ℝ) + 1) := by ring
  have hHsq : (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ ((h : ℝ) + η) * (121 / 100 * (l : ℝ)⁻¹) :=
    mul_le_mul hHr hsq hsq0 (by positivity)
  have hηxi : (20 * (η : ℝ)) * (l : ℝ)⁻¹ ≤ (h : ℝ) * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hηr hxi0
  have hl1n : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_one]
  have hA : (aS : ℝ) ≤ (M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1 := by
    have hd : ((M / (l - 1) : ℕ) : ℝ) ≤ (M : ℝ) / ((l - 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [hl1n, div_eq_mul_inv] at hd
    have he : (aS : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1 := by
      show ((M / (l - 1) + 1 : ℕ) : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1
      rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hF : (padicValNat l aS.factorial : ℝ) ≤ (aS : ℝ) * ((l : ℝ) - 1)⁻¹ := by
    have hfa := padicValNat_factorial_le_div_sub_one' l aS
    rwa [div_eq_mul_inv] at hfa
  have hFA : (aS : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ ((M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1) * ((l : ℝ) - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right hA hyi0
  have hyy : ((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹ ≤ 11 / 100 * (l : ℝ)⁻¹ := by
    have hq := mul_le_mul_of_nonneg_right hyi10 hyi0
    linarith
  have hMyy : (M : ℝ) * (((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹) ≤ (h : ℝ) * (11 / 100 * (l : ℝ)⁻¹) :=
    mul_le_mul hMr hyy (mul_self_nonneg _) (Nat.cast_nonneg h)
  have hMy : (M : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹) :=
    mul_le_mul hMr hyix hyi0 (Nat.cast_nonneg h)
  have hhy : (h : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hyix (Nat.cast_nonneg h)
  have hJsub : J ⊆ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)) ∪
      Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)) := by
    intro j hjJ
    rcases Finset.mem_union.1 hjJ with hA' | hB'
    · obtain ⟨hA1, hne⟩ := Finset.mem_filter.1 hA'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hA1
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 hp2
      obtain ⟨hu1, hu2⟩ := hj p.1 hp1
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      push_cast
      omega
    · obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hB'
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      push_cast
      omega
  have hw1 := sum_padicValInt_window_le l (-(M : ℤ)) M M (by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)
  have hw2 := sum_padicValInt_window_le l (1 : ℤ) (h + M) (h + M) (by
    intro i hi
    rw [Finset.mem_Ico] at hi
    push_cast at hi ⊢
    exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)
  have hdisj : Disjoint (Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)))
      (Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ))) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_Ico] at hx hy
    omega
  have hle : ∑ j ∈ J, padicValInt l j ≤
      ∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j +
        ∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset hJsub
  have hler : ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j : ℕ) : ℝ) +
        ((∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hcM : ((h + M : ℕ) : ℝ) = (h : ℝ) + M := Nat.cast_add h M
  rw [hcM, div_eq_mul_inv] at hw2
  rw [div_eq_mul_inv] at hw1
  have hU : ((2 * eW + eU : ℕ) : ℝ) = 2 * (eW : ℝ) + ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) +
      (aS : ℝ) + (padicValNat l aS.factorial : ℝ) := by
    show ((2 * eW + ((∑ j ∈ J, padicValInt l j) + aS + padicValNat l aS.factorial) : ℕ) : ℝ) = _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hU]
  have hgoal : (71 : ℝ) / 10 * (h : ℝ) / l = 71 / 10 * ((h : ℝ) * (l : ℝ)⁻¹) := by ring
  rw [hgoal]
  have hhx : 0 ≤ (h : ℝ) * (l : ℝ)⁻¹ := mul_nonneg (Nat.cast_nonneg h) hxi0
  linarith [hW, hHsq, hηxi, hlogH, hler, hw1, hw2, hA, hF, hFA, hMyy, hMy, hhy, hyi10]

theorem step0 (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (hb : 1 ≤ b) (hηb : 20 * η ≤ b) (hSb : 20 * S ≤ b)
    (hwb : 20 * w ≤ b) (hsm : (b : ℝ) / 4 < 40 * Sg l (b + η + S) w S η) :
    71 / 10 * ((b + η + S : ℕ) : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) ≤
      160 * Sg l (b + η + S) w S η := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) < l := by linarith
  have hX : ((b + η + S : ℕ) : ℝ) = (b : ℝ) + η + S := by push_cast; ring
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hηr : (20 : ℝ) * η ≤ b := by exact_mod_cast hηb
  have hSr : (20 : ℝ) * S ≤ b := by exact_mod_cast hSb
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hX1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by rw [hX]; linarith
  have hL : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := Real.logb_nonneg hl1 (by linarith)
  have hE : Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ≤ Sg l (b + η + S) w S η := by
    unfold Sg
    have e1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have e2 : 0 ≤ ((w : ℝ) + S + η) / l := by positivity
    linarith
  have hdiv : 71 / 10 * ((b + η + S : ℕ) : ℝ) / l ≤ 71 / 10 * ((b + η + S : ℕ) : ℝ) / 11 := by
    gcongr
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem lift_le_ePA (l : ℕ) [Fact l.Prime] (hl : 11 ≤ l) (h η H M : ℕ) (h1 : 1 ≤ h) (hη : 20 * η ≤ h)
    (hH : H ≤ h + η) (hM : M ≤ h) (jumps : Finset ℤ)
    (hj : ∀ u ∈ jumps, -(M : ℤ) ≤ u ∧ u ≤ h) :
    (Formalism.MainNotions.LiftingTheory.ePA l M H jumps : ℝ) ≤
      71 / 10 * (h : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * (h : ℝ)) := by
  unfold Formalism.MainNotions.LiftingTheory.ePA Formalism.MainNotions.LiftingTheory.eUA Formalism.MainNotions.LiftingTheory.eWA Formalism.MainNotions.LiftingTheory.aA Formalism.MainNotions.LiftingTheory.JSet
  exact lift_le l hl h η H M h1 hη hH hM jumps hj

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section
namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem exists_liftF_le_sg_of_thick : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L) (b w S η m : ℕ)
    (up : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool) (size Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ)
    (hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi)
    (hAlt : Alt b η up size) (hth : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i)
    (hbig : (b : ℝ) / 4 < 40 * Sg l b w S η size),
    ∃ e₀ : ℕ, (e₀ : ℝ) ≤ 160 * Sg l b w S η size ∧ f.LiftF ((D.loc l).PD K) e₀ := by
  intro D HW F Cm CR CA CB CK hU l _ K LL hG hK _ _ T₁ T₂ f b w S η m up size Mi hi hB hAlt hth hbig
  obtain ⟨hp11, hSet, hwb, hηb, hSb, ⟨j, hj⟩⟩ := hB
  obtain ⟨hCA, hSur, hηs, hJA, _hlow, hnt, _hJL⟩ := hSet
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl : 11 ≤ l := hp ▸ hp11
  have hLift : Formalism.MainNotions.LiftingTheory.coreLiftA ((HW l).W K 1 LL hG) := hU.a2.2.2.2.2.2.2.2.1 l K 1 LL hG

  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht
      omega
  have hb1 : 1 ≤ b := by
    have h1 := hnt j hj
    have h2 := hηs j
    omega
  have hhB : TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := if_pos hth

  let Mi' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ := fun i => if up i then size i + S else η
  have hJL' : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW l).W K 1 LL hG) T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hM : Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' ≤ b + η + S := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, Mi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hm : Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) hi' ≤ b + η + S := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hH : Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' hi' ≤ b + η + S + η := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hjumps : ∀ u ∈ Formalism.MainNotions.LiftingTheory.jumpSet ((HW l).W K 1 LL hG) T₁
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi')
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) hi'),
      -((Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' : ℕ) : ℤ) ≤ u ∧
        u ≤ ((b + η + S : ℕ) : ℤ) := by
    intro u hu
    simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc] at hu
    refine ⟨hu.1.1, ?_⟩
    have := hu.1.2
    push_cast at this ⊢
    omega
  have hL := Formalism.MainNotions.N.FrobeniusPowerSeries.lift_le_ePA l hl (b + η + S) η
    (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' hi')
    (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi') (by omega) (by omega) hH hM _ hjumps
  have hSg : Sg l b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) w S η := by
    unfold Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    rw [hhB]
  have h0 := Formalism.MainNotions.N.FrobeniusPowerSeries.step0 l hl b w S η hb1 hηb hSb hwb (by rw [← hSg]; exact hbig)
  have hLA := hLift hCA T₁ T₂ f Mi' hi' hSur hJL'
  refine ⟨_, ?_, hLA⟩
  rw [hp, hSg]
  linarith

end Formalism.MainNotions.N.Ln17
end
