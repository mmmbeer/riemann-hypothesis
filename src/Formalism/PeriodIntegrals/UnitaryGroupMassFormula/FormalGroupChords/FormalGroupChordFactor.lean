import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DXEqDerivative
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DvCoeffMulEqZeroOfLtOrder
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists

section
noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

theorem isWq_bridge {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h : IsWq W wq) : PI.AddIntG.IsWq W wq := h

end PI.FglChordFactor.Wk
end
end

section
noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS subst_mem_SerS subst_psubst)

variable {p : ℕ} [Fact p.Prime]

theorem hasSubst2 {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨by simpa using hu, by simpa using hv⟩)

theorem subst_pair_first_variable {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = u := by
  rw [MvPowerSeries.subst_X hs]; simp

theorem subst_pair_second_variable {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = v := by
  rw [MvPowerSeries.subst_X hs]; simp

theorem subst_pair_first_series {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) =
      PowerSeries.subst u f := by
  rw [subst_psubst (PowerSeries.HasSubst.X 0) hs, subst_pair_first_variable hs]

theorem subst_pair_second_series {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) f) =
      PowerSeries.subst v f := by
  rw [subst_psubst (PowerSeries.HasSubst.X 1) hs, subst_pair_second_variable hs]

theorem subst_pair_comp {u v u' v' : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v])
    (hs' : MvPowerSeries.HasSubst ![u', v']) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.subst ![u', v'] H) =
      MvPowerSeries.subst ![MvPowerSeries.subst ![u, v] u', MvPowerSeries.subst ![u, v] v'] H := by
  rw [MvPowerSeries.subst_comp_subst_apply hs' hs]
  congr 1
  funext i
  fin_cases i <;> simp

theorem subst_pair_variables_self (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] H = H := by
  have e : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] = MvPowerSeries.X := by
    funext i; fin_cases i <;> simp
  rw [e, MvPowerSeries.subst_self]; rfl

theorem X_mem_SerS (S : Subring ℂ_[p]) (i : Fin 2) :
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
  rw [mem_SerS]; intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem serS_unit {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} (h : ∀ n, PowerSeries.coeff n f ∈ S) :
    (f : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS]; intro e
  have he : e = Finsupp.single () (e ()) := by ext; simp
  rw [he]; exact h (e ())

theorem serS_unit_iff {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} :
    (f : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit ↔ ∀ n, PowerSeries.coeff n f ∈ S := by
  refine ⟨fun h n => ?_, serS_unit⟩
  exact (mem_SerS S _).1 h (Finsupp.single () n)

theorem coeff_mul_second_variable (f : MvPowerSeries (Fin 2) ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * MvPowerSeries.X 1) =
      if 1 ≤ e 1 then MvPowerSeries.coeff (e - Finsupp.single 1 1) f else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]

theorem single0_iff (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem fact_div {S : Subring ℂ_[p]} {H : MvPowerSeries (Fin 2) ℂ_[p]} {f : PowerSeries ℂ_[p]}
    (hf0 : PowerSeries.constantCoeff f = 0) (hfS : ∀ n, PowerSeries.coeff n f ∈ S) (hH : H ∈ SerS S (Fin 2))
    (hz : MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f] H = 0) :
    ∃ Q ∈ SerS S (Fin 2),
      H = (MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) * Q := by
  set a : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 0 with ha
  set b : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 1 with hb
  set s : MvPowerSeries (Fin 2) ℂ_[p] := PowerSeries.subst a f with hs
  have ha0 : MvPowerSeries.constantCoeff a = 0 := MvPowerSeries.constantCoeff_X 0
  have hb0 : MvPowerSeries.constantCoeff b = 0 := MvPowerSeries.constantCoeff_X 1
  have hs0 : MvPowerSeries.constantCoeff s = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 f hf0
  have haS : a ∈ SerS S (Fin 2) := X_mem_SerS S 0
  have hbS : b ∈ SerS S (Fin 2) := X_mem_SerS S 1
  have hsS : s ∈ SerS S (Fin 2) := subst_mem_SerS S ha0 haS (serS_unit hfS)
  have hP : MvPowerSeries.HasSubst ![a, b + s] := hasSubst2 ha0 (by rw [map_add, hb0, hs0, add_zero])
  have hM : MvPowerSeries.HasSubst ![a, b - s] := hasSubst2 ha0 (by rw [map_sub, hb0, hs0, sub_zero])
  have hZ : MvPowerSeries.HasSubst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] := hasSubst2 ha0 (map_zero _)
  set Hp := MvPowerSeries.subst ![a, b + s] H with hHp

  have hback : MvPowerSeries.subst ![a, b - s] Hp = H := by
    rw [hHp, subst_pair_comp hM hP, subst_pair_first_variable hM, MvPowerSeries.subst_add hM, subst_pair_second_variable hM, hs, subst_pair_first_series hM, ← hs,
      sub_add_cancel, ha, hb, subst_pair_variables_self]

  have hzero : MvPowerSeries.subst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] Hp = 0 := by
    rw [hHp, subst_pair_comp hZ hP, subst_pair_first_variable hZ, MvPowerSeries.subst_add hZ, subst_pair_second_variable hZ, hs, subst_pair_first_series hZ, ← hs,
      zero_add]
    exact hz

  set Qt : MvPowerSeries (Fin 2) ℂ_[p] := fun e => MvPowerSeries.coeff (e + Finsupp.single 1 1) Hp with hQt
  set r : PowerSeries ℂ_[p] := PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n) Hp with hr
  have hdec : Hp = Qt * b + PowerSeries.subst a r := by
    ext e
    rw [map_add, hb, coeff_mul_second_variable, ha, PowerSeries.coeff_subst_single]
    by_cases he : e 1 = 0
    · have he' : e = Finsupp.single 0 (e 0) := (single0_iff e).2 he
      rw [if_neg (by omega), if_pos he', zero_add, hr, PowerSeries.coeff_mk, ← he']
    · have he' : ¬ e = Finsupp.single 0 (e 0) := fun h => he ((single0_iff e).1 h)
      rw [if_pos (by omega), if_neg he', add_zero]
      show MvPowerSeries.coeff e Hp = MvPowerSeries.coeff (e - Finsupp.single 1 1 + Finsupp.single 1 1) Hp
      rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))]
  have hR : PowerSeries.subst a r = 0 := by
    have h1 := hzero
    rw [hdec, MvPowerSeries.subst_add hZ, MvPowerSeries.subst_mul hZ, subst_pair_second_variable hZ, mul_zero, zero_add, ha,
      subst_pair_first_series hZ] at h1
    exact h1
  have hdec' : Hp = Qt * b := by rw [hdec, hR, add_zero]
  have hQtS : Qt ∈ SerS S (Fin 2) := by
    have hHpS : Hp ∈ SerS S (Fin 2) :=
      mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
        (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using add_mem hbS hsS⟩) hH
    rw [mem_SerS]; intro e
    exact (mem_SerS S Hp).1 hHpS _
  refine ⟨MvPowerSeries.subst ![a, b - s] Qt, ?_, ?_⟩
  · exact mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
      (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using sub_mem hbS hsS⟩) hQtS
  · conv_lhs => rw [← hback, hdec', MvPowerSeries.subst_mul hM, hb, subst_pair_second_variable hM]
    ring

end PI.FglChordFactor.Wk
end
end

section
noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)

variable {p : ℕ} [Fact p.Prime]

abbrev cP (x : ℂ_[p]) : PowerSeries ℂ_[p] := algebraMap ℂ_[p] (PowerSeries ℂ_[p]) x

def Dser (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq)

def iW (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  -PowerSeries.X * (Dser W wq)⁻¹

theorem wq_const' {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  have h' : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  have e := congrArg PowerSeries.constantCoeff h'
  simpa using e

theorem D_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (Dser W wq) = 1 := by
  simp [Dser]

theorem iW_mul_D (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    iW W wq * Dser W wq = -PowerSeries.X := by
  have hc : PowerSeries.constantCoeff (Dser W wq) ≠ 0 := by rw [D_const]; exact one_ne_zero
  rw [iW, mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]

theorem iW_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (iW W wq) = 0 := by
  simp [iW]

theorem hasSubst_iW (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries.HasSubst (iW W wq) := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' (iW_const W wq)
  | exact PowerSeries.HasSubst.of_constantCoeff_zero (iW_const W wq)

theorem subst_isWq {W : WeierstrassCurve ℂ_[p]} {wq t : PowerSeries ℂ_[p]} (ht : PowerSeries.HasSubst t)
    (h : IsWq W wq) :
    PowerSeries.subst t wq = 1 + cP W.a₁ * t * PowerSeries.subst t wq + cP W.a₂ * t ^ 2 * PowerSeries.subst t wq +
      cP W.a₃ * t ^ 3 * PowerSeries.subst t wq ^ 2 + cP W.a₄ * t ^ 4 * PowerSeries.subst t wq ^ 2 +
      cP W.a₆ * t ^ 6 * PowerSeries.subst t wq ^ 3 := by
  have h' : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  have hφ : ∀ f : PowerSeries ℂ_[p], PowerSeries.subst t f = PowerSeries.substAlgHom ht f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hX : PowerSeries.substAlgHom ht (PowerSeries.X : PowerSeries ℂ_[p]) = t := by
    rw [← hφ, PowerSeries.subst_X ht]
  conv_lhs => rw [h']
  simp only [hφ, map_add, map_mul, map_pow, map_one, AlgHom.commutes, hX]

theorem fix_unique {a₁ a₂ a₃ a₄ a₆ : ℂ_[p]} {t V₁ V₂ : PowerSeries ℂ_[p]} (ht : PowerSeries.constantCoeff t = 0)
    (h₁ : V₁ = 1 + cP a₁ * t * V₁ + cP a₂ * t ^ 2 * V₁ + cP a₃ * t ^ 3 * V₁ ^ 2 + cP a₄ * t ^ 4 * V₁ ^ 2 +
      cP a₆ * t ^ 6 * V₁ ^ 3)
    (h₂ : V₂ = 1 + cP a₁ * t * V₂ + cP a₂ * t ^ 2 * V₂ + cP a₃ * t ^ 3 * V₂ ^ 2 + cP a₄ * t ^ 4 * V₂ ^ 2 +
      cP a₆ * t ^ 6 * V₂ ^ 3) : V₁ = V₂ := by
  have key : (V₁ - V₂) * (1 - (cP a₁ * t + cP a₂ * t ^ 2 + cP a₃ * t ^ 3 * (V₁ + V₂) +
      cP a₄ * t ^ 4 * (V₁ + V₂) + cP a₆ * t ^ 6 * (V₁ ^ 2 + V₁ * V₂ + V₂ ^ 2))) = 0 := by
    linear_combination h₁ - h₂
  have hc : PowerSeries.constantCoeff (1 - (cP a₁ * t + cP a₂ * t ^ 2 + cP a₃ * t ^ 3 * (V₁ + V₂) +
      cP a₄ * t ^ 4 * (V₁ + V₂) + cP a₆ * t ^ 6 * (V₁ ^ 2 + V₁ * V₂ + V₂ ^ 2))) ≠ 0 := by
    simp [ht]
  rcases mul_eq_zero.1 key with h | h
  · exact sub_eq_zero.1 h
  · exact absurd (by rw [h, map_zero]) hc

theorem wq_iW {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (iW W wq) wq = wq * Dser W wq ^ 2 := by
  have hw : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  refine fix_unique (a₁ := W.a₁) (a₂ := W.a₂) (a₃ := W.a₃) (a₄ := W.a₄) (a₆ := W.a₆) (iW_const W wq) ?_ ?_
  · exact subst_isWq (hasSubst_iW W wq) h
  · have e := iW_mul_D W wq
    generalize iW W wq = i at e ⊢
    generalize hDdef : Dser W wq = D at e ⊢
    have hD : D = 1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq) := hDdef.symm
    linear_combination (-(cP W.a₁) * wq * D - cP W.a₂ * wq * (i * D - PowerSeries.X)
      - cP W.a₃ * wq ^ 2 * D * ((i * D) ^ 2 - i * D * PowerSeries.X + PowerSeries.X ^ 2)
      - cP W.a₄ * wq ^ 2 * ((i * D) ^ 3 - (i * D) ^ 2 * PowerSeries.X + i * D * PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
      - cP W.a₆ * wq ^ 3 * ((i * D) ^ 5 - (i * D) ^ 4 * PowerSeries.X + (i * D) ^ 3 * PowerSeries.X ^ 2
          - (i * D) ^ 2 * PowerSeries.X ^ 3 + i * D * PowerSeries.X ^ 4 - PowerSeries.X ^ 5)) * e
      + hw + wq * (D + 1) * hD

theorem dX_eq (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  rw [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem derivative_flog' (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.derivative ℂ_[p] (flog W wq) = omegaW W wq := by
  ext n
  rw [PowerSeries.coeff_derivative, flog, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  push_cast
  exact div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero n)

theorem flog_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl]

theorem omega_mul {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) =
      -2 * wq - PowerSeries.X * PowerSeries.derivative ℂ_[p] wq := by
  have hM : PowerSeries.constantCoeff (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
    simp [wq_const' h, h2]
  simp only [omegaW]
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hM, mul_one, dX_eq]

theorem deriv_ext {f g : PowerSeries ℂ_[p]} (hd : PowerSeries.derivative ℂ_[p] f = PowerSeries.derivative ℂ_[p] g)
    (h0 : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) : f = g := by
  ext n
  rcases n with _ | n
  · simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
  · have e := congrArg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at e
    first
    | exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero n) e
    | exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) e

private theorem derivative_subst_eq_subst_derivative_mul (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.HasSubst a) :
    PowerSeries.derivative ℂ_[p] (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative ℂ_[p] f) * PowerSeries.derivative ℂ_[p] a := by
  have hpd : ∀ g : PowerSeries ℂ_[p], MvPowerSeries.pderiv ℂ_[p] () g = PowerSeries.derivative ℂ_[p] g := by
    intro g
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_derivative]
    show MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderiv ℂ_[p] () g) = _
    rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add, Finsupp.single_eq_same]
    rfl
  have := PI.AddIntG.Wk.pderiv_subst (σ := Unit) ha f ()
  rw [hpd, hpd] at this
  exact this

theorem flog_iW {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (iW W wq) (flog W wq) = -flog W wq := by
  have hs := hasSubst_iW W wq
  have hφ : ∀ f : PowerSeries ℂ_[p], PowerSeries.subst (iW W wq) f = PowerSeries.substAlgHom hs f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries ℂ_[p]) = iW W wq := by
    rw [← hφ, PowerSeries.subst_X hs]
  apply deriv_ext
  · have hwi := wq_iW h
    have e := iW_mul_D W wq
    have hD0 : Dser W wq = 1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq) := rfl
    have hom := omega_mul h
    have hom' := congrArg (PowerSeries.substAlgHom hs) hom
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, AlgHom.commutes, hX] at hom'
    simp only [← hφ] at hom'
    rw [hwi] at hom'
    have hcw := derivative_subst_eq_subst_derivative_mul (iW W wq) wq hs
    rw [hwi] at hcw
    have hdwD : PowerSeries.derivative ℂ_[p] (wq * Dser W wq ^ 2) =
        PowerSeries.derivative ℂ_[p] wq * Dser W wq ^ 2 +
          wq * (2 * Dser W wq * PowerSeries.derivative ℂ_[p] (Dser W wq)) := by
      rw [pow_two, Derivation.leibniz, Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
    have e2 := congrArg (PowerSeries.derivative ℂ_[p]) e
    rw [Derivation.leibniz, map_neg, PowerSeries.derivative_X] at e2
    simp only [smul_eq_mul] at e2
    have hDM : Dser W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
      intro h0
      have h00 := congrArg PowerSeries.constantCoeff h0
      have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
      simp [D_const, wq_const' h, h2] at h00
    rw [derivative_subst_eq_subst_derivative_mul (iW W wq) (flog W wq) hs, derivative_flog', map_neg, derivative_flog']
    have key : (PowerSeries.subst (iW W wq) (omegaW W wq) * PowerSeries.derivative ℂ_[p] (iW W wq) +
        omegaW W wq) * (Dser W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2))) = 0 := by
      linear_combination Dser W wq * hom + PowerSeries.derivative ℂ_[p] (iW W wq) * hom'
        - PowerSeries.derivative ℂ_[p] (iW W wq) * PowerSeries.subst (iW W wq) (omegaW W wq) * wq *
          Dser W wq * (cP W.a₁ + cP W.a₃ * wq * ((iW W wq * Dser W wq) ^ 2 -
            iW W wq * Dser W wq * PowerSeries.X + PowerSeries.X ^ 2)) * e
        - PowerSeries.derivative ℂ_[p] wq * Dser W wq * e
        + 2 * PowerSeries.derivative ℂ_[p] (iW W wq) * PowerSeries.subst (iW W wq) (omegaW W wq) * wq *
          Dser W wq * hD0
        - 2 * wq * Dser W wq * e2 + iW W wq * (hcw - hdwD)
    have h3 := (mul_eq_zero.1 key).resolve_right hDM
    linear_combination h3
  · obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (flog_const W wq)
    rw [map_neg, flog_const, neg_zero, hg, hφ, map_mul, hX, map_mul, iW_const, zero_mul]

theorem iW_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h1 : W.a₁ ∈ S)
    (h3 : W.a₃ ∈ S) (hw : ∀ n, PowerSeries.coeff n wq ∈ S) : ∀ n, PowerSeries.coeff n (iW W wq) ∈ S := by
  have hcP : ∀ x ∈ S, ∀ n, PowerSeries.coeff n (cP x) ∈ S := by
    intro x hx n
    rw [cP, Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_smul, PowerSeries.coeff_one]
    split_ifs
    · rw [smul_eq_mul, mul_one]; exact hx
    · rw [smul_zero]; exact S.zero_mem
  have hXm : (PowerSeries.X : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := serS_unit fun n => by
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have h1m := serS_unit (hcP _ h1)
  have h3m := serS_unit (hcP _ h3)
  have hwm := serS_unit hw
  have hDm : (Dser W wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (SerS S Unit).sub_mem (SerS S Unit).one_mem ((SerS S Unit).add_mem ((SerS S Unit).mul_mem h1m hXm)
      ((SerS S Unit).mul_mem ((SerS S Unit).mul_mem h3m ((SerS S Unit).pow_mem hXm 3)) hwm))
  have hi : (iW W wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (SerS S Unit).mul_mem ((SerS S Unit).neg_mem hXm) (inv_mem_SerS S (D_const W wq) hDm)
  exact serS_unit_iff.1 hi

end PI.FglChordFactor.Wk
end
end

section
noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)

variable {p : ℕ} [Fact p.Prime]

def Pser (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  MvPowerSeries.X 0 ^ 2 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq -
    MvPowerSeries.X 1 ^ 2 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq

theorem cc_psubst {u : MvPowerSeries (Fin 2) ℂ_[p]} (hu : MvPowerSeries.constantCoeff u = 0)
    (g : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (PowerSeries.subst u g) = PowerSeries.constantCoeff g := by
  have hu' : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [PowerSeries.constantCoeff_subst hu', finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, hu, zero_pow hd]

theorem cc_msubst {φ : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hφ : MvPowerSeries.HasSubst φ)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst φ H) = MvPowerSeries.constantCoeff H := by
  rw [MvPowerSeries.constantCoeff_subst hφ, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => φ s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      simp [hφ0, zero_pow hs]
    rw [h0, smul_zero]

theorem subst_pair_formal_add {l ex : PowerSeries ℂ_[p]} (hl0 : PowerSeries.constantCoeff l = 0)
    {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = add l ex u v := by
  have hA : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) l +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [map_add, cc_psubst (MvPowerSeries.constantCoeff_X 0), cc_psubst (MvPowerSeries.constantCoeff_X 1),
        hl0, add_zero])
  unfold PI.FglChordFactor.add PI.FglChordFactor.pt PI.FglChordFactor.lg
  rw [subst_psubst hA hs, ← MvPowerSeries.coe_substAlgHom hs, map_add, MvPowerSeries.coe_substAlgHom,
    subst_pair_first_series hs, subst_pair_second_series hs]

theorem subst_bivariateSeries_difference_pair {l ex : PowerSeries ℂ_[p]} (hl0 : PowerSeries.constantCoeff l = 0)
    {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (sub l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = sub l ex u v := by
  have hA : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) l -
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [map_sub, cc_psubst (MvPowerSeries.constantCoeff_X 0), cc_psubst (MvPowerSeries.constantCoeff_X 1),
        hl0, sub_zero])
  unfold PI.FglChordFactor.sub PI.FglChordFactor.pt PI.FglChordFactor.lg
  rw [subst_psubst hA hs, ← MvPowerSeries.coe_substAlgHom hs, map_sub, MvPowerSeries.coe_substAlgHom,
    subst_pair_first_series hs, subst_pair_second_series hs]

theorem negsub {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {u : MvPowerSeries (Fin 2) ℂ_[p]} (hu : PowerSeries.HasSubst u) :
    PowerSeries.subst (PowerSeries.subst u (iW W wq)) (flog W wq) = -PowerSeries.subst u (flog W wq) := by
  rw [← PowerSeries.subst_comp_subst_apply (hasSubst_iW W wq) hu, flog_iW h,
    ← PowerSeries.coe_substAlgHom hu, map_neg]

theorem mulD_at (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) {u : MvPowerSeries (Fin 2) ℂ_[p]}
    (hu : PowerSeries.HasSubst u) :
    PowerSeries.subst u (iW W wq) * PowerSeries.subst u (Dser W wq) = -u := by
  rw [← PowerSeries.coe_substAlgHom hu, ← map_mul, iW_mul_D, map_neg, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hu]

theorem constantCoeff_inverse_variable (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) = 0 := by
  rw [cc_psubst (MvPowerSeries.constantCoeff_X i) _, iW_const]

private theorem subst_zero_eq_zero_of_constantCoeff_zero {g : PowerSeries ℂ_[p]} (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (0 : MvPowerSeries (Fin 2) ℂ_[p]) g = 0 := by
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries (Fin 2) ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [hq, ← PowerSeries.coe_substAlgHom h0, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X h0,
    zero_mul]

theorem F_at_ia {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) :
    MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)]
      (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = 0 := by
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 0))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [negsub hW (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)), add_neg_cancel, subst_zero_eq_zero_of_constantCoeff_zero hex0]

theorem F'_at_aa {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 0]
      (sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = 0 := by
  rw [subst_bivariateSeries_difference_pair (flog_const W wq) (hasSubst2 (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 0))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [sub_self, subst_zero_eq_zero_of_constantCoeff_zero hex0]

theorem F'_eq {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq) :
    sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) =
      MvPowerSeries.subst ![MvPowerSeries.X 0,
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)]
        (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [negsub hW (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)), sub_eq_add_neg]

theorem P_at_diagonal (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 0] (Pser wq) = 0 := by
  have hs := hasSubst2 (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0) (MvPowerSeries.constantCoeff_X 0)
  unfold Pser
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, map_mul, map_mul, map_pow, map_pow,
    MvPowerSeries.coe_substAlgHom, subst_pair_first_variable hs, subst_pair_second_variable hs, subst_pair_first_series hs, subst_pair_second_series hs, sub_self]

theorem P_at_inverse {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : IsWq W wq) :
    MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)] (Pser wq) = 0 := by
  have hX0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hs := hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 0)
  have hm := mulD_at W wq hX0
  have key : ∀ a i d w : MvPowerSeries (Fin 2) ℂ_[p], i * d = -a → a ^ 2 * w - i ^ 2 * (w * d ^ 2) = 0 := by
    intro a i d w h
    linear_combination (-(i * d - a) * w) * h
  unfold Pser
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, map_mul, map_mul, map_pow, map_pow,
    MvPowerSeries.coe_substAlgHom, subst_pair_first_variable hs, subst_pair_second_variable hs, subst_pair_first_series hs, subst_pair_second_series hs,
    ← PowerSeries.subst_comp_subst_apply (hasSubst_iW W wq) hX0, wq_iW hW,
    ← PowerSeries.coe_substAlgHom hX0, map_mul, map_pow, PowerSeries.coe_substAlgHom]
  exact key _ _ _ _ hm

theorem formal_add_first_zero {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X) :
    MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = MvPowerSeries.X 1 := by
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hl : PowerSeries.HasSubst (flog W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (flog_const W wq)
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (map_zero _) (MvPowerSeries.constantCoeff_X 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [subst_zero_eq_zero_of_constantCoeff_zero (flog_const W wq), zero_add, ← PowerSeries.subst_comp_subst_apply hl hX1, hexl,
    PowerSeries.subst_X hX1]

theorem formal_sub_first_zero {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq)
    (hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X) :
    MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) := by
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hl : PowerSeries.HasSubst (flog W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (flog_const W wq)
  have hi : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_inverse_variable W wq 1)
  rw [subst_bivariateSeries_difference_pair (flog_const W wq) (hasSubst2 (map_zero _) (MvPowerSeries.constantCoeff_X 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [subst_zero_eq_zero_of_constantCoeff_zero (flog_const W wq), zero_sub, ← negsub hW hX1, ← PowerSeries.subst_comp_subst_apply hl hi,
    hexl, PowerSeries.subst_X hi]

end PI.FglChordFactor.Wk
end
end

section
noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS mvsubst_mem_SerS subst_mem_SerS)

theorem main_mv (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p])
    (h1 : IsIntP W.a₁) (h2 : IsIntP W.a₂) (h3 : IsIntP W.a₃) (h4 : IsIntP W.a₄) (h6 : IsIntP W.a₆)
    (hW : IsWq W wq) (hex0 : PowerSeries.constantCoeff ex = 0)
    (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : IntegralMv (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) ℂ_[p])) :
    ∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      MvPowerSeries.X 0 ^ 2 * (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ -
          MvPowerSeries.X 1 ^ 2 * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ =
        add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) *
          sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) * n := by
  obtain ⟨S, hS⟩ := PI.AddIntG.Wk.exists_intS p
  have hwS : ∀ n, PowerSeries.coeff n wq ∈ S :=
    PI.AddIntG.Wk.wq_mem ((hS _).2 h1) ((hS _).2 h2) ((hS _).2 h3) ((hS _).2 h4) ((hS _).2 h6) (isWq_bridge hW)
  have hiS := iW_mem ((hS _).2 h1) ((hS _).2 h3) hwS
  have hl0 := flog_const W wq
  have hl1 : PowerSeries.coeff 1 (flog W wq) = 1 := PI.AddIntG.Wk.coeff_one_flog (isWq_bridge hW)
  have hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X := PI.AddIntG.Wk.subst_left_inv hl0 hl1 hex0 hex
  have hwq0 := wq_const' hW
  have ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have hb0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hia0 := constantCoeff_inverse_variable W wq 0
  have hib0 := constantCoeff_inverse_variable W wq 1
  have haS := X_mem_SerS S 0
  have hbS := X_mem_SerS S 1
  have hiaS : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) ∈ SerS S (Fin 2) :=
    subst_mem_SerS S ha0 haS (serS_unit hiS)
  have hibS : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) ∈ SerS S (Fin 2) :=
    subst_mem_SerS S hb0 hbS (serS_unit hiS)
  have hwaS : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq ∈ SerS S (Fin 2) :=
    subst_mem_SerS S ha0 haS (serS_unit hwS)
  have hwbS : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq ∈ SerS S (Fin 2) :=
    subst_mem_SerS S hb0 hbS (serS_unit hwS)
  have hFS : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) :=
    (mem_SerS S _).2 fun e => (hS _).2 (hF e)
  have hF'S : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := by
    rw [F'_eq hW]
    exact mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simpa using hib0⟩)
      (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using hibS⟩) hFS
  have hPS : Pser wq ∈ SerS S (Fin 2) := by
    rw [Pser]
    exact sub_mem (mul_mem (pow_mem haS 2) hwaS) (mul_mem (pow_mem hbS 2) hwbS)
  have hXS : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ_[p]) ∈ S := by
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have hsX : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PowerSeries.X : PowerSeries ℂ_[p]) =
      MvPowerSeries.X 0 := PowerSeries.subst_X (PowerSeries.HasSubst.X 0)
  have hX0ne : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h0
    simp at this
  have hX1ne : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 1 1)) h0
    simp at this

  obtain ⟨P1, hP1S, hPd⟩ := fact_div PowerSeries.constantCoeff_X hXS hPS (by rw [hsX]; exact P_at_diagonal wq)
  rw [hsX] at hPd
  obtain ⟨U', hU'S, hF'd⟩ := fact_div PowerSeries.constantCoeff_X hXS hF'S (by rw [hsX]; exact F'_at_aa hex0)
  rw [hsX] at hF'd
  obtain ⟨U, hUS, hFd⟩ := fact_div (iW_const W wq) hiS hFS (F_at_ia hW hex0)
  have hs := hasSubst2 ha0 hia0
  have hDa : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq)) = 1 := by
    rw [cc_psubst ha0, D_const]
  have hne : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) - MvPowerSeries.X 0 ≠ 0 := by
    intro h0
    have hiD := mulD_at W wq (PowerSeries.HasSubst.X (S := ℂ_[p]) (0 : Fin 2))
    have h5 : MvPowerSeries.X 0 * (1 + PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p])
        (Dser W wq)) = 0 := by
      linear_combination hiD - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) * h0
    rcases mul_eq_zero.1 h5 with h | h
    · exact hX0ne h
    · have h7 := congrArg MvPowerSeries.constantCoeff h
      rw [map_add, map_one, hDa, map_zero] at h7
      norm_num at h7
  have hP1z : MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)] P1 = 0 := by
    have hz := P_at_inverse hW
    rw [hPd, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_sub hs, subst_pair_first_variable hs, subst_pair_second_variable hs] at hz
    exact (mul_eq_zero.1 hz).resolve_left hne
  obtain ⟨P2, hP2S, hP1d⟩ := fact_div (iW_const W wq) hiS hP1S hP1z

  have hs0 := hasSubst2 (map_zero (MvPowerSeries.constantCoeff (σ := Fin 2) (R := ℂ_[p]))) hb0
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff
      (![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] i) = 0 :=
    Fin.forall_fin_two.2 ⟨by simp, by simpa using hb0⟩
  have e_ia0 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) = 0 := by
    rw [subst_pair_first_series hs0, PowerSeries.subst_zero_of_constantCoeff_zero (iW_const W wq)]
  have hUc : MvPowerSeries.constantCoeff U = 1 := by
    have e := congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hFd
    rw [formal_add_first_zero hexl, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_sub hs0, subst_pair_second_variable hs0, e_ia0, sub_zero] at e
    have e2 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] U = 1 := by
      refine mul_left_cancel₀ hX1ne ?_
      rw [mul_one]; exact e.symm
    rw [← cc_msubst hs0 hφ0 U, e2, map_one]
  have hU'c : MvPowerSeries.constantCoeff U' = -1 := by
    have e := congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hF'd
    rw [formal_sub_first_zero hW hexl, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_sub hs0, subst_pair_second_variable hs0, subst_pair_first_variable hs0,
      sub_zero] at e
    have hiD1 := mulD_at W wq (PowerSeries.HasSubst.X (S := ℂ_[p]) (1 : Fin 2))
    have hDb : MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq)) = 1 := by
      rw [cc_psubst hb0, D_const]
    have h5 : MvPowerSeries.X 1 * (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] U' *
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) + 1) = 0 := by
      linear_combination hiD1 - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) * e
    have h7 := congrArg MvPowerSeries.constantCoeff ((mul_eq_zero.1 h5).resolve_left hX1ne)
    rw [map_add, map_mul, hDb, map_one, map_zero, mul_one, cc_msubst hs0 hφ0 U'] at h7
    linear_combination h7
  have hP2c : MvPowerSeries.constantCoeff P2 = -1 := by
    have hPP : Pser wq = (MvPowerSeries.X 1 - MvPowerSeries.X 0) *
        ((MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) * P2) := by
      rw [hPd, hP1d]
    have e := congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hPP
    rw [Pser] at e
    simp only [MvPowerSeries.subst_sub hs0, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_pow hs0, subst_pair_first_variable hs0,
      subst_pair_second_variable hs0, subst_pair_second_series hs0, e_ia0] at e
    have h5 : MvPowerSeries.X 1 ^ 2 * (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] P2 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 0 := by
      linear_combination -e
    have h7 := congrArg MvPowerSeries.constantCoeff ((mul_eq_zero.1 h5).resolve_left (pow_ne_zero 2 hX1ne))
    rw [map_add, cc_psubst hb0, hwq0, map_zero, cc_msubst hs0 hφ0 P2] at h7
    linear_combination h7

  have hwa0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 1 := by
    rw [cc_psubst ha0, hwq0]
  have hwb0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 1 := by
    rw [cc_psubst hb0, hwq0]
  have hV0 : MvPowerSeries.constantCoeff (-U') = 1 := by rw [map_neg, hU'c, neg_neg]
  have hUi : U * U⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hUc]; exact one_ne_zero)
  have hVi : (-U') * (-U')⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hV0]; exact one_ne_zero)
  have hwa : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq *
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hwa0]; exact one_ne_zero)
  have hwb : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq *
      (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hwb0]; exact one_ne_zero)
  have hnS : -(P2 * U⁻¹ * (-U')⁻¹) * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
      (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ ∈ SerS S (Fin 2) :=
    mul_mem (mul_mem (neg_mem (mul_mem (mul_mem hP2S (inv_mem_SerS S hUc hUS)) (inv_mem_SerS S hV0 (neg_mem hU'S))))
      (inv_mem_SerS S hwa0 hwaS)) (inv_mem_SerS S hwb0 hwbS)
  refine ⟨-(P2 * U⁻¹ * (-U')⁻¹) * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
      (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹, ?_, ?_, ?_⟩
  · intro e
    exact (hS _).1 ((mem_SerS S _).1 hnS e)
  · simp only [map_mul, map_neg, MvPowerSeries.constantCoeff_inv, hP2c, hUc, hU'c, hwa0, hwb0]
    norm_num
  · have hPd' : MvPowerSeries.X 0 ^ 2 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq -
        MvPowerSeries.X 1 ^ 2 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq =
        (MvPowerSeries.X 1 - MvPowerSeries.X 0) * P1 := hPd
    rw [hFd, hF'd]
    linear_combination
      (-(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hwa +
      ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 *
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hwb +
      ((PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hPd' +
      ((PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (MvPowerSeries.X 1 - MvPowerSeries.X 0)) * hP1d -
      ((MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) *
        (MvPowerSeries.X 1 - MvPowerSeries.X 0) * P2 *
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hUi -
      ((MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) *
        (MvPowerSeries.X 1 - MvPowerSeries.X 0) * P2 *
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ * U * U⁻¹) * hVi

theorem formal_group_chord_factor : PI.FglChordFactor.Lemma := by
  intro p _ W wq ex h1 h2 h3 h4 h6 _ hW hex0 hex hF
  exact main_mv p W wq ex h1 h2 h3 h4 h6 hW hex0 hex hF

end PI.FglChordFactor.Wk
end
end
