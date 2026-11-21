import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.IntegralityIffAwayAtD

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Pd

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

theorem pd_eq (inst : DecidableEq σ) (k : σ) (F : MvPowerSeries σ ℂ_[p]) :
    @pd σ inst ℂ_[p] _ k F = MvPowerSeries.pderiv ℂ_[p] k F := by
  ext n
  rw [MvPowerSeries.coeff_pderiv, mul_comm]
  rfl

theorem pderiv_comm (i j : σ) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.pderiv ℂ_[p] i (MvPowerSeries.pderiv ℂ_[p] j F) =
      MvPowerSeries.pderiv ℂ_[p] j (MvPowerSeries.pderiv ℂ_[p] i F) := by
  ext n
  simp only [MvPowerSeries.coeff_pderiv, Finsupp.add_apply]
  rw [add_right_comm n (Finsupp.single j 1) (Finsupp.single i 1)]
  by_cases h : i = j
  · subst h
    rfl
  · simp only [Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), add_zero]
    ring

theorem pderiv_C_mul (k : σ) (c : ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.pderiv ℂ_[p] k (algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c * F) =
      algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c * MvPowerSeries.pderiv ℂ_[p] k F := by
  rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, smul_eq_mul]

end Pd

section Der

variable {D : D7} {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

local notation "Ser" => MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]

theorem der_eq (y : Matrix (Fin N') (Fin N) D.host.E) (F : Ser) :
    der D lam y F = ∑ k : D.what₂.Tau × Fin N' × Fin N,
      algebraMap ℂ_[p] Ser (lamC lam (embT D k.1 (y k.2.1 k.2.2))) * MvPowerSeries.pderiv ℂ_[p] k F := by
  simp only [der, pd_eq]

theorem der_add (y : Matrix (Fin N') (Fin N) D.host.E) (F G : Ser) :
    der D lam y (F + G) = der D lam y F + der D lam y G := by
  simp only [der_eq, map_add, mul_add, Finset.sum_add_distrib]

theorem der_zero (y : Matrix (Fin N') (Fin N) D.host.E) : der D lam y (0 : Ser) = 0 := by
  simp only [der_eq, map_zero, mul_zero, Finset.sum_const_zero]

theorem der_mul (y : Matrix (Fin N') (Fin N) D.host.E) (F G : Ser) :
    der D lam y (F * G) = F * der D lam y G + G * der D lam y F := by
  rw [der_eq, der_eq, der_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem der_C (y : Matrix (Fin N') (Fin N) D.host.E) (c : ℂ_[p]) :
    der D lam y (algebraMap ℂ_[p] Ser c) = 0 := by
  simp only [der_eq, Derivation.map_algebraMap, mul_zero, Finset.sum_const_zero]

theorem der_comm (a b : Matrix (Fin N') (Fin N) D.host.E) (F : Ser) :
    der D lam a (der D lam b F) = der D lam b (der D lam a F) := by
  simp only [der_eq, map_sum, pderiv_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [pderiv_comm]
  ring

def Dl (l : List (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) : Ser :=
  l.foldr (fun y' G => der D lam y' G) F


theorem Dl_cons (a : Matrix (Fin N') (Fin N) D.host.E) (l : List (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) :
    Dl lam (a :: l) F = der D lam a (Dl lam l F) := rfl





theorem jetsInt_iff (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) :
    JetsInt D lam Y F ↔ ∀ l : List (Matrix (Fin N') (Fin N) D.host.E), (∀ y ∈ l, y ∈ Y) →
      IsIntP (MvPowerSeries.constantCoeff (Dl lam l F)) := by
  constructor
  · intro h l hl
    have h1 := h l.length l.get (fun i => hl _ (by simp))
    rw [List.ofFn_get] at h1
    exact h1
  · intro h n y hy
    refine h (List.ofFn y) (fun z hz => ?_)
    rw [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact hy i

variable {lam}


theorem isPadicIntegral_add {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x + y) :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)






end Der


end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Int

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

theorem isPadicIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) (h : ∀ i ∈ s, IsIntP (f i)) :
    IsIntP (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold IsIntP; simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isPadicIntegral_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isPadicIntegral_mul {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x * y) := by
  unfold IsIntP at *
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem integralMv_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  classical
  rw [MvPowerSeries.coeff_mul]
  exact isPadicIntegral_sum _ _ fun x _ => isPadicIntegral_mul (hF _) (hG _)

theorem integralMv_C {c : ℂ_[p]} (hc : IsIntP c) :
    IntegralMv (algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c) := fun n => by
  classical
  have e : MvPowerSeries.coeff n (algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c) = if n = 0 then c else 0 := by
    first
      | exact MvPowerSeries.coeff_C n c
      | exact MvPowerSeries.coeff_C (σ := σ) n c
      | (rw [MvPowerSeries.algebraMap_apply']; exact MvPowerSeries.coeff_C n c)
      | simp [MvPowerSeries.coeff_C]
      | simp [MvPowerSeries.coeff_C, MvPowerSeries.algebraMap_apply']
  rw [e]
  split_ifs
  · exact hc
  · unfold IsIntP; simp

end Int

section Subst

variable {p : ℕ} [Fact p.Prime]

theorem cc_psubst' {ι : Type*} {a : MvPowerSeries ι ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]

theorem cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl]

variable {D : D7} {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def atLogA : D.what₂.Tau × Fin N' × Fin N → MvPowerSeries (Fin r) ℂ_[p] :=
  fun k => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)

theorem atLogA_hasSubst : MvPowerSeries.HasSubst (atLogA lam Λ C wq b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro k
  simp only [atLogA, map_sum, map_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cc_psubst' (MvPowerSeries.constantCoeff_X i) (cc_flog _ wq), mul_zero]

theorem atLog_eq (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b F = MvPowerSeries.substAlgHom (atLogA_hasSubst lam Λ C wq b) F := by
  rw [MvPowerSeries.coe_substAlgHom]; rfl

end Subst

section Clauses

variable {D : D7} (T : Tor D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
  (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))

end Clauses

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
end
end
