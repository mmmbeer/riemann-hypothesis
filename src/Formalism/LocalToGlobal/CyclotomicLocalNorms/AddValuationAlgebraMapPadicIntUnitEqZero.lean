import Mathlib
import Formalism.LocalToGlobal.CyclotomicLocalNorms.NormSubToZModPowVal
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

section
noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped Classical

variable {l : ℕ} [Fact l.Prime]

theorem one_lt_l : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt

theorem exists_rat_norm {x : Om l} (hx : x ≠ 0) : ∃ q : ℚ, ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have h : ‖x‖ = ‖(minpoly ℚ_[l] x).coeff 0‖ ^ (1 / (minpoly ℚ_[l] x).natDegree : ℝ) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) x
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn : ((minpoly ℚ_[l] x).natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (minpoly.natDegree_pos hi).ne'
  refine ⟨((minpoly ℚ_[l] x).coeff 0).valuation / (minpoly ℚ_[l] x).natDegree, ?_⟩
  rw [h, Padic.norm_eq_zpow_neg_valuation h0, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  field_simp

def vq (x : Om l) : ℚ := if h : x = 0 then 0 else (exists_rat_norm h).choose

theorem norm_eq_rpow {x : Om l} (hx : x ≠ 0) : ‖x‖ = (l : ℝ) ^ (-(vq x : ℝ)) := by
  rw [vq, dif_neg hx]
  exact (exists_rat_norm hx).choose_spec

theorem vq_le_iff {x y : Om l} (hx : x ≠ 0) (hy : y ≠ 0) : vq x ≤ vq y ↔ ‖y‖ ≤ ‖x‖ := by
  rw [norm_eq_rpow hx, norm_eq_rpow hy, Real.rpow_le_rpow_left_iff one_lt_l, neg_le_neg_iff]
  exact_mod_cast Iff.rfl

theorem vq_eq_of_norm {x : Om l} {q : ℚ} (h : ‖x‖ = (l : ℝ) ^ (-(q : ℝ))) : vq x = q := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact (Real.rpow_pos_of_pos (by linarith [one_lt_l (l := l)]) _).ne h
  rw [norm_eq_rpow hx] at h
  have := (Real.rpow_right_inj (by linarith [one_lt_l (l := l)]) (one_lt_l (l := l)).ne').1 h
  exact_mod_cast neg_injective this

theorem vq_mul {x y : Om l} (hx : x ≠ 0) (hy : y ≠ 0) : vq (x * y) = vq x + vq y := by
  apply vq_eq_of_norm
  rw [norm_mul, norm_eq_rpow hx, norm_eq_rpow hy, ← Real.rpow_add (by linarith [one_lt_l (l := l)])]
  congr 1
  push_cast
  ring

def vfun (x : Om l) : WithTop ℚ := if x = 0 then ⊤ else (vq x : WithTop ℚ)

theorem vfun_zero : vfun (0 : Om l) = ⊤ := if_pos rfl

theorem vfun_of_ne {x : Om l} (hx : x ≠ 0) : vfun x = (vq x : WithTop ℚ) := if_neg hx

variable (l) in

def vΩ : AddValuation (Om l) (WithTop ℚ) :=
  AddValuation.of vfun vfun_zero
    (by
      rw [vfun_of_ne one_ne_zero]
      have : vq (1 : Om l) = 0 := vq_eq_of_norm (by simp)
      rw [this]; rfl)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · rw [hxy, vfun_zero]; exact le_top
      rw [vfun_of_ne hx, vfun_of_ne hy, vfun_of_ne hxy, ← WithTop.coe_min, WithTop.coe_le_coe,
        min_le_iff, vq_le_iff hx hxy, vq_le_iff hy hxy]
      exact le_max_iff.1 (PadicAlgCl.isNonarchimedean l x y))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx, vfun_zero]
      by_cases hy : y = 0
      · simp [hy, vfun_zero]
      rw [vfun_of_ne hx, vfun_of_ne hy, vfun_of_ne (mul_ne_zero hx hy), vq_mul hx hy]
      rfl)

theorem vΩ_apply (x : Om l) : vΩ l x = vfun x := rfl

theorem vΩ_of_ne {x : Om l} (hx : x ≠ 0) : vΩ l x = (vq x : WithTop ℚ) := vfun_of_ne hx

theorem le_vΩ_iff (q : ℚ) (x : Om l) : (q : WithTop ℚ) ≤ vΩ l x ↔ ‖x‖ ≤ (l : ℝ) ^ (-(q : ℝ)) := by
  by_cases hx : x = 0
  · subst hx
    rw [vΩ_apply, vfun_zero, norm_zero]
    exact ⟨fun _ => (Real.rpow_pos_of_pos (by linarith [one_lt_l (l := l)]) _).le, fun _ => le_top⟩
  · rw [vΩ_of_ne hx, WithTop.coe_le_coe, norm_eq_rpow hx, Real.rpow_le_rpow_left_iff one_lt_l,
      neg_le_neg_iff]
    exact_mod_cast Iff.rfl

theorem vΩ_eq_iff (q : ℚ) (x : Om l) : vΩ l x = (q : WithTop ℚ) ↔ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  constructor
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [vΩ_apply, vfun_zero] at h
      exact WithTop.top_ne_coe h
    rw [vΩ_of_ne hx, WithTop.coe_inj] at h
    rw [norm_eq_rpow hx, h]
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at h
      exact (Real.rpow_pos_of_pos (by linarith [one_lt_l (l := l)]) _).ne h
    rw [vΩ_of_ne hx, vq_eq_of_norm h]

theorem norm_l : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem vΩ_l : vΩ l ((l : ℕ) : Om l) = 1 := by
  have : vΩ l ((l : ℕ) : Om l) = ((1 : ℚ) : WithTop ℚ) := by
    rw [vΩ_eq_iff, norm_l]
    simp [Real.rpow_neg_one]
  rw [this]; rfl

theorem zero_le_vΩ_iff (x : Om l) : 0 ≤ vΩ l x ↔ ‖x‖ ≤ 1 := by
  have := le_vΩ_iff 0 x
  simpa using this

variable (l) in

def v (LL : FinExt l) : AddValuation ↥LL.1 (WithTop ℚ) := (vΩ l).comap (algebraMap ↥LL.1 (Om l))

instance towZLL (LL : IntermediateField ℚ_[l] (Om l)) : IsScalarTower ℤ_[l] ↥LL (Om l) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Formalism.L2.LocGap.Gal
end
end

section
noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups

variable {l : ℕ} [Fact l.Prime]

abbrev Q0 (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (Om l) := ⊥

theorem finiteDimensional_Q0_alt : FiniteDimensional ℚ_[l] (Q0 l) := inferInstance

def ofGQ (g : GQ l) : Neutral.B1.GK l (Q0 l) :=
  { g.toRingEquiv with
    commutes' := fun r => by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 r.2
      change g (r : Om l) = r
      rw [← ha]
      exact g.commutes a }

theorem qK_bot : LocalClassField.qK l (Q0 l) = l := by
  obtain ⟨f, hf, hq⟩ := LocalClassField.qK_eq_pow l (Q0 l) finiteDimensional_Q0_alt
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hle : LocalClassField.qK l (Q0 l) ≤ l := by
    have hs : Function.Surjective (fun n : Fin l =>
        (⟨((n : ℕ) : LocalClassField.kbar l), natCast_mem _ _⟩ : LocalClassField.resK l (Q0 l))) := by
      rintro ⟨c, hc⟩
      obtain ⟨x, hx, rfl⟩ := (LocalClassField.mem_resK_iff l (Q0 l) c).1 hc
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hx
      have ha1 : ‖a‖ ≤ 1 := by
        rw [← PadicAlgCl.norm_extends, show ((a : ℚ_[l]) : Om l) = (x : Om l) from ha]
        exact LocalClassField.mem_Obar_iff.1 x.2
      set A : ℤ_[l] := ⟨a, ha1⟩ with hA
      obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range A
      refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
      change ((n : ℕ) : LocalClassField.kbar l) = _
      rw [← map_natCast (IsLocalRing.residue (LocalClassField.Obar l)) n, eq_comm, LocalClassField.residue_eq_iff]
      have h2 : ‖A - (n : ℤ_[l])‖ < 1 := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PadicInt.not_isUnit_iff] at hmem
      have h3 : ((x : LocalClassField.Obar l) : Om l) - (((n : ℕ) : LocalClassField.Obar l) : Om l)
          = algebraMap ℚ_[l] (Om l) (a - (n : ℚ_[l])) := by
        rw [map_sub, ha, map_natCast]
        rfl
      rw [h3]
      have h4 := PadicAlgCl.norm_extends (p := l) (a - (n : ℚ_[l]))
      rw [show ((a - (n : ℚ_[l]) : ℚ_[l]) : Om l) = algebraMap ℚ_[l] (Om l) (a - (n : ℚ_[l])) from rfl] at h4
      rw [h4]
      rw [PadicInt.norm_def] at h2
      push_cast at h2
      exact h2
    have := Nat.card_le_card_of_surjective _ hs
    exact this.trans_eq ((Nat.card_eq_fintype_card (α := Fin l)).trans (Fintype.card_fin l))
  rw [hq] at hle ⊢
  have : f ≤ 1 := by
    by_contra hcon
    have h2 : l ^ 2 ≤ l ^ f := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have hf1 : f = 1 := by omega
  rw [hf1, pow_one]

theorem Kur_eq : LocalClassField.MaximalUnramifiedExtension l (Q0 l) = MaximalUnramifiedExtension l := by
  rw [LocalClassField.Kur_eq finiteDimensional_Q0_alt, bot_sup_eq, MaximalUnramifiedExtension]
  congr 1
  ext x
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l)), hm, hx⟩
  · rintro ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩

variable (l) in

def FrobQ : GQ l := (LocalClassField.frobK l (Q0 l)).restrictScalars ℚ_[l]

theorem FrobQ_apply (x : Om l) : FrobQ l x = LocalClassField.frobK l (Q0 l) x := rfl

theorem FrobQ_pow_apply (i : ℕ) (x : Om l) : (FrobQ l ^ i) x = (LocalClassField.frobK l (Q0 l) ^ i) x := by
  induction i generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, FrobQ_apply]

theorem FrobQ_spec (x : Om l) (hx : ‖x‖ ≤ 1) : ‖FrobQ l x - x ^ l‖ < 1 := by
  have := LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l)) x hx
  rwa [qK_bot] at this


section Fin

variable {F : IntermediateField ℚ_[l] (Om l)}

theorem norm_Kur {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : ∃ a : ℚ_[l], ‖x‖ = ‖a‖ := by
  rw [← Kur_eq] at hx
  obtain ⟨n, hn, hxn⟩ := (LocalClassField.mem_Kur_iff finiteDimensional_Q0_alt x).1 hx
  obtain ⟨y, hy, h⟩ := LocalClassField.norm_Kn l (Q0 l) finiteDimensional_Q0_alt hn hxn
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hy
  exact ⟨a, h.trans (PadicAlgCl.norm_extends l a)⟩

theorem eq_Kn (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) :
    F = LocalClassField.Kn l (Q0 l) (Module.finrank ℚ_[l] F) := by
  refine LocalClassField.eq_Kn_of_norm l (Q0 l) finiteDimensional_Q0_alt bot_le Module.finrank_pos ?_ ?_
  · rw [IntermediateField.finrank_bot, mul_one]
  · intro x hx
    obtain ⟨a, ha⟩ := norm_Kur (hle hx)
    exact ⟨algebraMap ℚ_[l] (Om l) a, IntermediateField.algebraMap_mem _ a,
      ha.trans (PadicAlgCl.norm_extends l a).symm⟩

theorem map_mem (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (g : GQ l) {x : Om l}
    (hx : x ∈ F) : g x ∈ F := by
  rw [eq_Kn hF hle] at hx ⊢
  exact LocalClassField.map_mem_Kn l (Q0 l) _ (ofGQ g) hx

theorem normal_of_le_Kur (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) : Normal ℚ_[l] F := by
  rw [IntermediateField.normal_iff_forall_map_le']
  rintro g _ ⟨x, hx, rfl⟩
  exact map_mem hF hle g hx

theorem exists_GQ_of_algHom (τ : F →ₐ[ℚ_[l]] Om l) : ∃ g : GQ l, ∀ x : F, g x = τ x := by
  refine ⟨AlgEquiv.ofBijective (τ.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _), ?_⟩
  intro x
  exact τ.liftNormal_commutes (Om l) x

theorem exists_pow_of_GQ (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (g : GQ l) :
    ∃ i < Module.finrank ℚ_[l] F, ∀ x ∈ F, g x = (FrobQ l ^ i) x := by
  obtain ⟨i, hi, h⟩ := LocalClassField.IsFrobOn.exists_pow l (Q0 l) finiteDimensional_Q0_alt (Module.finrank_pos (R := ℚ_[l]) (M := F))
    ((LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l))).isFrobOn _) (ofGQ g)
  refine ⟨i, hi, fun x hx => ?_⟩
  rw [FrobQ_pow_apply, ← h x (by rwa [← eq_Kn hF hle])]
  rfl

theorem pow_fixes_iff (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (i : ℕ) :
    (∀ x ∈ F, (FrobQ l ^ i) x = x) ↔ Module.finrank ℚ_[l] F ∣ i := by
  rw [← LocalClassField.IsFrobOn.pow_fixes_iff l (Q0 l) finiteDimensional_Q0_alt (Module.finrank_pos (R := ℚ_[l]) (M := F))
    ((LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l))).isFrobOn _) i, ← eq_Kn hF hle]
  simp only [FrobQ_pow_apply]

theorem eq_FrobQ_of_congr (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (g : GQ l)
    (hg : ∀ x ∈ F, ‖x‖ ≤ 1 → ‖g x - x ^ l‖ < 1) {x : Om l} (hx : x ∈ F) : g x = FrobQ l x := by
  have h1 : LocalClassField.IsFrobOn l (Q0 l) (Module.finrank ℚ_[l] F) (ofGQ g) := by
    intro y hy hy1
    rw [← eq_Kn hF hle] at hy
    rw [qK_bot]
    exact hg y hy hy1
  exact LocalClassField.IsFrobOn.eqOn l (Q0 l) finiteDimensional_Q0_alt (Module.finrank_pos (R := ℚ_[l]) (M := F)) h1
    ((LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l))).isFrobOn _) (by rwa [← eq_Kn hF hle])

end Fin

theorem mem_bot_of_FrobQ_fixed {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h : FrobQ l x = x) : x ∈ Q0 l := by
  rw [← Kur_eq] at hx
  exact LocalClassField.mem_of_frobK_fixed finiteDimensional_Q0_alt hx h

end Formalism.L2.LocGap.Gal
end
end

section
noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups

variable {l : ℕ} [Fact l.Prime]

theorem unramified_subfield_le_maxUnramified (K : FinExt l) : K0 K ≤ MaximalUnramifiedExtension l := inf_le_right

instance finiteDimensional_unramified_subfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : K0 K ≤ K.1 := inf_le_left
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

instance normal_unramified_subfield (K : FinExt l) : Normal ℚ_[l] ↥(K0 K) :=
  normal_of_le_Kur (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K)

instance neZero_finrank_maxUnramifiedSubfield (K : FinExt l) : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) :=
  ⟨Module.finrank_pos.ne'⟩

def σE (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) := (FrobQ l).restrictNormal ↥(K0 K)

def σ (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) := (σE K : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))

theorem σ_apply (K : FinExt l) (x : ↥(K0 K)) : σ K x = σE K x := rfl

theorem σ_bij (K : FinExt l) : Function.Bijective (σ K) := (σE K).bijective

theorem σE_pow_coe (K : FinExt l) (i : ℕ) (x : ↥(K0 K)) :
    (((σE K ^ i) x : ↥(K0 K)) : Om l) = (FrobQ l ^ i) (x : Om l) := by
  have h : σE K ^ i = (FrobQ l ^ i).restrictNormal ↥(K0 K) :=
    (map_pow (AlgEquiv.restrictNormalHom (K₁ := Om l) ↥(K0 K)) (FrobQ l) i).symm
  rw [h]
  exact AlgEquiv.restrictNormal_commutes (FrobQ l ^ i) ↥(K0 K) x

theorem σ_coe (K : FinExt l) (x : ↥(K0 K)) : ((σ K x : ↥(K0 K)) : Om l) = FrobQ l (x : Om l) := by
  have := σE_pow_coe K 1 x
  rwa [pow_one, pow_one] at this

theorem PD_σ (K : FinExt l) (x : ↥(K0 K)) (hx : ‖((x : ↥(K0 K)) : Om l)‖ ≤ 1) :
    ‖(((σ K x : ↥(K0 K))) : Om l) - ((x : ↥(K0 K)) : Om l) ^ l‖ < 1 := by
  rw [σ_coe]
  exact FrobQ_spec _ hx

theorem σE_pow_eq_one_iff (K : FinExt l) (i : ℕ) :
    σE K ^ i = 1 ↔ Module.finrank ℚ_[l] ↥(K0 K) ∣ i := by
  rw [← pow_fixes_iff (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) i]
  constructor
  · intro h x hx
    have := σE_pow_coe K i ⟨x, hx⟩
    rw [h] at this
    exact this.symm
  · intro h
    ext x
    rw [σE_pow_coe]
    exact h x x.2

theorem orderOf_σE (K : FinExt l) : orderOf (σE K) = Module.finrank ℚ_[l] ↥(K0 K) := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((σE_pow_eq_one_iff K _).2 dvd_rfl)
  · exact (σE_pow_eq_one_iff K _).1 (pow_orderOf_eq_one _)

theorem exists_pow_σE (K : FinExt l) (τ : ↥(K0 K) →ₐ[ℚ_[l]] Om l) :
    ∃ i < Module.finrank ℚ_[l] ↥(K0 K), ∀ x, τ x = (((σE K ^ i) x : ↥(K0 K)) : Om l) := by
  obtain ⟨g, hg⟩ := exists_GQ_of_algHom τ
  obtain ⟨i, hi, h⟩ := exists_pow_of_GQ (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) g
  exact ⟨i, hi, fun x => by rw [← hg, σE_pow_coe, h x x.2]⟩

theorem σ_fixed (K : FinExt l) (x : ↥(K0 K)) (h : σ K x = x) :
    ∃ a : ℚ_[l], algebraMap ℚ_[l] ↥(K0 K) a = x := by
  have h1 : FrobQ l (x : Om l) = x := by rw [← σ_coe, h]
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 (mem_bot_of_FrobQ_fixed (unramified_subfield_le_maxUnramified K x.2) h1)
  exact ⟨a, Subtype.ext ha⟩

theorem eq_σ_of_congr (K : FinExt l) (τ : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))
    (hτ : ∀ x : ↥(K0 K), ‖((x : ↥(K0 K)) : Om l)‖ ≤ 1 →
      ‖(((τ x : ↥(K0 K))) : Om l) - ((x : ↥(K0 K)) : Om l) ^ l‖ < 1) : τ = σ K := by
  obtain ⟨g, hg⟩ := exists_GQ_of_algHom ((K0 K).val.comp τ)
  have h1 : ∀ y ∈ K0 K, ‖y‖ ≤ 1 → ‖g y - y ^ l‖ < 1 := by
    intro y hy hy1
    have := hτ ⟨y, hy⟩ hy1
    have h2 : g y = ((τ ⟨y, hy⟩ : ↥(K0 K)) : Om l) := hg ⟨y, hy⟩
    rw [h2]
    exact this
  ext x
  rw [σ_coe, ← eq_FrobQ_of_congr (finiteDimensional_unramified_subfield K) (unramified_subfield_le_maxUnramified K) g h1 x.2]
  exact (hg x).symm

def emb {K LL : FinExt l} (hle : K0 K ≤ LL.1) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  (IntermediateField.inclusion hle).comp ((σE K ^ (-i).val : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K)) :
    ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K))

theorem emb_coe {K LL : FinExt l} (hle : K0 K ≤ LL.1) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (x : ↥(K0 K)) : ((emb hle i x : ↥LL.1) : Om l) = (((σE K ^ (-i).val) x : ↥(K0 K)) : Om l) := rfl

theorem σE_pow_val_eq {K : FinExt l} {a b : ℕ}
    (h : (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) = (b : ZMod _)) : σE K ^ a = σE K ^ b := by
  rw [pow_eq_pow_iff_modEq, orderOf_σE]
  exact (ZMod.natCast_eq_natCast_iff a b _).1 h

theorem emb_σ {K LL : FinExt l} (hle : K0 K ≤ LL.1) (τ : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K)) (hτ : τ = σ K)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) : (emb hle (i + 1)).comp τ = emb hle i := by
  subst hτ
  have h : σE K ^ (-(i + 1)).val * σE K = σE K ^ (-i).val := by
    rw [← pow_succ]
    apply σE_pow_val_eq
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  ext x
  rw [AlgHom.comp_apply, emb_coe, emb_coe, ← h]
  rfl

end Formalism.L2.LocGap.Gal
end
end

section
noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Filter Topology
open scoped Classical

variable {l : ℕ} [Fact l.Prime]

theorem modEq_of_pow_eq {k : ℕ} (hk : 0 < k) {ζ : Om l} (hz : IsPrimitiveRoot ζ k) {a b : ℕ}
    (h : ζ ^ a = ζ ^ b) : a ≡ b [MOD k] := by
  obtain ⟨U, rfl⟩ := hz.isUnit hk.ne'
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
    pow_eq_pow_iff_modEq, ← orderOf_units, ← hz.eq_orderOf] at h
  exact h

theorem norm_χZ_sub_le (g : GQ l) (k c : ℕ) (h : ∀ z : Om l, z ^ (l ^ k) = 1 → g z = z ^ c) :
    ‖((χZ l g : ℤ_[l]ˣ) : ℤ_[l]) - (c : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz := ζQ_primitive l k
  have h1 := χZ_spec g k (ζQ l k) hz.pow_eq_one
  rw [h _ hz.pow_eq_one] at h1
  have h2 := modEq_of_pow_eq (pow_pos (Fact.out : l.Prime).pos k) hz h1
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at h2
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_natCast, ← h2, sub_self]

theorem eq_of_norm_sub_le {x y : ℚ_[l]} (h : ∀ m : ℕ, ‖x - y‖ ≤ (l : ℝ) ^ (-(m : ℤ))) : x = y := by
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hpos
  exact absurd (h k) (not_le.2 hk)

theorem eq_χQ_of_cyc (χ' : GQ l →* ℚ_[l]ˣ)
    (h : ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
      ∃ a : ℕ, ‖(χ' g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a) :
    χ' = χQ l := by
  refine MonoidHom.ext fun g => Units.ext ?_
  apply eq_of_norm_sub_le
  intro m
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz := ζQ_primitive l m
  obtain ⟨a, ha, hga⟩ := h g m (ζQ l m) hz.pow_eq_one
  have h1 := norm_χZ_sub_le g m a (fun z hz' => by
    obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hz'
    rw [map_pow, hga, ← pow_mul, ← pow_mul, mul_comm])
  have h2 : ‖(χQ l g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    rw [χQ_coe]
    rw [PadicInt.norm_def] at h1
    push_cast at h1
    exact h1
  have h3 : (χ' g : ℚ_[l]) - (χQ l g : ℚ_[l]) =
      ((χ' g : ℚ_[l]) - (a : ℚ_[l])) - ((χQ l g : ℚ_[l]) - (a : ℚ_[l])) := by ring
  rw [h3, sub_eq_add_neg]
  refine (Padic.nonarchimedean _ _).trans ?_
  rw [norm_neg]
  exact max_le ha h2

theorem χQ_cyc_of (χ' : GQ l →* ℚ_[l]ˣ)
    (h : ∀ g : GQ l, (χ' g : ℚ_[l]) = ((cyclotomicCharacter (Om l) l g.toRingEquiv : ℤ_[l]) : ℚ_[l]))
    (g : GQ l) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    ∃ a : ℕ, ‖(χ' g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a := by
  rw [h g]
  exact χQ_cyc g m ζ hζ

section W

variable {LL : FinExt l}

end W

end Formalism.L2.LocGap.Gal
end
end
