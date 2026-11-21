import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

noncomputable section

namespace GlobalTheory.Cyc.Model

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

variable {l : ℕ} [Fact l.Prime]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isom_gal (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Isometry (g : _root_.Formalism.BasicNotions.Loc.Om l →+* _root_.Formalism.BasicNotions.Loc.Om l) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x => ?_
  change spectralNorm ℚ_[l] (PadicAlgCl l) (g x) = spectralNorm ℚ_[l] (PadicAlgCl l) x
  exact (spectralNorm_eq_of_equiv g x).symm

def extHom (g : GQ l) : PadicComplex l →+* PadicComplex l :=
  UniformSpace.Completion.mapRingHom (g : Om l →+* Om l) (isom_gal g).continuous

theorem extHom_coe (g : GQ l) (x : Om l) : extHom g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem extHom_cont (g : GQ l) : Continuous (extHom g) := UniformSpace.Completion.continuous_map

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem continuous_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Continuous (_root_.GlobalTheory.Cyc.Model.extHom g) :=
  UniformSpace.Completion.continuous_extension

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem cyc_extHom_coe (g : _root_.Formalism.BasicNotions.Loc.GQ l) (x : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Cyc.Model.extHom g (x : PadicComplex l) = ((g x : _root_.Formalism.BasicNotions.Loc.Om l) : PadicComplex l) := by
  simp only [_root_.GlobalTheory.Cyc.Model.extHom, UniformSpace.Completion.mapRingHom]
  rw [UniformSpace.Completion.extensionHom_coe]; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_mul (g h : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (g * h) y =
      _root_.GlobalTheory.Cyc.Model.extHom g (_root_.GlobalTheory.Cyc.Model.extHom h y) := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (continuous_cyc_extHom _)
    ((continuous_cyc_extHom g).comp (continuous_cyc_extHom h))) fun x => ?_
  rw [cyc_extHom_coe, cyc_extHom_coe, cyc_extHom_coe]; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_one (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (1 : _root_.Formalism.BasicNotions.Loc.GQ l) y = y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_cyc_extHom _) continuous_id) fun x => ?_
  rw [cyc_extHom_coe]; rfl

def actC : GQ l →* (PadicComplex l ≃+* PadicComplex l) where
  toFun g := { extHom g with
    invFun := extHom g⁻¹
    left_inv := fun y => by
      change extHom g⁻¹ (extHom g y) = y
      rw [← extHom_mul, inv_mul_cancel, extHom_one]
    right_inv := fun y => by
      change extHom g (extHom g⁻¹ y) = y
      rw [← extHom_mul, mul_inv_cancel, extHom_one] }
  map_one' := by ext y; exact extHom_one y
  map_mul' g h := by ext y; exact extHom_mul g h y

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem norm_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    ‖_root_.GlobalTheory.Cyc.Model.extHom g y‖ = ‖y‖ := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_norm.comp (continuous_cyc_extHom g)) continuous_norm) fun x => ?_
  rw [cyc_extHom_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact (_root_.GlobalTheory.Cyc.Model.isom_gal g).norm_map_of_map_zero (map_zero _) x

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isActC_actC :
    _root_.GlobalTheory.Cyc.IsActC (_root_.GlobalTheory.Cyc.Model.actC (l := l)) :=
  ⟨fun g x => cyc_extHom_coe g x, fun g y => norm_cyc_extHom g y⟩

def chiZ : GQ l →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l))

def chi : GQ l →* ℚ_[l]ˣ :=
  (Units.map (algebraMap ℤ_[l] ℚ_[l]).toMonoidHom).comp chiZ

theorem chi_val (g : GQ l) : (chi g : ℚ_[l]) = ((chiZ g : ℤ_[l]) : ℚ_[l]) := rfl

theorem chi_cont : Continuous fun g : GQ l => (chi g : ℚ_[l]) :=
  (continuous_subtype_val : Continuous fun x : ℤ_[l] => (x : ℚ_[l])).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (cyclotomicCharacter.continuous l ℚ_[l] (Om l)))

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.cyc_irred (n : ℕ) :
    Irreducible (cyclotomic (l ^ (n + 1)) ℚ_[l]) := by
  have hP : (Ideal.span {(l : ℤ_[l])}).IsPrime :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  have hnu : ¬ IsUnit (l : ℤ_[l]) := fun h => hP.ne_top (Ideal.span_singleton_eq_top.2 h)
  have hE := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt l n
  have hmap : taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l]) =
      ((cyclotomic (l ^ (n + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[l]) := by
    rw [taylor_apply, Polynomial.map_comp, map_cyclotomic]; simp
  have hmon : (taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l])).Monic := by
    rw [taylor_apply]; exact (cyclotomic.monic _ _).comp_X_add_C 1
  have hdeg : (taylor (1 : ℤ_[l]) (cyclotomic (l ^ (n + 1)) ℤ_[l])).natDegree =
      ((cyclotomic (l ^ (n + 1)) ℤ).comp (X + 1)).natDegree := by
    rw [natDegree_taylor, natDegree_comp, natDegree_cyclotomic, natDegree_cyclotomic,
      show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
  have hZ : Irreducible (cyclotomic (l ^ (n + 1)) ℤ_[l]) := by
    rw [← MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ_[l]))]
    change Irreducible (taylor (1 : ℤ_[l]) _)
    refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro k hk
      rw [degree_eq_natDegree hmon.ne_zero, Nat.cast_lt, hdeg] at hk
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hE.mem hk)
      rw [hmap, coeff_map, Ideal.mem_span_singleton, hd]
      exact ⟨d, by simp⟩
    · rw [degree_eq_natDegree hmon.ne_zero, natDegree_taylor, natDegree_cyclotomic, Nat.cast_pos]
      exact Nat.totient_pos.2 (pow_pos (Fact.out : l.Prime).pos _)
    · rw [taylor_coeff_zero, eval_one_cyclotomic_prime_pow, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hnu
      have hl : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
      refine isUnit_iff_exists_inv.2 ⟨c, mul_left_cancel₀ hl ?_⟩
      rw [mul_one, ← mul_assoc, ← pow_two]; exact hc.symm
  have h := (cyclotomic.monic (l ^ (n + 1)) ℤ_[l]).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ_[l]) |>.1 hZ
  rwa [map_cyclotomic] at h

def base (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

theorem norm_sub_of_pow_eq {ζ : Om l} {m a b : ℕ} (hζ : IsPrimitiveRoot ζ (l ^ m)) (h : ζ ^ a = ζ ^ b) :
    ‖(a : ℚ_[l]) - (b : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  have hl : l.Prime := Fact.out
  have hu := hζ.isUnit (pow_pos hl.pos m).ne'
  have h1 : a ≡ b [MOD l ^ m] := by
    rw [hζ.eq_orderOf]
    obtain ⟨u, rfl⟩ := hu
    rw [orderOf_units, ← pow_eq_pow_iff_modEq]
    ext; simpa using h
  have h2 : ((l : ℤ) ^ m) ∣ ((a : ℤ) - b) := by
    have := (Nat.modEq_iff_dvd.mp h1.symm); exact_mod_cast this
  have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - b) m).mpr h2
  simpa using this

theorem chi_Hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {σ : GQ l} (hσ : σ ∈ Hinf K) :
    (χ σ : ℚ_[l]) = 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have key : ∀ m : ℕ, ‖(χ σ : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)
    obtain ⟨a, ha, hga⟩ := hχ σ m ζ hζ.pow_eq_one
    have hmem : ζ ∈ Kinf K := (le_sup_right : _ ≤ Kinf K)
      (IntermediateField.subset_adjoin _ _ ⟨m, hζ.pow_eq_one⟩)
    have hfix : σ ζ = ζ := hσ ⟨ζ, hmem⟩
    have hb := norm_sub_of_pow_eq hζ (a := a) (b := 1) (by rw [← hga, hfix, pow_one])
    have := (Padic.nonarchimedean ((χ σ : ℚ_[l]) - (a : ℚ_[l])) _).trans (max_le ha hb)
    simpa using this
  by_contra hne
  have hpos : 0 < ‖(χ σ : ℚ_[l]) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hpos
  exact absurd (key k) (not_le.mpr hk)

def Utw (σ : GQ l) : Matrix (Fin 1) (Fin 1) (PadicComplex l) := fun _ _ => chiC chi 1 σ

theorem chiC_one (σ : GQ l) : chiC chi 1 σ = (((chi σ : ℚ_[l]) : Om l) : PadicComplex l) := by
  simp only [chiC, zpow_one]; rfl

end GlobalTheory.Cyc.Model
