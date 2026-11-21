import Mathlib

open NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a

theorem bar_bar (a : 𝓞 E) : bar E (bar E a) = a := by
  apply RingOfIntegers.ext
  simp [bar]

section Forms

variable (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]

def balancedForms : Submodule ℝ (Y →+ Y →+ ℝ) where
  carrier := {β | (∀ x x', β x x' = β x' x) ∧
    ∀ (a : 𝓞 E) (x x' : Y), β (a • x) x' = β x (bar E a • x')}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.add_apply]; rw [h1, k1]
    · simp only [AddMonoidHom.add_apply]; rw [h2, k2]
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c β ⟨h1, h2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.smul_apply]; rw [h1]
    · simp only [AddMonoidHom.smul_apply]; rw [h2]

variable {E Y}

noncomputable def quad (β : balancedForms E Y) (x : Y) : ℝ := β.1 x x / 2

def IsPosSemidef (β : balancedForms E Y) : Prop := ∀ x : Y, 0 ≤ β.1 x x

def IsPosDef (β : balancedForms E Y) : Prop :=
  ∀ (n : ℕ) (x : Fin n → Y), LinearIndependent ℤ x →
    ∀ t : Fin n → ℝ, t ≠ 0 → 0 < ∑ i, ∑ j, t i * t j * β.1 (x i) (x j)

variable (E Y)

structure Exponent where

  form : Module.Dual (𝓞 E) Y →+ Module.Dual (𝓞 E) Y →+ 𝓞 E
  smul_left : ∀ (a : 𝓞 E) y y', form (a • y) y' = a * form y y'
  hermitian : ∀ y y', form y' y = bar E (form y y')
  pos : ∀ (τ : E →+* ℂ) (y : Module.Dual (𝓞 E) Y), y ≠ 0 → 0 < (τ ((form y y : 𝓞 E) : E)).re

variable {E Y}

theorem Exponent.smul_right (l : Exponent E Y) (a : 𝓞 E) (y y' : Module.Dual (𝓞 E) Y) :
    l.form y (a • y') = bar E a * l.form y y' := by
  have hmul : ∀ b c : 𝓞 E, bar E (b * c) = bar E b * bar E c := fun b c =>
    map_mul (IsCMField.ringOfIntegersComplexConj E) b c
  rw [l.hermitian (a • y') y, l.smul_left, l.hermitian y y', hmul, bar_bar]

variable (E Y)

structure DualSystem where

  n : ℕ

  e : Fin n → Y

  y : Fin n → Module.Dual (𝓞 E) Y
  expand : ∀ x, ∑ j, y j x • e j = x

theorem nonempty_dualSystem [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] :
    Nonempty (DualSystem E Y) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Y
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨⟨n, fun j => f (fun k => if j = k then 1 else 0), fun j => LinearMap.proj j ∘ₗ s,
    fun x => ?_⟩⟩
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  calc _ = f (s x) := (LinearMap.pi_apply_eq_sum_univ f (s x)).symm
    _ = x := hx

variable {E Y}

noncomputable def DualSystem.pairing (D : DualSystem E Y) (l : Exponent E Y)
    (β : balancedForms E Y) : ℝ :=
  (∑ j, ∑ k, β.1 (l.form (D.y j) (D.y k) • D.e j) (D.e k)) / 2

theorem DualSystem.apply_eq (D : DualSystem E Y) (β : balancedForms E Y) (x x' : Y) :
    β.1 x x' = ∑ j, ∑ k, β.1 ((D.y j x * bar E (D.y k x')) • D.e j) (D.e k) := by
  obtain ⟨h1, h2⟩ := β.2
  have key : ∀ (a b : 𝓞 E) (u v : Y), β.1 (a • u) (b • v) = β.1 ((a * bar E b) • u) v := by
    intro a b u v
    rw [mul_comm, mul_smul, h2 (bar E b) (a • u) v, bar_bar]
  conv_lhs => rw [← D.expand x, ← D.expand x']
  simp only [map_sum, AddMonoidHom.finsetSum_apply, key]
  exact Finset.sum_comm

theorem DualSystem.pairing_of_sum (D : DualSystem E Y) (l : Exponent E Y)
    (β : balancedForms E Y) {ι : Type} [Fintype ι] (x x' : ι → Y)
    (h : ∀ y y', l.form y y' = ∑ i, y (x i) * bar E (y' (x' i))) :
    D.pairing l β = (∑ i, β.1 (x i) (x' i)) / 2 := by
  show (∑ j, ∑ k, β.1 (l.form (D.y j) (D.y k) • D.e j) (D.e k)) / 2 = _
  congr 1
  have hr : ∑ i, β.1 (x i) (x' i) =
      ∑ i, ∑ j, ∑ k, β.1 ((D.y j (x i) * bar E (D.y k (x' i))) • D.e j) (D.e k) :=
    Finset.sum_congr rfl fun i _ => D.apply_eq β (x i) (x' i)
  rw [hr]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h, Finset.sum_smul, map_sum, AddMonoidHom.finsetSum_apply]

theorem DualSystem.dual_expand (D : DualSystem E Y) (y : Module.Dual (𝓞 E) Y) :
    y = ∑ j, y (D.e j) • D.y j := by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [← D.expand x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]

theorem DualSystem.form_eq (D : DualSystem E Y) (l : Exponent E Y) (y y' : Module.Dual (𝓞 E) Y) :
    l.form y y' = ∑ p : Fin D.n × Fin D.n,
      y (l.form (D.y p.1) (D.y p.2) • D.e p.1) * bar E (y' (D.e p.2)) := by
  conv_lhs => rw [D.dual_expand y, D.dual_expand y']
  simp only [map_sum, AddMonoidHom.finsetSum_apply, l.smul_left, l.smul_right, map_smul,
    smul_eq_mul, Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem DualSystem.pairing_eq (D D' : DualSystem E Y) (l : Exponent E Y)
    (β : balancedForms E Y) : D.pairing l β = D'.pairing l β := by
  rw [D'.pairing_of_sum l β (fun p : Fin D.n × Fin D.n => l.form (D.y p.1) (D.y p.2) • D.e p.1)
    (fun p => D.e p.2) (D.form_eq l), Fintype.sum_prod_type]
  rfl

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

noncomputable def pairing (l : Exponent E Y) (β : balancedForms E Y) : ℝ :=
  (Classical.choice (nonempty_dualSystem E Y)).pairing l β

theorem pairing_eq_dualSystem (D : DualSystem E Y) (l : Exponent E Y) (β : balancedForms E Y) :
    pairing l β = D.pairing l β := by
  unfold pairing
  exact (Classical.choice (nonempty_dualSystem E Y)).pairing_eq D l β

theorem pairing_of_sum (l : Exponent E Y) (β : balancedForms E Y) {ι : Type} [Fintype ι]
    (x x' : ι → Y) (h : ∀ y y', l.form y y' = ∑ i, y (x i) * bar E (y' (x' i))) :
    pairing l β = (∑ i, β.1 (x i) (x' i)) / 2 := by
  obtain ⟨D⟩ := nonempty_dualSystem E Y
  rw [pairing_eq_dualSystem D]
  exact D.pairing_of_sum l β x x' h

def pairingValues (β : balancedForms E Y) : Set ℝ := Set.range fun l : Exponent E Y => pairing l β

def IsPhiC (β : balancedForms E Y) (r : ℝ) : Prop := IsLeast (pairingValues β) r

noncomputable def phiC (β : balancedForms E Y) (_hβ : IsPosSemidef β) : ℝ :=
  sInf (pairingValues β)

omit [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] in

noncomputable def Exponent.ofFamily {ι : Type} [Fintype ι] (x : ι → Y)
    (hx : ∀ y : Module.Dual (𝓞 E) Y, (∀ i, y (x i) = 0) → y = 0) : Exponent E Y where
  form := AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun y' => ∑ i, y (x i) * bar E (y' (x i)))
      (fun y' y'' => by simp [bar, mul_add, Finset.sum_add_distrib]))
    (fun y y'' => by ext y'; simp [add_mul, Finset.sum_add_distrib])
  smul_left a y y' := by simp [Finset.mul_sum, mul_assoc]
  hermitian y y' := by
    simp only [AddMonoidHom.mk'_apply]
    change _ = IsCMField.ringOfIntegersComplexConj E _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]
    exact congrArg _ (bar_bar E _).symm
  pos τ y hy := by
    have key : ∀ a : 𝓞 E, (τ ((a * bar E a : 𝓞 E) : E)).re = Complex.normSq (τ (a : E)) := by
      intro a
      have : ((a * bar E a : 𝓞 E) : E) = (a : E) * IsCMField.complexConj E (a : E) := by
        rw [← IsCMField.coe_ringOfIntegersComplexConj]; rfl
      rw [this, map_mul, IsCMField.complexEmbedding_complexConj, Complex.mul_conj,
        Complex.ofReal_re]
    simp only [AddMonoidHom.mk'_apply]
    have hs : (τ ((∑ i, y (x i) * bar E (y (x i)) : 𝓞 E) : E)).re
        = ∑ i, Complex.normSq (τ (y (x i) : E)) := by
      rw [← Finset.sum_congr rfl fun i _ => key (y (x i)), ← Complex.re_sum, ← map_sum]
      congr 2
      exact map_sum (algebraMap (𝓞 E) E) _ _
    rw [hs]
    by_contra hneg
    apply hy
    apply hx
    intro i
    have h0 : ∑ i, Complex.normSq (τ (y (x i) : E)) = 0 :=
      le_antisymm (not_lt.mp hneg) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).mp h0 i
      (Finset.mem_univ i)
    rw [Complex.normSq_eq_zero, map_eq_zero] at hi
    exact Subtype.ext hi





end Forms

noncomputable def traceForm : balancedForms E (𝓞 E) :=
  ⟨AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun x' => ∑ τ : E →+* ℂ, (τ (algebraMap (𝓞 E) E x) * starRingEnd ℂ (τ (algebraMap (𝓞 E) E x'))).re)
      (fun _ _ => by simp [mul_add, Finset.sum_add_distrib]))
    (fun _ _ => by ext; simp [add_mul, Finset.sum_add_distrib]), by
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.mk'_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [mul_comm]
    · simp only [AddMonoidHom.mk'_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have : algebraMap (𝓞 E) E (bar E a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) :=
        IsCMField.coe_ringOfIntegersComplexConj E a
      rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, map_mul, this, map_mul,
        IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
      congr 1
      ring⟩




end GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem
