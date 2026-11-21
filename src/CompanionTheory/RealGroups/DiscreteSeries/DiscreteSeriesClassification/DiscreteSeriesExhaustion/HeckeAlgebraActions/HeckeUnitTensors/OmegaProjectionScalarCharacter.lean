import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PrincipalSum

section
noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet qminor Tm GlRel)
open CompanionTheory.RgExh

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem continuous_apply_list_prod_ofFn_add_smul : ∀ (m : ℕ) (ℓ : Module.Dual ℂ W) (A B : Fin m → Module.End ℂ W) (f : W),
    Continuous (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) := by
  intro m
  induction m with
  | zero =>
    intro ℓ A B f
    simp only [List.ofFn_zero, List.prod_nil]
    exact continuous_const
  | succ m ih =>
    intro ℓ A B f
    have h : (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) =
        fun u : ℂ => (ℓ ∘ₗ A 0) ((List.ofFn fun k : Fin m => A k.succ + u • B k.succ).prod f) +
          u * (ℓ ∘ₗ B 0) ((List.ofFn fun k : Fin m => A k.succ + u • B k.succ).prod f) := by
      funext u
      simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, LinearMap.comp_apply]
    rw [h]
    exact (ih (ℓ ∘ₗ A 0) (fun k => A k.succ) (fun k => B k.succ) f).add
      (continuous_id.mul (ih (ℓ ∘ₗ B 0) (fun k => A k.succ) (fun k => B k.succ) f))

theorem cont_ofFn_prod (ℓ : Module.Dual ℂ W) : ∀ (m : ℕ) (A B : Fin m → Module.End ℂ W) (f : W),
    Continuous (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) := by
  intro m A B f
  exact continuous_apply_list_prod_ofFn_add_smul m ℓ A B f

theorem Tm_affine {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (u : ℂ) (k : ℂ) (a b : Fin n) :
    Tm E (u - k) a b = ((if a = b then algebraMap ℂ (Module.End ℂ W) (-k) else 0) + E a b) +
      u • (if a = b then (1 : Module.End ℂ W) else 0) := by
  unfold Tm
  split_ifs with h
  · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_smul]
    abel
  · simp

theorem cont_qdet {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (ℓ : Module.Dual ℂ W) (f : W) :
    Continuous (fun u : ℂ => ℓ (qdet E u f)) := by
  simp only [qdet, qminor, LinearMap.sum_apply, map_sum]
  refine continuous_finsetSum _ fun σ _ => ?_
  simp only [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, Tm_affine]
  exact (cont_ofFn_prod ℓ n _ _ f).const_smul _

theorem eq_zero_of_off {g : ℂ → ℂ} (hg : Continuous g) (u₀ : ℂ) (h : ∀ u, u ≠ u₀ → g u = 0) : g u₀ = 0 := by
  have hd : Dense ({u₀}ᶜ : Set ℂ) := dense_compl_singleton u₀
  have h0 : g = fun _ => 0 :=
    hg.ext_on hd (continuous_const : Continuous fun _ : ℂ => (0 : ℂ)) (fun u hu => h u hu)
  exact congrFun h0 u₀

end CompanionTheory.RgExh.Hk.UnitPf
end
end

section
noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet qminor Tm GlRel)
open Formalism.QuantumDeterminants (capP)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor)
open CompanionTheory.RgExh

variable {m : ℕ} (X : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1))

def omg : ℂ := cn (m + 1) - χ s

def kap : ℂ := ∏ t ∈ univ.erase s, (χ t - χ s)

def Pr : Module.End ℂ (Fin (m + 1) → X.V) := (kap χ s)⁻¹ • qdet (tensE X) (omg χ s)

variable {X χ s}

theorem qdet_scal (hS : ScalChar X χ) (u : ℂ) :
    qdet X.E u = capP χ (u - cn (m + 1)) • (1 : Module.End ℂ X.V) := by
  have := hS (u - cn (m + 1))
  have e : u - cn (m + 1) + ((↑(m + 1) : ℂ) - 1) / 2 = u := by rw [cn]; ring
  rwa [e] at this

theorem capelliPoly_root : capP χ (-(χ s)) = 0 :=
  Finset.prod_eq_zero (mem_univ s) (by ring)

theorem capelliPoly_eq_mul_prod_erase (u : ℂ) :
    capP χ u = (u + χ s) * ∏ t ∈ univ.erase s, (u + χ t) :=
  (Finset.mul_prod_erase univ (fun t => u + χ t) (mem_univ s)).symm

theorem qdet_omg (hS : ScalChar X χ) : qdet X.E (omg χ s) = 0 := by
  rw [qdet_scal hS, omg, show cn (m + 1) - χ s - cn (m + 1) = -χ s by ring, capelliPoly_root, zero_smul]

theorem compLeft_zero' : (0 : Module.End ℂ X.V).compLeft (Fin (m + 1)) = 0 := by
  ext f d; simp

theorem ct_omg (hS : ScalChar X χ) : qdet (tensE X) (omg χ s) = minorOp X (omg χ s - 1) := by
  rw [GlobalTheory.T.HeckeRankOne m X, qdet_omg hS, compLeft_zero', zero_add]

theorem om_ct (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) :
    om X (qdet (tensE X) (omg χ s) f) = (χ s - cn (m + 1)) • qdet (tensE X) (omg χ s) f := by
  have h := LinearMap.congr_fun (GlobalTheory.T.OmegaMinor m X (omg χ s)) f
  rw [qdet_omg hS, compLeft_zero'] at h
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply] at h
  rw [ct_omg hS]
  have h2 : om X (minorOp X (omg χ s - 1) f) = -(omg χ s • minorOp X (omg χ s - 1) f) := eq_neg_of_add_eq_zero_right h
  rw [h2, omg, ← neg_smul]
  congr 1; ring

theorem compLeft_smul_one (c : ℂ) (g : Fin (m + 1) → X.V) :
    (c • (1 : Module.End ℂ X.V)).compLeft (Fin (m + 1)) g = c • g := by
  funext d; simp

theorem ct_on_step (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) (hf : om X f = (χ s - cn (m + 1)) • f) :
    qdet (tensE X) (omg χ s) f = kap χ s • f := by
  set a : ℂ := χ s - cn (m + 1) with ha
  set q : ℂ → ℂ := fun u => ∏ t ∈ univ.erase s, (u - cn (m + 1) + χ t) with hq
  have key : ∀ u : ℂ, u ≠ -a → qdet (tensE X) u f = ((u + 1 + a) * q u) • f := by
    intro u hu
    have h := LinearMap.congr_fun (GlobalTheory.CompanionTheory.RgExh.qdetTens (m + 1) X u) f
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hf] at h
    rw [← add_smul, map_smul, qdet_scal hS, ← add_smul, LinearMap.map_smul, compLeft_smul_one,
      capelliPoly_eq_mul_prod_erase (s := s)] at h
    have hua : u + a ≠ 0 := fun h0 => hu (eq_neg_of_add_eq_zero_left h0)
    have e : u - cn (m + 1) + χ s = u + a := by rw [ha]; ring
    rw [e, smul_smul] at h
    have h3 : (u + a) • qdet (tensE X) u f = (u + a) • (((u + 1 + a) * q u) • f) := by
      rw [h, smul_smul]; congr 1; simp only [hq]; ring
    exact smul_right_injective _ hua h3
  have hcont : ∀ ℓ : Module.Dual ℂ (Fin (m + 1) → X.V),
      ℓ (qdet (tensE X) (omg χ s) f) = kap χ s * ℓ f := by
    intro ℓ
    have hg : Continuous (fun u : ℂ => ℓ (qdet (tensE X) u f) - (u + 1 + a) * q u * ℓ f) := by
      refine (cont_qdet (tensE X) ℓ f).sub (Continuous.mul (Continuous.mul (by fun_prop) ?_) continuous_const)
      exact continuous_finset_prod _ fun t _ => by fun_prop
    have h0 := eq_zero_of_off hg (-a) fun u hu => by rw [key u hu, map_smul, smul_eq_mul]; ring
    have e1 : omg χ s = -a := by rw [omg, ha]; ring
    have e2 : q (-a) = kap χ s := by
      simp only [hq, kap]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [ha]; ring
    rw [e1]
    have : -a + 1 + a = 1 := by ring
    rw [this, one_mul, e2] at h0
    exact sub_eq_zero.1 h0
  have : qdet (tensE X) (omg χ s) f - kap χ s • f = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    rw [map_sub, map_smul, hcont ℓ, smul_eq_mul, sub_self]
  exact sub_eq_zero.1 this

theorem kap_ne (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) : kap χ s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun t ht => sub_ne_zero.2 (hsimp t (Finset.ne_of_mem_erase ht))

theorem Pr_step (hS : ScalChar X χ) (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) (f : Fin (m + 1) → X.V)
    (hf : om X f = (χ s - cn (m + 1)) • f) : Pr X χ s f = f := by
  rw [Pr, LinearMap.smul_apply, ct_on_step hS f hf, smul_smul, inv_mul_cancel₀ (kap_ne hsimp), one_smul]

theorem om_Pr (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) :
    om X (Pr X χ s f) = (χ s - cn (m + 1)) • Pr X χ s f := by
  rw [Pr, LinearMap.smul_apply, map_smul, om_ct hS, smul_comm]

theorem Pr_om (f : Fin (m + 1) → X.V) : Pr X χ s (om X f) = om X (Pr X χ s f) := by
  have hc := GlobalTheory.CompanionTheory.RgExh.commute_qdet_of (tensE X) (om X) (fun a b => commute_om X a b) (omg χ s)
  simp only [Pr, LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun hc.eq f

theorem Pr_tensE (a b : Fin (m + 1)) (f : Fin (m + 1) → X.V) :
    Pr X χ s (tensE X a b f) = tensE X a b (Pr X χ s f) := by
  have hc := Formalism.REAL.qDetCentral (Module.End ℂ (Fin (m + 1) → X.V)) (m + 1) (tensE X) (glRel_tensE X) (omg χ s) a b
  simp only [Pr, LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun hc f

theorem ptr_Pr (hS : ScalChar X χ) (v : X.V) :
    ∑ c : Fin (m + 1), Pr X χ s (Pi.single c v) c = ((kap χ s)⁻¹ * -capP χ (-χ s - 1)) • v := by
  have e : ∀ c : Fin (m + 1), Pr X χ s (Pi.single c v) c =
      (kap χ s)⁻¹ • cminor X.E c.succAbove c.succAbove (omg χ s - 1) v := by
    intro c
    rw [Pr, LinearMap.smul_apply, ct_omg hS, Pi.smul_apply]
    congr 1
    show ∑ b : Fin (m + 1), ((-1 : ℂ) ^ ((c : ℕ) + (b : ℕ))) • cminor X.E c.succAbove b.succAbove (omg χ s - 1)
      ((Pi.single c v : Fin (m + 1) → X.V) b) = _
    rw [Finset.sum_eq_single c]
    · rw [Pi.single_eq_same, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, smul_zero]
    · intro h; exact absurd (mem_univ c) h
  simp only [e, ← Finset.smul_sum]
  have hp := GlobalTheory.T.PrincipalSum m X.V X.E X.gl (omg χ s)
  rw [← LinearMap.sum_apply, hp, LinearMap.sub_apply, qdet_omg hS, LinearMap.zero_apply, zero_sub,
    qdet_scal hS, show omg χ s - 1 - cn (m + 1) = -χ s - 1 by rw [omg]; ring, LinearMap.smul_apply,
    Module.End.one_apply, smul_neg, smul_smul, ← neg_smul]
  congr 1; ring

theorem capelliPoly_ne (hfree : ∀ r, χ r ≠ χ s + 1) : capP χ (-χ s - 1) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun t _ => ?_
  intro h; exact hfree t (by linear_combination h)

end CompanionTheory.RgExh.Hk.UnitPf
end
end

section
noncomputable section

set_option linter.unusedVariables false

open Finset

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem mem_of_eig {T : Module.End ℂ (Fin (m + 1) → X.V)} {μ : ℂ} {f : Fin (m + 1) → X.V} (h : T f = μ • f) :
    f ∈ T.maxGenEigenspace μ :=
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 h)

theorem Pr_mem (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) : Pr X χ s f ∈ stepSub X (χ s) :=
  mem_of_eig (om_Pr hS f)

variable (X) in

def y1 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) := LinearMap.pi fun c => (om X).comp (LinearMap.proj c)

variable (X) in

def y2 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) :=
  LinearMap.pi fun a => -∑ c, (tensE X a c).comp (LinearMap.proj c)

variable (X) in

def eta : X.V →ₗ[ℂ] (Fin (m + 1) → Fin (m + 1) → X.V) := LinearMap.pi fun c => LinearMap.single ℂ (fun _ => X.V) c

variable (X) in

def psi : (Fin (m + 1) → Fin (m + 1) → X.V) →ₗ[ℂ] X.V where
  toFun H := ∑ c, H c c
  map_add' H K := by simp [Finset.sum_add_distrib]
  map_smul' r H := by simp [Finset.smul_sum]

theorem left_casimir_apply (H : Fin (m + 1) → Fin (m + 1) → X.V) (c : Fin (m + 1)) : y1 X H c = om X (H c) := rfl

theorem right_casimir_apply (H : Fin (m + 1) → Fin (m + 1) → X.V) (a : Fin (m + 1)) :
    y2 X H a = -∑ c, tensE X a c (H c) := by
  simp [y2, LinearMap.pi_apply]

theorem eta_apply (v : X.V) (c : Fin (m + 1)) : eta X v c = Pi.single c v := rfl

theorem psi_apply (H : Fin (m + 1) → Fin (m + 1) → X.V) : psi X H = ∑ c, H c c := rfl

theorem commute_left_right_casimir : Commute (y1 X) (y2 X) := by
  refine LinearMap.ext fun H => funext fun a => ?_
  simp only [Module.End.mul_apply, left_casimir_apply, right_casimir_apply, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (LinearMap.congr_fun (commute_om X a c).eq (H c)).symm

theorem sum_tensE_single (v : X.V) (a : Fin (m + 1)) :
    ∑ c, tensE X a c (Pi.single c v) = om X (Pi.single a v) + ((m + 1 : ℕ) : ℂ) • (Pi.single a v : Fin (m + 1) → X.V) := by
  funext d
  simp only [Finset.sum_apply, tensE_apply, om_apply, Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single d]
    · rw [Pi.single_eq_same, Finset.sum_eq_single a]
      · rw [Pi.single_eq_same]
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
      · intro h; exact absurd (mem_univ a) h
    · intro c _ hc; rw [Pi.single_eq_of_ne (Ne.symm hc), map_zero]
    · intro h; exact absurd (mem_univ d) h
  · by_cases h : d = a
    · subst h
      simp only [Pi.single_eq_same, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
    · simp [h]

theorem right_casimir_eta (v : X.V) : y2 X (eta X v) = -(y1 X (eta X v) + ((m + 1 : ℕ) : ℂ) • eta X v) := by
  funext a
  rw [right_casimir_apply]
  simp only [eta_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, left_casimir_apply]
  rw [sum_tensE_single]

theorem right_casimir_add_eta_psi (H : Fin (m + 1) → Fin (m + 1) → X.V) (a d : Fin (m + 1)) :
    (y2 X H + eta X (psi X H)) a d = -∑ c, X.E a c (H c d) := by
  rw [Pi.add_apply, right_casimir_apply, eta_apply, psi_apply]
  simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, tensE_apply]
  rw [Finset.sum_add_distrib]
  by_cases h : d = a
  · subst h; simp [Pi.single_eq_same]
  · simp [h, Pi.single_eq_of_ne h]

def liftL (T : Module.End ℂ (Fin (m + 1) → X.V)) : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) where
  toFun H := fun a d => T (fun c => H c d) a
  map_add' H K := by
    funext a d
    show T (fun c => H c d + K c d) a = T (fun c => H c d) a + T (fun c => K c d) a
    rw [show (fun c => H c d + K c d) = (fun c => H c d) + (fun c => K c d) from rfl, map_add]; rfl
  map_smul' r H := by
    funext a d
    show T (fun c => r • H c d) a = r • T (fun c => H c d) a
    rw [show (fun c => r • H c d) = r • (fun c => H c d) from rfl, map_smul]; rfl

theorem liftL_apply (T : Module.End ℂ (Fin (m + 1) → X.V)) (H) (a d : Fin (m + 1)) :
    liftL T H a d = T (fun c => H c d) a := rfl

def liftR : Module.End ℂ (Fin (m + 1) → X.V) →+* Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) where
  toFun := liftL
  map_one' := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_mul' S T := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_zero' := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_add' S T := LinearMap.ext fun H => funext fun a => funext fun d => rfl

theorem liftR_smul_one (μ : ℂ) : liftR (X := X) (μ • 1) = μ • 1 :=
  LinearMap.ext fun H => funext fun a => funext fun d => rfl

theorem omegaP_eq : liftR (X := X) (omD X) = y2 X + (eta X).comp (psi X) := by
  refine LinearMap.ext fun H => funext fun a => funext fun d => ?_
  show liftL (omD X) H a d = (y2 X H + eta X (psi X H)) a d
  rw [right_casimir_add_eta_psi, liftL_apply]
  simp [omD, ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd, LinearMap.pi_apply]

end CompanionTheory.RgExh.Hk.UnitPf
end
end

section
noncomputable section

open Finset Polynomial

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem mem_of_eig' {M : Type*} [AddCommGroup M] [Module ℂ M] {T : Module.End ℂ M} {μ : ℂ} {f : M}
    (h : T f = μ • f) : f ∈ T.maxGenEigenspace μ :=
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 h)

variable (X) in
def Isub : Submodule ℂ (Fin (m + 1) → Fin (m + 1) → X.V) :=
  ⨆ k : ℕ, LinearMap.range ((y1 X ^ k) ∘ₗ eta X)

theorem mem_Isub (k : ℕ) (v : X.V) : (y1 X ^ k) (eta X v) ∈ Isub X :=
  Submodule.mem_iSup_of_mem k ⟨v, rfl⟩

theorem eta_mem_Isub (v : X.V) : eta X v ∈ Isub X := by
  simpa using mem_Isub (X := X) 0 v

theorem right_casimir_mem_submodule {H} (h : H ∈ Isub X) : y2 X H ∈ Isub X := by
  refine Submodule.iSup_induction _ (motive := fun H => y2 X H ∈ Isub X) h ?_ (by simp) ?_
  · rintro k _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← ((commute_left_right_casimir (X := X)).pow_left k).eq, Module.End.mul_apply, right_casimir_eta, map_neg,
      map_add, map_smul]
    refine neg_mem (add_mem ?_ (Submodule.smul_mem _ _ (mem_Isub k v)))
    have := mem_Isub (X := X) (k + 1) v
    rwa [pow_succ, Module.End.mul_apply] at this
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy

variable (X) in

def Om' : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) := y2 X + (eta X).comp (psi X)

theorem Om'_mem_Isub {H} (h : H ∈ Isub X) : Om' X H ∈ Isub X := by
  simp only [Om', LinearMap.add_apply, LinearMap.comp_apply]
  exact add_mem (right_casimir_mem_submodule h) (eta_mem_Isub _)

theorem Om'_pow_mem_Isub (k : ℕ) {H} (h : H ∈ Isub X) : (Om' X ^ k) H ∈ Isub X := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact Om'_mem_Isub ih

theorem aeval_mem_Isub (p : ℂ[X]) {H} (h : H ∈ Isub X) : aeval (Om' X) p H ∈ Isub X := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact add_mem hp hq
  | monomial k c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Om'_pow_mem_Isub k h)

theorem diff_mem_Isub (β : ℂ) (k : ℕ) (H) :
    ((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H ∈ Isub X := by
  induction k generalizing H with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    have e : (Om' X - β • 1) (((Om' X - β • 1) ^ k) H) - (y2 X - β • 1) (((y2 X - β • 1) ^ k) H) =
        (Om' X - β • 1) (((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H) +
          eta X (psi X (((y2 X - β • 1) ^ k) H)) := by
      simp only [map_sub, Om', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        Module.End.one_apply]
      abel
    rw [e]
    refine add_mem ?_ (eta_mem_Isub _)
    have hm := ih H
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact sub_mem (Om'_mem_Isub hm) (Submodule.smul_mem _ _ hm)

theorem left_casimir_pow_apply (k : ℕ) (H : Fin (m + 1) → Fin (m + 1) → X.V) (c : Fin (m + 1)) :
    (y1 X ^ k) H c = (om X ^ k) (H c) := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl

theorem Pr_om_pow (hS : ScalChar X χ) (k : ℕ) (f : Fin (m + 1) → X.V) :
    Pr X χ s ((om X ^ k) f) = (χ s - cn (m + 1)) ^ k • Pr X χ s f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, Pr_om, ih, map_smul, om_Pr hS, smul_smul, pow_succ]

theorem Pr_Isub (hS : ScalChar X χ) {H} (h : H ∈ Isub X) :
    ∃ v : X.V, ∀ c, Pr X χ s (H c) = Pr X χ s (Pi.single c v) := by
  refine Submodule.iSup_induction _ (motive := fun H => ∃ v : X.V, ∀ c, Pr X χ s (H c) = Pr X χ s (Pi.single c v))
    h ?_ ⟨0, by simp⟩ ?_
  · rintro k _ ⟨v, rfl⟩
    refine ⟨(χ s - cn (m + 1)) ^ k • v, fun c => ?_⟩
    simp only [LinearMap.comp_apply, left_casimir_pow_apply, eta_apply, Pr_om_pow hS, Pi.single_smul, map_smul]
  · rintro x y ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v + w, fun c => by rw [Pi.add_apply, map_add, hv, hw, Pi.single_add, map_add]⟩

end CompanionTheory.RgExh.Hk.UnitPf
end
end

section
noncomputable section

open Finset Polynomial

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

variable (X χ s) in

def toS (g : (step X (χ s)).V) : ↥(stepSub X (χ s)) := g

variable (X χ s) in
def ofS (g : ↥(stepSub X (χ s))) : (step X (χ s)).V := g

theorem toS_add (g g' : (step X (χ s)).V) : toS X χ s (g + g') = toS X χ s g + toS X χ s g' := rfl



theorem toS_neg (g : (step X (χ s)).V) : toS X χ s (-g) = -toS X χ s g := rfl

theorem toS_sum (g : Fin (m + 1) → (step X (χ s)).V) : toS X χ s (∑ c, g c) = ∑ c, toS X χ s (g c) :=
  map_sum (AddMonoidHom.mk' (toS X χ s) toS_add) g univ

theorem toS_E (a b : Fin (m + 1)) (g : (step X (χ s)).V) :
    ((toS X χ s ((step X (χ s)).E a b g) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V) =
      tensE X a b (toS X χ s g : Fin (m + 1) → X.V) := rfl

def coeY (G : Fin (m + 1) → (step X (χ s)).V) : Fin (m + 1) → Fin (m + 1) → X.V :=
  fun c => ((toS X χ s (G c) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V)

theorem coeY_injective : Function.Injective (coeY (X := X) (χ := χ) (s := s)) := fun G G' h =>
  funext fun c => (Subtype.ext (congrFun h c) : toS X χ s (G c) = toS X χ s (G' c))


theorem coeY_smul (r : ℂ) (G) : coeY (X := X) (χ := χ) (s := s) (r • G) = r • coeY G := by
  funext c; rfl

theorem coeY_sub (G G') : coeY (X := X) (χ := χ) (s := s) (G - G') = coeY G - coeY G' := by
  funext c; rfl

theorem coe_omD (G : Fin (m + 1) → (step X (χ s)).V) :
    coeY (omD (step X (χ s)) G) = y2 X (coeY G) := by
  funext a
  rw [right_casimir_apply]
  have h : omD (step X (χ s)) G a = -∑ c, (step X (χ s)).E a c (G c) := by
    simp [omD, ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd, LinearMap.pi_apply, LinearMap.sum_apply]
  show ((toS X χ s (omD (step X (χ s)) G a) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V) = _
  rw [h, toS_neg, toS_sum, Submodule.coe_neg, Submodule.coe_sum]
  simp only [toS_E]
  rfl

theorem coe_pow (β : ℂ) (k : ℕ) (G : Fin (m + 1) → (step X (χ s)).V) :
    coeY (((omD (step X (χ s)) - β • 1) ^ k) G) = ((y2 X - β • 1) ^ k) (coeY G) := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, coeY_sub, coeY_smul, coe_omD]

variable (χ s) in

def phi0 (hS : ScalChar X χ) : X.V →ₗ[ℂ] (Fin (m + 1) → (step X (χ s)).V) where
  toFun v := fun c => ofS X χ s ⟨Pr X χ s (Pi.single c v), Pr_mem hS _⟩
  map_add' v w := by
    funext c
    show ofS X χ s ⟨Pr X χ s (Pi.single c (v + w)), _⟩ =
      ofS X χ s ⟨Pr X χ s (Pi.single c v), _⟩ + ofS X χ s ⟨Pr X χ s (Pi.single c w), _⟩
    apply Subtype.ext
    show Pr X χ s (Pi.single c (v + w)) = Pr X χ s (Pi.single c v) + Pr X χ s (Pi.single c w)
    rw [Pi.single_add, map_add]
  map_smul' r v := by
    funext c
    show ofS X χ s ⟨Pr X χ s (Pi.single c (r • v)), _⟩ = r • ofS X χ s ⟨Pr X χ s (Pi.single c v), _⟩
    apply Subtype.ext
    show Pr X χ s (Pi.single c (r • v)) = r • Pr X χ s (Pi.single c v)
    rw [Pi.single_smul, map_smul]

theorem coe_projection_scalar_character (hS : ScalChar X χ) (v : X.V) : coeY (phi0 χ s hS v) = fun c => Pr X χ s (Pi.single c v) := by
  funext c; rfl

theorem omega_projection_scalar_character (hS : ScalChar X χ) (v : X.V) :
    omD (step X (χ s)) (phi0 χ s hS v) = (-(χ s + 1) - cn (m + 1)) • phi0 χ s hS v := by
  apply coeY_injective
  rw [coe_omD, coeY_smul, coe_projection_scalar_character]
  funext a
  rw [right_casimir_apply]
  simp only [← Pr_tensE]
  rw [← map_sum, sum_tensE_single, map_add, map_smul, Pr_om, om_Pr hS, ← add_smul, ← neg_smul, Pi.smul_apply]
  congr 1
  unfold cn; push_cast; ring

theorem tensVd_apply {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) (f : Fin n → M) (d : Fin n) :
    ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd E a b f d = E a b (f d) - if d = b then f a else 0 := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp

theorem tensE_single (a b d : Fin (m + 1)) (v : X.V) :
    tensE X a b (Pi.single d v) = Pi.single d (X.E a b v) + if b = d then Pi.single a v else 0 := by
  funext i
  rw [tensE_apply, Pi.add_apply]
  simp only [Pi.single_apply]
  by_cases hi : i = d <;> by_cases hb : b = d <;> by_cases ha : i = a <;> simp_all

end CompanionTheory.RgExh.Hk.UnitPf
end
end
