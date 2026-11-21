import Formalism.LocalToGlobal.IndefiniteReal.DatumF

noncomputable section

open MeasureTheory

namespace Formalism.IndefR.LiftF

section Chars

variable {C : Type*} [CommGroup C]

def tup (μ0 : ℕ → C) (ξ : C) (j : ℕ) : C := μ0 j * ξ

end Chars

section Step

variable {G H S Sinf Ds Dt : Type*} [MeasurableSpace H]
  [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]

def liftInt (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (s : S) (F : H → ℂ) (g : G) : ℂ :=
  ∫ h in 𝓕, th g h s * F h ∂ν

structure IsIo (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt) : Prop where

  integ : ∀ F : CCs, ∀ φ v g,
    IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν

  eq : ∀ F : CCs, ∀ φ v g,
    liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g = ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g

theorem IsIo.unique {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {pt : Sinf → S}
    {T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))}
    {CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))} {io io' : CCs →ₗ[ℂ] CCt}
    (hT : ∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) = 0) → u = 0)
    (h : IsIo ν 𝓕 th pt T CCs CCt io) (h' : IsIo ν 𝓕 th pt T CCs CCt io') : io = io' := by
  refine LinearMap.ext fun F => sub_eq_zero.1 (hT _ fun φ v => ?_)
  funext g
  have h1 := h.eq F φ v g
  have h2 := h'.eq F φ v g
  simp only [Submodule.coe_sub, LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply]
  rw [← h1, ← h2, sub_self]

def IsTPlus (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (ipDt : Dt →ₗ[ℂ] Dt →ₗ⋆[ℂ] ℂ) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) : Prop :=
  ∀ φ v' v, ipDt (T φ v') v = ipDs v' (Tp φ v)

structure IsIoUp [MeasurableSpace G] (νG : Measure G) (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (up : CCt →ₗ[ℂ] CCs) : Prop where

  integ : ∀ u : CCt, ∀ φ v h,
    IntegrableOn (fun g => starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g) 𝓕G νG

  eq : ∀ u : CCt, ∀ φ v h,
    ∫ g in 𝓕G, starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g ∂νG =
      ((up u : CCs) : Ds →ₗ[ℂ] (H → ℂ)) (Tp φ v) h

end Step

section Adj

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

def IsAdjOf (ipM : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (ipN : N →ₗ[ℂ] N →ₗ⋆[ℂ] ℂ) (A : M →ₗ[ℂ] N) (B : N →ₗ[ℂ] M) : Prop :=
  ∀ x y, ipN (A x) y = ipM x (B y)

theorem IsAdjOf.unique {ipM : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ} {ipN : N →ₗ[ℂ] N →ₗ⋆[ℂ] ℂ} {A : M →ₗ[ℂ] N}
    {B B' : N →ₗ[ℂ] M} (hnd : ∀ z, (∀ x, ipM x z = 0) → z = 0)
    (h : IsAdjOf ipM ipN A B) (h' : IsAdjOf ipM ipN A B') : B = B' := by
  refine LinearMap.ext fun y => sub_eq_zero.1 (hnd _ fun x => ?_)
  rw [map_sub, ← h x y, ← h' x y, sub_self]

end Adj

section Chain

variable {G : ℕ → Type*} {D : ℕ → Type*} [∀ j, AddCommGroup (D j)] [∀ j, Module ℂ (D j)]
  (CC : ∀ j, Submodule ℂ (D j →ₗ[ℂ] (G j → ℂ)))

end Chain

section Rows

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

def Umu (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) : Submodule ℂ V0 := LinearMap.ker (dn ∘ₗ V0.subtype)

abbrev Qmu (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) : Type _ := V0 ⧸ Umu dn V0

def iota (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) : Qmu dn V0 →ₗ[ℂ] N :=
  (Umu dn V0).liftQ (dn ∘ₗ V0.subtype) le_rfl

end Rows

section ThetaP

variable {G' H' S' Sinf' TK Tau : Type*} [MeasurableSpace H']
  [AddCommGroup Sinf'] [Module ℂ Sinf'] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]

def thetaPInt (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (f : H' → Tau) (e : TK) (g : G') : ℂ :=
  ∫ h in 𝓕, th g h (pt (io e (f h))) ∂ν

structure IsThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (A : Submodule ℂ (H' → Tau))
    (thP : A →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))) : Prop where

  integ : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν

  eq : ∀ f : A, ∀ e g, thP f e g = thetaPInt ν 𝓕 th pt io f e g

theorem IsThetaP.unique {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Sinf' → S'}
    {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf'} {A : Submodule ℂ (H' → Tau)}
    {thP thP' : A →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))}
    (h : IsThetaP ν 𝓕 th pt io A thP) (h' : IsThetaP ν 𝓕 th pt io A thP') : thP = thP' := by
  refine LinearMap.ext fun f => LinearMap.ext fun e => funext fun g => ?_
  rw [h.eq, h'.eq]

variable {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]

def Zj (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (thP : A →ₗ[ℂ] Amb) (good : Submodule ℂ A) : Submodule ℂ A :=
  (LinearMap.ker thP).orthogonalBilin ipA ⊓ good

def IsLamP {Sig : Type*} (thW : A →ₗ[ℂ] Amb) (adj : Amb →ₗ[ℂ] A) (part : Sig → Submodule ℂ Amb)
    (lam : Sig → ℝ) : Prop :=
  ∀ σ, ∀ x ∈ part σ, thW (adj x) = (lam σ : ℂ) • x

theorem IsLamP.unique {Sig : Type*} {thW : A →ₗ[ℂ] Amb} {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb}
    {lam lam' : Sig → ℝ} (h : IsLamP thW adj part lam) (h' : IsLamP thW adj part lam') {σ : Sig}
    (hσ : part σ ≠ ⊥) : lam σ = lam' σ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h2 : ((lam σ : ℂ) - lam' σ) • x = 0 := by rw [sub_smul, ← h σ x hx, ← h' σ x hx, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact_mod_cast sub_eq_zero.1 h3
  · exact absurd h3 hx0

end ThetaP

section Kap

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

def IsKap {Tup Sig : Type*} (m : ℕ) (dnup : Tup → N →ₗ[ℂ] N) (partE : Sig → Submodule ℂ N)
    (lam : Tup → ℕ → Sig → ℝ) (κ : ℝ) : Prop :=
  ∀ μ σ, ∀ x ∈ partE σ, dnup μ x = ((κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ) • x

theorem IsKap.unique {Tup Sig : Type*} {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam : Tup → ℕ → Sig → ℝ} {κ κ' : ℝ} (h : IsKap m dnup partE lam κ) (h' : IsKap m dnup partE lam κ')
    (μ : Tup) (σ : Sig) (hσ : partE σ ≠ ⊥) (hl : ∏ j ∈ Finset.Icc 1 m, lam μ j σ ≠ 0) : κ = κ' := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h2 : (((κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ) -
      ((κ' * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ)) • x = 0 := by
    rw [sub_smul, ← h μ σ x hx, ← h' μ σ x hx, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · have h4 : κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ = κ' * ∏ j ∈ Finset.Icc 1 m, lam μ j σ := by
      exact_mod_cast sub_eq_zero.1 h3
    exact mul_right_cancel₀ hl h4
  · exact absurd h3 hx0

end Kap

section Bu

variable {M N Mu : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

def IsBu (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (Bt : Mu → V0 → ℂ) (B : Mu → N → ℂ) : Prop :=
  ∀ φ (x : V0), B φ (iota dn V0 (Submodule.Quotient.mk x)) = Bt φ x

theorem IsBu.unique {dn : M →ₗ[ℂ] N} {V0 : Submodule ℂ M} {Bt : Mu → V0 → ℂ} {B B' : Mu → N → ℂ}
    (h : IsBu dn V0 Bt B) (h' : IsBu dn V0 Bt B') (φ : Mu) {y : N}
    (hy : y ∈ LinearMap.range (iota dn V0)) : B φ y = B' φ y := by
  obtain ⟨q, rfl⟩ := hy
  induction q using Submodule.Quotient.induction_on with
  | H x => rw [h φ x, h' φ x]

def zeta {I : Type*} [Monoid I] (ξ : I →* Circle) (a : I) : ℂ := ξ a

end Bu

section Statements

variable {M N Mu : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

def UpLiftInProjectedFormSpace (up : N →ₗ[ℂ] M) (EE : Submodule ℂ N) (V0 : Submodule ℂ M) : Prop := EE.map up ≤ V0

def pet {X : Type*} [MeasurableSpace X] (ν : Measure X) (𝓕 : Set X) (f₁ f₂ : X → ℂ) : ℂ :=
  ∫ x in 𝓕, f₁ x * starRingEnd ℂ (f₂ x) ∂ν

end Statements

section Kernels

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (xi0 : E)

variable (F) in

def intAfF : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

variable (F E) in

def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAfF F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def HasInfExpF (χ : (AEF F E)ˣ →* Circle) (τ : Tau) (a : ℚ) : Prop :=
  ∃ n : ℤ, (n : ℚ) = 2 * a ∧
    AllSome (IsInfFamF (F := F) tauE) fun θ =>
      ∀ x : (AEF F E)ˣ, finPartF F E (x : AEF F E) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPartF F E (x : AEF F E)) = 1) →
        ((χ x : Circle) : ℂ) = (θ τ (infPartF F E (x : AEF F E)) / (‖θ τ (infPartF F E (x : AEF F E))‖ : ℂ)) ^ n

end Kernels

end Formalism.IndefR.LiftF

end
