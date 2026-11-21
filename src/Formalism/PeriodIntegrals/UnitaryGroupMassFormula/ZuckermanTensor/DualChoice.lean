import Mathlib
import Formalism.PeriodIntegrals.ZuckTensor

section
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

def Cj (H : Type) : Type := H

namespace Cj
variable {H : Type}

def mk (x : H) : Cj H := x

def un (x : Cj H) : H := x

@[simp] theorem un_mk (x : H) : un (mk x) = x := rfl
@[simp] theorem mk_un (x : Cj H) : mk (un x) = x := rfl

instance [NormedAddCommGroup H] : NormedAddCommGroup (Cj H) := inferInstanceAs (NormedAddCommGroup H)

instance [NormedAddCommGroup H] [CompleteSpace H] : CompleteSpace (Cj H) := inferInstanceAs (CompleteSpace H)

instance [NormedAddCommGroup H] [Nontrivial H] : Nontrivial (Cj H) := inferInstanceAs (Nontrivial H)

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : Module ℂ (Cj H) := Module.compHom H (starRingEnd ℂ)

theorem un_smul (c : ℂ) (x : Cj H) : un (c • x) = (starRingEnd ℂ) c • un x := rfl

instance : NormedSpace ℂ (Cj H) where
  norm_smul_le c x := by
    show ‖(starRingEnd ℂ) c • un x‖ ≤ ‖c‖ * ‖un x‖
    rw [norm_smul, RCLike.norm_conj]

instance : InnerProductSpace ℂ (Cj H) where
  inner x y := ⟪un y, un x⟫_ℂ
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) (un x)
  conj_inner_symm x y := inner_conj_symm (un y) (un x)
  add_left x y z := inner_add_right (un z) (un x) (un y)
  smul_left x y r := by
    show ⟪un y, (starRingEnd ℂ) r • un x⟫_ℂ = (starRingEnd ℂ) r * ⟪un y, un x⟫_ℂ
    rw [inner_smul_right]

theorem inner_def (x y : Cj H) : ⟪x, y⟫_ℂ = ⟪un y, un x⟫_ℂ := rfl

end Cj

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cjOp (T : H →L[ℂ] H) : Cj H →L[ℂ] Cj H :=
  LinearMap.mkContinuous
    { toFun := fun x => Cj.mk (T (Cj.un x))
      map_add' := fun x y => by
        show T (Cj.un x + Cj.un y) = T (Cj.un x) + T (Cj.un y)
        exact map_add T _ _
      map_smul' := fun c x => by
        show T ((starRingEnd ℂ) c • Cj.un x) = (starRingEnd ℂ) c • T (Cj.un x)
        exact map_smul T _ _ }
    ‖T‖ (fun x => T.le_opNorm (Cj.un x))

theorem cjOp_apply (T : H →L[ℂ] H) (x : Cj H) : Cj.un (cjOp T x) = T (Cj.un x) := rfl

variable {n : ℕ}

def revM (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := g.submatrix Fin.rev Fin.rev

def revE (ε : Fin n → Bool) : Fin n → Bool := fun a => ε (Fin.rev a)

def revP (lam : Fin n → ℝ) : Fin n → ℝ := fun a => - lam (Fin.rev a)

def sigC (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Matrix (Fin n) (Fin n) ℂ → (Cj H →L[ℂ] Cj H) :=
  fun g => cjOp (σ (revM g))

end PI.ZuckTensorWork
end
end

section
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

section Sub
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cjSub (S : Submodule ℂ H) : Submodule ℂ (Cj H) where
  carrier := {x | Cj.un x ∈ S}
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun c _ hx => S.smul_mem ((starRingEnd ℂ) c) hx

def cjSubInv (S : Submodule ℂ (Cj H)) : Submodule ℂ H where
  carrier := {x | Cj.mk x ∈ S}
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun c x hx => by
    have h : (starRingEnd ℂ) c • Cj.mk x ∈ S := S.smul_mem ((starRingEnd ℂ) c) hx
    have e : (starRingEnd ℂ) c • Cj.mk x = Cj.mk (c • x) := by
      show (starRingEnd ℂ) ((starRingEnd ℂ) c) • x = c • x
      rw [Complex.conj_conj]
    show Cj.mk (c • x) ∈ S
    rw [← e]
    exact h

end Sub

def HCRev : Prop := ∀ (n : ℕ) (lam : Fin n → ℝ), IsHCParam lam → IsHCParam (revP lam)

def GapRev : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), GapAtLeast ε lam h → GapAtLeast (revE ε) (revP lam) h

def LowKRev : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), lowK (revE ε) (revP lam) = revP (lowK ε lam)

def VNormRev : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (ν : Fin n → ℝ), vNormSq (revE ε) (revP ν) = vNormSq ε ν

def CDomRev : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ Λ : Fin n → ℝ), CDom ε μ Λ → CDom (revE ε) (revP μ) (revP Λ)

def URepConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsURepOn (UJset (revE ε)) (sigC σ)

def IrredConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrredOn (UJset ε) σ → IsIrredOn (UJset (revE ε)) (sigC σ)

def SqIntConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntOn ε σ → IsSqIntOn (revE ε) (sigC σ)

def KTypeConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H),
    IsKTypeOf ε σ Λ S → IsKTypeOf (revE ε) (sigC σ) (revP Λ) (cjSub S)

def KTypeConjInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ (Cj H)),
    IsKTypeOf (revE ε) (sigC σ) Λ S → IsKTypeOf ε σ (revP Λ) (cjSubInv S)

def DSConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsDS ε lam σ → IsDS (revE ε) (revP lam) (sigC σ)


theorem revE_revE {n : ℕ} (ε : Fin n → Bool) : revE (revE ε) = ε := by
  funext a; simp [revE]


end PI.ZuckTensorWork
end
end
