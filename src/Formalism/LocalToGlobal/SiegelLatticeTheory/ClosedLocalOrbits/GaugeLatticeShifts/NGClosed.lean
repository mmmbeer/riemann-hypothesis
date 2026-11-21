import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightInvOfModular

section
noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

def PF (ι : Type*) : Subalgebra ℂ ((ι → ℝ) → ℂ) :=
  (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ))).range





end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

section PFm

variable {ι : Type*}






def MPF {α β : Type*} (M : (ι → ℝ) → Matrix α β ℂ) : Prop := ∀ i j, (fun y => M y i j) ∈ PF ι

variable {α β γ : Type*}











end PFm

section Coords

variable {ι : Type*} {n r : ℕ}


theorem hJ_eq_sum (ε : Fin n → Bool) (x v : Fin n → ℂ) :
    hJ ε x v = ∑ i, (star x ᵥ* Formalism.REAL.Jm ε) i * v i := by
  unfold hJ
  rw [Matrix.dotProduct_mulVec]
  rfl




def Fval (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℂ :=
  (∏ l ∈ Finset.Icc 1 r, Dl Z l) * (Gv T T' Z : ℂ)


def Qexpr (T T' : ℝ) (Z0 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (d : ℂ) : ℂ :=
  (∏ l ∈ Finset.Icc 1 r, Dl Z0 l) *
    (Dl Z0 (r + 1) * conj (Dl Z0 (r + 1)) - ((T * T' : ℝ) : ℂ) * (d * conj d) * (Dl Z0 r * conj (Dl Z0 r)))



end Coords

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL

section Pos

variable {n r k : ℕ} (ε : Fin n → Bool)

def hJL (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hJ ε x v
  map_add' v w := UnitaryIsometries.hJ_add_right ε x v w
  map_smul' a v := by simp [UnitaryIsometries.hJ_smul_right]

theorem hJ_self_pos {x : Fin n → ℂ} (hx : ∀ i, ε i = false → x i = 0) (hx0 : x ≠ 0) : 0 < (hJ ε x x).re := by
  have h : hJ ε x x = ∑ i, ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    unfold hJ Jm
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ε i = true
    · simp only [hi, if_true, one_mul]
      rw [mul_comm]
      push_cast
      exact Complex.mul_conj' (x i)
    · have : x i = 0 := hx i (by simpa using hi)
      simp [this]
  rw [h, Complex.re_sum]
  simp only [Complex.ofReal_re]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hx0 (funext h')
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩

end Pos

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} (ε : Fin n → Bool)

structure Frm (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ep : ∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0
  pp : ∀ a b, hJ ε (p a) (p b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  pz : ∀ a, hJ ε (p a) z = 0
  zz : hJ ε z z = -(T : ℂ)
  ew : ∀ a j, hJ ε (e a) (w j) = 0
  pw : ∀ a j, hJ ε (p a) (w j) = 0
  zw : ∀ j, hJ ε z (w j) = 0
  ww : ∀ i j, hJ ε (w i) (w j) = if i = j then 1 else 0
  T_ne : T ≠ 0

variable {ε}

theorem hJ_swap0 {x y : Fin n → ℂ} (h : hJ ε x y = 0) : hJ ε y x = 0 := by
  rw [UnitaryIsometries.hJ_conj, h, map_zero]

theorem hJ_swapδ {ι : Type*} [DecidableEq ι] {x y : ι → Fin n → ℂ} (h : ∀ a b, hJ ε (x a) (y b) = if a = b then 1 else 0)
    (a b : ι) : hJ ε (y b) (x a) = if a = b then 1 else 0 := by
  rw [UnitaryIsometries.hJ_conj, h]
  split_ifs <;> simp

def syn (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ)
    (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) : Fin n → ℂ :=
  ∑ a, α a • e a + ∑ a, β a • p a + (-γ / (T : ℂ)) • z + ∑ j, δ j • w j

section Coord

variable {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ} {T : ℝ}

theorem hJ_syn (x : Fin n → ℂ) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) :
    hJ ε x (syn e p z w T α β γ δ) = ∑ a, α a * hJ ε x (e a) + ∑ a, β a * hJ ε x (p a) +
      (-γ / (T : ℂ)) * hJ ε x z + ∑ j, δ j * hJ ε x (w j) := by
  simp only [syn, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_sum_right]

theorem syn_p (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (p c) (syn e p z w T α β γ δ) = α c := by
  rw [hJ_syn]
  simp [hJ_swapδ F.ep, F.pp, F.pz, F.pw]

theorem syn_e (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (e c) (syn e p z w T α β γ δ) = β c := by
  rw [hJ_syn]
  simp [F.ee, F.ep, F.ez, F.ew]

theorem synthesized_vector_z_pairing (F : Frm ε e p z w T) α β γ δ : hJ ε z (syn e p z w T α β γ δ) = γ := by
  rw [hJ_syn]
  have hT : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F.T_ne
  simp only [fun a => hJ_swap0 (F.ez a), fun a => hJ_swap0 (F.pz a), F.zz, F.zw, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  field_simp

theorem syn_w (F : Frm ε e p z w T) (c : Fin k) α β γ δ : hJ ε (w c) (syn e p z w T α β γ δ) = δ c := by
  rw [hJ_syn]
  simp [fun a => hJ_swap0 (F.ew a c), fun a => hJ_swap0 (F.pw a c), hJ_swap0 (F.zw c), F.ww]

def crd (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ) :=
  (LinearMap.pi fun a => hJL ε (p a)).prod ((LinearMap.pi fun a => hJL ε (e a)).prod
    ((hJL ε z).prod (LinearMap.pi fun j => hJL ε (w j))))

theorem crd_syn (F : Frm ε e p z w T) α β γ δ :
    crd (ε := ε) e p z w (syn e p z w T α β γ δ) = (α, β, γ, δ) := by
  ext c
  · exact syn_p F c α β γ δ
  · exact syn_e F c α β γ δ
  · exact synthesized_vector_z_pairing F α β γ δ
  · exact syn_w F c α β γ δ

theorem recon (F : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) (v : Fin n → ℂ) :
    v = syn e p z w T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  have hsurj : Function.Surjective (crd (ε := ε) e p z w) := fun c =>
    ⟨syn e p z w T c.1 c.2.1 c.2.2.1 c.2.2.2, crd_syn F _ _ _ _⟩
  have hfin : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ ((Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ)) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj
  apply hinj
  rw [crd_syn F]
  rfl

end Coord

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem uMat_inv_mul (g : UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  show (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

theorem uMat_mul_inv (g : UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  show _ * (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_mul (g h : UJ ε) : Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl

theorem inv_fix {g : UJ ε} {v : Fin n → ℂ} (h : Formalism.MainNotions.S.uMat g *ᵥ v = v) : Formalism.MainNotions.S.uMat g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [mulVec_mulVec, uMat_inv_mul, one_mulVec]

theorem fix_span {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ a, g *ᵥ e a = e a) (a : ℕ) :
    ∀ x ∈ spanLt e a, g *ᵥ x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact hg b
  | zero => exact mulVec_zero _
  | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
  | smul c x _ hx => rw [mulVec_smul, hx]

theorem InN_one : InN ε e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨UnitaryIsometries.RI.inS_one e z, fun y _ => by rw [sub_self, zero_mulVec]; exact Submodule.zero_mem _⟩

theorem InN_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InN ε e z g) (hh : InN ε e z h) : InN ε e z (g * h) := by
  refine ⟨UnitaryIsometries.RI.inS_mul e z hg.1 hh.1, fun y hy => ?_⟩
  have key : (g * h - 1) *ᵥ y = g *ᵥ ((h - 1) *ᵥ y) + (g - 1) *ᵥ y := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  rw [key]
  exact Submodule.add_mem _ (UnitaryIsometries.RI.inS_pres e z hg.1 r _ (hh.2 y hy)) (hg.2 y hy)

def NG : Subgroup (UJ ε) where
  carrier := NLoc ε e z
  one_mem' := InN_one ε e z
  mul_mem' {g h} hg hh := InN_mul ε e z hg hh
  inv_mem' {g} hg := by
    have hS : g⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
    refine ⟨hS, fun y hy => ?_⟩
    have key : (Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ y = -(Formalism.MainNotions.S.uMat g⁻¹ *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ y)) := by
      rw [mulVec_mulVec, Matrix.mul_sub, uMat_inv_mul, Matrix.mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec]
      abel
    rw [key]
    exact Submodule.neg_mem _ (UnitaryIsometries.RI.inS_pres e z hS r _ (hg.2 y hy))

def HG : Subgroup (UJ ε) where
  carrier := HLoc ε e p z
  one_mem' := ⟨fun a => one_mulVec _, fun a => one_mulVec _, one_mulVec _⟩
  mul_mem' {g h} hg hh := ⟨fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.1 a, hg.1 a],
    fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.2.1 a, hg.2.1 a],
    by rw [uMat_mul, ← mulVec_mulVec, hh.2.2, hg.2.2]⟩
  inv_mem' {g} hg := ⟨fun a => inv_fix ε (hg.1 a), fun a => inv_fix ε (hg.2.1 a), inv_fix ε hg.2.2⟩

theorem coe_NG : (NG ε e z : Set (UJ ε)) = NLoc ε e z := rfl

theorem coe_HG : (HG ε e p z : Set (UJ ε)) = HLoc ε e p z := rfl

theorem NG_closed : IsClosed (NG ε e z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((UnitaryIsometries.RI.continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (NG ε e z : Set (UJ ε)) = (UnitaryIsometries.RI.SG ε e z : Set (UJ ε)) ∩
      ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0},
        (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ y) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_NG, NLoc, InN, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
    rfl
  rw [e1]
  exact (UnitaryIsometries.RI.SG_closed ε e z).inter (isClosed_biInter fun y _ =>
    (Submodule.closed_of_finiteDimensional _).preimage (hc y))

theorem HG_closed : IsClosed (HG ε e p z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => Formalism.MainNotions.S.uMat g *ᵥ v) := fun v =>
    (UnitaryIsometries.RI.continuous_uMat ε).matrix_mulVec continuous_const
  have e1 : (HG ε e p z : Set (UJ ε)) = (⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ e a = e a}) ∩
      ((⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ p a = p a}) ∩ {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ z = z}) := by
    ext g
    simp only [coe_HG, HLoc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e1]
  exact (isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const))

theorem NG_le_SG : NG ε e z ≤ UnitaryIsometries.RI.SG ε e z := fun _ hg => hg.1

theorem HG_le_SG : HG ε e p z ≤ UnitaryIsometries.RI.SG ε e z := by
  intro g hg
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, one_mulVec, hg.1 a, sub_self]
    exact Submodule.zero_mem _
  · rw [Matrix.sub_mulVec, one_mulVec, hg.2.2, sub_self]
    exact Submodule.zero_mem _

theorem conj_mem {h g : UJ ε} (hh : h ∈ HG ε e p z) (hg : g ∈ NG ε e z) : h * g * h⁻¹ ∈ NG ε e z := by
  have hfix : ∀ a, Formalism.MainNotions.S.uMat h *ᵥ e a = e a := hh.1
  have hfix' : ∀ a, Formalism.MainNotions.S.uMat h⁻¹ *ᵥ e a = e a := fun a => inv_fix ε (hh.1 a)
  have key : ∀ v, (Formalism.MainNotions.S.uMat (h * g * h⁻¹) - 1) *ᵥ v =
      Formalism.MainNotions.S.uMat h *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ v)) := by
    intro v
    rw [uMat_mul, uMat_mul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      uMat_mul_inv, Matrix.sub_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, hfix', fix_span e hfix a.1 _ (hg.1.1 a)]
    exact hg.1.1 a
  · rw [key, inv_fix ε hh.2.2, fix_span e hfix r _ hg.1.2]
    exact hg.1.2
  · have hy' : ∀ a, hJ ε (e a) (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ y) = 0 := by
      intro a
      rw [← hfix' a, UnitaryIsometries.isIsom_uMat ε h⁻¹, hy a]
    rw [key, fix_span e hfix r _ (hg.2 _ hy')]
    exact hg.2 _ hy'

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end
