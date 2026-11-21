import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Density

section
namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set



end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set




end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set




end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Filter Topology Set



end GroundTheory.Automorphic.ArchWhittaker
end

section
namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

noncomputable abbrev πσ : BanachRep FiltrationCocycleLiftCriterion H := BanachRep.ofUnitary σ

abbrev IsSm (v : H) : Prop := hGL2.IsSmoothVector (πσ σ) v

theorem norm_πσ_le (g : FiltrationCocycleLiftCriterion) : ‖πσ σ g‖ ≤ 1 := σ.norm_map_le g

theorem isSm_map {v : H} (hv : IsSm σ v) (g : FiltrationCocycleLiftCriterion) : IsSm σ (σ g v) :=
  hGL2.isSmoothVector_map (πσ σ) hv g

noncomputable abbrev dπ (X : gl2) (v : H) : H := hGL2.derivOp (πσ σ) X v

theorem isSm_dπ {v : H} (hv : IsSm σ v) (X : gl2) : IsSm σ (dπ σ X v) :=
  hGL2.isSmoothVector_derivOp (πσ σ) hv X

variable (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ)

open Classical in

noncomputable def lT (x : H) : ℂ := if hx : IsSm σ x then l ⟨x, hx⟩ else 0

variable {σ l}

theorem lT_of {x : H} (hx : IsSm σ x) : lT σ l x = l ⟨x, hx⟩ := by
  rw [lT, dif_pos hx]


theorem lT_smul {x : H} (hx : IsSm σ x) (c : ℂ) : lT σ l (c • x) = c * lT σ l x := by
  rw [lT_of hx, lT_of ((hGL2.smoothVectors (πσ σ)).smul_mem c hx), ← smul_eq_mul, ← map_smul]; rfl

theorem lT_sub {x y : H} (hx : IsSm σ x) (hy : IsSm σ y) :
    lT σ l (x - y) = lT σ l x - lT σ l y := by
  rw [lT_of hx, lT_of hy, lT_of ((hGL2.smoothVectors (πσ σ)).sub_mem hx hy), ← map_sub]; rfl

theorem lT_zero : lT σ l 0 = 0 := by
  rw [lT_of (hGL2.isSmoothVector_zero (πσ σ))]
  exact map_zero l

variable (σ l)

noncomputable def Wt (u : H) (t : ℝ) : ℂ := lT σ l (σ (aT t) u)

variable {σ l}


theorem Wt_smul {u : H} (hu : IsSm σ u) (c : ℂ) (t : ℝ) : Wt σ l (c • u) t = c * Wt σ l u t := by
  simp only [Wt, map_smul]
  exact lT_smul (isSm_map σ hu _) c

theorem Wt_sub {u v : H} (hu : IsSm σ u) (hv : IsSm σ v) (t : ℝ) :
    Wt σ l (u - v) t = Wt σ l u t - Wt σ l v t := by
  simp only [Wt, map_sub]
  exact lT_sub (isSm_map σ hu _) (isSm_map σ hv _)


theorem lT_dπ_lE (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {β : ℂ}
    (hψ : HasDerivAt ψ β 0)
    (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {w : H} (hw : IsSm σ w) : lT σ l (dπ σ lE w) = β * lT σ l w := by
  have key := hl.hasDerivAt_map_expG (norm_πσ_le σ) hw 1 lE
  have e1 : (fun s : ℝ => l (hGL2.smoothMap (πσ σ) hw (1 * hGL2.expG (s • lE)))) =
      fun s => ψ s * lT σ l w := by
    funext s
    rw [one_mul, expG_lE, ← hW s w hw, lT_of (isSm_map σ hw _)]
    rfl
  rw [e1] at key
  have e2 : l (hGL2.smoothMap (πσ σ) (hGL2.isSmoothVector_derivOp (πσ σ) hw lE) 1) =
      lT σ l (dπ σ lE w) := by
    rw [lT_of (isSm_dπ σ hw lE)]
    congr 1
    apply Subtype.ext
    simp
  rw [e2] at key
  exact key.unique (hψ.mul_const _)

theorem Wt_dπ_lE (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {β : ℂ}
    (hψ : HasDerivAt ψ β 0)
    (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {u : H} (hu : IsSm σ u) (t : ℝ) :
    Wt σ l (dπ σ lE u) t = β * Real.exp (2 * t) * Wt σ l u t := by
  have e : σ (aT t) (dπ σ lE u) = ((Real.exp (2 * t) : ℝ) : ℂ) • dπ σ lE (σ (aT t) u) := by
    have := hGL2.derivOp_map (πσ σ) hu (aT t) lE
    rw [Ad_aT_lE, hGL2.derivOp_smul_left] at this
    rw [Complex.coe_smul]
    exact this.symm
  rw [Wt, e, lT_smul (isSm_dπ σ (isSm_map σ hu _) lE), lT_dπ_lE hl hψ hW (isSm_map σ hu _), Wt]
  ring

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

theorem hasDerivAt_chi (k : ℤ) (t : ℝ) : HasDerivAt (chi k) (chi k t * ((k : ℂ) * I)) t := by
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h1 : HasDerivAt (fun s : ℝ => (k : ℂ) * (s : ℂ) * I) ((k : ℂ) * 1 * I) t :=
    (h0.const_mul (k : ℂ)).mul_const I
  exact h1.cexp.congr_deriv (by simp [chi])

theorem dπ_add_left (X Y : gl2) (u : H) : dπ σ (X + Y) u = dπ σ X u + dπ σ Y u :=
  hGL2.derivOp_add_left _ X Y u

theorem dπ_smul_left (r : ℝ) (X : gl2) (u : H) : dπ σ (r • X) u = r • dπ σ X u :=
  hGL2.derivOp_smul_left _ r X u

theorem dπ_neg_left (X : gl2) (u : H) : dπ σ (-X) u = -dπ σ X u :=
  hGL2.derivOp_neg_left _ X u

theorem dπ_sub_left (X Y : gl2) (u : H) : dπ σ (X - Y) u = dπ σ X u - dπ σ Y u := by
  rw [sub_eq_add_neg, dπ_add_left, dπ_neg_left, ← sub_eq_add_neg]

theorem dπ_lW_of_mem {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) :
    dπ σ lW u = ((k : ℂ) * I) • u := by
  have h1 := hGL2.hasDerivAt_derivOp (πσ σ) hu lW
  have e : (fun t : ℝ => (πσ σ) (hGL2.expG (t • lW)) u) = fun t => chi k t • u := by
    funext t
    rw [expG_lW]
    exact hk t
  rw [e] at h1
  have h2 := (hasDerivAt_chi k 0).smul_const u
  have := h1.unique h2
  rw [show dπ σ lW u = hGL2.derivOp (πσ σ) lW u from rfl, this]
  simp [chi]

theorem lS_eq_two_lE_sub_lW : lS = (2 : ℝ) • lE - lW := by
  apply Subtype.ext
  simp only [coe_lS, Submodule.coe_sub, Submodule.coe_smul, coe_lE, coe_lW]
  ext i j; fin_cases i <;> fin_cases j <;> simp; norm_num

theorem dπ_lS (u : H) : dπ σ lS u = (2 : ℝ) • dπ σ lE u - dπ σ lW u := by
  rw [lS_eq_two_lE_sub_lW, dπ_sub_left, dπ_smul_left]

noncomputable def Rop (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (u : H) : H := dπ σ lH u + I • dπ σ lS u

noncomputable def Lop (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (u : H) : H := dπ σ lH u - I • dπ σ lS u



theorem map_dπ {u : H} (hu : IsSm σ u) (g : FiltrationCocycleLiftCriterion) (X : gl2) :
    σ g (dπ σ X u) = dπ σ (hGL2.Ad g X) (σ g u) :=
  (hGL2.derivOp_map (πσ σ) hu g X).symm

theorem dπ_smul_vec {u : H} (hu : IsSm σ u) (c : ℂ) (X : gl2) : dπ σ X (c • u) = c • dπ σ X u :=
  hGL2.derivOp_smul (πσ σ) hu c X

theorem exp_two_mul_I (θ : ℝ) :
    Complex.exp ((2 : ℂ) * θ * I) = (Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * I := by
  rw [show (2 : ℂ) * θ * I = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem Rop_mem {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) :
    Rop σ u ∈ weightSpace σ (k + 2) := by
  intro θ
  simp only [Rop, map_add, map_smul, map_dπ hu, Ad_kMat_lH, Ad_kMat_lS, hk θ, dπ_smul_vec hu,
    dπ_sub_left, dπ_add_left, dπ_smul_left]
  have hchi : chi (k + 2) θ = chi k θ * ((Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * I) := by
    rw [← exp_two_mul_I, chi, chi, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hchi]
  simp only [← Complex.coe_smul]
  match_scalars
  all_goals ring_nf
  all_goals (try simp only [Complex.I_sq])
  all_goals ring


theorem inner_dπ_left {v w : H} (hv : IsSm σ v) (hw : IsSm σ w) (X : gl2) :
    ⟪dπ σ X v, w⟫_ℂ = -⟪v, dπ σ X w⟫_ℂ := by
  have hv' := hGL2.hasDerivAt_derivOp (πσ σ) hv X
  have hw' := hGL2.hasDerivAt_derivOp (πσ σ) hw X
  have hd := hv'.inner ℂ hw'
  have hconst : (fun t : ℝ => ⟪(πσ σ) (hGL2.expG (t • X)) v, (πσ σ) (hGL2.expG (t • X)) w⟫_ℂ) =
      fun _ => ⟪v, w⟫_ℂ := by
    funext t; exact σ.inner_map_map _ v w
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const 0 _)
  simp only [zero_smul, IsExpLieAlgebra.expG_zero, BanachRep.map_one_apply] at h0
  linear_combination h0



end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H} {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}

noncomputable def bT (β : ℂ) (t : ℝ) : ℂ := 2 * I * β * (Real.exp (2 * t) : ℂ)

section Whittaker

variable (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {β : ℂ} (hψ : HasDerivAt ψ β 0)
  (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
include hl hψ hW

theorem Wt_dπ_lS {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) (t : ℝ) :
    Wt σ l (dπ σ lS u) t = (2 * β * Real.exp (2 * t) - (k : ℂ) * I) * Wt σ l u t := by
  rw [dπ_lS, ← Complex.coe_smul, Wt_sub ((hGL2.smoothVectors (πσ σ)).smul_mem _ (isSm_dπ σ hu lE))
    (isSm_dπ σ hu lW), Wt_smul (isSm_dπ σ hu lE), Wt_dπ_lE hl hψ hW hu, dπ_lW_of_mem hu hk,
    Wt_smul hu]
  push_cast
  ring





end Whittaker

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H} {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}







end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}



section Whittaker

variable {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
  (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {θ : ℝ} (hψ : HasDerivAt ψ (I * θ) 0)
  (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
include hl hψ hW





end Whittaker





end GroundTheory.Automorphic.ArchWhittaker
end

section
namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

theorem det_eps : (((eps : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  simp [Matrix.det_fin_two_of]



end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

def IsWhit (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (ψ : ℝ → ℂ) (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w

omit [CompleteSpace H] in
theorem eq_zero_of_mem_bot {V : Submodule ℂ H} (hV : V = ⊥) {u : H} (hu : u ∈ V) : u = 0 := by
  rw [hV, Submodule.mem_bot] at hu; exact hu



end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

noncomputable def whitSpace (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (ψ : ℝ → ℂ) :
    Submodule ℂ (hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) where
  carrier := {l | ∀ (x : ℝ) (w : hGL2.SmoothFrechet (πσ σ)),
    l (hGL2.smoothOp (πσ σ) (nMat x) w) = ψ x * l w}
  add_mem' {a b} ha hb := fun x w => by
    show a _ + b _ = ψ x * (a w + b w)
    rw [ha x w, hb x w]; ring
  zero_mem' := fun x w => by
    show (0 : ℂ) = ψ x * 0
    ring
  smul_mem' c a ha := fun x w => by
    show c * a _ = ψ x * (c * a w)
    rw [ha x w]; ring

noncomputable def toLin (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ where
  toFun w := l w
  map_add' a b := l.map_add a b
  map_smul' c a := l.map_smul c a

end GroundTheory.Automorphic.ArchWhittaker
end
