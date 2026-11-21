import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Model

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem fr_alg (m : ℕ) (x : ℚ_[l]) : fr l m (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x) = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x :=
  (frobUr l ^ m).commutes x

theorem kd_alg (x : ℚ_[l]) : kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x) = algebraMap ℚ_[l] P.R.BdR x := by
  change algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) x) = _
  rw [← IsScalarTower.algebraMap_apply]

theorem ks_alg (x : ℚ_[l]) : ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x) = Polynomial.C (algebraMap ℚ_[l] P.R.B x) := by
  change Polynomial.C (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x)) = _
  rw [← IsScalarTower.algebraMap_apply]

variable {n : Type} [Fintype n] [DecidableEq n]

def diagU {R : Type} [CommRing R] (u : n → Rˣ) : GL n R where
  val := Matrix.diagonal fun j => (u j : R)
  inv := Matrix.diagonal fun j => (((u j)⁻¹ : Rˣ) : R)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

def cycSum (K : FinExt l) (a : n → ℤ) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) where
  toFun g := diagU fun j => Units.map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) : ℚ_[l] →* ↥(MaximalUnramifiedExtension l)) (P.χQ (g : GQ l) ^ a j)
  map_one' := by ext i j; simp [diagU]
  map_mul' g h := by
    apply Units.ext
    simp [diagU, Matrix.diagonal_mul_diagonal, mul_zpow]

theorem cycSum_val (K : FinExt l) (a : n → ℤ) (g : ↥(GK K)) : (cycSum P K a g : Matrix n n ↥(MaximalUnramifiedExtension l)) =
    Matrix.diagonal fun j => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((P.χQ (g : GQ l) ^ a j : ℚ_[l]ˣ) : ℚ_[l]) := rfl

theorem isRat_cycSum {K : FinExt l} {r : ℕ} (hr : 0 < r) (hK : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1)
    (a : n → ℤ) : IsRat r (cycSum P K a) where
  pos := hr
  le := hK
  rat g i j := by
    rw [cycSum_val, Matrix.diagonal_apply]
    split_ifs
    · exact fr_alg _ _
    · exact map_zero _
  cont i j := by
    simp only [cycSum_val, Matrix.diagonal_apply]
    split_ifs
    · have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
      have h2 : Continuous fun g : ↥(GK K) => (P.χQ (g : GQ l) : ℚ_[l]) ^ a i :=
        (h.comp continuous_subtype_val).zpow₀ _ fun g => Or.inl (Units.ne_zero _)
      have h3 := (continuous_algebraMap ℚ_[l] (Om l)).comp h2
      refine h3.congr fun g => ?_
      simp only [Function.comp, Units.val_zpow_eq_zpow_val]
      rfl
    · exact continuous_const

def tU : P.R.Bˣ := (isUnit_tB P).unit

theorem actQ_tU (g : GQ l) (a : ℤ) : P.actQ g ((tU P ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P := by
    apply Units.ext
    simpa [tU, Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem actdR_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
  exact h.symm

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  change P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)
  rw [actdR_ι, actQ_tU, map_mul, AlgHom.commutes]

theorem deRham_of_framed {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hρ : IsRat r ρ)
    {w : Fin r → n → ℤ} (h : Framed P ρ w) : AdmDR P ρ := by
  intro m
  obtain ⟨U, -, hU⟩ := h ⟨m % r, Nat.mod_lt _ hρ.pos⟩
  have hper : ∀ g, matD P ρ m g = matD P ρ (m % r) g := fun g => by
    ext i j
    simp only [matD, Matrix.map_apply]
    congr 1
    have h1 : ∀ k : ℕ, (frobUr l ^ (r * k)) ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]; erw [hρ.rat g i j]; exact ih
    change (frobUr l ^ m) _ = (frobUr l ^ (m % r)) _
    conv_lhs => rw [← Nat.mod_add_div m r, pow_add, AlgHom.mul_apply, h1]
  set v := w ⟨m % r, Nat.mod_lt _ hρ.pos⟩
  refine ⟨U * diagU fun j => Units.map (P.ιB : P.R.B →* P.R.BdR) (tU P ^ (-v j)), fun g => ?_⟩
  have e : (diagU fun j => Units.map (P.ιB : P.R.B →* P.R.BdR) (tU P ^ (-v j)) : GL n P.R.BdR).val =
    Matrix.diagonal fun j => tz P (-v j) := rfl
  rw [Units.val_mul, e, hper, Matrix.map_mul, ← Matrix.mul_assoc, hU g, Matrix.diagonal_map (by simp),
    Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 2
  funext j
  rw [act_tz, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel]
  simp

end GlobalTheory.PMon.Model

end
