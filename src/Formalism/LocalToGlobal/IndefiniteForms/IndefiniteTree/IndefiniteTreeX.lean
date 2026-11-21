import Mathlib
import Formalism.HarderNarasimhan.Statement
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolydiscIntegrality.ExistsCoordBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.KernelExtensionOfKoszulLoweringImageLeviWeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Decomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.ProjKillsLiPow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.OfListTakeOfFn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuasiRegularSequence.RegularSequencePowerExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MiracleFlatness.MiracleFlatOfRegSeqDepth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MiracleFlatness.MulXProjQExact
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.EagonNorthcottExactOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.AugmentationDegreeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionLowersSecondDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.ExactSecondDegreeZeroOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.BasisZeroEqSingle
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.CardFilterLtInsert
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.LatticeInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottComplex.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottComplex.WregOfSubsingleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottComplex.StBaseOf

noncomputable section

open Complex

universe u

namespace Formalism.L2.Indef.Tree

def eisensteinE4 (τ : ℂ) : ℂ :=
  1 + 240 * ∑' n : ℕ, (ArithmeticFunction.sigma 3 (n + 1) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * τ) ^ (n + 1)

def jInv (τ : ℂ) : ℂ := eisensteinE4 τ ^ 3 / ModularForm.eta τ ^ 24

def reducedForms (D : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc 1 |D| ×ˢ (Finset.Icc (-|D|) |D| ×ˢ Finset.Icc 1 |D|))).filter fun f =>
    f.2.1 ^ 2 - 4 * f.1 * f.2.2 = D ∧ |f.2.1| ≤ f.1 ∧ f.1 ≤ f.2.2 ∧
      ((|f.2.1| = f.1 ∨ f.1 = f.2.2) → 0 ≤ f.2.1) ∧ Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1

def formRoot (D : ℤ) (f : ℤ × ℤ × ℤ) : ℂ :=
  (-(f.2.1 : ℂ) + Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) / (2 * (f.1 : ℂ))

def jacobiDChar (d : ℕ) [NeZero d] (hd : 1 < d) : DirichletCharacter ℂ d where
  toFun a := ((jacobiSym (a.val : ℤ) d : ℤ) : ℂ)
  map_one' := by
    have : (1 : ZMod d).val = 1 := by
      have : Fact (1 < d) := ⟨hd⟩
      exact ZMod.val_one d
    simp [this, jacobiSym.one_left]
  map_mul' a b := by
    have h : (((a * b).val : ℕ) : ℤ) = ((a.val : ℤ) * (b.val : ℤ)) % (d : ℤ) := by
      rw [ZMod.val_mul]; push_cast [Int.natCast_mod]; rfl
    simp only [h, ← jacobiSym.mod_left, jacobiSym.mul_left]
    push_cast; ring
  map_nonunit' a ha := by
    have hc : ¬ a.val.Coprime d := by
      rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    have : jacobiSym (a.val : ℤ) d = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hc
    show ((jacobiSym (a.val : ℤ) d : ℤ) : ℂ) = 0
    rw [this]
    simp

namespace KoszulExact

def form {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) : Module.Dual R (Fin D → R) :=
  ∑ i, s i • (LinearMap.proj i : (Fin D → R) →ₗ[R] R)

def dK {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) :
    ExteriorAlgebra R (Fin D → R) →ₗ[R] ExteriorAlgebra R (Fin D → R) :=
  CliffordAlgebra.contractLeft (form s)

end KoszulExact

def KoszulExact : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
      (∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ ⋀[R]^(j + 1) (Fin D → R) →
          KoszulExact.dK s x = 0 → ∃ y ∈ ⋀[R]^(j + 2) (Fin D → R), KoszulExact.dK s y = x) ∧
      (∀ r : R, (∃ y ∈ ⋀[R]^1 (Fin D → R), KoszulExact.dK s y = algebraMap R _ r) ↔
          r ∈ Ideal.span (Set.range s))

namespace EagonNorthcott

def lin {R : Type*} [CommRing R] {D : ℕ} (x : Fin D → R) (c : Fin D → ℤ) : R :=
  ∑ i, (c i : R) * x i

def dmap {R : Type*} [CommRing R] {D m n : ℕ} (x : Fin D → R) (C : Matrix (Fin m) (Fin n) (Fin D → ℤ)) :
    (Fin n → R) →ₗ[R] (Fin m → R) :=
  Matrix.mulVecLin (C.map (lin x))

def aug {R : Type*} [CommRing R] {D m : ℕ} (x : Fin D → R) (e : Fin m → Fin D → ℕ) : (Fin m → R) →ₗ[R] R :=
  ∑ k, (∏ i, x i ^ e k i) • (LinearMap.proj k : (Fin m → R) →ₗ[R] R)

def Shape (D a : ℕ) (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ)
    (_C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) : Prop :=
  (∀ j, max D 1 ≤ j → n j = 0) ∧ Function.Injective e ∧ ∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a

def Resolves {R : Type*} [CommRing R] {D : ℕ} (x : Fin D → R) (a : ℕ) {n : ℕ → ℕ} (e : Fin (n 0) → Fin D → ℕ)
    (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) : Prop :=
  LinearMap.range (aug x e) = Ideal.span (Set.range x) ^ a ∧
    LinearMap.ker (aug x e) = LinearMap.range (dmap x (C 0)) ∧
    ∀ j, LinearMap.ker (dmap x (C j)) = LinearMap.range (dmap x (C (j + 1)))

end EagonNorthcott

open EagonNorthcott in

def EagonNorthcott : Prop :=
  ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Shape D a n e C ∧
      ∀ (R : Type u) [CommRing R] (x : Fin D → R),
        RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) → Resolves x a e C

open scoped InnerProductSpace

def succMin {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin i → EuclideanSpace ℝ (Fin N),
    (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}

def dualZ {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Submodule ℤ (EuclideanSpace ℝ (Fin N)) where
  carrier := {x | ∀ y ∈ M, ∃ z : ℤ, ⟪x, y⟫_ℝ = z}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z1, h1⟩ := ha y hy
    obtain ⟨z2, h2⟩ := hb y hy
    exact ⟨z1 + z2, by rw [inner_add_left, h1, h2]; push_cast; ring⟩
  zero_mem' := fun y _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha y hy
    obtain ⟨z, h⟩ := ha y hy
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, real_inner_smul_left, h]; push_cast; ring⟩

def TransferenceMinima : Prop :=
  ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))),
    DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ →
    ∀ i, 1 ≤ i → i ≤ N → succMin M i * succMin (dualZ M) (N + 1 - i) ≤ N

def copies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ) (M : Submodule ℤ E) :
    Submodule ℤ (PiLp 2 (fun _ : Fin k => E)) where
  carrier := {x | ∀ i, WithLp.ofLp x i ∈ M}
  add_mem' := fun {a b} ha hb i => by simpa using M.add_mem (ha i) (hb i)
  zero_mem' := fun i => by simp
  smul_mem' := fun c {x} hx i => by simpa using M.smul_mem c (hx i)

theorem reduced_forms_neg_four : reducedForms (-4) = {(1, 0, 1)} := by decide

theorem premises_satisfiable₂ :
    (7 % 16 = 7 ∧ Squarefree 7) ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, |(Polynomial.X : Polynomial ℝ).eval x| ≤ 1) ∧
    0 < Complex.I.im ∧ 0 < (Complex.I / 1).im ∧ (reducedForms (-4)).Nonempty ∧
    RingTheory.Sequence.IsWeaklyRegular ℤ (List.ofFn (fun _ : Fin 1 => (2 : ℤ))) ∧
    RingTheory.Sequence.IsRegular ℤ ([] : List ℤ) ∧
    (∀ z : Fin 1 → ℂ_[2], (∀ i, ‖z i‖ < 1) →
      Summable (fun α : Fin 1 →₀ ℕ => (0 : ℂ_[2]) * ∏ i, z i ^ α i) ∧
      ‖∑' α : Fin 1 →₀ ℕ, (0 : ℂ_[2]) * ∏ i, z i ^ α i‖ ≤ 1) := by
  refine ⟨⟨by norm_num, (by norm_num : Nat.Prime 7).prime.squarefree⟩,
    fun x hx => by simp only [Polynomial.eval_X]; rw [abs_le]; constructor <;> linarith [hx.1, hx.2],
    by simp, by simp, by rw [reduced_forms_neg_four]; simp, ?_, ⟨RingTheory.Sequence.IsWeaklyRegular.nil ℤ ℤ, by simp⟩, ?_⟩
  · simp only [List.ofFn_succ, List.ofFn_zero]
    rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b h
    simp only [smul_eq_mul] at h
    omega
  · intro z _
    simp

end Formalism.L2.Indef.Tree
