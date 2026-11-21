import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

abbrev Orb {n : ℕ} (w : Pt E n) : Type := (IL n → E) × (IN w → E)

def orbMat {n : ℕ} (w : Pt E n) (xy : Orb w) : Matrix (Fin n) (Fin n) E :=
  uLow xy.1 * w.mat * uUp w xy.2

def orbMeas (M : Model F E) {n : ℕ} (w : Pt E n) : Measure (Orb w) :=
  (Measure.pi fun _ : IL n => M.mu).prod (Measure.pi fun _ : IN w => M.mu)

def phase (M : Model F E) {n : ℕ} (w : Pt E n) (xy : Orb w) : ℂ :=
  M.psiR (simpleLow (uLow xy.1) + simpleUp (uUp w xy.2))

def IsInt (M : Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a b, Z a b ∈ M.R) ∧ IsUnit Z.det

def toMat (M : Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) (h : IsInt M Z) : M.Mat n :=
  ⟨Matrix.of fun a b => ⟨Z a b, h.1 a b⟩, by
    have : (Matrix.of fun a b => (⟨Z a b, h.1 a b⟩ : M.R)).map M.R.subtype = Z := rfl
    rw [this]; exact h.2⟩

open scoped Classical in

def nIsoK (M : Model F E) {m : ℕ} (Z Z' : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : ℕ :=
  if h : IsInt M Z ∧ IsInt M Z' then M.nIso (toMat M Z h.1) (toMat M Z' h.2) else 0

def rowRaw (M : Model F E) {n : ℕ} (ZZ : M.Mat n) (j : Fin n) :
    (Fin n → M.R) →ₗ[M.R] E ⧸ M.Rsub :=
  M.Rsub.mkQ ∘ₗ (LinearMap.proj j) ∘ₗ
    ((ZZ.Z.map M.R.subtype)⁻¹.mulVecLin.restrictScalars M.R) ∘ₗ
    (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin n))

lemma rowRaw_range (M : Model F E) {n : ℕ} (ZZ : M.Mat n) (j : Fin n) :
    LinearMap.range ZZ.Z.mulVecLin ≤ LinearMap.ker (rowRaw M ZZ j) := by
  rintro _ ⟨x, rfl⟩
  simp only [rowRaw, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have h1 : (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin n)) (ZZ.Z.mulVecLin x)
      = (ZZ.Z.map M.R.subtype).mulVec (fun j => (x j : E)) := by
    funext i
    simp only [LinearMap.compLeft_apply, Function.comp_apply, Matrix.mulVecLin_apply,
      Algebra.linearMap_apply]
    exact RingHom.map_mulVec M.R.subtype ZZ.Z x i
  rw [h1]
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ZZ.unit, Matrix.one_mulVec, LinearMap.proj_apply]
  exact ⟨x j, rfl⟩

def lamJ (M : Model F E) {n : ℕ} (ZZ : M.Mat n) (j : Fin n) : M.Cok ZZ →ₗ[M.R] E ⧸ M.Rsub :=
  Submodule.liftQ _ (rowRaw M ZZ j) (rowRaw_range M ZZ j)

def TT (M : Model F E) {m : ℕ} (k : ℕ) (ZZ ZZ' : M.Mat (m + 1)) : Set (M.Iso ZZ ZZ') :=
  {φ | ∀ j : Fin (m + 1), k ≤ (j : ℕ) →
    (lamJ M ZZ' j) ∘ₗ (φ.1 : M.Cok ZZ →ₗ[M.R] M.Cok ZZ') - lamJ M ZZ j ∈
      Submodule.span M.R {f | ∃ l : Fin (m + 1), j < l ∧ f = lamJ M ZZ l}}

open scoped Classical in

def nTT (M : Model F E) {m : ℕ} (k : ℕ) (Z Z' : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : ℕ :=
  if h : IsInt M Z ∧ IsInt M Z' then Nat.card (TT M k (toMat M Z h.1) (toMat M Z' h.2)) else 0

open scoped Classical in

def NsE (M : Model F E) {m : ℕ} (s : ℕ+) (z : E) (h h' : Pt E m) : ℂ :=
  if hz : IsUnit z then M.Ns s hz.unit hz.unit h h' else 0

def volK (M : Model F E) (n : ℕ) : Measure (Fin n → E) := Measure.pi fun _ => M.mu

def quadPhase (M : Model F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : ℂ :=
  M.psiR (algebraMap F E (1 / 2) * dotProduct x (H.mulVec x))

def gaussI (M : Model F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E)) : ℂ :=
  ∫ x in S, quadPhase M H x ∂(volK M n)

def IsIndex (M : Model F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (γ : ℂ) : Prop :=
  ∃ S : Set (Fin n → E), IsCompact S ∧ ∀ L : AddSubgroup (Fin n → E),
    IsCompact (L : Set (Fin n → E)) → IsOpen (L : Set (Fin n → E)) → S ⊆ L →
      gaussI M H L = γ * ((M.modK H.det ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

def index (M : Model F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) : ℂ :=
  Classical.epsilon (IsIndex M H)

def hess (E : Type) [CommRing E] (m : ℕ) : Matrix (Fin m) (Fin m) E := 1 + Matrix.of fun _ _ => 1

def gaS (M : Model F E) (m : ℕ) (y : Eˣ) : ℂ := index M (((y⁻¹ : Eˣ) : E) • hess E m)

def gD {E : Type} [CommRing E] {m : ℕ} (D : E) (x : Fin m → E) : E :=
  ∑ k, x k + D * Ring.inverse (∏ k, x k)

end GlobalTheory.SgLoc
