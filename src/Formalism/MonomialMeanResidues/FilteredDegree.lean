import Mathlib
import Formalism.HarderNarasimhan.StatementPl

open Module NumberField Finset

noncomputable section

namespace Formalism.HermiteSiegelSlopes

open Formalism.HN

section Defs

variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

def degT (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  -Real.log (ht b X L) / (2 * (nPl K : ℝ))

def meanPl (A : InfinitePlace K → ℝ) : ℝ := (1 / (nPl K : ℝ)) * ∑ v, A v

def diagFrame {κ : Type*} [DecidableEq κ] (c : InfinitePlace K → κ → ℝ) :
    InfinitePlace K → Matrix κ κ ℂ :=
  fun v => Matrix.diagonal fun y => ((c v y : ℝ) : ℂ)

def piLattice₂ {σ κ : Type*} (Γ : Submodule (𝓞 K) (κ → K)) : Submodule (𝓞 K) (σ × κ → K) where
  carrier := {g | ∀ α, (fun y => g (α, y)) ∈ Γ}
  add_mem' := fun ha hb α => Γ.add_mem (ha α) (hb α)
  zero_mem' := fun _ => Γ.zero_mem
  smul_mem' := fun c _ hg α => Γ.smul_mem c (hg α)

end Defs

def FilteredDegree : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (κ : ℕ → Type) [∀ a, Fintype (κ a)] [∀ a, DecidableEq (κ a)]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (XG : ∀ a, InfinitePlace K → Matrix (κ a) (κ a) ℂ),
    (∀ v, IsUnit (X v).det) → (∀ a v, IsUnit (XG a v).det) →
    ∀ (k : ℕ) (φ : ∀ a, V →ₗ[K] (κ a → K)) (U : ℕ → Submodule K V) (M : Submodule (𝓞 K) V)
      (Γ : ∀ a, Submodule (𝓞 K) (κ a → K)) (A : ℕ → InfinitePlace K → ℝ) (ΛP ΛT : ℝ),
      M.FG → Submodule.span K (M : Set V) = ⊤ →
      (∀ a < k, U (a + 1) = U a ⊓ LinearMap.ker (φ a)) →
      (∀ a < k, Submodule.IsLattice K (Γ a)) → (∀ a < k, ∀ v, 0 < A a v) →
      (∀ a < k, ∀ γ ∈ Γ a, ∃ f ∈ M, f ∈ U a ∧ φ a f = γ) →
      (∀ a < k, ∀ v, ∀ x ∈ U a, ∀ ε : ℝ, 0 < ε → ∃ y ∈ U a, φ a y = 0 ∧
        Formalism.HermitianLatticesTheory.normAt b X v (x - y) ≤
          A a v * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (κ a)) (XG a) v (φ a x) + ε) →
      (∃ s : Set V, s ⊆ (M : Set V) ∧ s ⊆ (U k : Set V) ∧
        (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp ΛP) ∧ U k ≤ Submodule.span K s) →
      (∃ s : Set V, s ⊆ (M : Set V) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp ΛT) ∧
        Submodule.span K s = ⊤) →
      Module.finrank K (U 0) = (∑ a ∈ range k, Fintype.card (κ a)) + Module.finrank K (U k) ∧
      (∑ a ∈ range k, (degT (Pi.basisFun K (κ a)) (XG a) (Γ a)
            - (Fintype.card (κ a) : ℝ) * meanPl (fun v => Real.log (A a v))))
          - (Module.finrank K (U k) : ℝ) * ΛP
          - ((Module.finrank K V : ℝ) - (Module.finrank K (U 0) : ℝ)) * ΛT ≤ degT b X M

def BaseChange : Prop :=
  ∀ (F E ι : Type) [Field F] [NumberField F] [StarRing F] [IsTotallyComplex F]
    [Field E] [NumberField E] [StarRing E] [IsTotallyComplex E] [Algebra F E]
    [Fintype ι] [DecidableEq ι]
    (XF : InfinitePlace F → Matrix ι ι ℂ) (XE : InfinitePlace E → Matrix ι ι ℂ),
    (∀ v, IsUnit (XF v).det) → (∀ w, IsUnit (XE w).det) →
    (∀ (w : InfinitePlace E) (x : ι → F),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun E ι) XE w (fun i => algebraMap F E (x i)) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun F ι) XF (w.comap (algebraMap F E)) x) →
    ∀ M : Submodule (𝓞 F) (ι → F), M.FG →
      rkK (Submodule.span (𝓞 E) ((fun (x : ι → F) (i : ι) => algebraMap F E (x i)) '' (M : Set (ι → F))))
        = rkK M ∧
      degT (Pi.basisFun E ι) XE
          (Submodule.span (𝓞 E) ((fun (x : ι → F) (i : ι) => algebraMap F E (x i)) '' (M : Set (ι → F))))
        = degT (Pi.basisFun F ι) XF M

end Formalism.HermiteSiegelSlopes
