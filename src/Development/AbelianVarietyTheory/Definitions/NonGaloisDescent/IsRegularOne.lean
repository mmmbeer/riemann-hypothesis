import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.BCen

section Abstract

variable {M V W ι : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def shift (V : Type) [AddCommGroup V] [Module ℂ V] (μ : ι → ℤ) : Module.End ℂ ((ι → ℤ) →₀ V) :=
  Finsupp.lmapDomain V ℂ fun l => l + μ

def univ (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) : Representation ℂ M ((ι → ℤ) →₀ V) where
  toFun g := shift V (deg g).toAdd ∘ₗ Finsupp.mapRange.linearMap (ρ g)
  map_one' := by ext l v; simp [shift]
  map_mul' g h := by ext l v; simp [shift, add_assoc, add_comm (deg g).toAdd]

def lau (V : Type) [AddCommGroup V] [Module ℂ V] (c : (ι → ℤ) →₀ ℂ) : Module.End ℂ ((ι → ℤ) →₀ V) :=
  c.sum fun μ w => w • shift V μ

theorem shift_univ (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (μ : ι → ℤ) (g : M) :
    shift V μ ∘ₗ univ deg ρ g = univ deg ρ g ∘ₗ shift V μ := by
  ext l v; simp [shift, univ, add_right_comm]

def lauHom (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (c : (ι → ℤ) →₀ ℂ) :
    (univ deg ρ).IntertwiningMap (univ deg ρ) where
  toLinearMap := lau V c
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    simp only [lau, Finsupp.sum, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun μ _ => congrArg _ (LinearMap.congr_fun (shift_univ deg ρ μ g) y)

def evalLau [Fintype ι] (c : (ι → ℤ) →₀ ℂ) (u : ι → ℂˣ) : ℂ := c.sum fun μ w => w * ((∏ a, u a ^ μ a : ℂˣ) : ℂ)

def unr [Fintype ι] (deg : M →* Multiplicative (ι → ℤ)) (u : ι → ℂˣ) : M →* ℂˣ where
  toFun g := ∏ a, u a ^ (deg g).toAdd a
  map_one' := by simp
  map_mul' g h := by simp [zpow_add, Finset.prod_mul_distrib]

def part (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (τ : Representation ℂ M W) : Submodule ℂ W :=
  ⨆ φ : (univ deg ρ).IntertwiningMap τ, LinearMap.range φ.toLinearMap

variable [TopologicalSpace M] [IsTopologicalGroup M]

def IsLocProf (M : Type) [Group M] [TopologicalSpace M] : Prop :=
  ∀ U ∈ nhds (1 : M), ∃ K : Subgroup M, IsOpen (K : Set M) ∧ IsCompact (K : Set M) ∧ (K : Set M) ⊆ U

def IsCompactRep (ρ : Representation ℂ M V) : Prop :=
  IsSmooth ρ ∧ ∀ (v : V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual → ∃ C : Set M, IsCompact C ∧ ∀ g, l (ρ g v) ≠ 0 → g ∈ C

structure CuspDatum (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) : Prop where
  prof : IsLocProf M
  surj : Function.Surjective deg
  isOpen : IsOpen (deg.ker : Set M)
  index : (Subgroup.center M ⊔ deg.ker).FiniteIndex
  irr : ρ.IsIrreducible
  adm : IsAdmissible ρ
  central : ∀ z ∈ Subgroup.center M, ∃ c : ℂ, ∀ v, ρ z v = c • v
  cpt : IsCompactRep (ρ.comp deg.ker.subtype : Representation ℂ deg.ker V)

variable (M) in

structure Centre : Type 1 where

  act : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ M V), IsSmooth π → π.IntertwiningMap π
  nat : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ M V) (hπ : IsSmooth π)
    (τ : Representation ℂ M W) (hτ : IsSmooth τ) (f : π.IntertwiningMap τ) (v : V), f (act π hπ v) = act τ hτ (f v)

def Centre.one : Centre M where
  act π _ := .id π
  nat _ _ _ _ _ _ := rfl

end Abstract

section Linear

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def degL (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] : Levi k m →* Multiplicative (α → ℤ) where
  toFun g := Multiplicative.ofAdd fun a => ord k (Matrix.GeneralLinearGroup.det (g a))
  map_one' := by ext a; simp [ord_eq_zero]
  map_mul' g h := by ext a; simp [ord_mul]

def permLevi (w : α ≃ β) (f : ∀ a, m' (w a) ≃ m a) : Levi k m' →* Levi k m :=
  MonoidHom.pi fun a => (Units.map (Matrix.reindexAlgEquiv k k (f a)).toMonoidHom).comp (Pi.evalMonoidHom (fun j => GL (m' j) k) (w a))

variable {k}

def twFam {t : ℕ} (x : Fin t → IrrGL k) (u : Fin t → ℂˣ) (a : Fin t) : IrrGL k :=
  (x a).tw (unrChar k (u a)) (isSmoothChar_of_isUnram (isUnram_unrChar k (u a)))

def Reps (Z : Multiset (IrrGL k) → ℂ) {t : ℕ} (x : Fin t → IrrGL k) (c : (Fin t → ℤ) →₀ ℂ) : Prop :=
  ∀ u, Z (Finset.univ.val.map (twFam x u)) = evalLau c u

variable (k) in

def IsRegular (n : ℕ) (Z : Multiset (IrrGL k) → ℂ) : Prop :=
  ∀ (t : ℕ) (x : Fin t → IrrGL k), (∀ a, (x a).IsCusp) → ∑ a, (x a).1 = n → ∃ c, Reps Z x c

end Linear

end GlobalTheory.BCen

end
