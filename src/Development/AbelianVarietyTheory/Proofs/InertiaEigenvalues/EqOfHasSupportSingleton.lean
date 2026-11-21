import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableOfCharOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinCuspOne

section
noncomputable section

open GlobalTheory.PRep
open scoped Classical

namespace GlobalTheory.KTypeTest

variable {G : Type} [Group G] (K : Subgroup G) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

def charFn (σ : Representation ℂ K U) (g : G) : ℂ :=
  if hg : g ∈ K then starRingEnd ℂ (LinearMap.trace ℂ U (σ ⟨g, hg⟩)) else 0

def IsKMap (σ : Representation ℂ K U) (ρ : Representation ℂ G V) (f : U →ₗ[ℂ] V) : Prop :=
  ∀ κ : K, f ∘ₗ σ κ = ρ κ ∘ₗ f



end GlobalTheory.KTypeTest
end
end

section
noncomputable section

open GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def InComp (π₀ y : IrrGL k) : Prop :=
  ∃ s : Multiset (IrrGL k), HasSupport y.rep s ∧ ∀ x ∈ s, IrrGL.Inert π₀ x

def IsSegFamily {r : ℕ} (y : Fin r → IrrGL k) : Prop :=
  (∀ j, (y j).IsEssSqInt) ∨ (∀ j, ∃ Δ : Segment k, IsLSeg Δ (y j).rep)

def IsJMap {N : ℕ} (J : Subgroup (KO k (Fin N))) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
    [Module ℂ V] (τ : Representation ℂ J U) (ρ : Representation ℂ (GL (Fin N) k) V) (f : U →ₗ[ℂ] V) : Prop :=
  ∀ j : J, f ∘ₗ τ j = ρ ((j : KO k (Fin N)) : GL (Fin N) k) ∘ₗ f

def IsKTypeDatum (π₀ : IrrGL k) (t : ℕ) {N : ℕ} (J : Subgroup (KO k (Fin N))) {U : Type} [AddCommGroup U]
    [Module ℂ U] (τ : Representation ℂ J U) (S : Submodule ℂ (indSpace J τ))
    (hS : ∀ (κ : KO k (Fin N)), ∀ f ∈ S, ind J τ κ f ∈ S) : Prop :=
  (∃ K' : Subgroup (GL (Fin N) k), IsOpen (K' : Set (GL (Fin N) k)) ∧ K' ≤ KO k (Fin N) ∧
      (K'.subgroupOf (KO k (Fin N))).Normal ∧ (∀ κ : KO k (Fin N), (κ : GL (Fin N) k) ∈ K' → κ ∈ J) ∧
      ∀ j : J, ((j : KO k (Fin N)) : GL (Fin N) k) ∈ K' → τ j = 1) ∧
    FiniteDimensional ℂ S ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∃ j, ¬ InComp π₀ (y j)) →
      ∀ f, IsJMap J τ (prodIrr y hd) f → f = 0) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∀ j, InComp π₀ (y j)) →
      (∃ j, ¬ IrrGL.Inert π₀ (y j)) → ∀ f, IsKMap (KO k (Fin N)) (sub (ind J τ) S hS) (prodIrr y hd) f → f = 0) ∧
    ∃ (hN : ∑ _i : Fin t, π₀.1 = N) (f : S →ₗ[ℂ] _), f ≠ 0 ∧
      IsKMap (KO k (Fin N)) (sub (ind J τ) S hS) (prodIrr (fun _ : Fin t => π₀) hN) f

end GlobalTheory.KTypeDatum
end
end

section
noncomputable section

open GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsHeckeTypeDatum (π₀ : IrrGL k) (t : ℕ) {N : ℕ} (J : Subgroup (KO k (Fin N))) {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ J W) (q : ℕ) (T : ℕ → Module.End ℂ (indSpace J τ)) : Prop :=
  2 ≤ q ∧ FiniteDimensional ℂ (indSpace J τ) ∧
    (∃ K' : Subgroup (GL (Fin N) k), IsOpen (K' : Set (GL (Fin N) k)) ∧ K' ≤ KO k (Fin N) ∧
      (K'.subgroupOf (KO k (Fin N))).Normal ∧ (∀ κ : KO k (Fin N), (κ : GL (Fin N) k) ∈ K' → κ ∈ J) ∧
      ∀ j : J, ((j : KO k (Fin N)) : GL (Fin N) k) ∈ K' → τ j = 1) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∃ j, ¬ InComp π₀ (y j)) →
      ∀ f, IsJMap J τ (prodIrr y hd) f → f = 0) ∧
    (∀ i, i + 1 < t → ∀ κ : KO k (Fin N), T i * ind J τ κ = ind J τ κ * T i) ∧
    (∀ i, i + 1 < t → (T i - (q : ℂ) • 1) * (T i + 1) = 0) ∧
    (∀ i j, j + 1 < t → i + 2 ≤ j → T i * T j = T j * T i) ∧
    (∀ i, i + 2 < t → T i * T (i + 1) * T i = T (i + 1) * T i * T (i + 1)) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∀ j, InComp π₀ (y j)) →
      (∃ j, ¬ IrrGL.Inert π₀ (y j)) → ∀ F, IsKMap (KO k (Fin N)) (ind J τ) (prodIrr y hd) F →
      (∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F) → F = 0) ∧
    ∃ (hN : ∑ _i : Fin t, π₀.1 = N) (F : indSpace J τ →ₗ[ℂ] _), F ≠ 0 ∧
      IsKMap (KO k (Fin N)) (ind J τ) (prodIrr (fun _ : Fin t => π₀) hN) F ∧
      ∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

section Generic

variable {G : Type} [Group G] {K : Subgroup G} {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
  [Module ℂ V] {σ : Representation ℂ K U} {ρ : Representation ℂ G V} {e : Module.End ℂ U}

theorem range_stable (hc : ∀ κ : K, σ κ * e = e * σ κ) :
    ∀ κ : K, ∀ f ∈ LinearMap.range e, σ κ f ∈ LinearMap.range e := by
  rintro κ _ ⟨x, rfl⟩
  refine ⟨σ κ x, ?_⟩
  have := congrArg (fun L : Module.End ℂ U => L x) (hc κ)
  simpa [Module.End.mul_apply] using this.symm






end Generic

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end GlobalTheory.KTypeDatum
end
end

section
noncomputable section

open ValuativeRel Matrix GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest GlobalTheory.KTypeDatum GlobalTheory.DZero

namespace GlobalTheory.DZeroHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsDZType (π₀ : IrrGL k) {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀]
    (σ : Representation ℂ (GL (Fin π₀.1) 𝓀[k]) W₀) : Prop :=
  FiniteDimensional ℂ W₀ ∧ σ.IsIrreducible ∧ FinCusp σ ∧ ∃ j : W₀ →ₗ[ℂ] π₀.2.rep.V, HasType π₀.rep σ j

variable {d t N : ℕ}

abbrev dzBlocks (hN : ∑ _i : Fin t, d = N) : (Σ _a : Fin t, Fin d) ≃ Fin N :=
  stdBlocks (fun _ : Fin t => d) hN

variable (k) in

def dzJ (hN : ∑ _i : Fin t, d = N) : Subgroup (KO k (Fin N)) :=
  (parahoric k (dzBlocks hN)).subgroupOf (KO k (Fin N))

variable (k) in

def dzJIncl (hN : ∑ _i : Fin t, d = N) : dzJ k hN →* parahoric k (dzBlocks hN) :=
  (((KO k (Fin N)).subtype).comp (dzJ k hN).subtype).codRestrict _ fun x => x.2

def dzTau {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀] (σ : Representation ℂ (GL (Fin d) 𝓀[k]) W₀)
    (hN : ∑ _i : Fin t, d = N) : Representation ℂ (dzJ k hN) (PiTensorProduct ℂ fun _a : Fin t => W₀) :=
  (piTensor fun _a : Fin t => σ).comp ((parahoricProj k (dzBlocks hN)).comp (dzJIncl k hN))

def dzPerm (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Equiv.Perm (Fin N) :=
  if h : i + 1 < t then
    ((dzBlocks hN).symm.trans (Equiv.sigmaCongrLeft (β := fun _ : Fin t => Fin d) (Equiv.swap (⟨i, by omega⟩ : Fin t) ⟨i + 1, h⟩))).trans (dzBlocks hN)
  else 1

variable (k) in

def dzW (hN : ∑ _i : Fin t, d = N) (i : ℕ) : KO k (Fin N) :=
  toKO k (Fin N) ((Matrix.permMatrixHom (R := 𝒪[k])).toHomUnits (dzPerm hN i))

variable (k) in

def dzCoset (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Set (KO k (Fin N)) :=
  {g | ∃ a b : dzJ k hN, g = (a : KO k (Fin N)) * dzW k hN i * b}

variable (k) in

def dzQ (d : ℕ) : ℕ := resCard k ^ d

end GlobalTheory.DZeroHecke
end
end

section
noncomputable section

open ValuativeRel GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.GenericUnitary GlobalTheory.KTypeTest GlobalTheory.KTypeDatum GlobalTheory.DZero
  GlobalTheory.DZeroHecke

namespace GlobalTheory.DZeroDegOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_hasSupport_singleton {y z : IrrGL k} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun _ : Fin 1 => z.1) hd) _).1
    (piTensor fun _ => z.rep)
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)) hi z.2.rep.irr
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

end GlobalTheory.DZeroDegOne
end
end
