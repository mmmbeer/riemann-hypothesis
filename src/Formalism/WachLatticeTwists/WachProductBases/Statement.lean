import Mathlib
import Formalism.CoboundaryTransfers.Statement
import Formalism.CoboundaryTransfers.StatementAPI

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

structure HidaSetting (O A : Type) [CommRing O] [CommRing A] [Algebra O A] where
  ℓ : ℕ
  hℓ : ℓ.Prime
  s : ℕ
  hs : 1 ≤ s
  hs2 : ℓ = 2 → 2 ≤ s
  φ : A →ₐ[O] A
  γ : A →ₐ[O] A
  comm : ∀ a, φ (γ a) = γ (φ a)
  π : A
  φπ : φ π = (1 + π) ^ ℓ - 1
  c₀ : O
  c₁ : A
  γπ : γ (1 + π) = (1 + π) * (1 + (⇑φ)^[s] π * (algebraMap O A c₀ + (⇑φ)^[s] π * c₁))

namespace HidaSetting

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A)

def X : A := (⇑S.φ)^[S.s - 1] S.π

def Q : A := ∑ k ∈ Finset.range S.ℓ, ((S.ℓ.choose (k + 1) : ℕ) : A) * S.X ^ k

def ε : A := 1 + S.π

def u : O := 1 + (S.ℓ : O) ^ S.s * S.c₀

def Rad : Prop := S.π ∈ (⊥ : Ideal A).jacobson

def Decomp : Prop :=
  ∀ g : A, ∃! e : Fin S.ℓ → A, g = ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) * S.φ (e j)

theorem φ_ε : S.φ S.ε = S.ε ^ S.ℓ := by
  simp [ε, S.φπ]

theorem iter_π (k : ℕ) : (⇑S.φ)^[k] S.π = S.ε ^ (S.ℓ ^ k) - 1 := by
  induction k with
  | zero => simp [ε]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_sub, map_pow, map_one, S.φ_ε, ← pow_mul, pow_succ']

theorem X_eq : S.X = S.ε ^ (S.ℓ ^ (S.s - 1)) - 1 := S.iter_π _

theorem one_add_pow_sub_one (x : A) (n : ℕ) :
    (1 + x) ^ n - 1 = x * ∑ k ∈ Finset.range n, ((n.choose (k + 1) : ℕ) : A) * x ^ k := by
  rw [add_comm, add_pow, Finset.sum_range_succ', Finset.mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem φ_X : S.φ S.X = S.X * S.Q := by
  have h : S.φ S.X = (1 + S.X) ^ S.ℓ - 1 := by
    rw [S.X_eq, map_sub, map_pow, map_one, S.φ_ε]
    ring
  rw [h, Q, one_add_pow_sub_one]

theorem iterate_phi_s_pi_eq_X_mul_Q : (⇑S.φ)^[S.s] S.π = S.X * S.Q := by
  have : S.s = (S.s - 1) + 1 := by have := S.hs; omega
  rw [← S.φ_X, X]
  conv_lhs => rw [this]
  rw [Function.iterate_succ_apply']

def base : Formalism.CoboundaryTransfers.Base O A where
  p := S.ℓ
  hp := S.hℓ
  φ := S.φ
  γ := S.γ
  X := S.X
  Q := S.Q
  comm := S.comm
  φX := ⟨S.Q, S.φ_X⟩

def prodBase (ι : Type) (pr : Equiv.Perm ι) : Formalism.CoboundaryTransfers.Base O (ι → A) where
  p := S.ℓ
  hp := S.hℓ
  φ :=
    { toFun := fun a i => S.φ (a (pr i))
      map_one' := by funext i; simp
      map_mul' := by intro a b; funext i; simp
      map_zero' := by funext i; simp
      map_add' := by intro a b; funext i; simp
      commutes' := by intro r; funext i; simp [Pi.algebraMap_apply] }
  γ :=
    { toFun := fun a i => S.γ (a i)
      map_one' := by funext i; simp
      map_mul' := by intro a b; funext i; simp
      map_zero' := by funext i; simp
      map_add' := by intro a b; funext i; simp
      commutes' := by intro r; funext i; simp [Pi.algebraMap_apply] }
  X := fun _ => S.X
  Q := fun _ => S.Q
  comm := by intro a; funext i; exact S.comm _
  φX := ⟨fun _ => S.Q, by funext i; exact S.φ_X⟩

end HidaSetting

end Formalism.RepresentationBoundsCohomology.N1
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers

def BaseFacts : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A),
    (∃ t : A, S.X = S.π * t) ∧
    (∃ t : A, S.Q = (S.ℓ : A) + S.X * t) ∧
    S.φ S.X = S.X * S.Q ∧
    (∃ t : A, S.γ S.X = S.X * (algebraMap O A S.u + S.X * t)) ∧
    (∃ t : A, S.γ S.X - S.X = S.X * S.Q * t) ∧
    (∃ t : A, S.γ S.Q = S.Q * (1 + S.X * t) ∧ (S.Rad → IsUnit (1 + S.X * t)))

def BaseWach : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A),
    S.base.PhiX 1 ∧ S.base.GammaX S.u ∧ (S.Rad → S.base.GammaQ)

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

structure NData (S : HidaSetting O A) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] where
  N : ι → Submodule A D
  φ : ι → D →ₗ[O] D
  γ : ι → D →ₗ[O] D
  φ_smul : ∀ (i : ι) (a : A) (x : D), φ i (a • x) = S.φ a • φ i x
  γ_smul : ∀ (i : ι) (a : A) (x : D), γ i (a • x) = S.γ a • γ i x
  comm : ∀ (i : ι) (x : D), φ i (γ (pr i) x) = γ i (φ i x)
  X_bij : Function.Bijective (fun x : D => S.X • x)
  Q_bij : Function.Bijective (fun x : D => S.Q • x)
  etale : ∀ i : ι, Function.Bijective
    (fun m : Fin S.ℓ → D => ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) • φ i (m j))

namespace NData

variable {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D]
  [Module A D] [Module O D] [IsScalarTower O A D] (W : NData S ι pr D)

def P2 : Prop := ∀ i, ∀ x ∈ W.N i, ∃ x' ∈ W.N i, W.γ i x - x = S.X • x'

def P5 (M h : ι → ℕ) : Prop :=
  (∀ i, ∀ x ∈ W.N (pr i), S.Q ^ M i • W.φ i x ∈ W.N i) ∧
    ∀ i, ∀ x ∈ W.N i, S.Q ^ h i • x ∈ Submodule.span A (W.φ i '' (W.N (pr i) : Set D))

end NData

structure NHom {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) where
  f : ι → D₁ →ₗ[A] D₂
  φ_comm : ∀ i x, f i (W₁.φ i x) = W₂.φ i (f (pr i) x)
  γ_comm : ∀ i x, f i (W₁.γ i x) = W₂.γ i (f i x)
  N_le : ∀ i, ∀ x ∈ W₁.N i, f i x ∈ W₂.N i

def NHom.Kills {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₁ : NData S ι pr D₁} {W₂ : NData S ι pr D₂} (F : NHom W₁ W₂) (i : ι) (a : A) : Prop :=
  ∀ n ∈ W₂.N i, ∃ n₁ ∈ W₁.N i, F.f i n₁ = a • n

def ToWach : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (M h : ι → ℕ) (M₀ h₀ : ℕ),
    S.Rad → W.P2 → W.P5 M h → (∀ i, M i ≤ M₀) → (∀ i, h i ≤ h₀) →
    ∃ W' : WachMod S.base M₀ (ι → D),
      W'.N = Submodule.pi Set.univ W.N ∧
      (∀ x i, W'.φ x i = W.φ i (x (pr i))) ∧ (∀ x i, W'.γ x i = W.γ i (x i)) ∧
      W'.HeightLower h₀

def FreeMembershipHeightOne : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] (N : Type)
    [AddCommGroup N] [Module A N] [Module.Free A N] (b : A) (x : N), b ≠ 0 →
    (∀ p : A, Prime p → p ∣ b → ∃ s : A, ¬ p ∣ s ∧ ∃ n : N, s • x = b • n) →
    ∃ n : N, x = b • n

def ComapLeOfSaturated : Prop :=
  ∀ (A : Type) [CommRing A] (D₀ D₁ : Type) [AddCommGroup D₀] [Module A D₀] [AddCommGroup D₁]
    [Module A D₁] (f : D₀ →ₗ[A] D₁) (N₀ : Submodule A D₀) (N₁ : Submodule A D₁) (l : A),
    (∀ x, f x ∈ N₁ → ∃ k : ℕ, l ^ k • x ∈ N₀) →
    (∀ x, l • x ∈ N₀ → x ∈ N₀) →
    ∀ x, f x ∈ N₁ → x ∈ N₀

def CokernelKilledByPower : Prop :=
  ∀ (A : Type) [CommRing A] (D₁ D₂ : Type) [AddCommGroup D₁] [Module A D₁] [AddCommGroup D₂]
    [Module A D₂] (f : D₁ →ₗ[A] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂) (π l : A) (a : ℕ),
    Function.Surjective f →
    (∀ n ∈ N₁, f n ∈ N₂) →
    (∀ n ∈ N₂, ∃ n₁ ∈ N₁, f n₁ = l ^ a • n) →
    (∀ d : D₁, ∃ k : ℕ, ∃ n₁ ∈ N₁, ∃ d' : D₁, π ^ k • d = n₁ + l ^ a • d') →
    (∀ d : D₂, (∃ k : ℕ, π ^ k • (l • d) ∈ N₂) → ∃ k : ℕ, π ^ k • d ∈ N₂) →
    N₂.FG →
    ∃ c : ℕ, ∀ n ∈ N₂, ∃ n₁ ∈ N₁, f n₁ = π ^ c • n

def InvariantNorm : Prop :=
  ∀ (A : Type) [CommRing A] (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (φ γ : A →+* A) (π q r E u t : A) (w : Δ → A),
    (∀ (d : Δ) (a : A), φ (d • a) = d • φ a) → (∀ (d : Δ) (a : A), γ (d • a) = d • γ a) →
    φ π = π * q → (∀ d, IsUnit (w d)) → (∀ d, d • π = w d * π) →
    IsUnit r → q = r * E → (∀ d : Δ, d • E = E) →
    γ π = π * (u + π * t) → (∀ d : Δ, d • u = u) →
    (∀ d : Δ, d • (∏ d' : Δ, d' • π) = ∏ d' : Δ, d' • π) ∧
    (∃ v, IsUnit v ∧ ∏ d : Δ, d • π = v * π ^ Fintype.card Δ) ∧
    (∃ v, IsUnit v ∧ (∀ d : Δ, d • v = v) ∧
      φ (∏ d : Δ, d • π) = v * (∏ d : Δ, d • π) * E ^ Fintype.card Δ) ∧
    (∃ t', γ (∏ d : Δ, d • π) = (∏ d : Δ, d • π) * (u ^ Fintype.card Δ + π * t'))

def InvariantBasisAverage : Prop :=
  ∀ (A : Type) [CommRing A] (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (N : Type) [AddCommGroup N] [Module A N] (κ : Type) [Fintype κ] (_b : Module.Basis κ A N)
    (ρ : Δ → N →+ N) (π : A),
    (∀ d d' x, ρ (d * d') x = ρ d (ρ d' x)) → (∀ x, ρ 1 x = x) →
    (∀ d (a : A) x, ρ d (a • x) = (d • a) • ρ d x) →
    π ∈ (⊥ : Ideal A).jacobson → IsUnit ((Fintype.card Δ : ℕ) : A) →
    (∀ d x, ∃ x', ρ d x - x = π • x') →
    ∃ b' : Module.Basis κ A N, ∀ d k, ρ d (b' k) = b' k

def GammaSubOnePiInvariants : Prop :=
  ∀ (A : Type) [CommRing A] (Δ : Type) [Group Δ] [MulSemiringAction Δ A]
    (N : Type) [AddCommGroup N] [Module A N] (κ : Type) [Fintype κ] (b : Module.Basis κ A N)
    (ρ : Δ → N →+ N) (γ : N →+ N) (π π' : A),
    (∀ d (a : A) x, ρ d (a • x) = (d • a) • ρ d x) → (∀ d k, ρ d (b k) = b k) →
    (∀ d x, γ (ρ d x) = ρ d (γ x)) →
    (∀ x, ∃ x', γ x - x = π • x') →
    (∀ a : A, (∀ d : Δ, d • (π * a) = π * a) → ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ π * a = π' * a') →
    ∀ x, (∀ d, ρ d x = x) → ∃ x', (∀ d, ρ d x' = x') ∧ γ x - x = π' • x'

def GlobalWachProductConsequence : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (N : Submodule A D) (γ : D →ₗ[O] D) (Q : A) (y : ℕ)
    (p : Polynomial O) (ρ : Type) (P : ρ → Type) [∀ x, AddCommGroup (P x)] [∀ x, Module O (P x)]
    (loc : ∀ x, D →ₗ[O] P x) (γl : ∀ x, P x →ₗ[O] P x) (Ll Ly : ∀ x, Submodule O (P x)),
    (∀ x d, (∃ k : ℕ, Q ^ k • d ∈ N) → loc x (γ d) = γl x (loc x d)) →
    (∀ d, (∃ k : ℕ, Q ^ k • d ∈ N) → (∀ x, loc x d ∈ Ll x) → d ∈ N) →
    (∀ d, (∃ k : ℕ, Q ^ k • d ∈ N) → ∃ k : ℕ, Q ^ k • γ d ∈ N) →
    (∀ d, Q ^ y • d ∈ N → ∀ x, loc x d ∈ Ly x) →
    (∀ x, ∀ v ∈ Ly x, Polynomial.aeval (γl x) p v ∈ Ll x) →
    ∀ d, Q ^ y • d ∈ N → Polynomial.aeval γ p d ∈ N

def C5 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ), ℓ ≠ 2 → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1 →
    ∃ c : ℤ → ℤ_[ℓ], (∀ x, (ℓ : ℤ_[ℓ]) * c x = 1 - ((u ^ (-x) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ∧ c 0 = 0 ∧
      ∀ x y, x ≠ y → Associated (c x - c y) ((ℓ : ℤ_[ℓ]) ^ padicValInt ℓ (x - y))

def C3 : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ) (D : Type)
    [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D] (W : WachMod B M D) (y : ℕ),
    B.GammaQ → ∀ x : D, B.Q ^ y • x ∈ W.N → ∃ x' : D, B.Q ^ y • x' ∈ W.N ∧ W.γ x - x = B.X • x'

def ProductBasisInclusion : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (D' D : Type)
    [AddCommGroup D'] [Module A D'] [AddCommGroup D] [Module A D] (Φ : D' →+ D)
    (N₂' N'' : Submodule A D') (N₂ N' : Submodule A D) (M h : ℕ) (aa' : Ideal A) (g : A),
    S.Decomp →
    (∀ (a : A) (x : D'), Φ (a • x) = S.φ a • Φ x) →
    (∀ m : Fin S.ℓ → D', (∀ j, m j ∈ N₂') → ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) • Φ (m j) = 0 →
      ∀ j, m j = 0) →
    N'' ≤ N₂' →
    (∀ a, a ∈ aa' ↔ ∀ n ∈ N₂', a • n ∈ N'') →
    (∀ n ∈ N₂', S.Q ^ M • Φ n ∈ N₂) →
    (∀ n ∈ N', S.Q ^ h • n ∈ Submodule.span A (Φ '' (N'' : Set D'))) →
    (∀ n ∈ N₂, g • n ∈ N') →
    S.Q ^ (M + h) * g ∈ Ideal.map (S.φ : A →+* A) aa'

def ProductBasisPsiOperator : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] (φA : A →+* A) (ε X Q : A) (H c : ℕ)
    (ι : Type) (pr : ι → ι) (aa : ι → Ideal A),
    Function.Surjective pr →
    φA ε = ε ^ ℓ →
    (∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) →
    φA X = X * Q →
    (∀ i, ∀ a ∈ aa i, Q ^ H * a ∈ Ideal.map φA (aa (pr i))) →
    (∀ i, (ε - 1) ^ c ∈ aa i) →
    ∀ i, X ^ H ∈ aa i

def Lemma3a : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type)
    (pr : Equiv.Perm ι) (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (F : NHom W₁ W₂) (M h : ι → ℕ) (H c : ℕ),
    S.Decomp → W₁.P5 M h → W₂.P5 M h → (∀ i, M i + h i ≤ H) →
    (∀ i, F.Kills i (S.π ^ c)) →
    ∀ i, F.Kills i (S.X ^ H)

def ProductBasisTameExponent : Prop :=
  ∀ (A : Type) [CommRing A] (aa : Ideal A) (π π' w : A) (ℓ e s' H : ℕ),
    2 ≤ ℓ → e * s' = ℓ - 1 → π' = w * π ^ s' → π ^ H ∈ aa →
    π' ^ ⌈((e * H : ℕ) : ℚ) / ((ℓ - 1 : ℕ) : ℚ)⌉₊ ∈ aa

def ProductBasisInvariants : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (Δ : Type) [Group Δ] [Fintype Δ]
    (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (ρ₁ : Δ →* Module.End O D₁) (ρ₂ : Δ →* Module.End O D₂) (f : D₁ →ₗ[A] D₂)
    (N₁ : Submodule A D₁) (N₂ : Submodule A D₂) (a : A),
    IsUnit ((Fintype.card Δ : ℕ) : O) →
    (∀ d, ∀ x ∈ N₁, ρ₁ d x ∈ N₁) → (∀ d x, f (ρ₁ d x) = ρ₂ d (f x)) →
    (∀ d x, ρ₂ d (a • x) = a • ρ₂ d x) →
    (∀ n ∈ N₂, ∃ n₁ ∈ N₁, f n₁ = a • n) →
    ∀ n ∈ N₂, (∀ d, ρ₂ d n = n) → ∃ n₁ ∈ N₁, (∀ d, ρ₁ d n₁ = n₁) ∧ f n₁ = a • n

end Formalism.RepresentationBoundsCohomology.N1
end
end
