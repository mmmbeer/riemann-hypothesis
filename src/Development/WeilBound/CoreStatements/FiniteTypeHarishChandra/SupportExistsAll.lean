import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.SupportExistsOf

section
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ]

def IsIrr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))

def centralIdem [Fintype Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) :
    MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ γ⁻¹))

theorem zIdem_eq_centralIdem [Fintype Γ] (τ : FDRep ℂ Γ) : zIdem τ = centralIdem τ.ρ := rfl

def Mk.piTensorRep {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (V : ∀ i, FDRep ℂ (G i)) :
    Representation ℂ (∀ i, G i) (PiTensorProduct ℂ fun i => (V i : Type)) where
  toFun g := PiTensorProduct.map fun i => (V i).ρ (g i)
  map_one' := by simp [PiTensorProduct.map_one]
  map_mul' g h := by simp [PiTensorProduct.map_mul]

open Classical in

def ip [Fintype Γ] (S : Set Γ) (a b : Γ → ℂ) : ℂ :=
  (S.ncard : ℂ)⁻¹ * ∑ g, if g ∈ S then a g⁻¹ * b g else 0

open Classical in

def indF [Fintype Γ] (H : Subgroup Γ) (φ : Γ → ℂ) (g : Γ) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x, if x * g * x⁻¹ ∈ H then φ (x * g * x⁻¹) else 0

def cj (x : Γ) (B : Subgroup Γ) : Subgroup Γ := B.comap (MulAut.conj x).toMonoidHom

theorem mem_cj {x h : Γ} {B : Subgroup Γ} : h ∈ cj x B ↔ x * h * x⁻¹ ∈ B := Iff.rfl

def IsClassOn (A : Subgroup Γ) (a : Γ → ℂ) : Prop := ∀ x ∈ A, ∀ h ∈ A, a (x * h * x⁻¹) = a h

end Gen

section GeneralLinearIntegers

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

abbrev IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ

def glReindex {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β) :
    GL α K ≃* GL β K := glEquiv K e

omit [Fintype K] [DecidableEq K] in
theorem glReindex_val {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (g : GL α K) : ((glReindex K e g : GL β K) : Matrix β β K) = (g : Matrix α α K).submatrix e.symm e.symm := rfl

def CuspIso {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) : Prop :=
  ∃ (e : α ≃ β) (φ : lam ≃ₗ[ℂ] mu), ∀ g x, φ (lam.ρ g x) = mu.ρ (glReindex K e g) (φ x)

abbrev IsSupport {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (τ : FDRep ℂ (GL ι K)) : Prop :=
  Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧ IsConstituent τ (hcRep K b lam)

def MackeyCusp : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K)),
    Function.Surjective b → Function.Surjective b' →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → (∀ c, Simple (mu c) ∧ IsCuspidal K (mu c)) →
    Module.finrank ℂ (Intw (hcRep K b lam) (hcRep K b' mu)) =
      Nat.card {π : Fin s ≃ Fin s' // ∀ c, CuspIso K (lam c) (mu (π c))}

def SupportUnique : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
    (τ : FDRep ℂ (GL (Fin n) K)), Simple τ → IsSupport K b lam τ → IsSupport K b' mu τ →
    ∃ π : Fin s ≃ Fin s', ∀ c, CuspIso K (lam c) (mu (π c))

def HC.HCSupportExists : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (τ : FDRep ℂ (GL ι K)), Simple τ →
    ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), IsSupport K b lam τ

def SqfreeIrr : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) →
    (∀ c c', CuspIso K (lam c) (lam c') → c = c') → IsIrrRep (hcRep K b lam)

def SqfreeDim : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b →
    (∀ c, (Module.finrank ℂ (lam c) : ℤ) =
      ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) →
    (Module.finrank ℂ (hcSpace K b lam) : ℤ) * ∏ c, ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1) =
      ∏ i ∈ Finset.Icc 1 n, ((Fintype.card K : ℤ) ^ i - 1)

def SqfreeUnique : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
    (τ τ' : FDRep ℂ (GL (Fin n) K)), Simple τ → Simple τ' → IsSupport K b lam τ → IsSupport K b' mu τ' →
    (∀ c c', CuspIso K (lam c) (lam c') → c = c') →
    (∃ π : Fin s ≃ Fin s', ∀ c, CuspIso K (lam c) (mu (π c))) → Nonempty (τ ≅ τ')

def SqfreeCore : Prop := SqfreeIrr K ∧ SqfreeDim K ∧ SqfreeUnique K

variable {K} in

def reRep {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (τ : FDRep ℂ (GL α K)) : FDRep ℂ (GL β K) := transp e τ

instance HC.finiteDimensional_hcSpace {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) : FiniteDimensional ℂ (hcSpace K b lam) := by
  have : FiniteDimensional ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c))
  infer_instance

variable {K}

open Classical in

def blkGL {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s) (g : GL ι K) :
    GL {i // b i = c} K :=
  if h : g ∈ parab K b then levi K b c ⟨g, h⟩ else 1

def hcFun {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
    (χ : ∀ c : Fin s, GL {i // b i = c} K → ℂ) (g : GL ι K) : ℂ :=
  ∏ c, χ c (blkGL b c g)

variable (K) in

def pm {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) : GL ι K :=
  (Matrix.permMatrixHom (n := ι) (R := K)).toHomUnits σ

variable (K) in

def patSet {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) : Set (GL ι K) :=
  {u | ∀ i j, (i = j → (u : Matrix ι ι K) i j = 1) ∧ (i ≠ j → ¬ Φ i j → (u : Matrix ι ι K) i j = 0)}

def patChar {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (u : GL ι K) : ℂ :=
  ψ₀ (∑ i, ∑ j, E i j * (u : Matrix ι ι K) i j)

open Classical in

def wh {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E : ι → ι → K) (ψ₀ : AddChar K ℂ)
    (χ : GL ι K → ℂ) : ℂ :=
  ((patSet K Φ).ncard : ℂ)⁻¹ * ∑ u, if u ∈ patSet K Φ then (patChar E ψ₀ u)⁻¹ * χ u else 0

def IsPat {ι : Type} (Φ : ι → ι → Prop) : Prop := (∀ i, ¬ Φ i i) ∧ ∀ i j k, Φ i j → Φ j k → Φ i k

def IsPatChar {ι : Type} (Φ : ι → ι → Prop) (E : ι → ι → K) : Prop :=
  (∀ i j, E i j ≠ 0 → Φ i j) ∧ ∀ i j k, Φ i j → Φ j k → E i k = 0

variable (K) in
open Classical in

def covE {ι : Type} [LT ι] (i j : ι) : K := if i ⋖ j then 1 else 0

variable (K) in

def cutE (N k : ℕ) (i j : Fin N) : K := if (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k then 1 else 0

def colPat (N k : ℕ) (i j : Fin N) : Prop := i < j ∧ (j : ℕ) ≠ k

def rowPat (N k a : ℕ) (i j : Fin N) : Prop := i < j ∧ ¬ ((i : ℕ) = a ∧ (j : ℕ) < k)

variable (K) in

def rowE (N k a : ℕ) (i j : Fin N) : K :=
  if ((i : ℕ) = a ∧ (j : ℕ) = k) ∨ ((j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k ∧ (i : ℕ) ≠ a) then 1 else 0

def chainPat (m k t : ℕ) : Fin m ⊕ Fin k → Fin m ⊕ Fin k → Prop
  | .inl a, .inl a' => a < a'
  | .inr w, .inr w' => w < w'
  | .inl a, .inr _ => (a : ℕ) < t
  | .inr _, .inl a => t < (a : ℕ)

variable (K) in

def chainE (m k : ℕ) : Fin m ⊕ Fin k → Fin m ⊕ Fin k → K
  | .inl a, .inl a' => if (a' : ℕ) = a + 1 then 1 else 0
  | .inr w, .inr w' => if (w' : ℕ) = w + 1 then 1 else 0
  | _, _ => 0

variable (K) in

def jE (N kk s : ℕ) (i j : Fin N) : K :=
  if ((j : ℕ) = i + 1 ∧ ((j : ℕ) < s ∨ (s ≤ (i : ℕ) ∧ (j : ℕ) < s + kk) ∨ s + kk ≤ (i : ℕ))) ∨
    ((i : ℕ) + 1 = s ∧ (j : ℕ) = s + kk) then 1 else 0

end GeneralLinearIntegers

namespace Lq

def entN {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (a b : ℕ) : A :=
  if h : a < N ∧ b < N then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def IsUniUp {A : Type} [Zero A] [One A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b : Fin N, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

def eDat (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) := by
  classical
  exact ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)⁻¹ •
    ∑ u ∈ Finset.univ.filter (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))),
      MonoidAlgebra.single u (ψ₀ (φ (u : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹

def phiJ {g : ℕ} (kk s : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (ZMod g)) : ZMod g :=
  (∑ i ∈ Finset.range (s - 1), entN M i (i + 1)) +
    (if 1 ≤ s then entN M (s - 1) (s + kk) + entN M (s + kk) (s + kk + 1) else 0) +
    (∑ i ∈ Finset.range (s - 1), entN M (s + kk + 1 + i) (s + kk + 2 + i)) +
    ∑ a ∈ Finset.range (kk - 1), entN M (s + a) (s + a + 1)

def eJ (g N : ℕ) [NeZero g] (kk s : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + kk → entN M a (s + kk) = 0) (phiJ kk s) ψ₀

end Lq

end ReciprocityTheory.Ty.Fin
end
end

section
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin.St

def SimpleIffIrr : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrr τ.ρ) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v)

def CentralIdemAct : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), IsIrr ρ → IsIrr σ →
    σ.asAlgebraHom (centralIdem ρ) = (open Classical in if Nonempty (Representation.Equiv ρ σ) then 1 else 0)

def SepIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (x : MonoidAlgebra ℂ Γ), (∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = 0) → x = 0

def ZIdemFacts : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → ¬ Nonempty (τ ≅ σ) → zIdem τ * zIdem σ = 0) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → Nonempty (τ ≅ σ) → Representation.asAlgebraHom σ.ρ (zIdem τ) = 1) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (I : Type) [Fintype I] (V : I → FDRep ℂ Γ), (∀ i, Simple (V i)) →
    (∀ i j, Nonempty (V i ≅ V j) → i = j) → (∀ W : FDRep ℂ Γ, Simple W → ∃ i, Nonempty (W ≅ V i)) → ∑ i, zIdem (V i) = 1

def IntwIp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W),
    (Module.finrank ℂ (Intw ρ σ) : ℂ) = ip Set.univ ρ.character σ.character

def MaschkeFacts : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V), Simple τ →
    (IsConstituent τ ρ ↔ ∃ ψ ∈ Intw ρ τ.ρ, ψ ≠ 0)) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), Simple τ → IsConstituent τ ρ → IsConstituent τ σ →
    Module.finrank ℂ (Intw ρ σ) ≠ 0) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V), Module.finrank ℂ (Intw ρ ρ) = 1 → IsIrr ρ) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), IsIrr ρ → IsIrr σ → Module.finrank ℂ (Intw ρ σ) ≠ 0 → RepIso ρ σ

def FrobIp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (A : Subgroup Γ) (a c : Γ → ℂ), (∀ x g, c (x * g * x⁻¹) = c g) →
    ip Set.univ (indF A a) c = ip (A : Set Γ) a c ∧ ip Set.univ c (indF A a) = ip (A : Set Γ) c a

def MackeyIp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (A B : Subgroup Γ) (a b : Γ → ℂ), IsClassOn A a → IsClassOn B b →
    ∀ (R : Type) [Fintype R] (g : R → Γ),
    (∀ r r', (∃ β ∈ B, ∃ α ∈ A, g r' = β * g r * α) → r = r') →
    (∀ x, (∃ r, ∃ β ∈ B, ∃ α ∈ A, x = β * g r * α) ∨
      ∃ y, (∃ β ∈ B, ∃ α ∈ A, x = β * y * α) ∧ ip ((A ⊓ cj y B : Subgroup Γ) : Set Γ) a (fun h => b (y * h * y⁻¹)) = 0) →
    ip (A : Set Γ) a (indF B b) = ∑ r, ip ((A ⊓ cj (g r) B : Subgroup Γ) : Set Γ) a (fun h => b (g r * h * (g r)⁻¹))

def HCChar : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    (hcRep K b lam).character = indF (parab K b) (hcFun b fun c => (lam c).character) ∧
      IsClassOn (parab K b) (hcFun b fun c => (lam c).character)

def HCDim : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Module.finrank ℂ (hcSpace K b lam) * Nat.card (parab K b) = Nat.card (GL ι K) * ∏ c, Module.finrank ℂ (lam c)

def CardParab : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι],
    ((Nat.card (GL ι K) : ℤ) = (Fintype.card K : ℤ) ^ (Fintype.card ι).choose 2 *
      ∏ i ∈ Finset.Icc 1 (Fintype.card ι), ((Fintype.card K : ℤ) ^ i - 1)) ∧
    ∀ (s : ℕ) (b : ι → Fin s), Nat.card (parab K b) =
      Fintype.card K ^ Fintype.card {p : ι × ι // b p.1 < b p.2} * ∏ c, Nat.card (GL {i // b i = c} K) ∧
      (Fintype.card ι).choose 2 = Fintype.card {p : ι × ι // b p.1 < b p.2} + ∑ c, (Fintype.card {i // b i = c}).choose 2

def SqfreeDimAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], SqfreeDim K

def PmFacts : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι),
    (∀ i j, (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0) ∧
    (∀ g : GL ι K, pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g) ∧
    (∀ (s : ℕ) (b : ι → Fin s), cj (pm K σ) (parab K b) = parab K (b ∘ σ)) ∧
    ∀ (s : ℕ) (b : ι → Fin s) (χ : ∀ c : Fin s, GL {i // b i = c} K → ℂ) (g : GL ι K),
      hcFun b χ (glEquiv K σ g) =
        hcFun (b ∘ σ) (fun c x => χ c (glEquiv K (σ.subtypeEquiv (p := fun i => (b ∘ σ) i = c) (q := fun j => b j = c) fun _ => Iff.rfl) x)) g

def BruhatTwo : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n : ℕ),
    (∀ (s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s') (g : GL (Fin n) K),
      ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b', ∃ α ∈ parab K b, g = β * pm K σ * α) ∧
    ∀ (s : ℕ) (b : Fin n → Fin s) (g : GL (Fin n) K),
      ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b, ∃ u ∈ patSet K (fun i j : Fin n => i < j), g = β * pm K σ * u

def BruhatUniq : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s s' : ℕ) (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι),
    (∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) →
    ∀ c c', Fintype.card {i // b i = c ∧ b' (σ i) = c'} = Fintype.card {i // b i = c ∧ b' (τ i) = c'}

def CuspVanish : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s s' : ℕ) (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → (∃ i j, b i = b j ∧ β i ≠ β j) →
    ∀ (H : Subgroup (GL ι K)) (F : GL ι K → ℂ), H ≤ parab K b →
      (∀ u ∈ unip K β, (∀ i j, b i ≠ b j → (u : Matrix ι ι K) i j = 0) → u ∈ H ∧ ∀ h ∈ H, F (h * u) = F h) →
      (open Classical in ∑ h, if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0

def SamePart : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s s' : ℕ) (b : ι → Fin s) (π : Fin s ≃ Fin s')
    (χ : ∀ c : Fin s, GL {i // b i = c} K → ℂ) (ψ : ∀ c : Fin s', GL {i // (π ∘ b) i = c} K → ℂ),
    ip ((parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)) : Set (GL ι K)) (hcFun b χ) (hcFun (π ∘ b) ψ) =
      ∏ c, ip Set.univ (χ c) (fun x => ψ (π c) (glEquiv K
        (Equiv.subtypeEquivRight (p := fun i => b i = c) (q := fun i => (π ∘ b) i = π c) fun _ => π.injective.eq_iff.symm) x))

def IpCuspIso : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β), Simple lam → Simple mu →
    (ip Set.univ lam.character (fun x => mu.character (glEquiv K e x)) =
      (open Classical in if CuspIso K lam mu then 1 else 0)) ∧
    (CuspIso K lam mu ↔ Nonempty (transp e lam ≅ mu))

def MackeyAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], MackeyCusp K

def CuspIsoFacts : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (α β γ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (lam lam' : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (nu : FDRep ℂ (GL γ K)) (e : α ≃ β),
    (CuspIso K lam mu → CuspIso K mu lam) ∧ (CuspIso K lam mu → CuspIso K mu nu → CuspIso K lam nu) ∧
    (Nonempty (lam ≅ lam') → CuspIso K lam lam') ∧ CuspIso K lam (reRep e lam) ∧
    ∀ g : GL β K, glReindex K e (glReindex K e.symm g) = g

def FromMackey : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], MackeyCusp K → SupportUnique K ∧ SqfreeIrr K ∧ SqfreeUnique K

def ProdSimpleAll : Prop :=
  PI.GreenHCLabel.ProdSimple

def JacquetAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)), Simple τ →
    ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
      (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ),
      Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧ Φ ≠ 0 ∧
      ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ

def SupportExistsAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], HC.HCSupportExists K

def MirrorsOf : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (O : LabelMap K C), HC.HCSupportExists K → SupportUnique K → SqfreeCore K →
    (HCLabelO O ∧ (CuspParamO O → LabelSurjO O ∧ SqfreeO O))

def PatGroup : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop), IsPat Φ →
    (∃ H : Subgroup (GL ι K), (H : Set (GL ι K)) = patSet K Φ) ∧
    (patSet K Φ).ncard = Fintype.card K ^ Nat.card {p : ι × ι // Φ p.1 p.2} ∧
    ∀ (E : ι → ι → K) (ψ₀ : AddChar K ℂ), IsPatChar Φ E →
      (∀ u ∈ patSet K Φ, ∀ v ∈ patSet K Φ, patChar E ψ₀ (u * v) = patChar E ψ₀ u * patChar E ψ₀ v) ∧
      patChar E ψ₀ (1 : GL ι K) = 1 ∧ (∀ u ∈ patSet K Φ, patChar E ψ₀ u⁻¹ = (patChar E ψ₀ u)⁻¹) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (GL ι K) V), ∃ m : ℕ, wh Φ E ψ₀ ρ.character = m

def WhSym : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Φ : κ → κ → Prop) (E : κ → κ → K)
    (ψ₀ : AddChar K ℂ) (χ : GL κ K → ℂ),
    (∀ e : ι ≃ κ, wh (fun i j => Φ (e i) (e j)) (fun i j => E (e i) (e j)) ψ₀ (fun x => χ (glEquiv K e x)) = wh Φ E ψ₀ χ) ∧
    ((∀ x g, χ (x * g * x⁻¹) = χ g) →
      (∀ (e e' : ι ≃ κ) (x : GL ι K), χ (glEquiv K e x) = χ (glEquiv K e' x)) ∧
      ∀ t : κ → Kˣ, wh Φ (fun i j => (t i : K) * E i j * ((t j)⁻¹ : Kˣ)) ψ₀ χ = wh Φ E ψ₀ χ)

def RootExchange : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (W : ι → Prop) (p q : ι)
    (χ : GL ι K → ℂ), IsPat Φ → ψ₀ ≠ 1 → (∀ x g, χ (x * g * x⁻¹) = χ g) →
    (∀ w, W w → Φ p w ∧ Φ w q) → E p q ≠ 0 → (∀ i j, E i j ≠ 0 → Φ i j) → (∀ w, W w → E p w = 0 ∧ E w q = 0) →
    (∀ w z, W w → Φ w z → Φ z q → W z) → (∀ w z, W w → Φ p z → Φ z w → W z) →
    (∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q ∧ W j) →
    wh (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) E ψ₀ χ = wh (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) E ψ₀ χ

def ChainIndep : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (m k t : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin m ⊕ Fin k) K → ℂ), ψ₀ ≠ 1 →
    (∀ x g, χ (x * g * x⁻¹) = χ g) → t < m →
    wh (chainPat m k t) (chainE K m k) ψ₀ χ = wh (chainPat m k 0) (chainE K m k) ψ₀ χ

def ColRec : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (N k : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin N) K → ℂ), ψ₀ ≠ 1 → (∀ x g, χ (x * g * x⁻¹) = χ g) → k < N →
    wh (colPat N k) (cutE K N k) ψ₀ χ = wh (fun i j : Fin N => i < j) (cutE K N k) ψ₀ χ +
      ((Fintype.card K : ℂ) - 1) * ∑ a ∈ Finset.range k, wh (rowPat N k a) (rowE K N k a) ψ₀ χ

def CuspWh : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (τ : FDRep ℂ (GL (Fin d) K)), ψ₀ ≠ 1 → IsCuspidal K τ →
    (Module.finrank ℂ τ : ℂ) = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ τ.character *
      ∏ i ∈ Finset.Ico 1 d, ((Fintype.card K : ℂ) ^ i - 1)

end ReciprocityTheory.Ty.Fin.St
end
end
