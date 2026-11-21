import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.L2.SG.ClassAct

open Formalism.UG Module

section Abstract

variable {G : Type} [Group G]

def Normalises (D K : Subgroup G) : Prop := ∀ δ ∈ D, ∀ κ ∈ K, δ * κ * δ⁻¹ ∈ K

theorem Normalises.inv_conj {D K : Subgroup G} (h : Normalises D K) {δ : G} (hδ : δ ∈ D) {κ : G}
    (hκ : κ ∈ K) : δ⁻¹ * κ * δ ∈ K := by
  have := h δ⁻¹ (D.inv_mem hδ) κ hκ
  simpa using this

def DiaFree (Γ K D : Subgroup G) : Prop :=
  ∀ x : G, ∀ δ ∈ D, DoubleCoset.mk Γ K (x * δ) = DoubleCoset.mk Γ K x → δ ∈ K


def AMFChi (k : Type) [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Γ K : Subgroup G)
    (ρ : Representation k Γ W) (χ : K →* kˣ) : Submodule k (G → W) where
  carrier := {f | ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ((χ κ : kˣ) : k) • ρ γ (f g)}
  zero_mem' := by intro γ g κ; simp
  add_mem' := by
    intro f f' hf hf' γ g κ
    simp only [Pi.add_apply, hf γ g κ, hf' γ g κ, map_add, smul_add]
  smul_mem' := by
    intro c f hf γ g κ
    simp only [Pi.smul_apply, hf γ g κ, map_smul]
    rw [smul_comm]

def rtF (k : Type) [CommRing k] (W : Type) [AddCommGroup W] [Module k W] (δ : G) : (G → W) →ₗ[k] (G → W) :=
  LinearMap.funLeft k W (fun g => g * δ)

def FixAt (k : Type) [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Γ K : Subgroup G)
    (ρ : Representation k Γ W) (χ : K →* kˣ) (D : Subgroup G) : Submodule k (G → W) :=
  AMFChi k Γ K ρ χ ⊓ ⨅ δ : D, LinearMap.ker (rtF k W (δ : G) - LinearMap.id)


end Abstract

def FixedDim : Prop :=
  ∀ (G : Type) [Group G] (Γ K K₀ D : Subgroup G) (k : Type) [Field k] (W : Type) [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (ρ : Representation k Γ W) (χ : K →* kˣ),
    K ≤ K₀ → D ≤ K₀ → IsNeat Γ K₀ → Normalises D K →
    (∀ δ ∈ D, ∀ κ κ' : K, (κ' : G) = δ * κ * δ⁻¹ → χ κ' = χ κ) →
    (∀ κ : K, (κ : G) ∈ D → χ κ = 1) →
    Finite (ClassSet Γ K) →
    finrank k (FixAt k Γ K ρ χ D) * K.relIndex D = finrank k (AMFChi k Γ K ρ χ)

end Formalism.L2.SG.ClassAct
