import Mathlib

section
noncomputable section

namespace SiegelEisensteinSeries.BRoad

open Filter Topology

structure Datum (G : Type*) [Group G] (r : ℕ) where
  Γ : Subgroup G
  Bo : Subgroup G
  K : Subgroup G
  Pa : Fin r → Subgroup G
  Hv : G → Fin r → ℝ
  ht : G → ℝ
  rho : Fin r → ℝ
  root : Fin r → Fin r → ℝ
  coroot : Fin r → Fin r → ℝ

variable {G : Type*} [Group G] {r : ℕ}

def cpair (lam : Fin r → ℂ) (x : Fin r → ℝ) : ℂ := ∑ j, lam j * (x j : ℂ)

def onCoroot (lam : Fin r → ℂ) (c : Fin r → ℝ) : ℂ := cpair lam c

namespace Datum

variable (D : Datum G r)

structure IsGood [TopologicalSpace G] : Prop where
  iwa : ∀ g : G, ∃ b ∈ D.Bo, ∃ k ∈ D.K, g = b * k
  cpt : IsCompact (D.K : Set G)
  hv_cont : Continuous D.Hv
  hv_right : ∀ g, ∀ k ∈ D.K, D.Hv (g * k) = D.Hv g
  hv_mul : ∀ b ∈ D.Bo, ∀ g, D.Hv (b * g) = D.Hv b + D.Hv g
  hv_rat : ∀ γ ∈ D.Γ ⊓ D.Bo, D.Hv γ = 0
  ht_cont : Continuous D.ht
  ht_ge : ∀ g, 1 ≤ D.ht g
  pa_ge : ∀ a, D.Bo ≤ D.Pa a

abbrev Cos := Quotient (QuotientGroup.rightRel (D.Bo.subgroupOf D.Γ))

def term (φ : G → ℂ) (lam : Fin r → ℂ) (g : G) : ℂ :=
  Complex.exp (cpair (lam + fun j => (D.rho j : ℂ)) (D.Hv g)) * φ g

def refl (a : Fin r) (lam : Fin r → ℂ) : Fin r → ℂ := fun j => lam j - onCoroot lam (D.coroot a) * (D.root a j : ℂ)

def cone (R : ℝ) : Set (Fin r → ℝ) := {x | ∀ a, R < ∑ j, x j * D.coroot a j}

structure IsSec [TopologicalSpace G] (χ : G → ℂ) (φ : G → ℂ) : Prop where
  cont : Continuous φ
  equiv : ∀ b ∈ D.Bo, ∀ g, φ (b * g) = χ b * φ g
  unit : ∀ b ∈ D.Bo, ‖χ b‖ = 1
  rat : ∀ γ ∈ D.Γ ⊓ D.Bo, χ γ = 1
  bdd : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M

end Datum

end SiegelEisensteinSeries.BRoad
end
end

section
noncomputable section

namespace SiegelEisensteinSeries.BRoad

open Filter Topology

namespace Datum

variable {G : Type*} [Group G] [TopologicalSpace G] {r : ℕ} (D : Datum G r)

structure Plucker (L : Fin r → Type*) (ℓ : ∀ i, D.Cos → L i) (nrm : ∀ i, L i → G → ℝ) (s0 : Fin r → ℝ) : Prop where
  inj : Function.Injective (fun q : D.Cos => fun i => ℓ i q)
  pos : ∀ i l g, 0 < nrm i l g
  factor : ∀ (q : D.Cos) (g : G) (i : Fin r), D.Hv ((Quotient.out q).1 * g) i = -Real.log (nrm i (ℓ i q) g)
  zeta : ∀ i, ∀ s > s0 i, ∃ (c : ℝ) (N : ℕ), ∀ g, Summable (fun l => nrm i l g ^ (-s)) ∧
    ∑' l, nrm i l g ^ (-s) ≤ c * D.ht g ^ N
  loc : ∀ i (g0 : G), ∃ U ∈ 𝓝 g0, ∃ c > 0, ∀ g ∈ U, ∀ l, c * nrm i l g0 ≤ nrm i l g ∧ nrm i l g ≤ c⁻¹ * nrm i l g0

end Datum

end SiegelEisensteinSeries.BRoad
end
end
