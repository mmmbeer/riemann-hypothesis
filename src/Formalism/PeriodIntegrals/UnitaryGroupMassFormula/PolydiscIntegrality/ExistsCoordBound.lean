import Mathlib
import Formalism.PeriodIntegrals.PolydiscInt

section
namespace PI.PolydiscIntegrality₂

def Hyp (p : ℕ) [Fact p.Prime] (n : ℕ) (a : (Fin n →₀ ℕ) → ℂ_[p]) : Prop :=
  ∀ z : Fin n → ℂ_[p], (∀ i, ‖z i‖ < 1) →
      Summable (fun α : Fin n →₀ ℕ => a α * ∏ i, z i ^ α i) ∧
      ‖∑' α : Fin n →₀ ℕ, a α * ∏ i, z i ^ α i‖ ≤ 1

end PI.PolydiscIntegrality₂
end

section
namespace PI.PolydiscIntegrality₂

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

theorem norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' p (N : ℚ_[p])
  simp only [map_natCast, PadicComplex.coe_natCast] at h1
  rw [h1]
  exact Padic.norm_natCast_eq_one_iff.mpr (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr h)

end PI.PolydiscIntegrality₂
end

section
namespace PI.PolydiscIntegrality₂

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

theorem exists_coord_bound {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    ∃ B : ℕ, ∀ γ ∈ S, ∀ i, γ i ≤ B := by
  refine ⟨∑ γ ∈ S, ∑ i, γ i, fun γ hγ i => ?_⟩
  calc γ i ≤ ∑ i, γ i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ ∑ γ ∈ S, ∑ i, γ i := Finset.single_le_sum (f := fun γ : Fin n →₀ ℕ => ∑ i, γ i)
        (fun _ _ => Nat.zero_le _) hγ

end PI.PolydiscIntegrality₂
end
