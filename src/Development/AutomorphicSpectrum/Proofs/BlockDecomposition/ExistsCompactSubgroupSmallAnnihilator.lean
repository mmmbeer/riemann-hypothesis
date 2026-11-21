import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelConjugation

section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix ValuativeRel GlobalTheory.SplitWeil
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZBeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_gl {X : Type*} [TopologicalSpace X] {m : ℕ} (f : X → GL (Fin m) k)
    (hf : Continuous fun x => ((f x : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have h : (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) =
      fun x => (Matrix.det (f x : Matrix (Fin m) (Fin m) k))⁻¹ •
        Matrix.adjugate (f x : Matrix (Fin m) (Fin m) k) := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  show Continuous (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
  rw [h]
  have hd : ∀ x, Matrix.det (f x : Matrix (Fin m) (Fin m) k) ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (f x).isUnit).ne_zero
  exact (Continuous.inv₀ hf.matrix_det hd).smul hf.matrix_adjugate

theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have hv : Continuous fun g : GL (Fin n) k => ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val
  have h : Continuous fun g : GL (Fin n) k => glEmb k n g := by
    refine continuous_gl _ ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun g : GL (Fin n) k => glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast j => simpa [glEmbMat] using continuous_const
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast j =>
        simp only [glEmbMat, Fin.lastCases_castSucc]
        exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  exact h.subtype_mk (fun g => glEmb_mem_Mir k n g)

end GlobalTheory.CompanionTheory.BZBeta

end
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZOnto

variable {k : Type} [Field k]

def rowM {n : ℕ} (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  ((mirabolicProjection k (n + 1) g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)

def perp (ψ : AddChar k Circle) {m : ℕ} (Λ : AddSubgroup (Fin m → k)) : AddSubgroup (Fin m → k) where
  carrier := {b | ∀ l ∈ Λ, ψ (b ⬝ᵥ l) = 1}
  add_mem' {a b} ha hb l hl := by rw [add_dotProduct, AddChar.map_add_eq_mul, ha l hl, hb l hl, one_mul]
  zero_mem' l _ := by simp
  neg_mem' {a} ha l hl := by rw [neg_dotProduct, AddChar.map_neg_eq_inv, ha l hl, inv_one]

open GlobalTheory.BZMir.Fun GlobalTheory.CompanionTheory.BZBeta
open scoped Topology

section Row

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Row

end GlobalTheory.CompanionTheory.BZOnto

end
end

section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.CompanionTheory.BZBeta GlobalTheory.CompanionTheory.BZOnto GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZOnto.PerpSmall

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (m : ℕ) (s : kˣ) : AddSubgroup (Fin m → k) where
  carrier := {l | ∀ j, l j ∈ cball s}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' _ := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_box {m : ℕ} {s : kˣ} {l : Fin m → k} : l ∈ box m s ↔ ∀ j, l j ∈ cball s := by
  exact Iff.rfl

theorem coe_box (m : ℕ) (s : kˣ) :
    (box m s : Set (Fin m → k)) = Set.univ.pi fun _ => cball s := by
  ext l
  simp only [SetLike.mem_coe, mem_box, Set.mem_univ_pi]

theorem isCompact_box (m : ℕ) (s : kˣ) : IsCompact (box m s : Set (Fin m → k)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s

theorem box_mem_nhds (m : ℕ) (s : kˣ) : (box m s : Set (Fin m → k)) ∈ 𝓝 (0 : Fin m → k) := by
  rw [coe_box]
  exact set_pi_mem_nhds Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.cball_mem_nhds s

theorem exists_box_subset {m : ℕ} {Ω : Set (Fin m → k)} (hΩ : Ω ∈ 𝓝 (0 : Fin m → k)) :
    ∃ r : kˣ, (box m r : Set (Fin m → k)) ⊆ Ω := by
  rw [nhds_pi, Filter.mem_pi'] at hΩ
  obtain ⟨I, t, ht, hsub⟩ := hΩ
  choose s hs using fun i => GlobalTheory.SplitWeil.exists_cball_subset (by simpa using ht i)
  by_cases hm : Nonempty (Fin m)
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ValuativeRel.valuation k (s i : k))
      Finset.univ_nonempty
    refine ⟨s i₀, fun l hl => hsub fun i _ => hs i ?_⟩
    exact le_trans (show ValuativeRel.valuation k (l i) ≤ _ from (mem_box.1 hl) i) (hi₀ i (Finset.mem_univ _))
  · exact ⟨1, fun l _ => hsub fun i _ => (hm ⟨i⟩).elim⟩

theorem dotProduct_mem_cball {m : ℕ} {r s : kˣ} {b l : Fin m → k} (hb : b ∈ box m (r * s⁻¹))
    (hl : l ∈ box m s) : b ⬝ᵥ l ∈ cball r := by
  unfold dotProduct
  refine Finset.sum_induction _ (· ∈ cball r) (fun a b ha hb => add_mem_cball ha hb) ?_ ?_
  · simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k 0 ≤ _
    simp
  · intro j _
    have h1 := (mem_box.1 hb) j
    have h2 := (mem_box.1 hl) j
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k (b j * l j) ≤ ValuativeRel.valuation k (r : k)
    rw [map_mul]
    calc ValuativeRel.valuation k (b j) * ValuativeRel.valuation k (l j)
        ≤ ValuativeRel.valuation k ((r * s⁻¹ : kˣ) : k) * ValuativeRel.valuation k (s : k) := mul_le_mul' h1 h2
      _ = ValuativeRel.valuation k (r : k) := by
        rw [← map_mul]
        congr 1
        simp

end GlobalTheory.CompanionTheory.BZOnto.PerpSmall
end
