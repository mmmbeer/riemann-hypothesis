import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace

section
open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.SympNormal

open GlobalTheory.ArchUniq Module

section Gen

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def omegaL {P : V → V → ℝ} (h : IsPairing P) : (V × V) →ₗ[ℝ] (V × V) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (omega P)
    (fun w w' w'' => by simp only [omega, Prod.fst_add, Prod.snd_add, h.addL, h.addR]; ring)
    (fun c w w' => by simp only [omega, Prod.smul_fst, Prod.smul_snd, h.smulL, h.smulR, smul_eq_mul]; ring)
    (fun w w' w'' => by simp only [omega, Prod.fst_add, Prod.snd_add, h.addL, h.addR]; ring)
    (fun c w w' => by simp only [omega, Prod.smul_fst, Prod.smul_snd, h.smulL, h.smulR, smul_eq_mul]; ring)

@[simp] theorem omegaL_apply {P : V → V → ℝ} (h : IsPairing P) (w w' : V × V) :
    omegaL h w w' = omega P w w' := rfl

end Gen

section Main

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
variable {P : V → V → ℝ} {P₁ : V₁ → V₁ → ℝ} {j : V₁ × V₁ → V × V} {L : Set (V × V)}

def jL (hS : Setup P P₁ j L) : (V₁ × V₁) →ₗ[ℝ] (V × V) where
  toFun := j
  map_add' := hS.add
  map_smul' := hS.smul

def LSub (hS : Setup P P₁ j L) : Submodule ℝ (V × V) where
  carrier := L
  add_mem' {a b} ha hb := hS.max _ (fun l hl => by
      rw [← omegaL_apply hS.pair, map_add, LinearMap.add_apply]; simp [hS.iso _ ha _ hl, hS.iso _ hb _ hl])
    (fun w => by rw [← omegaL_apply hS.pair, map_add, LinearMap.add_apply]; simp [hS.orth _ ha, hS.orth _ hb])
  zero_mem' := hS.max _ (fun l _ => by simp [omega, hS.pair.zero_left, hS.pair.zero_right])
    (fun w => by simp [omega, hS.pair.zero_left, hS.pair.zero_right])
  smul_mem' c a ha := hS.max _ (fun l hl => by
      rw [← omegaL_apply hS.pair, map_smul, LinearMap.smul_apply]; simp [hS.iso _ ha _ hl])
    (fun w => by rw [← omegaL_apply hS.pair, map_smul, LinearMap.smul_apply]; simp [hS.orth _ ha])

def deltaL (hS : Setup P P₁ j L) (m : ℕ) (f g : Fin m → V × V) :
    ((V₁ × (Fin m → ℝ)) × (V₁ × (Fin m → ℝ))) →ₗ[ℝ] V × V where
  toFun s := j (s.1.1, s.2.1) + ∑ i, s.1.2 i • f i + ∑ i, s.2.2 i • g i
  map_add' s t := by
    have : ((s + t).1.1, (s + t).2.1) = ((s.1.1, s.2.1) + (t.1.1, t.2.1) : V₁ × V₁) := rfl
    rw [this, hS.add]
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c s := by
    have : ((c • s).1.1, (c • s).2.1) = (c • (s.1.1, s.2.1) : V₁ × V₁) := rfl
    rw [this, hS.smul]
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
      RingHom.id_apply, smul_add]

end Main

end GlobalTheory.SympNormal
end
end

section
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  first | exact @GlobalTheory.ArchUniq.exists_pairing_coords | exact GlobalTheory.ArchUniq.exists_pairing_coords | (intros; apply GlobalTheory.ArchUniq.exists_pairing_coords <;> assumption)
end

section
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  first | exact @GlobalTheory.exists_symplecticGroup_of_sympl | exact GlobalTheory.exists_symplecticGroup_of_sympl | (intros; apply GlobalTheory.exists_symplecticGroup_of_sympl <;> assumption)
end

section
open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.ArchUniq

open GlobalTheory.RealWeil

theorem pairingCoords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland

theorem symplMatrix : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm

end GlobalTheory.ArchUniq

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

end GlobalTheory.ArchUniq
end
end
