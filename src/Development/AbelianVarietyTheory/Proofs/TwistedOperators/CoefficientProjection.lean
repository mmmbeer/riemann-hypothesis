import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε : Fin n → Bool}

theorem umat_mem (h : UJ ε) : umat h ∈ UJset ε := h.2

theorem umat_mul (a b : UJ ε) : umat (a * b) = umat a * umat b := rfl

theorem umat_one : umat (1 : UJ ε) = 1 := rfl

theorem continuous_umat : Continuous (umat : UJ ε → Matrix (Fin n) (Fin n) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem exists_umat {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : ∃ h : UJ ε, umat h = g := by
  have hJ := Jm_mul_self ε
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hL : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJ]
  have hR : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.1 hL
  exact ⟨⟨⟨g, _, hR, hL⟩, hg⟩, rfl⟩

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem rep_one (hσ : IsURepOn (UJset ε) σ) : σ (umat (1 : UJ ε)) = 1 := by
  rw [umat_one]; exact hσ.1.1

theorem rep_one_apply (hσ : IsURepOn (UJset ε) σ) (x : H) : σ (umat (1 : UJ ε)) x = x := by
  rw [rep_one hσ]; rfl

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) (a b : UJ ε) (x : H) :
    σ (umat (a * b)) x = σ (umat a) (σ (umat b) x) := by
  rw [umat_mul, hσ.1.2 _ (umat_mem a) _ (umat_mem b)]; rfl


theorem rep_inner (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (x y : H) :
    ⟪σ (umat a) x, σ (umat a) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ (umat a)).toLinearMap, hσ.2.1 _ (umat_mem a)⟩
  exact L.inner_map_map x y

theorem rep_inv_apply (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (x : H) :
    σ (umat a) (σ (umat a⁻¹) x) = x := by
  rw [← rep_mul hσ, mul_inv_cancel, rep_one_apply hσ]

theorem rep_inner_left (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (x y : H) :
    ⟪σ (umat a) x, y⟫_ℂ = ⟪x, σ (umat a⁻¹) y⟫_ℂ := by
  conv_lhs => rw [← rep_inv_apply hσ a y]
  exact rep_inner hσ a x _

theorem rep_continuous (hσ : IsURepOn (UJset ε) σ) (x : H) : Continuous fun h : UJ ε => σ (umat h) x :=
  (hσ.2.2 x).comp_continuous continuous_umat umat_mem


end Rep

end GlobalTheory.SepReal.UnitaryMatrixFamily

namespace GlobalTheory.SepReal.CoefProjProof

open GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε' : Fin n → Bool} {H' K : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


theorem fixes (σ : Mat n → (H' →L[ℂ] H')) (ρ : Mat n → (K →L[ℂ] K)) (d : ℝ) (w : H') (Q : K →L[ℂ] K)
    (hfd : IsFdeg (muG ε') σ d) (hw : ‖w‖ = 1)
    (hQ : ∀ x y, ⟪y, Q x⟫_ℂ = (d : ℂ) * ∫ h, star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, ρ (umat h) x⟫_ℂ ∂muG ε')
    (j : H' →L[ℂ] K) (hj : ∀ h ∈ UJset ε', ∀ a, j (σ h a) = ρ h (j a)) : Q (j w) = j w := by
  refine ext_inner_left ℂ fun y => ?_
  rw [hQ]
  have h1 : ∀ h : UJ ε', star ⟪w, σ (umat h) w⟫_ℂ * ⟪y, ρ (umat h) (j w)⟫_ℂ =
      coefOn σ w (ContinuousLinearMap.adjoint j y) h * star (coefOn σ w w h) := by
    intro h
    rw [← hj _ (umat_mem h), ← ContinuousLinearMap.adjoint_inner_left j]
    simp only [coefOn]; ring
  simp_rw [h1]
  rw [(hfd.2 w _ w w).2, inner_self_eq_norm_sq_to_K, hw, ContinuousLinearMap.adjoint_inner_left]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast hfd.1.ne'
  field_simp
  simp

end GlobalTheory.SepReal.CoefProjProof

namespace GlobalTheory.SepReal.CoefProjProof

open GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε' : Fin n → Bool} {H' K : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem dense_orbit (σ : Mat n → (H' →L[ℂ] H')) (hσ : IsURepOn (UJset ε') σ) (hirr : IsIrredOn (UJset ε') σ)
    (w : H') (hw : w ≠ 0) : DenseRange (Finsupp.linearCombination ℂ fun g : UJ ε' => σ (umat g) w) := by
  set A := Finsupp.linearCombination ℂ fun g : UJ ε' => σ (umat g) w with hA
  set S := (LinearMap.range A).topologicalClosure with hS
  have hSc : IsClosed (S : Set H') := (LinearMap.range A).isClosed_topologicalClosure
  have hstab : ∀ s ∈ UJset ε', ∀ v ∈ S, σ s v ∈ S := by
    intro s hs v hv
    obtain ⟨a, rfl⟩ := exists_umat hs
    have hmap : LinearMap.range A ≤ S.comap (σ (umat a)).toLinearMap := by
      rintro _ ⟨c, rfl⟩
      show σ (umat a) (A c) ∈ S
      apply Submodule.le_topologicalClosure
      refine ⟨c.mapDomain (a * ·), ?_⟩
      rw [hA, Finsupp.linearCombination_mapDomain, ← ContinuousLinearMap.coe_coe,
        Finsupp.apply_linearCombination]
      exact congrArg (fun f => Finsupp.linearCombination ℂ f c) (funext fun g => rep_mul hσ a g w)
    have hcl : IsClosed ((S.comap (σ (umat a)).toLinearMap : Submodule ℂ H') : Set H') :=
      hSc.preimage (σ (umat a)).continuous
    exact Submodule.topologicalClosure_minimal _ hmap hcl hv
  rcases hirr S hSc hstab with h | h
  · exfalso
    apply hw
    have : w ∈ S := Submodule.le_topologicalClosure _ ⟨Finsupp.single 1 1, by simp [hA, rep_one_apply hσ]⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : Dense ((LinearMap.range A : Submodule ℂ H') : Set H') :=
      (Submodule.dense_iff_topologicalClosure_eq_top).2 h
    rw [DenseRange, ← LinearMap.coe_range]; exact this

end GlobalTheory.SepReal.CoefProjProof

namespace GlobalTheory.SepReal.CoefProjProof

open GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε' : Fin n → Bool} {H' K : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]



end GlobalTheory.SepReal.CoefProjProof
