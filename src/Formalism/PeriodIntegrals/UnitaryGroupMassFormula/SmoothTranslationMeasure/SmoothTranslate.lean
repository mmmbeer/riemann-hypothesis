import Formalism.PeriodIntegrals.PhMeasCore

section
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

def MulOnUH {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ ∀ a ∈ UH Hm, ∀ b ∈ UH Hm, σ (a * b) = (σ a).comp (σ b)

def StepRed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin n) (Fin n) ℂ),
    IsUnit P → Pᴴ * Jm ε * P = Hm →
    (σ (P⁻¹ * 1 * P) = 1 ∧ ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) →
    IsUnit Hm ∧ MulOnUH Hm σ

def StepExp : Prop :=
  ∀ (n : ℕ) (Hm X : Matrix (Fin n) (Fin n) ℂ), IsUnit Hm → InLie Hm X →
    ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm

def StepSub : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → w ∈ smoothVecs Hm σ →
    (∀ g ∈ UH Hm, σ g w ∈ smoothVecs Hm σ) ∧
    ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, v - v' ∈ smoothVecs Hm σ

section Deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Deriv

def StepWord : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → (∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm) →
    w ∈ smoothVecs Hm σ →
    ∀ ws : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ ws, InLie Hm X) →
      ContinuousOn (fun g => dsigW σ ws (σ g w)) (UH Hm) ∧
      ∀ g ∈ UH Hm, ∀ g₀ ∈ UH Hm,
        dsigW σ ws (σ g w - σ g₀ w) = dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)

theorem isClosed_UH {n : ℕ} (Hm : Matrix (Fin n) (Fin n) ℂ) : IsClosed (UH Hm) := isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
  continuous_id) continuous_const



end PI.PhMeasCore.UnitaryGroupMassFormula

end
end

section
open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

theorem mul_mem_UH {n : ℕ} {Hm a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UH Hm) (hb : b ∈ UH Hm) :
    a * b ∈ UH Hm := by
  have ha' : aᴴ * Hm * a = Hm := ha
  have hb' : bᴴ * Hm * b = Hm := hb
  show (a * b)ᴴ * Hm * (a * b) = Hm
  calc (a * b)ᴴ * Hm * (a * b) = bᴴ * (aᴴ * Hm * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm := by rw [ha', hb']

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_matMul {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a => LinearMap.toContinuousLinearMap
          { toFun := fun b => a * b
            map_add' := fun b c => Matrix.mul_add a b c
            map_smul' := fun r b => by simp }
        map_add' := fun a b => by
          ext c : 1
          simp [Matrix.add_mul]
        map_smul' := fun r a => by
          ext c : 1
          simp }
  have h : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => L p.1 p.2) :=
    L.isBoundedBilinearMap.contDiff
  exact h

theorem contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * g) :=
  (@contDiff_matMul n).comp (contDiff_id.prodMk contDiff_const)

end Smooth

end PI.PhMeasCore.UnitaryGroupMassFormula

end
end

section
open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_translate {w : H} (hmul : MulOnUH Hm σ) (hw : w ∈ smoothVecs Hm σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH Hm) : σ g w ∈ smoothVecs Hm σ := by
  have hw' : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x w) := hw
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (σ g w))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hFeq⟩ := hw' (g₀ * g) (mul_mem_UH (a := g₀) hg₀ hg)
  refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g),
    hU.preimage (contDiff_mulRight g).continuous, hmem, ?_, ?_⟩
  · exact hF.comp (contDiff_mulRight g).contDiffOn (fun x hx => hx)
  · intro x hx hxI
    have e : σ (x * g) w = F (x * g) := hFeq (x * g) hx (mul_mem_UH hxI hg)
    show σ x (σ g w) = F (x * g)
    rw [← e, hmul.2 x hxI g hg, ContinuousLinearMap.comp_apply]

theorem smooth_sub {v v' : H} (hv : v ∈ smoothVecs Hm σ) (hv' : v' ∈ smoothVecs Hm σ) :
    v - v' ∈ smoothVecs Hm σ := by
  have h₁ : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x v) := hv
  have h₂ : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x v') := hv'
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (v - v'))
  intro g₀ hg₀
  obtain ⟨U₁, F₁, hU₁, m₁, hF₁, e₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, F₂, hU₂, m₂, hF₂, e₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun x => F₁ x - F₂ x, hU₁.inter hU₂, ⟨m₁, m₂⟩, ?_, ?_⟩
  · exact (hF₁.mono Set.inter_subset_left).sub (hF₂.mono Set.inter_subset_right)
  · intro x hx hxI
    have a₁ : σ x v = F₁ x := e₁ x hx.1 hxI
    have a₂ : σ x v' = F₂ x := e₂ x hx.2 hxI
    show σ x (v - v') = F₁ x - F₂ x
    rw [map_sub, a₁, a₂]

end PI.PhMeasCore.UnitaryGroupMassFormula

end
end
