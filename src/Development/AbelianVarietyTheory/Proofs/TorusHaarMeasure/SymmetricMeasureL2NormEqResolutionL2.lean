import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCMulImHermCEqSignMulTrace
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusCoordinates
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TorusMarkingPhase
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TorusThetaNorms

namespace GlobalTheory.TorusMirror

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 GlobalTheory.ThetaHol
open scoped ComplexConjugate ContDiff

noncomputable section

section Deriv

variable {W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

variable (J : W →L[ℝ] W') {F : W → ℂ} {G : W' → ℂ} (hF : ContDiff ℂ ω F) (hG : ContDiff ℂ ω G)
  (h : ∀ w, G (J w) = conj (F w))
include hF hG h

end Deriv

section Torus

variable {E : Type} [Field E] [NumberField E]

theorem act_cj (X : PT E) {dim : (E →+* ℂ) → ℕ} (σ : Idx dim ≃ Idx X.dim)
    (hσ : ∀ i, (σ i).1 = ComplexEmbedding.conjugate i.1) (α : 𝓞 E) (y : Vsp X.dim) :
    act α (cj X σ y) = cj X σ (act α y) := by
  ext i
  simp [act, cj_apply, hσ]

def conjBasis (X : PT E) {dim : (E →+* ℂ) → ℕ} (σ : Idx dim ≃ Idx X.dim) :
    Module.Basis (Fin (2 * Fintype.card (Idx dim))) ℝ (Vsp dim) :=
  (X.b.map (cj X σ)).reindex (finCongr (by rw [Fintype.card_congr σ]))

theorem mem_conjBasis (X : PT E) {dim : (E →+* ℂ) → ℕ} (σ : Idx dim ≃ Idx X.dim) (y : Vsp X.dim) :
    cj X σ y ∈ lat (conjBasis X σ) ↔ y ∈ lat X.b := by
  simp only [lat, Module.Basis.mem_span_iff_repr_mem, conjBasis, Module.Basis.repr_reindex_apply,
    Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact ⟨fun h i => h (finCongr (by rw [Fintype.card_congr σ]) i), fun h i => h _⟩

section

variable (X : PT E) (σ : Idx (fun τ => X.dim (ComplexEmbedding.conjugate τ)) ≃ Idx X.dim)
  (hσ : ∀ i, (σ i).1 = ComplexEmbedding.conjugate i.1)

end

end Torus

section Coord

open TorusCoord TorusAtDataPf IndefiniteRowSideFullHecke.TorusThetaNorms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {D : Data E r}
  {x : Frame D.Ψ r} {w0 : 𝓞 E}

def fr (T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x) (τ : D.Ψ) (a : Fin r) : Fin r → ℂ :=
  (√(D.c τ) : ℂ) • FD.col (mat T.e τ) a

variable (T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x)

end Coord

section Mirror

open TorusCoord TorusAtDataPf IndefiniteRowSideFullHecke.TorusThetaNorms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {D : Data E r}
  {x : Frame D.Ψ r} {w0 : 𝓞 E}

structure Mirror (A : I2.TorusAt D x) (T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x)
    (σ : Idx T.X.dim ≃ Idx A.T.dim) : Prop where
  rankOne_base_weight_eq_cmTheta : A.w0 = w0
  frame : ∀ τ a, A.e τ a = (√(D.c τ) : ℂ) • FD.col (mat T.e τ) a
  swap : ∀ i, (σ i).1 = ComplexEmbedding.conjugate i.1
  order_neg : ∀ i, i.1 ∈ D.Ψ → ((σ i).2 : ℕ) = i.2
  order_pos : ∀ i, i.1 ∉ D.Ψ → ((σ i).2 : ℕ) + i.2 + 1 = D.p0
  gen : ∀ y, T.s (fun _ => cj A.T σ y) = conj (A.s fun _ => y)

open Classical in

def realExt (A : I2.TorusAt D x) (w : D.Ψ → Fin r → ℂ) : Vsp A.T.dim :=
  WithLp.toLp 2 fun j =>
    if h : j.1 ∈ D.Ψ then pr D A.e w ⟨j.1, h⟩
      ⟨j.2, (j.2.2.trans_eq (A.dim_pos ⟨_, h⟩)).trans_le D.p0_le⟩
    else -conj (pr D A.e w ⟨_, conj_mem D h⟩ ⟨D.p0 + j.2, by
      have h1 := j.2.2.trans_eq ((congrArg A.T.dim (conj_conj_X j.1).symm).trans
        (A.dim_neg ⟨_, conj_mem D h⟩))
      omega⟩)

namespace Mirror

variable {A : I2.TorusAt D x} {T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x} {σ : Idx T.X.dim ≃ Idx A.T.dim}
  (h : Mirror A T σ)
include h

end Mirror

end Mirror

section Exist

open TorusCoord TorusAtDataPf IndefiniteRowSideFullHecke.TorusThetaNorms SemicharIndep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {D : Data E r}

end Exist

end

end GlobalTheory.TorusMirror
