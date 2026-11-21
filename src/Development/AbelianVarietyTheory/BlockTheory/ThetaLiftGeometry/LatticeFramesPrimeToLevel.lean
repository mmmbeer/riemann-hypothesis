import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Neutral.B1
open scoped Matrix

section Adelic

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

abbrev Ad : Type := FiniteAdeleRing (𝓞 H.E) H.E

def StabAt (l : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (Ad H)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H l v →
    (∀ a b, M a b v ∈ v.adicCompletionIntegers H.E) ∧ Valued.v (M.det v) = 1

def IsBasisAt (l : ℕ) {N : ℕ} (g : GL (Fin N) (Ad H)) (b : Matrix (Fin N) (Fin N) H.E) : Prop :=
  StabAt H l (((g⁻¹ : GL (Fin N) (Ad H)) : Matrix (Fin N) (Fin N) (Ad H)) * b.map (algebraMap H.E (Ad H)))

end Adelic

section abelian₂

variable {l : ℕ} [Fact l.Prime] (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l])

def IntAt (z : ℂ) : Prop := ∃ h : z ∈ algebraicClosure ℚ ℂ, ‖lam ⟨z, h⟩‖ ≤ 1

end abelian₂

abbrev Reps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → GL (Fin (D.R.N i)) (Ad D.host)

abbrev Frames (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ

def eps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : ℂ :=
  (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c'

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts
