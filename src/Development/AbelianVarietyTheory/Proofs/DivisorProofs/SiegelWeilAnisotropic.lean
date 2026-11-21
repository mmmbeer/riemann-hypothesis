import Mathlib
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)

open Classical in

def withReal {F : Type} [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Finset (Pl F) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Sf.map ⟨Sum.inr, Sum.inr_injective⟩

section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)

def HalfPlaneCont (π : O.Pi) (S : Finset (Pl F)) (t : ℕ) (g : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ g {s | (t : ℝ) / 2 ≤ s.re} ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → HasProd (fun v : {v : Pl F // v ∉ S} => O.Lv π v (s + 1 / 2)) (g s)

variable (F E) in

def DInvAnalytic : Prop :=
  ∀ (n M : ℕ) (P : HeightOneSpectrum (𝓞 F) → Prop), ∃ e : ℂ → ℂ, AnalyticOnNhd ℂ e {s | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 / 2 < s.re → e s ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 F), dvLoc (E := E) n M w s ≠ 0) ∧
      HasProd (fun w : {w // P w} => (dvLoc (E := E) n M w.1 s)⁻¹) (e s)

def CuspDecay : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (N : ℝ),
    Integrable (fun g : O.GQ × O.GQ => (max 1 (O.ht (O.io g.1 g.2))) ^ N * ‖O.form π f₁ g.1‖ * ‖O.form π f₂ g.2‖)
      (O.muG.prod O.muG)

def SiegelWeilAnisotropic : Prop :=
  ∀ t : ℕ, B.rank = A.rank + t → 1 ≤ t → wittIdx B = 0 → ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ → ∀ g,
    AnalyticAt ℂ (fun s => O.Eis (O.tensor φ₁ φ₂) s g) ((t : ℂ) / 2) ∧
      O.Eis (O.tensor φ₁ φ₂) ((t : ℂ) / 2) g = Ith O (O.tensor φ₁ φ₂) g

variable {O}

def IsAdmissible {π : O.Pi} {n : ℕ} {I K Xf : Type} (t : ℕ) (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) (φ : I → K → O.Sch) : Prop :=
  ∀ ι ι' i i' k a b, RFData O π (vec ι i a) (vec ι' i' b) (φ i k) (φ i' k) (withReal Sf) ((t : ℂ) / 2)

end Interface

def IsLValue {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B) (π : O.Pi) (S : Finset (Pl F)) (t : ℕ) (c : ℂ) : Prop :=
  ∀ g, HalfPlaneCont O π S t g → c = g ((t : ℂ) / 2)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Towers

variable (T : ThetaX D)

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

open Classical in

def finPl (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (μ : D.what₂.Tup) : Finset (Formalism.MainNotions.InnerProductFormulaField.Pl D) :=
  X.Sg ∪ Finset.univ.map (e μ)

def BlockPart (j : ℕ) (πf : D.what₂.FT) {O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)} {I : Type}
    (evW : D.what₂.Mj j →ₗ[ℂ] (I → O.GQ → ℂ)) {π : O.Pi} {n : ℕ} {Xf : Type}
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) : Prop :=
  D.what₂.isot j πf ≤ Submodule.span ℂ {x : D.what₂.Mj j | ∃ ι a, ∀ i, evW x i = O.form π (vec ι i a)}

end GlobalTheory.ThetaInner

end
