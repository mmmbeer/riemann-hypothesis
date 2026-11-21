import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

noncomputable section

open scoped TensorProduct ENNReal Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianGramMatrices

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)

theorem tF_herm (r : ℕ) (T : F) (a b : Fin (r + 1)) :
    σ (TF r (algebraMap F E T) b a) = TF r (algebraMap F E T) a b := by
  unfold TF
  by_cases h : a = b
  · subst h
    by_cases h' : a = Fin.last r <;> simp [h']
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

def gramTwo {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin ((r + 1) + (r + 1))) (Fin ((r + 1) + (r + 1))) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (TF r (algebraMap F E T)) Z (cT (σ : E →+* E) Z) (TF r (algebraMap F E T')))

def hermF (r : ℕ) (T : F) : HermR R σ (r + 1) :=
  hermOf R σ (TF r (algebraMap F E T)) (tF_herm σ r T)

end Gram

section Local

variable {F : Type} (E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def intV : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

variable {E}

def latAt {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (intV E v) (Fin n → Fv F v ⊗[F] E) :=
  Submodule.span (intV E v) {y | ∃ x ∈ Λ, y = fun i => (1 : Fv F v) ⊗ₜ[F] x i}

def PrimAt {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) {ι : Type}
    (X : ι → Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ (κ : Type) (Y : κ → Fin n → Fv F v ⊗[F] E),
    LinearIndependent (intV E v) (Sum.elim X Y) ∧
      Submodule.span (intV E v) (Set.range (Sum.elim X Y)) = latAt v Λ

variable (δ : v.adicCompletionIntegers F)

def scal (r : ℕ) (b : Fin (r + 1)) : Fv F v := ((δ : Fv F v)⁻¹) ^ (r - (b : ℕ))

def locFr {n r : ℕ} (P : Fin (r + 1) → Fin n → Fv F v ⊗[F] E) :
    Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => scal v δ r b • P b

def locZ {r : ℕ} (Z : Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E) :
    Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E :=
  fun a b => (scal v δ r a * scal v δ r b) • Z a b

open scoped Classical in

def levAt (g₁ g₂ : ℕ) : Option ℕ :=
  if (g₁ : 𝓞 F) ∈ v.asIdeal then some g₁ else if (g₂ : 𝓞 F) ∈ v.asIdeal then some g₂ else none

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
  (g₁ g₂ : ℕ) (r : ℕ) (T T' : F)

def Om : Set ((Fin (r + 1) → Fin n → Fv F v ⊗[F] E) × (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) :=
  {p | LinearIndependent (Fv F v ⊗[F] E) p.1 ∧ gramR (Fv F v) σ J p.1 = (hermF (Fv F v) σ r T).1 ∧
    LinearIndependent (Fv F v ⊗[F] E) p.2 ∧ gramR (Fv F v) σ J p.2 = (hermF (Fv F v) σ r T').1 ∧
    PrimAt v Λ (locFr v δ p.1) ∧ PrimAt v Λ (locFr v δ p.2) ∧
    ∀ q, levAt v g₁ g₂ = some q →
      ∀ b, ((q : Fv F v)⁻¹) • (locFr v δ p.2 b - locFr v δ p.1 b) ∈ latAt v Λ}

def yZero (q : ℕ) (Z : Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E) :
    Fin (r + 1) → Fin (r + 1) → Fv F v ⊗[F] E :=
  fun a b => ((q : Fv F v)⁻¹) • (locZ v δ Z a b - (hermF (Fv F v) σ r T).1 a b)

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def stabK (Λ : Submodule (𝓞 E) (Fin n → E)) : Set (HA (Af F) σ J) :=
  {h | ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E), y ∈ latAt v Λ ↔
    (((HA.mat (Af F) σ J h : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map
      (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))).mulVec y ∈ latAt v Λ}

def IsRho {a : ℕ} (μi : Measure (HA (Ainf F) σ J)) (S : HermR (Ainf F) σ a)
    (ω : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (ρ : ℝ) : Prop :=
  AllSome (fun X₀ : Fin a → Fin n → Ainf F ⊗[F] E =>
      LinearIndependent (Ainf F ⊗[F] E) X₀ ∧ gramR (Ainf F) σ J X₀ = S.1) fun X₀ =>
    ∀ Φ : (Fin a → Fin n → Ainf F ⊗[F] E) → ℝ≥0∞, Measurable Φ →
      ∫⁻ X, Φ X ∂ω = ENNReal.ofReal ρ * ∫⁻ g, Φ (g • X₀) ∂μi

def HasSig (p : ℕ) : Prop :=
  ∀ τ : E →+* ℂ, ∃ P : Matrix (Fin n) (Fin n) ℂ,
    P.conjTranspose * J.map τ * P = Matrix.diagonal fun i : Fin n => if (i : ℕ) < p then 1 else -1

def SplitsFully (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E

end Global

example {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ} (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    gramTwo σ T T' Z (Fin.castAdd (r + 1) a) (Fin.natAdd (r + 1) b) = Z a b := by
  simp only [gramTwo, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂]

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianGramMatrices
