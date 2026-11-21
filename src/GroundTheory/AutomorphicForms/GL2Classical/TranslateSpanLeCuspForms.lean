import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke

section
open NumberField IsDedekindDomain Matrix CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

def triHecke (x z : ℕ) [NeZero x] [NeZero z] (c : ℤ) : GL (Fin 2) ℚ where
  val := !![(x : ℚ), -c; 0, z]
  inv := !![(x : ℚ)⁻¹, c / (x * z); 0, (z : ℚ)⁻¹]
  val_inv := by
    have hx := natCast_ne_zero_rat x
    have hz := natCast_ne_zero_rat z
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  inv_val := by
    have hx := natCast_ne_zero_rat x
    have hz := natCast_ne_zero_rat z
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

variable (p q : ℕ) [NeZero p] [NeZero q]

instance : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩

variable [Fact p.Prime]

variable [Fact q.Prime] (N : ℕ) [NeZero N]

variable {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup ComplexConjugate
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Reduction RightCosetSpace

set_option linter.unusedSectionVars false

variable (μ : Measure (normOneGL ℚ 2)) [μ.IsHaarMeasure]

def adelicPetersson (φ₁ φ₂ : AdelicGL ℚ 2 → ℂ) : ℂ :=
  ∫ x in fundamentalDomain (rationalGLOne ℚ 2), conj (φ₁ x) * φ₂ x ∂μ

variable {N : ℕ} [NeZero N] {k : ℤ}

def scalarQ (c : ℚ) (hc : c ≠ 0) : GL (Fin 2) ℚ where
  val := !![c, 0; 0, c]
  inv := !![c⁻¹, 0; 0, c⁻¹]
  val_inv := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
  inv_val := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]

variable {N : ℕ} [NeZero N] {k : ℤ}

variable (p : ℕ) [NeZero p]

def heckeTranslate (ξ : GL (Fin 2) ℚ) : AdelicGL ℚ 2 :=
  finEmb ℚ 2 (finiteDiagonal ℚ 2 ξ) *
    realEmb (kGL (Real.sqrt p : ℂ) (by exact_mod_cast (Real.sqrt_pos.2 (natCast_pos_real p)).ne'))

variable [Fact p.Prime]

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm ValuativeRel Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Rat.HeightOneSpectrum

variable (p : ℕ) [hp : Fact p.Prime]

def placeAt : HeightOneSpectrum (𝓞 ℚ) := (primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩

variable {p}

variable (p)

abbrev Qp : Type := (placeAt p).adicCompletion ℚ

def toInts (x : 𝒪[Qp p]) : (placeAt p).adicCompletionIntegers ℚ :=
  ⟨x, (GroundTheory.Global.mem_valuationInteger_iff (placeAt p) (x : Qp p)).1 x.2⟩

def ofInts (y : (placeAt p).adicCompletionIntegers ℚ) : 𝒪[Qp p] :=
  ⟨(y : Qp p), (GroundTheory.Global.mem_valuationInteger_iff (placeAt p) (y : Qp p)).2 y.2⟩

theorem uniformizer_ne_zero : (GLnLocal.uniformizer (Qp p) : Qp p) ≠ 0 := fun h =>
  (GLnLocal.irreducible_uniformizer (Qp p)).ne_zero (Subtype.ext h)

variable {N : ℕ} [NeZero N]

open Spherical Iwasawa

def localRightRep : Representation ℂ (GL (Fin 2) (Qp p)) (AdelicGL ℚ 2 → ℂ) :=
  finRightRep.comp (localEmbedding (placeAt p))

variable {k : ℤ}

theorem gMat_univ (c : Pairs (Finset.univ : Finset (Fin 2)) → 𝓀[Qp p]) :
    gMat Finset.univ c = torusPow (Qp p) 2 (fun _ => 1) := by
  ext i j
  rw [gMat_apply, coe_torusPow, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
  simp [lamS, Matrix.one_apply, Matrix.diagonal_apply]

variable [MeasurableSpace (GL (Fin 2) (Qp p))] [BorelSpace (GL (Fin 2) (Qp p))]
  (μ : Measure (GL (Fin 2) (Qp p))) [μ.IsHaarMeasure]

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm ValuativeRel Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Spherical Iwasawa GLnLocal HeckeAlgebra

variable (p : ℕ) [hp : Fact p.Prime]

def translateSpan (φ : AdelicGL ℚ 2 → ℂ) : Submodule ℂ (AdelicGL ℚ 2 → ℂ) :=
  Submodule.span ℂ (Set.range fun g : FiniteAdelicGL ℚ 2 => finRightRep g φ)

theorem translateSpan_le_comap (φ : AdelicGL ℚ 2 → ℂ) (g : FiniteAdelicGL ℚ 2) :
    translateSpan φ ≤ (translateSpan φ).comap (finRightRep g) := by
  rw [translateSpan, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
  exact Submodule.subset_span ⟨g * h, rfl⟩

def translateRep (φ : AdelicGL ℚ 2 → ℂ) : Representation ℂ (GL (Fin 2) (Qp p)) (translateSpan φ) :=
  (finRightRep.subrepresentation (translateSpan φ) (translateSpan_le_comap φ)).comp
    (localEmbedding (placeAt p))

variable {N : ℕ} [NeZero N] [MeasurableSpace (GL (Fin 2) (Qp p))] [BorelSpace (GL (Fin 2) (Qp p))]
  (μ : Measure (GL (Fin 2) (Qp p))) [μ.IsHaarMeasure]

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Spherical

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem translateSpan_le_cuspForms (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ≤ cuspForms ℚ 2 := by
  rw [translateSpan, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  have h := mem_cuspForms.1 (liftEquiv_mem_cuspForms f)
  exact ⟨h.1.rightTranslate_finEmb g, h.2.translate _⟩

end GL2Classical

end

end GroundTheory.Automorphic
end
