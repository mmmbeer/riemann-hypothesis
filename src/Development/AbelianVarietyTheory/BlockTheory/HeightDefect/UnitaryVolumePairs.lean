import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Volume

variable {D : D7}

def IsRealFrames (V : HSp D) (P Q : ℕ) (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) : Prop :=
  P + Q = V.rank ∧ ∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq P Q * A ρ = gramAt D V ρ

def volBox (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (B : D.what₂.Tau → Set (UpqT P Q)) : Set (GA D V) :=
  {h | ∃ k ∈ KsphC V ∅, ∃ g ∈ GinfC V, h = k * g ∧
    ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) g}

def IsProductForm (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (μ : Measure (GA D V)) : Prop :=
  ∀ B : D.what₂.Tau → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) →
    μ (volBox θ V A B) = ∏ ρ, D.cd.cd P Q (B ρ)

def IsVolMeasure (V : HSp D) (P Q : ℕ) (μ : Measure (GA D V)) : Prop :=
  μ.IsHaarMeasure ∧ ∃ θ, IsInfFam θ ∧
    ∃ A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ, IsRealFrames V P Q A ∧ IsProductForm θ V A μ

def IsVolPair (V : HSp D) (P Q : ℕ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsVolMeasure V P Q μ ∧ IsFundamentalDomain (GQ V) 𝓕 μ

def IsOfKind (V : HSp D) (P Q : ℕ) : Prop := V.SigOK ∧ ∀ τ, V.sig τ = (P, Q)

variable (D)

def VolumeTie : Prop :=
  ∀ (V : HSp D) (P Q : ℕ), IsOfKind V P Q →
    (∃ μ 𝓕, IsVolPair V P Q μ 𝓕) ∧ ∀ μ 𝓕, IsVolPair V P Q μ 𝓕 → μ 𝓕 = ENNReal.ofReal (D.vol V)

def VolPairExists : Prop :=
  ∀ (V : HSp D) (P Q : ℕ), IsOfKind V P Q →
    (∃ μ 𝓕, IsVolPair V P Q μ 𝓕) ∧ ∀ μ 𝓕, IsVolPair V P Q μ 𝓕 → 0 < μ 𝓕 ∧ μ 𝓕 < ⊤

end Volume

section Ideles

variable (D : D7)

abbrev AE : Type := AF D.host.F ⊗[D.host.F] D.host.E

abbrev IdE : Type := (AE D)ˣ

abbrev IdF : Type := (AF D.host.F)ˣ

def infPart : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def finPart : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def locPart (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom.comp (finPart D)

def ratE : D.host.Eˣ →* IdE D := Units.map (incA D).toMonoidHom

def resF : IdF D →* IdE D :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    AF D.host.F →+* AF D.host.F ⊗[D.host.F] D.host.E).toMonoidHom

def ratF : D.host.Fˣ →* IdF D := Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom

def conjId : IdE D →* IdE D := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def normId : IdE D →* IdE D := MonoidHom.id (IdE D) * conjId D

def intAfE : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, y = a ⊗ₜ[D.host.F] (x : D.host.E)}

def IsIntUnit (u : IdE D) : Prop :=
  infPart D u = 1 ∧ finPart D u ∈ intAfE D ∧ finPart D (u⁻¹ : IdE D) ∈ intAfE D

end Ideles

section Hecke

variable (D : D7)

def HeckeChar : Subgroup (IdE D →* Circle) where
  carrier := {χ | Continuous χ ∧ ∀ x, χ (ratE D x) = 1}
  one_mem' := ⟨continuous_const, fun _ => rfl⟩
  mul_mem' := by
    rintro χ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨h1.mul h3, fun x => by simp [h2 x, h4 x]⟩
  inv_mem' := by
    rintro χ ⟨h1, h2⟩
    exact ⟨h1.inv, fun x => by simp [h2 x]⟩

def normGroup : Subgroup (IdF D) := (ratF D).range ⊔ (normId D).range.comap (resF D)

open Classical in

def eta (a : IdF D) : ℂ := if a ∈ normGroup D then 1 else -1

variable {D}

def IsAtPlace (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (ρ : D.what₂.Tau) (u : IdE D) : Prop :=
  finPart D u = 1 ∧ ∀ ρ', ρ' ≠ ρ → θ ρ' (infPart D u) = 1

def HasExponent (χ : IdE D →* Circle) (ρ : D.what₂.Tau) (a : ℚ) : Prop :=
  ∃ n : ℤ, (n : ℚ) = 2 * a ∧ ∃ θ, IsInfFam θ ∧ ∀ u : IdE D, IsAtPlace θ ρ u →
    (χ u : ℂ) = (θ ρ (infPart D u) / (‖θ ρ (infPart D u)‖ : ℂ)) ^ n

def RestrictsToEtaPow (χ : IdE D →* Circle) (k : ℕ) : Prop := ∀ a : IdF D, (χ (resF D a) : ℂ) = eta D a ^ k

def TrivialOnF (χ : IdE D →* Circle) : Prop := ∀ a : IdF D, χ (resF D a) = 1

def IsUnramified (χ : IdE D →* Circle) : Prop := ∀ u, IsIntUnit D u → χ u = 1

def IsUnramifiedAt (χ : IdE D →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ u, IsIntUnit D u → (∀ v', v' ≠ v → locPart D v' u = 1) → χ u = 1

def conjChar (χ : IdE D →* Circle) : IdE D →* Circle := χ.comp (conjId D)

def IsEtaTilde (χ : IdE D →* Circle) : Prop :=
  χ ∈ HeckeChar D ∧ IsUnramified χ ∧ RestrictsToEtaPow χ 1 ∧ ∀ ρ, HasExponent χ ρ (1 / 2)

variable (D) in

def FirstPropositionFrame : Subgroup (IdE D) := (normId D).ker

variable (D)

end Hecke

section Witt

variable {D : D7}

def IsMinusHyp (V : HSp D) (i : ℕ) (V' : HSp D) : Prop :=
  ∃ (ι : V'.V →ₗ[D.host.E] V.V) (e f : Fin i → V.V),
    HSpace.IsIsomEmb V' V ι ∧
    (∀ a b, V.hD (e a) (e b) = 0) ∧ (∀ a b, V.hD (f a) (f b) = 0) ∧
    (∀ a b, V.hD (e a) (f b) = if a = b then 1 else 0) ∧
    (∀ a x, V.hD (ι x) (e a) = 0 ∧ V.hD (ι x) (f a) = 0) ∧
    LinearMap.range ι ⊔ Submodule.span D.host.E (Set.range e ∪ Set.range f) = ⊤

variable (D)

end Witt

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

end
