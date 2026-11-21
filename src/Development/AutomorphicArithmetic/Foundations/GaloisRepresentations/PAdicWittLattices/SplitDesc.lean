import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
import Development.EtaleCohomology.WeilConjectures.StabPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV

namespace UpperTheory.Gal.G3

abbrev FinSub (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Type := {L : IntermediateField k Ω // FiniteDimensional k L}

def finDiag (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : FinSub k Ω ⥤ Under (CommRingCat.of k) where
  obj L := Under.mk (CommRingCat.ofHom (algebraMap k L.1))
  map {L M} h := Under.homMk (CommRingCat.ofHom (IntermediateField.inclusion (show L.1 ≤ M.1 from h.le)).toRingHom)

def finCocone (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Cocone (finDiag k Ω ⋙ Under.forget _) where
  pt := CommRingCat.of Ω
  ι := { app := fun L => CommRingCat.ofHom (algebraMap L.1 Ω) }

def SplitDesc : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (J : Type) [Finite J]
  (σ : J → (W ⟶ Y)), Splits s c σ → IsFinite s ∧ Etale s

def CharVan : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) = 0 → ∀ {X : Scheme.{0}} (_ : X ⟶ sp k) (n i : ℤ),
  Subsingleton (Hl l (sch.obj X) n i)

def CorrUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (_ : Z ⟶ sp k) (s : Y ⟶ Z) (t : Y ⟶ Z')
  (A A' : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)), IsCorrOp l s t A → IsCorrOp l s t A' → A = A'

def VBcS : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] (φ : k →+* Ω),
  IsUnit (l : k) → ∀ {X : Scheme.{0}} (p : X ⟶ sp k) [IsProper p] [Smooth p] (n i : ℤ),
  Function.Bijective (pullHQ l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) n i)

end UpperTheory.Gal.G3

end
