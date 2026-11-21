import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

section
noncomputable section

open Polynomial Finset GlobalTheory.Cong

namespace UpperTheory.Gal.CharacterCongruences

section Approx

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

def PolyApproxAt (ε : ℝ) (θ : J → k) (S : Set (J → k)) : Prop :=
  ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

omit [IsUltrametricDist k] in

theorem PolyApproxAt.comp {ε : ℝ} {θ : J → k} {S : Set (J → k)} (h : PolyApproxAt ε θ S) {J' : Type} (f : J' → J) :
    PolyApproxAt ε (θ ∘ f) ((· ∘ f) '' S) := by
  classical
  obtain ⟨s, c, hs, hc⟩ := h
  refine ⟨s.image (· ∘ f), fun z => ∑ η ∈ s.filter (fun η => η ∘ f = z), c η, ?_, fun P => ?_⟩
  · rw [Finset.coe_image]; exact Set.image_mono hs
  · convert hc (MvPolynomial.rename f P) using 2
    rw [MvPolynomial.aeval_rename]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := (· ∘ f)) (t := s.image (· ∘ f)) fun η hη => Finset.mem_image_of_mem _ hη]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun η hη => ?_
    rw [MvPolynomial.aeval_rename, (Finset.mem_filter.1 hη).2]

end Approx

section Ring

variable (O : Type) [CommRing O] (l N m : ℕ)

def phi : O[X] := ∑ i ∈ range (l ^ m), X ^ (i * l ^ (N - m))

abbrev abelian₂ : Type := AdjoinRoot (phi O l N m)

end Ring

abbrev Ch (n : ℕ) : Type := Multiplicative (ZMod n) →* ℂˣ

end UpperTheory.Gal.CharacterCongruences

end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep
open ValuativeRel

namespace UpperTheory.Gal.CharacterCongruences

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

structure IsLevel (C : Subgroup (UA E a)) : Prop where
  fin : C ≤ finU E a
  compact : IsCompact (C : Set (UA E a))
  isOpen : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E a ⊆ C

def TorsFreeAt (K : Subgroup (UA E a)) (u : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ k ∈ K, IsOfFinOrder (cLoc u k) → cLoc u k = 1

structure OfVec (lam : (E →+* ℂ) → DomWeight a) (p : (UA E a → ℂ) → Prop) (U : Submodule ℂ (UA E a → ℂ)) : Prop where
  aut : IsAutRepU U
  wt : ∀ τ, HasWeightAt U τ (lam τ)
  vec : ∃ φ ∈ U, φ ≠ 0 ∧ p φ

def NeatOfPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C → ∀ u, TorsFreeAt C u →
    ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c ∈ C, ∀ x ∈ infU E a, γ * g = g * c * x → c = 1

end UpperTheory.Gal.CharacterCongruences

end
end
