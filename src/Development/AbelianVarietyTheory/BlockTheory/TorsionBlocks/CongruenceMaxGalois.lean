import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

def IsReduction {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l a : ℕ} [Fact l.Prime]
    (r : Γ →* GL (Fin a) (Qbar l)) (rb : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsSSRep rb ∧ IsOpen (rb.ker : Set Γ) ∧
    ∃ red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l, ∀ g : Γ, ∃ p : (Zbar l)[X],
      p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
      p.map red = ((rb g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) :
        Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

variable (D : D7)

abbrev GalE : Type := G D.host.E D.nd.Om

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (φ : GalE D),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) φ →
    ((r φ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

end
