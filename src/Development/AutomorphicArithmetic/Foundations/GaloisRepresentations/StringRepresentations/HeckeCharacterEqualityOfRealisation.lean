import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified

section
noncomputable section

namespace UpperTheory.GalN

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At UpperTheory.Lit.Car

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def LGCatN {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) (A : NAut N) (w : PlE H) : Prop :=
  ∀ x, ∃ P, A.ptV i P = some x ∧
    RelW N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w) (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2))

variable (A : NAut N)

def AwayRepN (i : N.Loc) (m : ℕ) (L : ∀ w, A.LP w) : Prop :=
  ∃ r : G H.E N.Om →* GL (Fin m) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧
    ∀ w, w ∉ placesOver H.E (N.l i) → RelW N A (A.wdOf i r w) (L w)

def GalIsoN (i : N.Loc) : Prop := ∀ (P : A.AV i) (Pa : List (Part A.CG)), IsBCV N A i P Pa →
  ∃ r : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i)),
    Continuous (fun g => ((r g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))) ∧
    IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      RelW N A (A.wdOf i r w) (A.lpTw (isoLoc N A Pa w) ((1 - (R.nV : ℝ)) / 2))
end

def LGCN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w : PlE D.host, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → LGCatN D.nd r D.naut w

def RowRepAtGN (D : D7) : Prop := ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
  ∃ (Sig : List (Part D.naut.CG)) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)),
    HasParamW D.nd D.naut i σ Sig ∧ IsRepOfSig D.nd D.naut i Sig ρ ∧
    ∀ k v, D.nd.l i ≠ D.host.g k →
      RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v))
        (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2))

end UpperTheory.GalN
end
end

section
noncomputable section

namespace UpperTheory.GalN

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def GalAwayN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))) ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        RelW D.nd D.naut (D.naut.wdOf i r w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def IsStringRepN (D : D7) (i : D.nd.Loc) (p : Part D.naut.CG)
    (R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((R g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i)))) ∧ IsSSRep R ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut
      (D.naut.wdOf i R w) (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2))

theorem strN' {D : D7} {i : D.nd.Loc} {p : Part D.naut.CG} {R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))}
    (h : IsStringRepN D i p R) : IsStringRepN D i p R := h

def HeckeCharacterEqualityOfRealisation : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → ∀ (i : D.nd.Loc) (χ χ' : D.naut.CG 1) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))),
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG χ w) s)) →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ' w) s) →
    χ = χ'

theorem unr_part {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {w : PlE H} :
    ∀ L : List (Part A.CG), A.unr (isoLoc N A L w) → ∀ p ∈ L, 1 ≤ p.d → A.unr (A.locG p.π w)
  | [], _, _, hp, _ => absurd hp List.not_mem_nil
  | q :: L, hun, p, hp, hd => by
    have hun' : A.unr (A.lpSum (spehLoc N A q w) (isoLoc N A L w)) := hun
    have h12 := (A.unr_sum _ _).1 hun'
    rcases List.mem_cons.1 hp with rfl | hp
    · have h := h12.1
      obtain ⟨d, hd'⟩ : ∃ d, p.d = d + 1 := ⟨p.d - 1, by omega⟩
      rw [GlobalTheory.StringDecomp.spehLoc_eq, hd', List.range_succ_eq_map] at h
      exact (A.unr_tw _ _).1 ((A.unr_sum _ _).1 h).1
    · exact unr_part L h12.2 p hp hd

end UpperTheory.GalN
end
end
