import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

abbrev Trip (a : D.nd.Loc) : Type := D.ntw.Sig (D.ntw.twOf a)

def rhoTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* GL (Fin D.R.r) (D.nd.O a) :=
  mapRep (D.ntw.twist₂ a) (D.ntw.rhoS (D.ntw.twOf a) s)

def chiTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  (Units.map (D.ntw.twist₂ a).toMonoidHom).comp
    (D.ntw.chi1 (D.ntw.twOf a) (D.ntw.jS (D.ntw.twOf a) s) (D.ntw.side (D.ntw.twOf a) s))

def tTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a) :=
  twistM ((Units.coeHom _).comp (rhoTrip D a s)) (chiTrip D a s)⁻¹

def badS (a : D.nd.Loc) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {v | ((∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨ v ∈ D.ntw.pD (D.ntw.twOf a)) ∧
    v ∉ placesOver D.host.E (D.nd.l a)}

def selT (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) :
    Submodule (D.nd.O a) (H1 (WKG (twistM (tTrip D a s) ψ⁻¹))) :=
  Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (badS D a ∪ ↑(D.nd.Q a))
    (twistM (tTrip D a s) ψ⁻¹)

def psiAt (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  if D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a then D.ntw.psiL a else (D.ntw.psiL a)⁻¹

def IsGoodRow (a : D.nd.Loc) (σ : D.what₂.FT) : Prop :=
  D.what₂.isot (D.nd.j a) σ ≠ ⊥ ∧ D.nd.goodRow σ

def IsRhoOfRow (a : D.nd.Loc) (σ : D.what₂.FT) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  IsSSRep (mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) ρ) ∧
  ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w →
    ∀ (B : ValuationSubring D.nd.Om) (g : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) g →
      ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).charpoly.map
          (iotaO D.nd D.naut a) =
        galPol D.naut (D.naut.lpTw (D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w))
          ((1 - (D.R.nV : ℝ)) / 2))

def IsTripleOf (a : D.nd.Loc) (σ : D.what₂.FT) (s : Trip D a) : Prop :=
  D.ntw.jS (D.ntw.twOf a) s = D.nd.j a ∧ D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a ∧
    IsRhoOfRow D a σ (rhoTrip D a s)

def TripAll : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT), IsGoodRow D a σ → ∃ s : Trip D a, IsTripleOf D a σ s

def IsRowOf (a : D.nd.Loc) (π : D.nd.X a) (σ : D.what₂.FT) : Prop :=
  IsGoodRow D a σ ∧ ∃ Sg : List (Part D.naut.CG),
    HasParamW D.nd D.naut a σ Sg ∧ HasParamX D.nd D.naut a π Sg

def Attached (a : D.nd.Loc) (π : D.nd.X a) (s : Trip D a) : Prop :=
  ∃ σ, IsRowOf D a π σ ∧ IsTripleOf D a σ s

def ind2 (l : ℕ) : ℚ := if l = 2 then 1 else 0

def epsL (l : ℕ) : ℚ := ((l : ℚ) ^ 2)⁻¹

def dGood (j : ℕ) (w : D.what₂.places.Pl) : ℕ :=
  ∑ a ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood a, D.nd.mult a π

theorem badS_eq (a : D.nd.Loc) : badS D a = ↑(D.nd.S a) := by
  ext v
  have h := D.ntw.pD_eq (D.ntw.twOf a)
  rw [D.ntw.twOf_l a] at h
  have h' : v ∈ D.ntw.pD (D.ntw.twOf a) ↔
      v ∈ placesOver D.host.E (if D.nd.l a = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← h]; rfl
  simp only [badS, Set.mem_setOf_eq, Finset.mem_coe, D.nd.S_def, h', Fin.exists_fin_two, or_assoc]

example : ind2 2 + epsL 2 + epsL 2 = 3 / 2 := by norm_num [ind2, epsL]

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

end
