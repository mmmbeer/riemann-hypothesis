import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word)

variable (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolumeIndexRepresentationNonzero : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
      (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
      t.relevant → t.generic → NormRep t w F₁ L₁ U₁ → Formalism.MainNotions.S.Lat.Gval (lf D F0) F₁ ≠ 0 → NormRep t w F₂ L₂ U₂ → Formalism.MainNotions.S.Lat.Gval (lf D F0) F₂ ≠ 0 →
        volIdx D u u' F0 what₂ δ M t w F₁ L₁ = volIdx D u u' F0 what₂ δ M t w F₂ L₂

end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

variable {G : Type*} [Group G]

def ratio (A S : Subgroup G) : ℝ := (A.relIndex S : ℝ) / (S.relIndex A : ℝ)





abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom


end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def loGen (n : ℕ) (K : Type*) [Field K] : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) :=
  Subgroup.closure {a | ∀ i j, (i < j → (a : Matrix (Fin n) (Fin n) K) i j = 0) ∧
    (i = j → (a : Matrix (Fin n) (Fin n) K) i j = 1)}

def UniConjIdx (n : ℕ) (K : Type*) [Field K] : Prop :=
  ∀ (X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) (g : Matrix.GeneralLinearGroup (Fin n) K),
    g ∈ loGen n K → X ≤ loGen n K → X.relIndex (cj g X) ≠ 0 → (cj g X).relIndex X ≠ 0 →
      X.relIndex (cj g X) = (cj g X).relIndex X

variable (D : D7) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxFinP : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
  (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
    t.relevant → t.generic → NormRep t w F' L U → Formalism.MainNotions.S.Lat.Gval (lf D F0) F' ≠ 0 →
      (stabAut D u u' F0 what₂ t F' L).relIndex (stabInt D u u' δ M w) ≠ 0 ∧
      (stabInt D u u' δ M w).relIndex (stabAut D u u' F0 what₂ t F' L) ≠ 0

def StabAutConjP : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
    NormRep t w F₁ L₁ U₁ → NormRep t w F₂ L₂ U₂ →
      ∃ g : GLR D, g ∈ loGen (D.R.rS + 1) D.host.E ∧
        stabAut D u u' F0 what₂ t F₂ L₂ = cj g (stabAut D u u' F0 what₂ t F₁ L₁)



end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end
