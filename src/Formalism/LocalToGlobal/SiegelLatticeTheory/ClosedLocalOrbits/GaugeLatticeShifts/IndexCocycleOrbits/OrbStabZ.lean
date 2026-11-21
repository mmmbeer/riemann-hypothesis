import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.VIOS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word)

variable (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

end Formalism.L2.SG.Pf.VIOS
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxRatio {G : Type} [Group G] (A B : Subgroup G) : ℝ :=
  (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

def IdxCocycle : Prop :=
  ∀ (G : Type) [Group G] (A B C : Subgroup G), B ≤ C → B.relIndex C ≠ 0 →
    IdxRatio A B = (B.relIndex C : ℝ) * IdxRatio A C

abbrev LF (D : D7) (u' : D.what₂.Word) : Type := LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)

abbrev PtR (D : D7) : Type := Point D.host.E (D.R.rS + 1)

section Data

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def NDataG (t : Term D u u' F0 what₂) (w : PtR D) (F' : LF D u') (L U : MatR D) : Prop :=
  t.relevant ∧ t.generic ∧ NormRep t w F' L U ∧ Gval (lf D F0) F' ≠ 0

end Data

variable (D : D7) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def OrbStabZ (C : MatR D → MatR D → Subgroup (GLR D)) : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : PtR D) (F' : LF D u') (L U : MatR D),
    NDataG t w F' L U → stabAut D u u' F0 what₂ t F' L ≤ C (ZhatL (lf D F0) F') L ∧
      (stabAut D u u' F0 what₂ t F' L).relIndex (C (ZhatL (lf D F0) F') L) =
        (orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).ncard

end Formalism.L2.SG.Pf.IndexCocycleOrbits
end
end
