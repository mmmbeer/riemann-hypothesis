import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SettingExistsAdapted
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.SettingExistsAdapted

namespace Formalism.L2.SG.Pf.Set3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7}

abbrev Ix (D : D7) : Type := Fin D.R.rS ⊕ (Fin D.R.rS ⊕ Unit)

def gstd (T : D.host.E) : Ix D → Ix D → D.host.E
  | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
  | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => -T
  | _, _ => 0

def swp : Ix D → Ix D
  | Sum.inl a => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inl a) => Sum.inl a
  | Sum.inr (Sum.inr t) => Sum.inr (Sum.inr t)

end Witt

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

variable (D : D7)

def WBlkExists : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L), Nonempty (WBlk A L Bu Pi Mu)

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

variable {D : D7}

variable (D)

end Formalism.L2.SG.Pf.Set3
