import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.WittLeviObjects
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

namespace Formalism.L2.S.S7.IwasawaBase

open MeasureTheory NumberField
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups

variable (I : AutInst)

theorem muA_right (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] : (I.muA μf).IsMulRightInvariant := by
  have : μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds I μf
  exact rr_muA_right I μf

end Formalism.L2.S.S7.IwasawaBase

end
