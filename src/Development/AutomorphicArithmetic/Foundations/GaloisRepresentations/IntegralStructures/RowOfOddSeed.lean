import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TLiftK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ToCoreK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.CoreAllOfRowStarCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.CongFinOddOfLvLac
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.InertCharpoly.GaloisLocalGlobalOfLocalGlobalCompatibility
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.LimFinOddOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightEmbeddingOverPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.GaloisCompatUnlinkedSupportOfSpherical
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedOfUnlinked

namespace UpperTheory.Gal.Int

open GlobalTheory.CongL

def recT : UpperTheory.GalStar.RecNotion := fun h rc => UpperTheory.Zero.LLC.IsRecT h rc

theorem coreAll_of (seed : SeedFinOdd) (cong : CongFinOdd) (up : UpperTheory.TP.TLiftK) : GlobalTheory.RoadU.CoreAll :=
  UpperTheory.Gal.Int.Inp.coreAll_of_core
    (UpperTheory.Gal.Int.Core.toCoreK up UpperTheory.Gal.ClosedPhiFromClosedTrace.congPhi_holds UpperTheory.Gal.Desc.descOffT (UpperTheory.Gal.Lim.limFinOdd_of seed cong))

theorem rest (h : GlobalTheory.RoadU.CoreAll) : UpperTheory.GalStar.Row0 recT :=
  UpperTheory.Gal.Int.Row.galoisLocalGlobal_of_localGlobalCompatibility h (UpperTheory.Gal.ToralGalois.galoisCompat_unlinkedSupport_of_spherical h) (UpperTheory.Gal.ToralGalois.R2.localGlobalCompatAtIwahoriFixed_of_unlinked (UpperTheory.Gal.ToralGalois.galoisCompat_unlinkedSupport_of_spherical h))

theorem galoisLocalGlobal_of_seed (seed : SeedFinOdd) (up : UpperTheory.TP.TLiftK := UpperTheory.TP.K.tLiftK) : UpperTheory.GalStar.Row0 recT :=
  rest (coreAll_of seed (UpperTheory.Gal.Int.Cong.congFinOdd_of_ex UpperTheory.Gal.Wt.wtLacEx_holds) up)

end UpperTheory.Gal.Int
