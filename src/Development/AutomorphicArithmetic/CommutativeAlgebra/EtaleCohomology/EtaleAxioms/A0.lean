import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCoverStatement
import Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
import Development.EtaleCohomology.EtaleSheaves.LeafChernPf
import Development.EtaleCohomology.EtaleSheaves.LeafNatPf
import Development.EtaleCohomology.EtaleSheaves.UnimodularBlockEqToHomValEqOne
import Development.EtaleCohomology.EtaleSheaves.LeafMapWPf
import Development.EtaleCohomology.EtaleSheaves.LeafCover2Of
import Development.EtaleCohomology.EtaleSheaves.LeafWhitneyPf
import Development.EtaleCohomology.EtaleSheaves.LeafLinePf
import Development.EtaleCohomology.EtaleSheaves.LeafNewtonPf

namespace UpperTheory.Et.D2

open LateralTheory.E

theorem a0 : EtaleChapterDTwo := by
  have naturality := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  exact D2.goal_of
    (D2.LeafRing_of naturality GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold)
    D2.LeafChern_of (D2.LeafNat_of naturality)
    (D2.LeafWhitney_of
      (LeafGeomPfLoc.LeafGeom_of LeafHalf1Pf.LeafHalf1_of
        (HalfDegreeVanishing.LeafHalf2_of LeafMapWPf.LeafMapW_of))
      LeafCover2Pf.LeafCover2_of GlobalTheory.T.cup_vanishes_on_two_member_cover naturality)
    (D2.LeafLine_of naturality) LeafNewtonPf.LeafNewton_of

theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDTwo := a0

end UpperTheory.Et.D2
