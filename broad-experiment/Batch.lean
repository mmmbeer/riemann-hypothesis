import Env
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockHomomorphism
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BorelApproximation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryOfGenerator
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplexNormedInstanceCompat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContDiffHerm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EMulSubMulCapelliMatrixPow
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqZeroOfForallIntegralCoeff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemBis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FgZ1T
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericMap
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HloweqTransfer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HolSubMul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraTer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreExtra
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestMore
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialFifth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionInvariants
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrMap
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeIffLtColH
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapPowSub
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemOfClosed
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulMemIntA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairCases
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PlaceRankTwoOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Qminor
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuantumMinorsCasimir
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RangeExtension
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RegularUnitPoints
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEquality
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SelectionLemmas
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareOfApproximation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StandardLattice
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnopSMul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZeroContDiffOnSupported
import Lemmata.CurryModusPonens.CurryMp
import Lemmata.GeneralBFactRightTerForm.Imports
import Lemmata.GeneralBFactThirdVersion.Imports
import Lemmata.PosDefOfRealQuadratic.QuadFormRealSmul

#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.IsSmooth
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.glCongr
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.aux3
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.aux4
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.blkHom
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.blkGL
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.blkAt
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.FixK
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.aux9
#compact_type UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK

#compact_type UpperTheory.Reformulated.B.BorelApproximation.aux4
#compact_type UpperTheory.Reformulated.B.BorelApproximation.aux6
#compact_type UpperTheory.Reformulated.B.BorelApproximation.aux7
#compact_type UpperTheory.Reformulated.B.BorelApproximation.aux8
#compact_type UpperTheory.Reformulated.B.BorelApproximation.parab
#compact_type UpperTheory.Reformulated.B.BorelApproximation.borel
#compact_type UpperTheory.Reformulated.B.BorelApproximation.iwahori
#compact_type UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported
#compact_type UpperTheory.Reformulated.B.BorelApproximation.iwGL
#compact_type UpperTheory.Reformulated.B.BorelApproximation.dcos_left

#compact_type UpperTheory.Reformulated.B.CoboundaryOfGenerator.cobOfGen

#compact_type UpperTheory.Reformulated.B.Re3.aux3
#compact_type UpperTheory.Reformulated.B.Re3.aux4
#compact_type UpperTheory.Reformulated.B.Re3.aux5
#compact_type UpperTheory.Reformulated.B.Re3.UJ
#compact_type UpperTheory.Reformulated.B.Re3.aux8
#compact_type UpperTheory.Reformulated.B.Re3.aux9
#compact_type UpperTheory.Reformulated.B.Re3.laurent_T_neg_one_mul_T_one
#compact_type UpperTheory.Reformulated.B.Re3.complex_normed_instance_compat
#compact_type UpperTheory.Reformulated.B.Re3.rregG
#compact_type UpperTheory.Reformulated.B.Re3.rreg
#compact_type UpperTheory.Reformulated.B.Re3.hloweq_transfer

#compact_type UpperTheory.Reformulated.B.Yzd4.aux2
#compact_type UpperTheory.Reformulated.B.Yzd4.aux3
#compact_type UpperTheory.Reformulated.B.Yzd4.aux4
#compact_type UpperTheory.Reformulated.B.Yzd4.UJ
#compact_type UpperTheory.Reformulated.B.Yzd4.aux6
#compact_type UpperTheory.Reformulated.B.Yzd4.aux7
#compact_type UpperTheory.Reformulated.B.Yzd4.sigR
#compact_type UpperTheory.Reformulated.B.Yzd4.aux9
#compact_type UpperTheory.Reformulated.B.Yzd4.laurent_T_neg_one_mul_T_one
#compact_type UpperTheory.Reformulated.B.Yzd4.aux11
#compact_type UpperTheory.Reformulated.B.Yzd4.aux12
#compact_type UpperTheory.Reformulated.B.Yzd4.inclR
#compact_type UpperTheory.Reformulated.B.Yzd4.JR
#compact_type UpperTheory.Reformulated.B.Yzd4.HR
#compact_type UpperTheory.Reformulated.B.Yzd4.HA
#compact_type UpperTheory.Reformulated.B.Yzd4.topTens
#compact_type UpperTheory.Reformulated.B.Yzd4.d18
#compact_type UpperTheory.Reformulated.B.Yzd4.blockM_one_partner_eq_one
#compact_type UpperTheory.Reformulated.B.Yzd4.blockM_mul_alt
#compact_type UpperTheory.Reformulated.B.Yzd4.conj_invariant_character_mem
#compact_type UpperTheory.Reformulated.B.Yzd4.lcsc_HA

#compact_type UpperTheory.Reformulated.B.Qj20.Hpk
#compact_type UpperTheory.Reformulated.B.Qj20.aux4
#compact_type UpperTheory.Reformulated.B.Qj20.eI
#compact_type UpperTheory.Reformulated.B.Qj20.xR

#compact_type UpperTheory.Reformulated.B.CovariantDegrees.jE
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.KwF
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.aux6
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.aux7
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.laurent_T_neg_one_mul_T_one
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.aux11
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.aux12
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.resQ
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.zero_contDiffOn_supported
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.resE
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.column_matrix_mul_inverse
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.complex_normed_instance_compat
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.padic_embedding_algebra_compat
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.blockM_one_partner_eq_one
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.blockM_mul_alt
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.conj_invariant_character_mem
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.rootGL_mem_unitary
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.conj_invariant_character_transport
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.rHom
#compact_type UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom

#compact_type UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow

#compact_type UpperTheory.Reformulated.B.Gwa7.aux3
#compact_type UpperTheory.Reformulated.B.Gwa7.aux4
#compact_type UpperTheory.Reformulated.B.Gwa7.aux5
#compact_type UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff

#compact_type UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem

#compact_type UpperTheory.Reformulated.B.Gub2.fg_Z1T

#compact_type UpperTheory.Reformulated.B.GenericMap.genPt
#compact_type UpperTheory.Reformulated.B.GenericMap.Cpt
#compact_type UpperTheory.Reformulated.B.GenericMap.aux4
#compact_type UpperTheory.Reformulated.B.GenericMap.genMap
#compact_type UpperTheory.Reformulated.B.GenericMap.regAt
#compact_type UpperTheory.Reformulated.B.GenericMap.unitAt
#compact_type UpperTheory.Reformulated.B.GenericMap.InFibre
#compact_type UpperTheory.Reformulated.B.GenericMap.Char0
#compact_type UpperTheory.Reformulated.B.GenericMap.main

#compact_type UpperTheory.Reformulated.B.Re4.aux3
#compact_type UpperTheory.Reformulated.B.Re4.aux4
#compact_type UpperTheory.Reformulated.B.Re4.aux5
#compact_type UpperTheory.Reformulated.B.Re4.UJ
#compact_type UpperTheory.Reformulated.B.Re4.aux8
#compact_type UpperTheory.Reformulated.B.Re4.aux9
#compact_type UpperTheory.Reformulated.B.Re4.laurent_T_neg_one_mul_T_one
#compact_type UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat
#compact_type UpperTheory.Reformulated.B.Re4.rregG
#compact_type UpperTheory.Reformulated.B.Re4.rreg
#compact_type UpperTheory.Reformulated.B.Re4.hloweq_transfer

#compact_type UpperTheory.Reformulated.B.Qe28.IsHolCusp
#compact_type UpperTheory.Reformulated.B.Qe28.holSub
#compact_type UpperTheory.Reformulated.B.Qe28.holSub_mul

#compact_type UpperTheory.Reformulated.B.Ue16.exists_smul_mem

#compact_type UpperTheory.Reformulated.B.Qh15.aux2
#compact_type UpperTheory.Reformulated.B.Qh15.aux3
#compact_type UpperTheory.Reformulated.B.Qh15.chRep
#compact_type UpperTheory.Reformulated.B.Qh15.act_mul

#compact_type UpperTheory.Reformulated.B.Yha7.main

#compact_type UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux2
#compact_type UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.aux4

#compact_type UpperTheory.Reformulated.B.InvolutionInvariants.aux3
#compact_type UpperTheory.Reformulated.B.InvolutionInvariants.aux4
#compact_type UpperTheory.Reformulated.B.InvolutionInvariants.aux5
#compact_type UpperTheory.Reformulated.B.InvolutionInvariants.UJ
#compact_type UpperTheory.Reformulated.B.InvolutionInvariants.aux8
#compact_type UpperTheory.Reformulated.B.InvolutionInvariants.aux9
#compact_type UpperTheory.Reformulated.B.InvolutionInvariants.laurent_T_neg_one_mul_T_one

#compact_type UpperTheory.Reformulated.B.Qi38.Irr
#compact_type UpperTheory.Reformulated.B.Qi38.mapRep
#compact_type UpperTheory.Reformulated.B.Qi38.irr_map

#compact_type UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH

#compact_type UpperTheory.Reformulated.B.MapPowSub.map_pow_sub

#compact_type UpperTheory.Reformulated.B.Qi13.aux1
#compact_type UpperTheory.Reformulated.B.Qi13.aux4
#compact_type UpperTheory.Reformulated.B.Qi13.aux6
#compact_type UpperTheory.Reformulated.B.Qi13.bb
#compact_type UpperTheory.Reformulated.B.Qi13.aux8
#compact_type UpperTheory.Reformulated.B.Qi13.blift
#compact_type UpperTheory.Reformulated.B.Qi13.linIndep

#compact_type UpperTheory.Reformulated.B.Uc13.aux3
#compact_type UpperTheory.Reformulated.B.Uc13.aux4
#compact_type UpperTheory.Reformulated.B.Uc13.evalV
#compact_type UpperTheory.Reformulated.B.Uc13.intA
#compact_type UpperTheory.Reformulated.B.Uc13.mul_mem_intA

#compact_type UpperTheory.Reformulated.B.Qk34.norm_le_sum

#compact_type UpperTheory.Reformulated.B.PairCases.pair_cases

#compact_type UpperTheory.Reformulated.B.Qf14.phi_mul

#compact_type UpperTheory.Reformulated.B.placeRankTwoOne.aux3
#compact_type UpperTheory.Reformulated.B.placeRankTwoOne.aux4
#compact_type UpperTheory.Reformulated.B.placeRankTwoOne.aux5
#compact_type UpperTheory.Reformulated.B.placeRankTwoOne.UJ
#compact_type UpperTheory.Reformulated.B.placeRankTwoOne.aux8
#compact_type UpperTheory.Reformulated.B.placeRankTwoOne.aux9
#compact_type UpperTheory.Reformulated.B.placeRankTwoOne.laurent_T_neg_one_mul_T_one

#compact_type UpperTheory.Reformulated.B.Qf10.casimir

#compact_type UpperTheory.Reformulated.B.QuantumMinorsCasimir.casimir

#compact_type UpperTheory.Reformulated.B.RangeExtension.mem_range

#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.genPt
#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.Cpt
#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.aux4
#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.genMap
#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.regAt
#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.unitAt
#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.InFibre
#compact_type UpperTheory.Reformulated.B.RegularUnitPoints.main

#compact_type UpperTheory.Reformulated.B.RootEquality.LC
#compact_type UpperTheory.Reformulated.B.RootEquality.aux5
#compact_type UpperTheory.Reformulated.B.RootEquality.aux6
#compact_type UpperTheory.Reformulated.B.RootEquality.aux7
#compact_type UpperTheory.Reformulated.B.RootEquality.Zl
#compact_type UpperTheory.Reformulated.B.RootEquality.unrBare

#compact_type UpperTheory.Reformulated.B.SelectionLemmas.aux6
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.aux7
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.aux8
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.hform
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.IsLocBasis
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.complex_normed_instance_compat
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.padic_embedding_algebra_compat
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.matLat
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.gramR
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.quotGram
#compact_type UpperTheory.Reformulated.B.SelectionLemmas.main

#compact_type UpperTheory.Reformulated.B.SquareOfApproximation.IsCMExt
#compact_type UpperTheory.Reformulated.B.SquareOfApproximation.aux2
#compact_type UpperTheory.Reformulated.B.SquareOfApproximation.IsSplit
#compact_type UpperTheory.Reformulated.B.SquareOfApproximation.main

#compact_type UpperTheory.Reformulated.B.StandardLattice.aux5
#compact_type UpperTheory.Reformulated.B.StandardLattice.aux6
#compact_type UpperTheory.Reformulated.B.StandardLattice.rlToK
#compact_type UpperTheory.Reformulated.B.StandardLattice.atL
#compact_type UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff

#compact_type UpperTheory.Reformulated.B.Qk3.unopS
#compact_type UpperTheory.Reformulated.B.Qk3.unopS_mul

#compact_type UpperTheory.Reformulated.B.H23.aux4
#compact_type UpperTheory.Reformulated.B.H23.aux6
#compact_type UpperTheory.Reformulated.B.H23.aux7
#compact_type UpperTheory.Reformulated.B.H23.aux8
#compact_type UpperTheory.Reformulated.B.H23.parab
#compact_type UpperTheory.Reformulated.B.H23.borel
#compact_type UpperTheory.Reformulated.B.H23.iwahori
#compact_type UpperTheory.Reformulated.B.H23.zero_contDiffOn_supported
#compact_type UpperTheory.Reformulated.B.H23.iwGL
#compact_type UpperTheory.Reformulated.B.H23.dcos_right

#compact_type goal1

#compact_type goal1

#compact_type goal1

#compact_type goal1
