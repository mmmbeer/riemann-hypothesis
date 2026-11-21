import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HcfjHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTateFE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinOutOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoceulerHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocfinHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeLAdicCharacterAboveOfPublished
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOrthogonalityHolds
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.DefiniteNHolds
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.ModularityOfHyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTemp
import Development.AutomorphicArithmetic.ThetaCorrespondence.GaloisRepresentations.BlochKatoLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.GaloisRepresentations.GreenbergWiles
import Development.AutomorphicArithmetic.ThetaCorrespondence.GaloisRepresentations.HeckeDeRham
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLiftHypothesesOfNonvanishing
import Development.DiscreteGroups.GlobalIrreducibility.LConvFinal
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesAut
import Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.DeligneRibetHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.WeilBound.CoreStatements.PublishedTheorems.ClozelPurity.Bridge
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GlobalEulerCharOfLemmaX
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.GlobalFiniteness
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.PoitouTateNormalisedHolds
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
import Development.WeilBound.CoreStatements.TotallyDisjointProducts.SLGLProductIrreducibility.TdpFill
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomological
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteOfCuspOfConstTerm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll

set_option synthInstance.maxHeartbeats 200000

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where
  caraianiLocalGlobalDual : _root_.UpperTheory.One.M.Row
  localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists
  galoisRepOfPolarizedPairLit : _root_.UpperTheory.One.M.Row

theorem UpperTheory.LiteratureTheorems.ellipticMainTheoremCM' (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.EllipticMainTheoremCM :=
  PositivityTheory.Prw.ellipticMainTheoremCM_holds

theorem UpperTheory.LiteratureTheorems.heckeTateFunctionalEquation' (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.HeckeTateFunctionalEquation :=
  GlobalTheory.Top.heckeTateFE

theorem UpperTheory.LiteratureTheorems.hilbertClassFieldJ' (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.HilbertClassFieldJ :=
  GlobalTheory.Laid.hcfj_holds

theorem UpperTheory.LiteratureTheorems.partial_zeta_functional_equation_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.PartialZetaFunctionalEquation :=
  PositivityTheory.Prw.partialZetaFunctionalEquation_holds

theorem UpperTheory.LiteratureTheorems.deligne_ribet_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.DeligneRibet :=
  PositivityTheory.PfDR.deligneRibet_holds

theorem UpperTheory.LiteratureTheorems.siegel_klingen_deligne_ribet_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  PositivityTheory.Prw.siegelKlingenDeligneRibet_of PositivityTheory.Prw.siegelKlingen_holds (_root_.UpperTheory.LiteratureTheorems.deligne_ribet_of_literature O)

theorem UpperTheory.LiteratureTheorems.join_out_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Mem.LiteralAutomorphy.JoinOut :=
  GlobalTheory.JoinFun.joinOut_of_five (_root_.UpperTheory.LiteratureTheorems.ellipticMainTheoremCM' O) (_root_.UpperTheory.LiteratureTheorems.hilbertClassFieldJ' O) (_root_.UpperTheory.LiteratureTheorems.siegel_klingen_deligne_ribet_of_literature O) (_root_.UpperTheory.LiteratureTheorems.partial_zeta_functional_equation_of_literature O) (_root_.UpperTheory.LiteratureTheorems.heckeTateFunctionalEquation' O)

theorem UpperTheory.LiteratureTheorems.abelian_de_rham_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.AbelianDeRham :=
  GlobalTheory.abelianDeRham

theorem UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.DeRhamPotSemistable :=
  GlobalTheory.deRham_potentiallySemistable

theorem UpperTheory.LiteratureTheorems.global_artin_reciprocity_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.GlobalArtinReciprocity :=
  GlobalTheory.globalArtinReciprocity_holds

theorem UpperTheory.LiteratureTheorems.hecke_l_adic_character_de_rham_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.HeckeLAdicCharacterDeRham :=
  UpperTheory.Lit.heckeLAdicCharacterDeRham

theorem UpperTheory.LiteratureTheorems.algebraic_character_wd_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.AlgebraicCharacterWD :=
  UpperTheory.Lit.CharWD.algebraicCharacterWD (_root_.UpperTheory.LiteratureTheorems.global_artin_reciprocity_of_literature O) (_root_.UpperTheory.LiteratureTheorems.hecke_l_adic_character_de_rham_of_literature O) (_root_.UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_literature O)

theorem UpperTheory.LiteratureTheorems.automorphic_forms_finite_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.AutomorphicFormsFiniteGL :=
  CuspFormAutomorphicBounds.automorphicFormsFiniteGL

theorem UpperTheory.LiteratureTheorems.base_change_isobaric (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.BaseChangeIsobaricTransfer :=
  UpperTheory.BaseChangeIdentities.baseChangeN

theorem UpperTheory.LiteratureTheorems.bernstein_unitary_product_irreducible_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.BernsteinUnitaryProductIrreducible :=
  PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible

theorem UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds

theorem UpperTheory.LiteratureTheorems.bloch_kato_local_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.BlochKatoLocal :=
  UpperTheory.Lit.blochKatoLocal

theorem UpperTheory.LiteratureTheorems.brauer_degree_zero_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.BrauerDegreeZero :=
  (GlobalTheory.BrauerZero.brauerDegreeZero )

theorem UpperTheory.LiteratureTheorems.ess_square_integrable_segments_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  PositivityTheory.Exh.essSquareIntegrableSegments_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem UpperTheory.LiteratureTheorems.local_converse_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.LocalConverseGL :=
  DiscreteGroups.sglob.LConv.localConverseGL

theorem UpperTheory.LiteratureTheorems.local_langlands_recT_exists_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : _root_.UpperTheory.Zero.LLC.RecTExists :=
  O.localLanglandsExists

theorem UpperTheory.LiteratureTheorems.pair_u_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : _root_.UpperTheory.GalS.PairUAlt :=
  _root_.UpperTheory.GalS.field_of_starFull_alt (_root_.UpperTheory.LiteratureTheorems.local_langlands_recT_exists_of_literature O) (_root_.UpperTheory.LiteratureTheorems.local_converse_gl_of_literature O) (PositivityTheory.Exh.langlandsExhaustionGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)) O.galoisRepOfPolarizedPairLit

theorem UpperTheory.LiteratureTheorems.cusp_forms_bounded_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.CuspFormsBoundedGL :=
  RfCs.cuspidalSpectrumGL.2.2

theorem UpperTheory.LiteratureTheorems.jacquet_shalika_rigidity_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.JacquetShalikaRigidity :=
  PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity

theorem UpperTheory.LiteratureTheorems.gelfand_kazhdan_dual_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.GelfandKazhdanDual :=
  PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity (_root_.UpperTheory.LiteratureTheorems.jacquet_shalika_rigidity_of_literature O) (_root_.UpperTheory.LiteratureTheorems.cusp_forms_bounded_gl_of_literature O)

theorem UpperTheory.LiteratureTheorems.generic_unlinked_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 (PositivityTheory.RgGu.segmentRepresentation)

theorem UpperTheory.LiteratureTheorems.chevalley_units_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.ChevalleyUnits :=
  (GlobalTheory.Published.chevalleyUnits' )

theorem UpperTheory.LiteratureTheorems.geometric_restriction_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.CompanionTheory.GeoLink.geometricLemma

theorem UpperTheory.LiteratureTheorems.grothendieck_ring_polynomial_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  PositivityTheory.Groth.grothendieckRingPolynomial_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem UpperTheory.LiteratureTheorems.segment_representation_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.SegmentRepresentation :=
  PositivityTheory.RgGu.segmentRepresentation

theorem UpperTheory.LiteratureTheorems.zelevinsky_polynomial_ring_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds (_root_.UpperTheory.LiteratureTheorems.segment_representation_of_literature O) (_root_.UpperTheory.LiteratureTheorems.grothendieck_ring_polynomial_of_literature O)

theorem UpperTheory.LiteratureTheorems.depth_zero_induction_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.DepthZeroInduction :=
  (GlobalTheory.DepthZeroPass.depthZeroInduction (_root_.UpperTheory.LiteratureTheorems.geometric_restriction_of_literature O) (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_literature O) (_root_.UpperTheory.LiteratureTheorems.zelevinsky_polynomial_ring_of_literature O))

theorem UpperTheory.LiteratureTheorems.langlands_exhaustion_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.LanglandsExhaustionGL :=
  PositivityTheory.Exh.langlandsExhaustionGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem UpperTheory.LiteratureTheorems.langlands_multisegments_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.LanglandsMultisegments :=
  PositivityTheory.Exh.langlandsMultisegments_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem UpperTheory.LiteratureTheorems.standard_cosocle_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.StandardCosocleGL :=
  PositivityTheory.Exh.standardCosocleGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : _root_.UpperTheory.Zero.LLC.RecTExists :=
  O.localLanglandsExists

theorem UpperTheory.LiteratureTheorems.irreducible_admissible_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top

theorem UpperTheory.LiteratureTheorems.standard_functors_finite_length_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.StandardFunctorsFiniteLength :=
  PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top

theorem UpperTheory.LiteratureTheorems.tempered_product_of_square_integrable_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.TemperedProductOfSquareIntegrable :=
  UpperTheory.Lit.Cas.temperedProduct (_root_.UpperTheory.LiteratureTheorems.geometric_restriction_of_literature O) (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_literature O) (_root_.UpperTheory.LiteratureTheorems.irreducible_admissible_gl_of_literature O) (_root_.UpperTheory.LiteratureTheorems.standard_functors_finite_length_of_literature O) (_root_.UpperTheory.LiteratureTheorems.langlands_exhaustion_gl_of_literature O) (_root_.UpperTheory.LiteratureTheorems.standard_cosocle_gl_of_literature O) (_root_.UpperTheory.LiteratureTheorems.langlands_multisegments_of_literature O) (_root_.UpperTheory.LiteratureTheorems.ess_square_integrable_segments_of_literature O)

theorem UpperTheory.LiteratureTheorems.clozel_cohomological_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.ClozelCohomological :=
  PositivityTheory.Rg.Cz.clozelCohomological

theorem UpperTheory.LiteratureTheorems.clozel_purity_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.ClozelPurity :=
  PositivityTheory.Lit1.ClozelPurity.clozelPurity

theorem UpperTheory.LiteratureTheorems.cusp_rapid_decay_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.CuspRapidDecay :=
  (GlobalTheory.RapidDecay.cuspRapidDecay )

theorem UpperTheory.LiteratureTheorems.cuspidal_spectrum_gl_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.CuspidalSpectrumGL :=
  RfCs.cuspidalSpectrumGL

theorem UpperTheory.LiteratureTheorems.green_regular_characters_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.GreenRegularCharacters :=
  PositivityTheory.Stage1.PM.greenRegularCharacters

theorem UpperTheory.LiteratureTheorems.abelian_lifting_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.AbelianLifting :=
  GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers

theorem UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.GrothendieckDeformation :=
  GlobalTheory.Published.grothendieckDeformation_of_lifting (_root_.UpperTheory.LiteratureTheorems.abelian_de_rham_of_literature O) (_root_.UpperTheory.LiteratureTheorems.abelian_lifting_of_literature O)

theorem UpperTheory.LiteratureTheorems.harish_chandra_finite_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.HarishChandraFinite :=
  PositivityTheory.RgHf.harishChandraFinite

theorem UpperTheory.LiteratureTheorems.hecke_l_adic_character_crystalline_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.HeckeLAdicCharacterCrystalline :=
  GlobalTheory.Published.CharCrysModel.of_three (_root_.UpperTheory.LiteratureTheorems.hecke_l_adic_character_de_rham_of_literature O) (_root_.UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_literature O) (_root_.UpperTheory.LiteratureTheorems.algebraic_character_wd_of_literature O)

theorem UpperTheory.LiteratureTheorems.hecke_l_adic_character_above_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.HeckeLAdicCharacterAbove :=
  GlobalTheory.HeckeAboveBridge.heckeLAdicCharacterAbove_of_potSemistable (_root_.UpperTheory.LiteratureTheorems.hecke_l_adic_character_de_rham_of_literature O) (_root_.UpperTheory.LiteratureTheorems.hecke_l_adic_character_crystalline_of_literature O) (_root_.UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_literature O)

theorem UpperTheory.LiteratureTheorems.jacquet_shalika_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.JacquetShalika :=
  PositivityTheory.AdelicQuotientData.jacquetShalika

theorem UpperTheory.LiteratureTheorems.moy_prasad_jacquet_iso_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.MoyPrasadJacquetIso :=
  PositivityTheory.Prw.moyPrasadJacquetIso_holds

theorem UpperTheory.LiteratureTheorems.poitou_tate_normalised_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.PoitouTateNormalised :=
  PositivityTheory.Lit1.PTN.poitouTateNormalised_holds

theorem UpperTheory.LiteratureTheorems.ray_class_field_st_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.RayClassFieldSt :=
  PositivityTheory.Stage1.PM.rayClassFieldSt

theorem UpperTheory.LiteratureTheorems.square_integrable_segment_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.SquareIntegrableSegment :=
  PositivityTheory.Prw.squareIntegrableSegment_of (_root_.UpperTheory.LiteratureTheorems.ess_square_integrable_segments_of_literature O)

theorem UpperTheory.LiteratureTheorems.totally_disjoint_product_irreducible_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  PositivityTheory.SlGl.totallyDisjointProductIrreducible_of_parts (GlobalTheory.geometricLemma_of_filtration PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.Geo.geometricLemmaFiltration) (PositivityTheory.RgGu.segmentRepresentation) (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg (PositivityTheory.RgGu.segmentRepresentation))

theorem UpperTheory.LiteratureTheorems.dual_abelian_scheme_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.DualAbelianScheme :=
  GlobalTheory.dualAbelianScheme

theorem UpperTheory.LiteratureTheorems.global_euler_char_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : ReciprocityTheory.Gal.GlobalEulerChar :=
  PositivityTheory.Lit1.GEN.globalEulerChar_full

theorem UpperTheory.LiteratureTheorems.global_finiteness_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : ReciprocityTheory.Gal.GlobalFiniteness :=
  PositivityTheory.Lit1.GF.globalFiniteness

theorem UpperTheory.LiteratureTheorems.localEulerChar_alt_alt (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : ReciprocityTheory.Gal.LocalEulerChar :=
  GlobalTheory.Laid.loceuler_holds

theorem UpperTheory.LiteratureTheorems.local_finiteness_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : ReciprocityTheory.Gal.LocalFiniteness :=
  GlobalTheory.Laid.locfin_holds

theorem UpperTheory.LiteratureTheorems.local_tate_duality_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : ReciprocityTheory.Gal.LocalTateDuality :=
  GlobalTheory.LocalDualityAll.localTateDuality

theorem UpperTheory.LiteratureTheorems.greenberg_wiles_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : ReciprocityTheory.Gal.GreenbergWiles :=
  UpperTheory.Lit.greenbergWiles (_root_.UpperTheory.LiteratureTheorems.poitou_tate_normalised_of_literature O) (_root_.UpperTheory.LiteratureTheorems.global_euler_char_of_literature O) (_root_.UpperTheory.LiteratureTheorems.local_tate_duality_of_literature O) (_root_.UpperTheory.LiteratureTheorems.localEulerChar_alt_alt O) (_root_.UpperTheory.LiteratureTheorems.local_finiteness_of_literature O)

theorem UpperTheory.LiteratureTheorems.unramified_orthogonality_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  GlobalTheory.unramifiedOrthogonality_holds

theorem UpperTheory.LiteratureTheorems.local_euler_char_k_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : Formalism.GaloisCohomology.LocalEulerCharK :=
  CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler

theorem UpperTheory.LiteratureTheorems.local_finiteness_k_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : Formalism.GaloisCohomology.LocalFinitenessK :=
  CompanionTheory.LocalTateOrthogonality.Gcoh.top_locfin

theorem UpperTheory.LiteratureTheorems.local_tate_duality_k_of_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : Formalism.GaloisCohomology.LocalTateDualityK :=
  CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate

theorem UpperTheory.LiteratureTheorems.literature_local (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt where
  bz := (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_literature O)
  bern := (_root_.UpperTheory.LiteratureTheorems.bernstein_unitary_product_irreducible_of_literature O)
  geo := (_root_.UpperTheory.LiteratureTheorems.geometric_restriction_of_literature O)
  zel := (_root_.UpperTheory.LiteratureTheorems.zelevinsky_polynomial_ring_of_literature O)
  disj := (_root_.UpperTheory.LiteratureTheorems.totally_disjoint_product_irreducible_of_literature O)
  mp := (_root_.UpperTheory.LiteratureTheorems.moy_prasad_jacquet_iso_of_literature O)
  temp := (_root_.UpperTheory.LiteratureTheorems.tempered_product_of_square_integrable_of_literature O)
  seg := (_root_.UpperTheory.LiteratureTheorems.ess_square_integrable_segments_of_literature O)
  sq := (_root_.UpperTheory.LiteratureTheorems.square_integrable_segment_of_literature O)
  gen := (_root_.UpperTheory.LiteratureTheorems.generic_unlinked_gl_of_literature O)
  multi := (_root_.UpperTheory.LiteratureTheorems.langlands_multisegments_of_literature O)
  exh := (_root_.UpperTheory.LiteratureTheorems.langlands_exhaustion_gl_of_literature O)
  cos := (_root_.UpperTheory.LiteratureTheorems.standard_cosocle_gl_of_literature O)
  llc := (_root_.UpperTheory.LiteratureTheorems.local_langlands_recT_exists_of_literature O)
  conv := (_root_.UpperTheory.LiteratureTheorems.local_converse_gl_of_literature O)
  dzi := (_root_.UpperTheory.LiteratureTheorems.depth_zero_induction_of_literature O)
  brauer := (_root_.UpperTheory.LiteratureTheorems.brauer_degree_zero_of_literature O)
  chev := (_root_.UpperTheory.LiteratureTheorems.chevalley_units_of_literature O)
  green := (_root_.UpperTheory.LiteratureTheorems.green_regular_characters_of_literature O)

theorem UpperTheory.LiteratureTheorems.literature_automorphy (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' where
  decay := (_root_.UpperTheory.LiteratureTheorems.cusp_rapid_decay_of_literature O)
  hc := (_root_.UpperTheory.LiteratureTheorems.harish_chandra_finite_of_literature O)
  fin := (_root_.UpperTheory.LiteratureTheorems.automorphic_forms_finite_gl_of_literature O)
  js := (_root_.UpperTheory.LiteratureTheorems.jacquet_shalika_of_literature O)
  cusp := (_root_.UpperTheory.LiteratureTheorems.cuspidal_spectrum_gl_of_literature O)
  bc := (_root_.UpperTheory.LiteratureTheorems.base_change_isobaric O)
  gk := (_root_.UpperTheory.LiteratureTheorems.gelfand_kazhdan_dual_of_literature O)
  gal := (_root_.UpperTheory.LiteratureTheorems.pair_u_of_literature O)
  car := O.caraianiLocalGlobalDual
  pur := (_root_.UpperTheory.LiteratureTheorems.clozel_purity_of_literature O)
  coh := (_root_.UpperTheory.LiteratureTheorems.clozel_cohomological_of_literature O)
  art := (_root_.UpperTheory.LiteratureTheorems.global_artin_reciprocity_of_literature O)
  ray := (_root_.UpperTheory.LiteratureTheorems.ray_class_field_st_of_literature O)
  chA := (_root_.UpperTheory.LiteratureTheorems.hecke_l_adic_character_above_of_literature O)
  chW := (_root_.UpperTheory.LiteratureTheorems.algebraic_character_wd_of_literature O)
  berger := (_root_.UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_literature O)

theorem UpperTheory.LiteratureTheorems.literature_cohomology (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Mem.LiteralAutomorphy.LitCoh where
  pt := (_root_.UpperTheory.LiteratureTheorems.poitou_tate_normalised_of_literature O)
  lf := (_root_.UpperTheory.LiteratureTheorems.local_finiteness_of_literature O)
  lt := (_root_.UpperTheory.LiteratureTheorems.local_tate_duality_of_literature O)
  le := (_root_.UpperTheory.LiteratureTheorems.localEulerChar_alt_alt O)
  gf := (_root_.UpperTheory.LiteratureTheorems.global_finiteness_of_literature O)
  ge := (_root_.UpperTheory.LiteratureTheorems.global_euler_char_of_literature O)
  uo := (_root_.UpperTheory.LiteratureTheorems.unramified_orthogonality_of_literature O)
  gw := (_root_.UpperTheory.LiteratureTheorems.greenberg_wiles_of_literature O)
  lfK := (_root_.UpperTheory.LiteratureTheorems.local_finiteness_k_of_literature O)
  ltK := (_root_.UpperTheory.LiteratureTheorems.local_tate_duality_k_of_literature O)
  leK := (_root_.UpperTheory.LiteratureTheorems.local_euler_char_k_of_literature O)
  bk := (_root_.UpperTheory.LiteratureTheorems.bloch_kato_local_of_literature O)

theorem UpperTheory.LiteratureTheorems.literature_nonexistence (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt where
  loc := (_root_.UpperTheory.LiteratureTheorems.literature_local O)
  aut := (_root_.UpperTheory.LiteratureTheorems.literature_automorphy O)
  coh := (_root_.UpperTheory.LiteratureTheorems.literature_cohomology O)
  join := (_root_.UpperTheory.LiteratureTheorems.join_out_of_literature O)
  fe := (_root_.UpperTheory.LiteratureTheorems.heckeTateFunctionalEquation' O)
