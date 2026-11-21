import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GlobalModelExists
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeft
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PartIHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliSchemesExist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.NotIsGlobalPrimePow
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem prov_an : Prov.An :=
  ⟨GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds, GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds,
    GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_provision_holds : Prov.An := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Link.prov_an
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem levelMaps_heckePoints_of_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
      1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun E _ _ _ H D h => GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H D h

end GlobalTheory.CompanionTheory.Ar.Top
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem modelClause_of_rankZero
    (hz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
      D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D)) :
    PartI ∧ N1ab ∧ N1c ∧
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D) := by
  refine ⟨partI_holds, moduli_schemes_exist, complex_uniformisation_holds, ?_⟩
  intro E _ _ _ H D
  by_cases h : D.p + D.q = 0
  · exact hz E H D h
  · exact levelMaps_heckePoints_of_pos E H D (by omega)

end GlobalTheory.CompanionTheory.Ar.Top
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LevelZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem zeta_mul_pow {a c : ℕ} (ha : 0 < a) (hc : 0 < c) : zeta (a * c) ^ c = zeta a := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · obtain ⟨c, hc⟩ := h
    have hc0 : 0 < c := Nat.pos_of_ne_zero fun h0 => l₂.A_pos.ne' (by rw [hc, h0, mul_zero])
    rw [← zeta_mul_pow l.A_pos hc0, ← hc]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

def simOne (hD : D.p + D.q = 0) : Sim D :=
  have := subsingleton_La hD
  { f := fun _ => LinearMap.id
    ν := fun _ => 1
    tower := fun _ _ _ _ _ => ⟨0, Subsingleton.elim _ _⟩
    inv := fun _ _ => ⟨LinearMap.id, fun _ => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
    mult := fun _ _ a b => by
      rw [Subsingleton.elim b 0]
      simp }

theorem simOne_inGam (hD : D.p + D.q = 0) (l l₂ : Level H) : (simOne hD).InGam l l₂ := by
  have := subsingleton_La hD
  refine ⟨by simp [simOne], fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim ((simOne hD).f l.M a - a) 0]
  exact zero_mem _

theorem trivAt (hD : D.p + D.q = 0) (g : Sim D) (l₂ : Level H) : g.TrivAt l₂ := by
  have := subsingleton_La hD
  refine ⟨fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim (g.f l₂.M a - a) 0]
  exact zero_mem _

theorem isIso_spMap_inclusion {F F' : IntermediateField ℚ ℂ} (h : F = F') :
    IsIso (spMap (IntermediateField.inclusion h.le).toRingHom) := by
  subst h
  have : (IntermediateField.inclusion (le_refl F)).toRingHom = RingHom.id F := RingHom.ext fun _ => rfl
  rw [this]
  have e : spMap (RingHom.id F) = 𝟙 _ := Spec.map_id _
  rw [e]
  infer_instance

def jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l →+* KA l₂ := (IntermediateField.inclusion (KA_le h)).toRingHom

theorem coe_jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) (x : KA l) : ((jKA h x : KA l₂) : ℂ) = ((x : KA l) : ℂ) :=
  IntermediateField.coe_inclusion (KA_le h) x

theorem spMap_square {l l₂ : Level H} (h : l.A ∣ l₂.A) (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) :
    spMap (IntermediateField.inclusion c₂.le).toRingHom ≫ spMap (jKA h) =
      spMap (IntermediateField.inclusion hc.le).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [RankZero.spMap_comp, RankZero.spMap_comp]
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext rfl)

theorem exists_isIso_rF {l l₂ : Level H} (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hs : IsIso Xo.s) (hs₂ : IsIso Xo₂.s)
    (h : l.A ∣ l₂.A) (r : Xo₂.X ⟶ Xo.X) (hr : r ≫ Xo.s = Xo₂.s ≫ spMap (jKA h)) (c : Coeff l) (c₂ : Coeff l₂)
    (hc : c.F = c₂.F) : ∃ rF : Xo₂.XF c₂ ⟶ Xo.XF c,
      rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r ∧
      rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom ∧ IsIso rF := by
  have hw : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_square h c c₂ hc, Category.assoc]
  have h₂ := pullback.lift_snd _ _ hw
  have := isIso_spMap_inclusion hc
  exact ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ hw, h₂, IsIso.of_isIso_fac_right h₂⟩

theorem lev_rank_zero (hD : D.p + D.q = 0) : ToroidalLevelCompatibility (H := H) (D := D) := by
  intro l l₂ Xo Xo₂ hd
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs₂, hG₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂
  obtain ⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (jKA hd.2.2) :=
    ⟨Xo₂.s ≫ spMap (jKA hd.2.2) ≫ inv Xo.s, by simp⟩
  obtain ⟨m⟩ := nonempty_sabMap hG₂ hG r
  obtain ⟨ν⟩ := nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom
  have hlev : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _) := fun g =>
    ⟨Category.id_comp _, ν, fun a => sec_comm hG₂ ν.cart.1.w _ _, fun a => sec_comm hG₂ ν.cart.1.w _ _⟩
  refine ⟨r, jKA hd.2.2, m, coe_jKA _, hr, fun a => sec_comm hG m.cart.1.w _ _, fun a => sec_comm hG m.cart.1.w _ _,
    fun g _ => ⟨Iso.refl _, hlev g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩
  obtain ⟨rF, h₁, h₂, hF⟩ := exists_isIso_rF Xo Xo₂ hs hs₂ hd.2.2 r hr c c₂ hc
  refine ⟨rF, h₁, h₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ?_⟩
  obtain rfl : y = y' := (cancel_mono rF).1 h
  exact ⟨⟨simOne hD, Iso.refl _, simOne_inGam hD l l₂, hlev _, Category.id_comp _,
    by simp only [Iso.refl_hom, Category.comp_id]⟩, fun g _ _ _ _ => trivAt hD g l₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun _ _ _ _ _ _ hD => ⟨lev_rank_zero hD, GoodModel.hecke_rank_zero hD⟩

end GlobalTheory.CompanionTheory.Ar.Top.LevelZero

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_and_hecke_of_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem modelClause_holds :
    PartI ∧ N1ab ∧ N1c ∧
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D) :=
  modelClause_of_rankZero GlobalTheory.T.level_and_hecke_of_zero_signature

end GlobalTheory.CompanionTheory.Ar.Top
end
