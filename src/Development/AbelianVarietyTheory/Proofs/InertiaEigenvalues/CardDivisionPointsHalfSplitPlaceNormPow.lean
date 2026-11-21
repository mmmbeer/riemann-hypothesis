import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.EigenSplitStrings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeHermitianPairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementSecondPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricFunctionInverseInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetRowOfGaloisRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPolyOfRecTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicRepIsobaricDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelAdaptedCharAbs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtString

open GlobalTheory.SphPar GlobalTheory.SphGal GlobalTheory.Hk3 GlobalTheory.CuspRep GlobalTheory.IndefiniteRowSideFullHecke.EigenSplitStrings Formalism.UG Polynomial
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {D : D7}

theorem isSplit_iff_conj (P : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  rw [GlobalTheory.LFun.isSplit_iff, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  constructor
  · rintro ⟨w, w', hne, h, h'⟩ e
    have e' : Formalism.DivisionValues.conjPl P = P := HeightOneSpectrum.ext e
    have a := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have b := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h'
    rw [e', or_self] at a b
    exact hne (a.trans b.symm)
  · intro h
    exact ⟨P, Formalism.DivisionValues.conjPl P, fun e => h (congrArg HeightOneSpectrum.asIdeal e).symm, rfl,
      (GlobalTheory.LevelPlaces.under_eq_of_isConjPl (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)).symm⟩

section Sizes

variable {c q r t : ℕ} {m d : Fin c → ℕ} {B : Fin c → Multiset ℂˣ}

end Sizes

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

open GlobalTheory.DownLift GlobalTheory.DownLift.Params GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

end Real

end GlobalTheory.PtString

end
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.IdemIota

set_option maxHeartbeats 800000 in

theorem toCompl_map_mem {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ intAE D) :
    GlobalTheory.LFun.toCompl h (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) z)
      ∈ w.adicCompletionIntegers D.host.E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, rfl⟩ := hz
    have e2 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)
        (b ⊗ₜ[D.host.F] (x : D.host.E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q b ⊗ₜ[D.host.F] (x : D.host.E) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    rw [e2]
    exact GlobalTheory.LFun.InertChart.toCompl_mem h (GlobalTheory.AdelicU.tmul_mem_intLoc (hb q) x)
  | zero =>
    rw [map_zero (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_zero (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).zero_mem
  | add y y' _ _ h1 h2 =>
    rw [map_add (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_add (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).add_mem _ _ h1 h2
  | neg y _ h1 =>
    rw [map_neg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_neg (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).neg_mem _ h1

theorem cw_mem_integers {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) {a : AE D} (ha : finPart D a ∈ intAE D) :
    GlobalTheory.Core.Rk.SWQ.cw h a ∈ w.adicCompletionIntegers D.host.E := by
  have e : GlobalTheory.Core.Rk.SWQ.cw h a = GlobalTheory.LFun.toCompl h
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) (finPart D a)) := by
    show GlobalTheory.LFun.toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E q a) = _
    congr 1
    clear ha
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e]
  exact toCompl_map_mem h _ ha

theorem idemAt_eq_iota_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P →
    ∀ ι : P.adicCompletion D.host.E →+ AE D,
      GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  intro D P e he ι hι
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := hι
  have hq : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := rfl
  have hee : e * e = e := he.1.1
  have hec : e * cA D e = 0 := he.1.2.1
  have hne : e ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (he.2 x hx0).1 hx
    rw [h0, zero_mul, map_zero] at this
    exact this (zero_mem _)
  have idem01 : ∀ a : AE D, a * a = a → GlobalTheory.Core.Rk.SWQ.cw hq a = 0 ∨ GlobalTheory.Core.Rk.SWQ.cw hq a = 1 := fun a ha =>
    IsIdempotentElem.iff_eq_zero_or_one.mp
      (by show GlobalTheory.Core.Rk.SWQ.cw hq a * GlobalTheory.Core.Rk.SWQ.cw hq a = GlobalTheory.Core.Rk.SWQ.cw hq a; rw [← map_mul, ha])
  have he' := GlobalTheory.ExportSeries.LatHalf.isIdemAt_conjPl he
  have hPP : Formalism.L2.DIV.conjPl P ≠ P := by
    intro hP
    rw [hP] at he'
    have h1 := GlobalTheory.Tow.idemAt_unique he' he
    apply hne
    rw [← hee]
    nth_rewrite 2 [← h1]
    exact hec
  obtain ⟨x, hxP, hxP'⟩ : ∃ x ∈ P.asIdeal, x ∉ (Formalism.L2.DIV.conjPl P).asIdeal := by
    by_contra hc
    push Not at hc
    exact hPP (HeightOneSpectrum.ext (P.isMaximal.eq_of_le (Formalism.L2.DIV.conjPl P).isPrime.ne_top hc)).symm
  have hx0 : x ≠ 0 := by rintro rfl; exact hxP' (Formalism.L2.DIV.conjPl P).asIdeal.zero_mem
  have hint : finPart D (cA D e * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hxP' ((he'.2 x hx0).2 hc)
  have hc0 : GlobalTheory.Core.Rk.SWQ.cw hq (cA D e) = 0 := by
    have hm := cw_mem_integers hq hint
    rw [map_mul, GlobalTheory.Core.Rk.SecPar.cw_incA] at hm
    rcases idem01 (cA D e) (by rw [← map_mul, hee]) with h | h
    · exact h
    · exfalso
      have hv : Valued.v ((algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P)) ((x : D.host.E))⁻¹)
          = HeightOneSpectrum.valuation D.host.E P ((x : D.host.E))⁻¹ :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
      rw [h, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, hv] at hm
      have hv0 : HeightOneSpectrum.valuation D.host.E P (x : D.host.E) ≠ 0 := by simpa using hx0
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← not_lt,
        HeightOneSpectrum.valuation_lt_one_iff_mem] at hm
      exact hm hxP
  have he0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin (P.under (𝓞 D.host.F)) 1)) =
      e + cA D e := by
    rw [Formalism.IndefR.Fin.below_of_idemAt he]
    show _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (Formalism.IndefR.Fin.sglV _ 1))
    have hb : Formalism.IndefR.Fin.belowPl P = P.under (𝓞 D.host.F) := HeightOneSpectrum.ext rfl
    rw [hb]
    congr 2
  have h6e := h6 e
  rw [he0, add_mul, hee, mul_comm (cA D e) e, hec, add_zero, hc0, map_zero, map_zero, add_zero] at h6e
  rcases idem01 e hee with h | h
  · rw [h, map_zero] at h6e
    exact absurd h6e hne
  · rw [h] at h6e
    exact h6e

end GlobalTheory.IdemIota

end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_idempotent_eq_completionEmbedding_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  atlas_forward_decl GlobalTheory.IdemIota.idemAt_eq_iota_one
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.DivPtLocalCard

open GlobalTheory.Core.Rk.SWQ

variable {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

def phi (h : w.under (𝓞 D.host.F) = q) {m n : ℕ} (B : Matrix (Fin m) (Fin m) (w.adicCompletion D.host.E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion D.host.E)) :
    Matrix (Fin m) (Fin n) (AE D) →+ Matrix (Fin m) (Fin n) (w.adicCompletion D.host.E) :=
  AddMonoidHom.mk' (fun y => B * y.map (cw h) * A) fun y y' => by
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem phi_apply (h : w.under (𝓞 D.host.F) = q) {m n : ℕ} (B : Matrix (Fin m) (Fin m) (w.adicCompletion D.host.E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion D.host.E)) (y : Matrix (Fin m) (Fin n) (AE D)) :
    phi h B A y = B * y.map (cw h) * A := rfl

theorem eq_iota_cw {h : w.under (𝓞 D.host.F) = q} {ι : w.adicCompletion D.host.E →+ AE D}
    (hι : GlobalTheory.DivPtLocal.IsIotaAt h ι) {x : AE D} (hx : ι 1 * x = x) : x = ι (cw h x) := by
  obtain ⟨-, -, -, -, h4, -, -, -⟩ := hι
  have := h4 x 1
  rw [mul_one] at this
  rw [← this, mul_comm, hx]

theorem gl_cancel {k : Type} [Field k] {m n : ℕ} (b : GL (Fin m) k) (a : GL (Fin n) k) (Y : Matrix (Fin m) (Fin n) k) :
    b.1 * ((b⁻¹).1 * Y * a.1) * (a⁻¹).1 = Y := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc b.1, Units.mul_inv, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem gl_cancel' {k : Type} [Field k] {m n : ℕ} (b : GL (Fin m) k) (a : GL (Fin n) k) (Y : Matrix (Fin m) (Fin n) k) :
    (b⁻¹).1 * (b.1 * Y * (a⁻¹).1) * a.1 = Y := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (b⁻¹).1, Units.inv_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.DivPtLocalCard

set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Rk.SWQ in

theorem GlobalTheory.DivPtLocalCard.card_DQ_eq : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) (ι 1) N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  intro D S T ΛS ΛT hS hT P hs ι hι N hN
  obtain ⟨e, ⟨⟨a, ha, -⟩, -⟩, -, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart (GlobalTheory.AdelicU.isCMExt_host D)
    (GlobalTheory.Doubling.isHermND_gram S) hS.1.fg hS.1.span_eq_top (rfl : P.under (𝓞 D.host.F) = _) hs
    (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hS _)
  obtain ⟨b, hb⟩ := GlobalTheory.Core.Rk.SWQ.LatHalf.mem_latO_iff_intM D _ P rfl hs S T ΛS ΛT hS hT a ha
  have hP : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := rfl
  have hι' := hι
  obtain ⟨-, h1, h2, h3, h4, -, -, -⟩ := hι'
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (fun v => v = P.under (𝓞 D.host.F)) with hΛ
  set c := ι 1 with hc
  set Φ := GlobalTheory.DivPtLocalCard.phi hP (b⁻¹).1 a.1 with hΦ
  have hent : ∀ y : WO S T, c • y = y → ∀ i j, y i j = ι (cw hP (y i j)) := fun y hy i j =>
    GlobalTheory.DivPtLocalCard.eq_iota_cw hι (by simpa [Matrix.smul_apply] using congrFun (congrFun hy i) j)
  have hoff : ∀ y : WO S T, c • y = y → offM (P.under (𝓞 D.host.F)) y = 0 := by
    intro y hy
    ext i j
    simp only [offM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [hent y hy i j, h3, sub_self]
  have hcA : ∀ y : WO S T, c • y = y → ∀ i j, cw hP (cA D (y i j)) = 0 := by
    intro y hy i j
    rw [hent y hy i j]
    exact h2 _
  have hmem : ∀ y : WO S T, c • y = y → (y ∈ Λ ↔ GlobalTheory.Core.Rk.SWQ.IntM (Φ y)) := fun y hy => hb y (hoff y hy) (hcA y hy)
  have hInt : ∀ Z, GlobalTheory.Core.Rk.SWQ.IntM Z ↔ Z ∈ GlobalTheory.DivPtLocal.locInt P T.rank S.rank := fun Z => Iff.rfl
  have hIntN : ∀ Z, GlobalTheory.Core.Rk.SWQ.IntM (N • Z) ↔ Z ∈ GlobalTheory.DivPtLocal.locDiv P N T.rank S.rank := by
    intro Z
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.smul_apply, nsmul_eq_mul]
    rfl
  have hcN : ∀ y : WO S T, c • y = y → c • (N • y) = N • y := fun y hy => by rw [smul_comm, hy]
  let Ψ : Matrix (Fin T.rank) (Fin S.rank) (P.adicCompletion D.host.E) → WO S T :=
    fun Z => (b.1 * Z * (a⁻¹).1).map ι
  have hΨc : ∀ Z, c • Ψ Z = Ψ Z := by
    intro Z
    ext i j
    simp only [Ψ, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, hc, h4, h1, one_mul]
  have hΦΨ : ∀ Z, Φ (Ψ Z) = Z := by
    intro Z
    rw [hΦ, GlobalTheory.DivPtLocalCard.phi_apply]
    have : (Ψ Z).map (cw hP) = b.1 * Z * (a⁻¹).1 := by
      ext i j
      simp only [Ψ, Matrix.map_apply, h1]
    rw [this, GlobalTheory.DivPtLocalCard.gl_cancel']
  have hinj : ∀ y y' : WO S T, c • y = y → c • y' = y' → Φ y = Φ y' → y = y' := by
    intro y y' hy hy' H
    have H' : y.map (cw hP) = y'.map (cw hP) := by
      rw [← GlobalTheory.DivPtLocalCard.gl_cancel b a (y.map (cw hP)), ← GlobalTheory.DivPtLocalCard.gl_cancel b a (y'.map (cw hP))]
      exact congrArg (fun M => b.1 * M * (a⁻¹).1) H
    ext i j
    rw [hent y hy i j, hent y' hy' i j]
    exact congrArg ι (congrFun (congrFun H' i) j)
  have hdiv : ∀ y : ↥(GlobalTheory.DivPtFourier.divPts Λ c N), Φ y ∈ GlobalTheory.DivPtLocal.locDiv P N T.rank S.rank := by
    rintro ⟨y, hy1, hy2⟩
    rw [← hIntN, ← map_nsmul]
    exact (hmem _ (hcN y hy1)).1 hy2
  let f : ↥(GlobalTheory.DivPtFourier.divPts Λ c N) →+ GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank :=
    (QuotientAddGroup.mk' _).comp ((Φ.comp (GlobalTheory.DivPtFourier.divPts Λ c N).subtype).codRestrict _ hdiv)
  have hsurj : Function.Surjective f := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H Z =>
    have hy2 : N • Ψ Z ∈ Λ := by
      rw [hmem _ (hcN _ (hΨc Z)), map_nsmul, hΦΨ, hIntN]
      exact Z.2
    refine ⟨⟨Ψ Z, hΨc Z, hy2⟩, ?_⟩
    change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    congr 1
    exact Subtype.ext (hΦΨ Z)
  have hker : f.ker = (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (GlobalTheory.DivPtFourier.divPts Λ c N) := by
    ext ⟨y, hy1, hy2⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
    change (QuotientAddGroup.mk _ : GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change Φ y ∈ GlobalTheory.DivPtLocal.locInt P T.rank S.rank ↔ y ∈ Λ ∧ y ∈ GlobalTheory.PlaceModel.half S T c
    rw [← hInt, ← hmem y hy1]
    exact ⟨fun h => ⟨h, hy1⟩, fun h => h.1⟩
  exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj)).toEquiv

end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisionPoints_splitPlace_local_matrices : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) (ι 1) N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  atlas_forward_decl GlobalTheory.DivPtLocalCard.card_DQ_eq
end

section
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.DivPtLocal.Count

variable {E : Type} [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))

def red (N m n : ℕ) : ↥(locDiv w N m n) →+
    (Fin m → Fin n → (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)})) where
  toFun X i j := Ideal.Quotient.mk _ (⟨(N : w.adicCompletion E) * X.1 i j, X.2 i j⟩ : w.adicCompletionIntegers E)
  map_zero' := by
    funext i j
    rw [Pi.zero_apply, Pi.zero_apply, ← map_zero (Ideal.Quotient.mk _)]
    congr 1
    apply Subtype.ext
    simp
  map_add' X Y := by
    funext i j
    rw [Pi.add_apply, Pi.add_apply, ← map_add]
    congr 1
    apply Subtype.ext
    simp [mul_add]

theorem natCast_ne_zero {N : ℕ} (hN : 0 < N) : (N : w.adicCompletion E) ≠ 0 := by
  have h : (N : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (N : E) := by simp
  rw [h]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hN.ne')

theorem red_surjective {N : ℕ} (hN : 0 < N) (m n : ℕ) : Function.Surjective (red w N m n) := by
  intro Y
  have hN' := natCast_ne_zero w hN
  choose Z hZ using fun i j => Ideal.Quotient.mk_surjective (Y i j)
  have key : ∀ i j, (N : w.adicCompletion E) * ((N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E))
      = Z i j := fun i j => by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]
  refine ⟨⟨Matrix.of fun i j => (N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E), ?_⟩, ?_⟩
  · intro i j
    rw [Matrix.of_apply, key]
    exact (Z i j).2
  · funext i j
    rw [← hZ]
    change Ideal.Quotient.mk _ _ = _
    congr 1
    apply Subtype.ext
    exact key i j

theorem ker_red {N : ℕ} (hN : 0 < N) (m n : ℕ) :
    (red w N m n).ker = (locInt w m n).addSubgroupOf (locDiv w N m n) := by
  have hN' := natCast_ne_zero w hN
  ext X
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_locInt]
  simp only [funext_iff, Pi.zero_apply]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change Ideal.Quotient.mk _ _ = _ ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg (fun z : w.adicCompletionIntegers E => (z : w.adicCompletion E)) hc
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast] at h
    rw [mul_left_cancel₀ hN' h]
    exact c.2
  · intro h
    refine ⟨⟨X.1 i j, h⟩, ?_⟩
    apply Subtype.ext
    simp

theorem card_locQ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (N m n : ℕ) (hN : 0 < N) :
    Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) =
      Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  have e := (QuotientAddGroup.quotientAddEquivOfEq (ker_red w hN m n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (red w N m n) (red_surjective w hN m n))
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]

end GlobalTheory.DivPtLocal.Count

end
end

open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_localMatrixDivisionPointQuotient : ∀ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (N m n : ℕ), 0 < N → Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) = Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  atlas_forward_decl GlobalTheory.DivPtLocal.Count.card_locQ
end

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.DivPtLocal

open GlobalTheory.AdelicU in

theorem mem_latO_true_iff_at : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D) (u : WO S T), algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) • u = u → (u ∈ latO S T LS LT (fun _ => True) ↔ u ∈ latO S T LS LT (fun v => v = q)) := by
  intro D S T LS LT q u hu
  set e0 := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) with he0
  constructor
  · intro h
    let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun x => e0 • x)
      fun x y => Matrix.ext fun i j => mul_add e0 (x i j) (y i j)
    have main : latO S T LS LT (fun _ => True) ≤ (latO S T LS LT (fun v => v = q)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
      refine AddSubgroup.subset_closure ⟨GlobalTheory.AdelicU.singleFin q 1 * α, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]
        by_cases hv : v = q
        · subst hv
          rw [evalV_singleFin_self]
          simpa using hα v
        · rw [evalV_singleFin_ne hv, zero_mul]
          exact zero_mem _
      · rw [map_mul, evalV_singleFin_ne hv, zero_mul]
      · ext i j
        simp only [Ψ, AddMonoidHom.mk'_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, he0,
          Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        rw [Algebra.algebraMap_self, RingHom.id_apply]
        exact Prod.ext (mul_zero (0 : Ainf D.host.F)) rfl
    have := main h
    rw [AddSubgroup.mem_comap] at this
    exact hu ▸ this
  · intro h
    refine AddSubgroup.closure_mono ?_ h
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ h' => absurd trivial h', rest⟩

theorem isSplit_of_isIdemAt : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) := by
  intro D P e he
  rw [GlobalTheory.PtString.isSplit_iff_conj, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  intro h
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he (IsDedekindDomain.HeightOneSpectrum.ext h)

theorem natCard_DQ_eq_locQ : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  intro D S T ΛS ΛT hS hT P e he N hN
  have hs := isSplit_of_isIdemAt D P e he
  obtain ⟨ι, hι⟩ := GlobalTheory.DivPtLocal.exists_isIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) hs
  have he1 := GlobalTheory.T.splitPlace_idempotent_eq_completionEmbedding_one D P e he ι hι
  have h3 := hι.2.2.2.1
  have key : ∀ u : WO S T, e • u = u → (u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun v => v = P.under (𝓞 D.host.F))) := by
    intro u hu
    refine mem_latO_true_iff_at D S T _ _ _ u ?_
    rw [← hu, smul_smul, he1, h3]
  have hd : GlobalTheory.DivPtFourier.divPts (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N =
      GlobalTheory.DivPtFourier.divPts (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) e N := by
    ext y
    rw [GlobalTheory.DivPtFourier.mem_divPts, GlobalTheory.DivPtFourier.mem_divPts]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key _ (by rw [smul_comm, h1])).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key _ (by rw [smul_comm, h1])).2 h2⟩
  have hh : (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e =
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) ⊓ GlobalTheory.PlaceModel.half S T e := by
    ext y
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(key _ ((GlobalTheory.PlaceModel.mem_half S T).1 h2)).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(key _ ((GlobalTheory.PlaceModel.mem_half S T).1 h2)).2 h1, h2⟩
  unfold GlobalTheory.DivPtFourier.DQ
  rw [hd, hh]
  subst he1
  exact GlobalTheory.T.card_divisionPoints_splitPlace_local_matrices D S T ΛS ΛT hS hT P hs ι hι N hN

theorem natCard_DQ : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT P e he N hN
  have hI : (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  rw [natCard_DQ_eq_locQ D S T ΛS ΛT hS hT P e he N hN, GlobalTheory.T.card_localMatrixDivisionPointQuotient D.host.E P N T.rank S.rank hN, mul_comm T.rank,
    ← GlobalTheory.LocalDifferentProduct.card_quot_map P hI, Ideal.map_span, Set.image_singleton, map_natCast]

end GlobalTheory.DivPtLocal
end
