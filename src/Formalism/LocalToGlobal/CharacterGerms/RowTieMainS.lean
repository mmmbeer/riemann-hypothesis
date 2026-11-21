import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
import Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives
import Formalism.LocalToGlobal.CharacterGerms.NormOneIntegral
import Formalism.LocalToGlobal.CharacterGerms.FinTwoNeOneSub
import Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant
import Formalism.LocalToGlobal.CharacterGerms.NormOneRowDegrees
import Formalism.LocalToGlobal.CharacterGerms.RowTieGermI
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEq2
import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
import Formalism.LocalToGlobal.CharacterGerms.RowTieCH
import Formalism.LocalToGlobal.CharacterGerms.RowTieChar
import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
import Formalism.LocalToGlobal.CharacterGerms.RowTieDesc
import Formalism.LocalToGlobal.CharacterGerms.RowTiePFBMapSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanFinal
import Formalism.LocalToGlobal.CharacterGerms.RowTieValK
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFBTop
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2
import Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord
import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
import Formalism.LocalToGlobal.CharacterGerms.UnitSeriesFrobenius
import Formalism.LocalToGlobal.CharacterGerms.CoeffPowCharFrobenius
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroSecondCoordinate
import Formalism.LocalToGlobal.CharacterGerms.CanonicalGaugeFirstPartialLawEq
import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear
import Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfUnconditional
import Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
import Formalism.SharpRestriction.GrowthBounds.ProofRowTieVals
import Formalism.LocalToGlobal.CharacterGerms.RowTieCharS
import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjHolds

section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ}

private theorem cc_subst_lemma_2 {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem cc_ev_eq {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  exact cc_subst_lemma_2 (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f

theorem constantCoeff_eval_pair {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    constantCoeff (ev ![a, b] f) = constantCoeff f := cc_ev_eq ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MapFB

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}

theorem constantCoeff_eval_single {n : ℕ} (a : Pt K n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS K 1 d) :
    constantCoeff (ev ![a] f) = constantCoeff f :=
  cc_ev_eq _ (by intro j i; fin_cases j; simp [ha]) f

theorem map_pderiv {σ : Type} (x : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (pderiv K x f) = pderiv C x (MvPowerSeries.map φ f) := by
  ext n
  simp [coeff_pderiv, coeff_map]

theorem map_DofN (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (f : PS K n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  unfold DofN
  simp only [map_sum, map_mul, MvPowerSeries.map_C,
    map_ev2 φ (pt K d b) 0 (fun i => cc_pt b i) zc_zero, mpt_pt, mpt_zero, map_pderiv]

theorem map_iter_DofN (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (m : ℕ) (f : PS K n d) :
    MvPowerSeries.map φ ((DofN F b u)^[m] f) =
      (DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)))^[m] (MvPowerSeries.map φ f) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]

theorem map_DmonN (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (m : ι →₀ ℕ) (f : PS K n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_iter_DofN, ih]

theorem map_DpolyN (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (P : MvPolynomial ι K) (f : PS K n d) :
    MvPowerSeries.map φ (DpolyN F cp u P f) =
      DpolyN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) (MvPolynomial.map φ P)
        (MvPowerSeries.map φ f) := by
  unfold DpolyN
  rw [map_sum, MvPolynomial.support_map_of_injective P φ.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, MvPolynomial.coeff_map, map_DmonN]

theorem map_expS' [Algebra ℚ K] [Algebra ℚ C] {n : ℕ} (f : PS K n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS K f) = FB.expS C (MvPowerSeries.map φ f) := by
  unfold FB.expS
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), PowerSeries.map_exp]

theorem map_nabValN [Algebra ℚ K] [Algebra ℚ C] {O : Type} [CommRing O] [StarRing O]
    (B : FB K d O) (B' : FB C d O) (hF : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j))
    (hA : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)) (h : PS K 2 d)
    (hh : constantCoeff h = 0) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {ι : Type} [Fintype ι]
    (cp : ι → Fin n) (u : ι → Fin d → K) (P : MvPolynomial ι K) :
    nabValN B' C (MvPowerSeries.map φ h) w0 m (MvPowerSeries.map φ f) cp (fun l i => φ (u l i))
        (MvPolynomial.map φ P) = φ (nabValN B K h w0 m f cp u P) := by
  unfold nabValN
  rw [← constantCoeff_map]
  congr 1
  have e1 : B.FK K = B.G.F := rfl
  have e2 : B'.FK C = fun j => MvPowerSeries.map φ (B.G.F j) := funext hF
  have eA : mpt φ (B.A.act w0) = B'.actK C w0 := by
    funext j; exact (hA w0 j).symm
  have eK : B.actK K w0 = B.A.act w0 := rfl
  have p0 : ∀ i, constantCoeff (pt K d (0 : Fin 1) i) = 0 := cc_pt (R := K) (d := d) 0
  have q0 : ∀ i, constantCoeff (comp1 (B.A.act w0) (pt K d (0 : Fin 1)) i) = 0 :=
    cc_comp1 (B.A.act w0) (B.A.const w0) (pt K d (0 : Fin 1)) p0
  have hL : MvPowerSeries.map φ (B.hL K h w0) = B'.hL C (MvPowerSeries.map φ h) w0 := by
    unfold FB.hL
    rw [eK, map_ev2 φ (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, mpt_pt,
      mpt_comp1 φ (B.A.act w0) (pt K d 0) p0, mpt_pt, eA]
  have hcL : constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    rw [eK, constantCoeff_eval_pair (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, hh]
  have hcb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := fun b => by
    rw [constantCoeff_eval_single (pt K d b) (cc_pt (R := K) (d := d) b), hcL]
  have hcs : constantCoeff ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_sum, Finset.sum_eq_zero fun b _ => hcb b, smul_zero]
  have hsum : ∑ b : Fin n, MvPowerSeries.map φ (ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![pt C d b] (B'.hL C (MvPowerSeries.map φ h) w0) :=
    Finset.sum_congr rfl fun b _ => by
      rw [map_ev1 φ (pt K d b) (cc_pt (R := K) (d := d) b), mpt_pt, hL]
  rw [e1, e2, map_DpolyN, map_mul, map_expS' φ _ hcs, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    map_nsmul, map_sum, hsum]

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

open MvPowerSeries MapFB Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem nabMapSt_holds : NabMapSt Xo c := by
  intro T io y C3 C _ _ V ι k Y hY a n f P
  have hga : (a3B C3).IsCanonGauge T.Fr (a3h C3) := by
    let := io.toAlgebra
    exact C3.ch.gauge
  have hcc : constantCoeff (a3h C3) = 0 := by
    have e := congrArg constantCoeff hga.ax0
    rwa [constantCoeff_eval_pair _ _ zc_zero (by simp), map_zero] at e
  unfold FBChart.nab chartDerivativeCoefficient
  rw [hY.h, hY.w0, hY.k]
  exact map_nabValN ι (a3B C3) Y.B hY.F hY.act (a3h C3) hcc H.w0 k f _ _ P

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem nvalEqSt_holds : NvalEqSt := by
  intro T C _ V ι hι x
  unfold nval eOf
  have hl : 0 ≤ vV T.V ((V.l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rwa [map_natCast] at h
  by_cases hx : x = 0
  · subst hx
    rw [if_pos rfl, map_zero, AddValuation.map_zero]
    rfl
  · rw [if_neg hx, hι x hx]
    have he : ((vV T.V ((V.l : ℕ) : T.Fr)).toNat : ℝ) = (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
      first
        | exact_mod_cast Int.toNat_of_nonneg hl
        | rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg hl]
    rw [he]
    rfl

end Formalism.L2.FormalSeriesBounds
end
end

section
namespace Formalism.L2.FormalSeriesBounds



end Formalism.L2.FormalSeriesBounds
end

section
namespace Formalism.L2.FormalSeriesBounds





end Formalism.L2.FormalSeriesBounds
end

section
namespace Formalism.L2.FormalSeriesBounds




theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds


end Formalism.L2.FormalSeriesBounds
end

section
namespace Formalism.L2.FormalSeriesBounds


end Formalism.L2.FormalSeriesBounds
end

section
namespace Formalism.L2.FormalSeriesBounds



theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
end

section
namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_holds : PTSelfSt := ptSelf_of_eig RowTiePKey.keyEig_holds

end Formalism.L2.FormalSeriesBounds
end

section
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LMulP

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval

theorem pderiv_comm' {σ K : Type} [CommRing K] (i j : σ) (f : MvPowerSeries σ K) :
    pderiv K i (pderiv K j f) = pderiv K j (pderiv K i f) := by
  ext n
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases h : i = j
  · subst h; rfl
  · have e1 : ((n + Finsupp.single i 1 : σ →₀ ℕ) : σ → ℕ) j = n j := by
      simp [h]
    have e2 : ((n + Finsupp.single j 1 : σ →₀ ℕ) : σ → ℕ) i = n i := by
      simp [Ne.symm h]
    rw [add_right_comm n (Finsupp.single i 1), e1, e2]
    ring

section Law

variable {C : Type} [Field C] [CharZero C] {d : ℕ} (G : FGLaw C d)

def Mm (j k : Fin d) : PS C 1 d := ev (n := 1) ![pt C d 0, 0] (pderiv C ((1 : Fin 2), k) (G.F j))

end Law

section Alg

variable {C : Type} [Field C] {V : VF C}

end Alg

section Rec

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (Y : FBChart C V O d)

end Rec

end LMulP

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UnitSeriesFrobeniusLemmas

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval LMulP

section Gen

variable {C : Type} [Field C] {V : VF C}

end Gen

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (Y : FBChart C V O d)

theorem hz1 : Z0 (![pt C d 1] : Fin 1 → Pt C 2 d) := z0_1 _ fun i => z0_pt 1 i

def Mz (j k : Fin d) : PS C 2 d := ev (n := 2) ![pt C d 1, 0] (pderiv C ((1 : Fin 2), k) (Y.B.G.F j))

end Main

end UnitSeriesFrobeniusLemmas

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleCoordinateParts

open PartialDerivEval CocycleIdentity

section Exps

variable {dd : ℕ}

def lpart (α : Fin 3 × Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => α (Fin.castSucc p.1, p.2)

end Exps

section Ser

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

end Ser

section Kill

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

variable {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

end Kill

section Closed

end Closed

end CocycleCoordinateParts

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleSliceMultiplication

open PartialDerivEval CocycleIdentity CocycleCoordinateParts

section Gen

variable {C : Type} [Field C] {V : VF C} {σ : Type}

end Gen

section Ser

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def z1 (ζ : Fin dd →₀ ℕ) : Fin 1 × Fin dd →₀ ℕ := ζ.mapDomain fun j => ((0 : Fin 1), j)

theorem z2 : Z0 (![pt C dd 2] : Fin 1 → Pt C 3 dd) := by
  intro k i
  simp [pt]

variable {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

def TT (ν : Fin 2 × Fin dd →₀ ℕ) (ζ : Fin dd →₀ ℕ) (d : Fin 3 × Fin dd →₀ ℕ) : C :=
  coeff d Y.B.ph1 * (if lpart d = ν then coeff (z1 ζ) (∏ j, Y.nmul V.l j ^ d ((2 : Fin 3), j)) else 0)

end Ser

section Facts

variable {dd : ℕ}

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

end Facts

section Slice

variable {dd : ℕ} {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
  (Y : FBChart C V O dd)

end Slice

end CocycleSliceMultiplication

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

structure GeoIn : Prop where

  lab : LabGeoCoreSt Xo c

  ndg : NondegenerateCharts Xo c

  ch : UpFBr.CharacterHypothesisUnramified Xo c

theorem descent_holds : DescentSt Xo c := descent_of (nabMapSt_holds Xo c) descent_span nvalEqSt_holds

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def EnoughCharactersSelfUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, CHCharSelfSt Y (selfOfLab ha hg o)

def CharacterHypothesisSelfUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]


end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

structure GeoInS : Prop where
  lab : LabSGeoCoreSt Xo c
  ndg : NondegenerateCharts Xo c

  ch : CharacterHypothesisSelfUnramified Xo c

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]



end Formalism.L2.FormalSeriesBounds
end
end
