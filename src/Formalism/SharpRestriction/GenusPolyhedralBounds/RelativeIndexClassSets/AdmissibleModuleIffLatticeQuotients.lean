import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Geo NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.FamilyHypotheses

def SupBoundPageRows (D : D7) (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) : Prop :=
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  lrd D ≤ 2 * large₂.sc.L ∧
  Real.log D.host.d ≤ 2 * large₂.sc.L ∧
  Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * large₂.sc.L ∧
  Real.log D.R.f ≤ 2 * large₂.sc.L ∧
  Real.log D.host.pde ≤ large₂.sc.L ∧
  Real.log D.host.pde' ≤ large₂.sc.L ∧
  Real.log (1 + DF ka) ≤ 2 * large₂.sc.L ∧
  Real.log ka.n ≤ large₂.sc.L

def OwnPr (D : D7) (p : ℕ) : Prop := p = Formalism.MainNotions.DIV.Cons.po D ∨ p = Formalism.MainNotions.DIV.Cons.po2 D

theorem ownPr_iff (D : D7) (p : ℕ) : OwnPr D p ↔ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ) := Iff.rfl




section Split

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def FourthHypothesisSizes (large₂ : SizeData₂ D) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  large₂.sc.b ≤ ka.size ∧ (T : ℝ) * wL.size ≤ 2 * ka.size ∧
  wF.size ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T ∧
  WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (T : ℝ) ^ 2 ≤ large₂.sc.b ∧
  WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ≤ large₂.sc.b ∧
  (∀ i, 2 * DF ka + 2 < D.host.g i)

def I4 (large₂ : SizeData₂ D) (X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) (nW : ℕ) : Prop :=
  ∃ PLam lNc : ℝ, PLam ≤ 1009 * Zb D large₂ ∧ lNc ≤ 81 * Zb D large₂ ^ 2 ∧
  (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th ∈ B.Mlat j w1, X.NonZeroComp w1 th ∧
    ∀ σ, Real.log (B.supN j w1 σ th) ≤ 2 * PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size) ∧
  ∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 ∧ ∃ th ∈ B.Mlat j w2, X.NonZeroComp w2 th ∧
    ∀ σ, Real.log (B.supN j w2 σ th) ≤ PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size

theorem fourthHypothesis_iff_sizes_and_index (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nW : ℕ) :
    H4 large₂ X H C2 A2 CR ka wL wF T nW ↔ FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e, f⟩, g⟩, fun ⟨⟨a, b, c, d, e, f⟩, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

def HypPage (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (h0 : ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ H3 large₂ H C2 A2 CR 0 wL T ∧
    FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ (T : ℝ) ≤ large₂.sc.x ^ CT

theorem hyp_iff (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Hyp large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ↔
      HypPage large₂ X H C2 A2 CR CT ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧ H1 large₂ X H S wL nus ∧
        H2 X S ka wL wF ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, f, ((fourthHypothesis_iff_sizes_and_index ..).1 g).1, h⟩, c, d, e, ((fourthHypothesis_iff_sizes_and_index ..).1 g).2⟩,
    fun ⟨⟨a, b, f, g, h⟩, c, d, e, i⟩ => ⟨a, b, c, d, e, f, (fourthHypothesis_iff_sizes_and_index ..).2 ⟨g, i⟩, h⟩⟩

theorem hypC_iff (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ↔
      HypPage large₂ X H C2 A2 CR CT ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
        Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ X wL nus ∧ H2 X S ka wL wF ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, f, ((fourthHypothesis_iff_sizes_and_index ..).1 g).1, h⟩, c, d, e, ((fourthHypothesis_iff_sizes_and_index ..).1 g).2⟩,
    fun ⟨⟨a, b, f, g, h⟩, c, d, e, i⟩ => ⟨a, b, c, d, e, f, (fourthHypothesis_iff_sizes_and_index ..).2 ⟨g, i⟩, h⟩⟩


def ZSel {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF) (T : ℕ) : Prop :=
  (∀ k, ∑ i, G.alz k i = Formalism.MainNotions.Gaps.EtaleWeightGaps.a0 D j T) ∧
  (∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β) ∧
  (∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)


def refill {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF)
    (del : ℕ) (th' : Fin del → B.Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF)) (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ B.Cusp j ka)
    (rq : ℕ) (th : Fin rq → B.Mlat j ka) (iet : ℕ) (et : B.Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF :=
  ⟨G₀.N, G₀.w, del, th', rz, alz, th0, zc, rq, th, iet, et, G₀.mx⟩


end Split

section Views

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def MSt (F : ShimFam D G Lev) : Prop := WeightFamilies.adm1 (toWeightFamilies F)

def GSt (F : ShimFam D G Lev) (large₂ : SizeData₂ D) (CG AG : ℝ) : Prop := WeightFamilies.adm2 large₂ (toWeightFamilies F) CG AG

variable (F : ShimFam D G Lev) (I : Type) (dat : I → Dat D Lev) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I)
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j)

def AdmissibilitySecond (large₂ : SizeData₂ D) (CA C1 A1 CG AG : ℝ) : Prop := WeightAlgebra.adm2 large₂ (toWeightAlgebra F I dat hI iW hiW) CA C1 A1 CG AG

def IntegralityFamily (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    H2 (toWeightAlgebra F I dat hI iW hiW j h1 h2) (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) ka wL wF

def ScalSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ScalB large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H.C1 H.A1 (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) ka wL wF T

def FourthHypothesisIndexBound (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    I4 large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) wL wF nW

def DeepSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT CG AG : ℝ) (Pd : (j : ℕ) → WeightFamilies.Wt D j → ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal (toWeightFamilies F)) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (toWeightFamilies F).KO) → ℝ),
    Hyp large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepIn (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka large₂ CG AG (Pd j ka)

def LatSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (toWeightFamilies F) j ka

def SupL2AtFamily (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT CG AG : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.SupBoundByL2AtWeight large₂ (toWeightFamilies F) j ka CG AG

def DeepHermSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepHerm (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka

def DeepSubMulSt : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepSubMul (toWeightAlgebra F I dat hI iW hiW j h1 h2)

def DeepLogDSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (Pd : (j : ℕ) → WeightFamilies.Wt D j → ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepLogD (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka (Pd j ka)

def TiedWSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc Prw : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF,
      G.TiedW (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) Gc Prw

def TiedThSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j wF), Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j wF)) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ i, G.th' i ∈ Sh) →
        G.TiedTh (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) Gc

def TiedZSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF)),
      Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ k, G.th0 k ∈ Sh) → ZSel G T →
        G.TiedZ (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) T Gc





theorem MSt.latSt (h : MSt F) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : LatSt F I dat hI iW hiW large₂ H C2 A2 CR CT :=
  fun j h1 h2 ka _ _ _ _ _ _ _ => h j h1 h2 ka





def IntegralityAtPrime (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    H2 (toWeightAlgebra F I dat hI iW hiW j h1 h2) (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) ka wL wF

def ScalStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ScalB large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H.C1 H.A1 (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) ka wL wF T

def TiedWStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc Prw : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF,
      G.TiedW (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) Gc Prw

def TiedThStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j wF), Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j wF)) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ i, G.th' i ∈ Sh) →
        G.TiedTh (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) Gc

def TiedZStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF)),
      Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ k, G.th0 k ∈ Sh) → ZSel G T →
        G.TiedZ (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) T Gc













end Views

end Formalism.MainNotions.Gaps.FamilyHypotheses
