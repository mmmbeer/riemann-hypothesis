import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeometrySectionsEqRiemannRoch
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VarietyWithModels

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam

variable {D : D7}

section Same

theorem samePt_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') {y : Λ.Pt Λ.YY} {y' : Λ'.Pt Λ'.YY} (hy : HEq y y') :
    Λ.fld y = Λ'.fld y' ∧
      (∃ e : Λ.Ylat y ≃ₗ[𝓞 D.host.E] Λ'.Ylat y', ∀ a b, Λ'.be y' (e a) (e b) = Λ.be y a b) ∧
      (Λ.good y ↔ Λ'.good y') ∧ Λ.phiCy y = Λ'.phiCy y' ∧ Λ.dP y = Λ'.dP y' := by
  subst hr hj; cases hΛ; cases hy
  exact ⟨rfl, ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩, Iff.rfl, rfl, rfl⟩

theorem lat_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') {y : Λ.Pt Λ.YY} {y' : Λ'.Pt Λ'.YY} (hy : HEq y y') {Y : Type} [AddCommGroup Y]
    [Module (𝓞 D.host.E) Y] (β : Y → Y → ℝ)
    (hY : ∃ e : Λ.Ylat y ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ.be y a b) :
    ∃ e : Λ'.Ylat y' ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ'.be y' a b := by
  subst hr hj; cases hΛ; cases hy; exact hY

end Same

section Comparison₂

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)} (t : ParTie T.Q h.pins.1 F) {L : CmList (ambOf T.Q h.pins.1)}
  {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C) {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (k : Kits F L C jC ng)

def LocTie : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p,
  HEq (T.G.P.loc (T.G.dat j) p) ((k.at (datW D F.κg j)).pad.loc p)

variable {h t K R k}

theorem rk_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.rk (T.G.dat j) = (datW D κ j).N :=
  (h.datum_condition j h1 hm).1.trans (datW_N D κ j).symm

theorem jj_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.jj (T.G.dat j) = (datW D κ j).j :=
  (h.datum_condition j h1 hm).2.trans (datW_j D κ h1 hm.le).symm

theorem LocTie.samePt (H : LocTie h k) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η') :
    (T.G.P.loc (T.G.dat j) p).fld η = ((k.at (datW D F.κg j)).pad.loc p).fld η' ∧
      (∃ e : (T.G.P.loc (T.G.dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] ((k.at (datW D F.κg j)).pad.loc p).Ylat η',
        ∀ a b, ((k.at (datW D F.κg j)).pad.loc p).be η' (e a) (e b) = (T.G.P.loc (T.G.dat j) p).be η a b) ∧
      ((T.G.P.loc (T.G.dat j) p).good η ↔ ((k.at (datW D F.κg j)).pad.loc p).good η') ∧
      (T.G.P.loc (T.G.dat j) p).phiCy η = ((k.at (datW D F.κg j)).pad.loc p).phiCy η' ∧
      (T.G.P.loc (T.G.dat j) p).dP η = ((k.at (datW D F.κg j)).pad.loc p).dP η' :=
  samePt_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm p) he

theorem LocTie.lat (H : LocTie h k) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {la : HeightOneSpectrum (𝓞 T.Q.c.F)}
    {z : PointsOfFlagModel.Pt (T.G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : T.G.IsAlgPt j la z) {η : T.G.PY j (WeightAlgebra.resCh la)}
    (hr : T.G.rel j _ η z)
    {η' : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Pt ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).YY}
    (he : HEq η η') (A : DatAt ((T.G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1) :
    ∃ e : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Ylat η' ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).be η' a b :=
  lat_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm _) he (fun a b => A.beta a b)
    (h.lattice_condition j h1 hm la z hz η hr A)


example {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η')
    (hη : (T.G.P.loc (T.G.dat j) p).good η) (hη' : ¬ ((k.at (datW D F.κg j)).pad.loc p).good η') : ¬ LocTie h k :=
  fun H => hη' ((H.samePt h1 hm he).2.2.1.1 hη)

example {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η')
    (hne : (T.G.P.loc (T.G.dat j) p).phiCy η ≠ ((k.at (datW D F.κg j)).pad.loc p).phiCy η') : ¬ LocTie h k :=
  fun H => hne (H.samePt h1 hm he).2.2.2.1

section Phi

variable {P : FormsOver K R k} (hg : F.κg.primes = Finset.univ.image D.host.g)
  {I : Type} {dat : I → Dat D (Lv (ambOf T.Q h.pins.1))} (hI : ∀ i, (dat i).Indef) {iW : ℕ → I}
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D (famOf K R k hg P).κg j)

end Phi

end Comparison₂

end GlobalTheory.ShFam
end
end

section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

variable {D : D7}

def KitClass.Ex (Q : KitClass D) : Prop :=
  ∀ A N j S κ s L jC, jC.Pinned → ∃ k d, Q A N j S κ s L jC k d

def KitClass.Loc (Q : KitClass D) : Prop :=
  ∀ A N j S κ s L jC k d, jC.Pinned → Q A N j S κ s L jC k d →
    ∃ (F : StFam S κ) (cts : Ats S κ), cts.Over jC ∧ LocSt.ofPkg k.pad = locStOf F cts

structure FamOver (Q : KitClass D) (T : Top D) (h : LawsP T) (c : ℕ) : Type 1 where
  F : SrcFam (ambOf T.Q h.pins.1)
  t : ParTie T.Q h.pins.1 F
  exp : F.κs.l.A = 15 ^ c
  L : CmList (ambOf T.Q h.pins.1)
  jC : JC D
  pin : jC.Pinned
  k : Kits F L (cxSt D.what₂.LL) jC ngTrue
  d : ∀ N j hN hj κ, (F.src N j hN hj κ).Comp → D.what₂.Tau → ℝ
  mem : ∀ N j hN hj κ, Q _ N j _ κ (F.src N j hN hj κ) L jC (k N j hN hj κ) (d N j hN hj κ)
  hg : F.κg.primes = Finset.univ.image D.host.g
  P : FormsOver (cutSt _) (resSt _) k
  forms : FormsAre h t (cutSt _) (resSt _) k P
  prov : ∃ (I : Type) (dat : I → Dat D (Lv (ambOf T.Q h.pins.1))) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I),
    (∀ w : Dat D (Lv (ambOf T.Q h.pins.1)), w.Indef → ∃ i, (dat i).N = w.N ∧ (dat i).j = w.j ∧ (dat i).κ = w.κ) ∧
    (∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) ∧
    T.G.P = indefiniteDataFamily (shimOf (cutSt _) (resSt _) k) I dat hI ∧ ∀ j, 1 ≤ j → j < D.R.m → HEq (T.G.dat j) (iW j)

namespace FamOver

variable {Q : KitClass D} {T : Top D} {h : LawsP T} {c : ℕ} (Φ : FamOver Q T h c)

def fam : ShimFam D (geoTrue D.what₂.LL) (Lv (ambOf T.Q h.pins.1)) := famOf (cutSt _) (resSt _) Φ.k Φ.hg Φ.P

def dH (j : ℕ) : (Φ.fam.Uw j).Comp → D.what₂.Tau → ℝ :=
  Φ.d _ _ (datW D Φ.F.κg j).two_le (datW D Φ.F.κg j).j_le (datW D Φ.F.κg j).κ


def Reads (X₀ : DivX D)
    (iM : ∀ j (a : (Φ.fam.Uw j).Comp), (X₀.MjH j).V →ₗ[D.what₂.LL] (geoTrue D.what₂.LL).Fn ((Φ.fam.Uw j).alg.Yv a)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (∀ x, (∀ a, iM j a x = 0) → x = 0) ∧
    ∃ (w : WeightFamilies.Wt D j) (s : Submodule Φ.P.KO (Φ.P.Cusp j w)) (φ : s →ₛₗ[Φ.P.sig0] D.what₂.Mj j),
      w.n = D.R.nV ∧ Formalism.L2.Geo.wtOf w = DV.kapW D j ∧ Submodule.span ℂ (Set.range φ) = ⊤ ∧
      (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
      (∀ x : s, (x : Φ.P.Cusp j w) ∈ Φ.P.Mlat j w ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
      (∃ vol : ℝ, ∀ x : s, ‖φ x‖ = Real.sqrt (vol * dimKap D j) * Φ.P.l2NormAlt j w Φ.P.sig0 x) ∧
      ∀ (f : s) x, X₀.jM j x = φ f → ∀ a, iM j a x = Φ.P.cmp j w a f

end FamOver

def IsGeoOf (Q : KitClass D) (J : Core D) (c : ℕ) (X : DivX D) : Prop :=
  ∃ (T : Top D) (h : LawsP T) (Φ : FamOver Q T h c) (X₀ : DivX D) (iM : _) (hiM : _), T.toCore = J ∧
    X = GlobalTheory.VarietyModelRecord.record X₀ Φ.fam iM hiM Φ.dH ∧ Φ.Reads X₀ iM ∧ X.vdd = fun p _ => vDiff D.host.E p

def LargeFor (Q : Par D) (h : Q.PinHost) (c : ℕ) : Prop :=
  IsLargeFor (ambOf Q h) (D.host.g 0 * D.host.g 1) ∧ IsLargeFor (ambOf Q h) (Nat.lcm (D.host.g 0 * D.host.g 1) (15 ^ c))

end GlobalTheory.ShFam
end
end
