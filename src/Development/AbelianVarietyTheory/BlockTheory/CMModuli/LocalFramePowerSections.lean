import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections

abbrev PowSec {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (N : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (N : ℤ)))

def IsTrait {R₁ W : Type} [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W)
    (κ : FractionRing R₁ →+* FractionRing W) : Prop :=
  GlobalTheory.UU.CDVR W ∧ κ.comp (algebraMap R₁ (FractionRing R₁)) = (algebraMap W (FractionRing W)).comp ρ

section Frames

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G)

def IsCombAt {K W : Type} [Field K] [CommRing W] [IsDomain W] (y : Sp K ⟶ S) (κ : K →+* FractionRing W) (N : ℕ) {r : ℕ}
    (s : Fin r → PowSec L.L (pullback.fst G.hom y) N) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (LW : RigLB GW)
    (φ : ((Over.pullback (Out.jK W)).obj GW).left ⟶ G.left)
    (w : LB.Iso (LW.L.pull (pullback.fst GW.hom (Out.jK W))) (L.L.pull φ))
    (σ : PowSec LW.L (𝟙 GW.left) N) (a : Fin r → W) : Prop :=
  ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (Out.jK W)).obj GW).left) (x' : T ⟶ pullback G.hom y),
    x' ≫ pullback.fst G.hom y = x ≫ φ → x' ≫ pullback.snd G.hom y = x ≫ pullback.snd GW.hom (Out.jK W) ≫ spMap κ →
    ∀ (z : T) (JW : (T ⟶ GW.left) → LW.L.ι) (J : (T ⟶ G.left) → L.L.ι), Good LW.L z JW → Good L.L z J →
      (gw w x z (J (x ≫ φ)) (fun _ => JW (x ≫ pullback.fst GW.hom (Out.jK W)))).val ^ N *
          sval σ (x ≫ pullback.fst GW.hom (Out.jK W)) z JW =
        ∑ k, gs (x ≫ pullback.fst GW.hom (Out.jK W)) z ⊤ (Out.scal GW.hom (a k)) * sval (s k) x' z J

omit [IsCommMonObj G] [GrpObj G] in

def TraitDense : Prop :=
  IsReduced S ∧ ∀ V : S.Opens, (V : Set S).Nonempty → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W)
    (ξ : Sp W ⟶ S), GlobalTheory.UU.CDVR W ∧ Set.range ξ ⊆ V ∧ Set.range (Out.jK W ≫ ξ) ⊆ abLocus G

end Frames

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  (Xo : Moduli D l) {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def GoodRedAt {W : Type} [CommRing W] [IsDomain W] (v₀ : Sp (FractionRing W) ⟶ Xo.X) : Prop :=
  ∃ (t : SAB H (Sp W)) (t' : SAB H (Sp (FractionRing W))) (_ : SABMap t' t (Out.jK W)) (_ : SABMap t' Xo.univ.t v₀),
    IsProper t.G.hom

def ArcDataAt {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) {W : Type} [CommRing W]
    [IsDomain W] [IsLocalRing W] (f : O' →+* W) (u : W) (v₀ : Sp (FractionRing W) ⟶ Xo.X) : Prop :=
  ∃ (t : SAB H (Sp W)) (t' : SAB H (Sp (FractionRing W))) (m₁ : SABMap t' t (Out.jK W)) (m₂ : SABMap t' Xo.univ.t v₀)
    (P : PELUnif (IsLocalRing.maximalIdeal W) t) (φ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X),
    letI := H.starRing
    IsGrpPullback P.D.toPre.P.A a.D₀.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.D.toPre.P.A) (fun _ => 1)) P.D.toPre.rig
      (rigPullOf φ (spMap f) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (P.oD.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.D.toPre.c (e y)).left ≫ φ = spMap f ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing O') F] (uF : F),
      (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing W) F (algebraMap W _ (f x))) →
      uF = algebraMap (FractionRing W) F (algebraMap W _ u) →
      (∀ y, GenRel w (LB.pullGen _ _ _ (P.D.toPre.psi (e y)) (Out.jFK (R := W) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F)) (uF ^ (a.be y y / 2))) ∧
      ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
        ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Xo.univ.etaA v) ∨
          (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
            HEq p₀ (a.eta v) ∧ σ = Xo.univ.eta v)) →
        ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := W) F ⟶ P.A.A)
          (x' : Sp F ⟶ t'.G.left), QkExt (algebraMap _ F) p₀ q₀ → q.y = e q₀.y →
          (∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / k))) →
          x' ≫ m₁.φ = x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK W) →
          x' ≫ m₂.φ = (spMap (algebraMap (FractionRing W) F) ≫ v₀) ≫ σ.left →
          P.ToA F k q x

def DataAtTraits {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) {R₁ : Type} [CommRing R₁]
    [IsDomain R₁] (f : PowerSeries O' →+* R₁) (y : Sp (FractionRing R₁) ⟶ Xo.XF c) : Prop :=
  CharZero R₁ ∧ Function.Injective (f.comp (PowerSeries.C (R := O'))) ∧ f PowerSeries.X ≠ 0 ∧
    y ≫ pullback.snd _ _ ≫ spMap β = Out.jK R₁ ≫ spMap f ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b ∧
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W) (κ : FractionRing R₁ →+* FractionRing W),
      IsTrait ρ κ →
      (¬ IsUnit (ρ (f PowerSeries.X)) →
        ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (i : W →+* W')
          (κ' : FractionRing R₁ →+* FractionRing W'), Function.Injective i ∧ i.Finite ∧ IsTrait (i.comp ρ) κ' ∧
          ArcDataAt Xo a (((i.comp ρ).comp f).comp (PowerSeries.C (R := O'))) (i (ρ (f PowerSeries.X)))
            (spMap κ' ≫ y ≫ pullback.fst _ _)) ∧
      (IsUnit (ρ (f PowerSeries.X)) → GoodRedAt Xo (spMap κ ≫ y ≫ pullback.fst _ _))

end Data

example (p : ℕ) [Fact p.Prime] : IsTrait (RingHom.id ℤ_[p]) (RingHom.id _) :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, rfl⟩

example {R₁ W : Type} [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [IsLocalRing W] {ρ : R₁ →+* W} {κ}
    (h : IsTrait ρ κ) : Function.Injective ρ := by
  have : Function.Injective ((algebraMap W (FractionRing W)).comp ρ) := by
    rw [← h.2]; exact κ.injective.comp (IsFractionRing.injective R₁ _)
  exact Function.Injective.of_comp (f := algebraMap W (FractionRing W)) this

end GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections
end
