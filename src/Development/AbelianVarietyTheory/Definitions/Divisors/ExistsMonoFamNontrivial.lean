import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartOfPeriodTauMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcWitnessModelPoint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFan

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out.InhTate
open GlobalTheory.Toroidal GlobalTheory.ToricData

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart.Model

theorem gm_gv {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (a : Γ(Y, ⊤)ˣ) :
    gm r z V (InhTate.gv a V) = gm (𝟙 Z) z ⊤ (pullTop r a) := by
  rw [InhTate.gv, gm_res r z _ h]
  have := gm_pull (𝟙 Z) r z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem val_const {W Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ W)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb (Inh.trivLB W) φ ε)} {a : Γ(Y, ⊤)ˣ} (h : IsConst t a) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ W) → (Inh.trivLB W).ι) : Geo.Tor.val t r z J = gm (𝟙 Z) z ⊤ (pullTop r a) := by
  have hm : r z ∈ LB.wchart (Inh.trivLB W) φ (fun k => J (r ≫ φ k)) := by rw [wchart_triv]; trivial
  exact (congrArg (gm r z _) (h _)).trans (gm_gv r z _ hm a)


theorem good_triv {W Z : Scheme.{0}} (z : Z) : Good (Inh.trivLB W) z (fun _ => PUnit.unit) := fun _ => trivial

theorem gm_eq_of_top {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {V : Y.Opens} (hV : V = ⊤) (a : Γ(Y, V)ˣ) :
    gm r z V a = gm (𝟙 Z) z ⊤ (pullTop r (res hV.ge a)) := by
  subst hV
  rw [← gm_gv r z (⊤ : Y.Opens) (show r z ∈ (⊤ : Y.Opens) from trivial), InhTate.gv, res_self, res_self]

theorem one_isGen {W Y : Scheme.{0}} (f g : Y ⟶ W) :
    LB.Gen.IsGen (⟨fun _ => 1⟩ : LB.Iso ((Inh.trivLB W).pull f) ((Inh.trivLB W).pull g)) := by
  intro i j
  have hg : (LB.div ((Inh.trivLB W).pull g) ((Inh.trivLB W).pull f)).g i j = 1 := by
    have h₁ := Inh.linComb_triv_g (fun _ : PUnit => f) (fun _ => 1) i.2 j.2
    have h₂ := Inh.linComb_triv_g (fun _ : PUnit => g) (fun _ => 1) i.1 j.1
    unfold LB.div
    dsimp only
    rw [h₁, h₂, map_one, map_one, inv_one, _root_.mul_one]
  rw [hg, _root_.one_mul]
  rfl

theorem constHom_apply {R k : Type} [CommRing R] [Field k] (ρ : R →+* DualNumber k) (r : R) :
    constHom ρ r = TrivSqZeroExt.inl (ρ r).fst := rfl


variable {R : Type} [CommRing R] [IsDomain R] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (q : X → (FractionRing R)ˣ) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ X)



abbrev A : Type := PowerSeries (PowerSeries ℚ)

abbrev tt : A := PowerSeries.X

abbrev ss : A := PowerSeries.C PowerSeries.X

theorem ss_mem : ss ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C,
    PowerSeries.isUnit_iff_constantCoeff]
  simp

theorem isUnit_one_add {x : A} (h : x ∈ maximalIdeal A) : IsUnit (1 + x) := by
  have := isUnit_one_sub_self_of_mem_nonunits (-x) ((mem_maximalIdeal _).1 (neg_mem h))
  simpa using this

def frm : LinearMap.BilinForm ℤ (ℤ × ℤ) := LinearMap.mk₂ ℤ (fun y z => 2 * (y.1 * z.1 + y.2 * z.2))
  (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

def nrm (y : ℤ × ℤ) : ℕ := (y.1 * y.1 + y.2 * y.2).toNat


def per (v : Aˣ) (b : ℤ × ℤ → ℤ) (y : ℤ × ℤ) : (FractionRing A)ˣ :=
  Units.mk0 (algebraMap A _ (tt ^ nrm y * (v ^ b y : Aˣ)))
    ((map_ne_zero_iff _ (IsFractionRing.injective A _)).2
      (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (Units.ne_zero _)))




def tang : A →+* DualNumber ℚ := RingHom.comp
  { toFun := fun f : PowerSeries ℚ => TrivSqZeroExt.inl (PowerSeries.constantCoeff f) + TrivSqZeroExt.inr (PowerSeries.coeff 1 f)
    map_one' := by ext <;> simp [PowerSeries.coeff_one]
    map_mul' := fun f g => by
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
          TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, PowerSeries.coeff_mul]
        rw [Finset.Nat.antidiagonal_succ]
        first
          | (simp [PowerSeries.coeff_zero_eq_constantCoeff]; done)
          | (simp [PowerSeries.coeff_zero_eq_constantCoeff]; ring)
    map_zero' := by ext <;> simp
    map_add' := fun f g => by ext <;> simp [add_add_add_comm] } PowerSeries.constantCoeff





def vs : Aˣ := (isUnit_one_add ss_mem).unit

def vts : Aˣ := (isUnit_one_add (Ideal.mul_mem_left _ tt ss_mem)).unit






end GlobalTheory.RigChart.Model
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def Classifies (Xo : Moduli Dw l) (c : Coeff l) {T T' : Scheme.{0}} (t : SAB H T) (g : T' ⟶ T) (y : T' ⟶ Xo.XF c) : Prop :=
  ∃ t' : SAB H T', Nonempty (SABMap t' t g) ∧ Nonempty (SABMap t' Xo.univ.t (y ≫ pullback.fst _ _))

theorem genOf_iff (Xo : Moduli Dw l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : GlobalTheory.UPoinc.GenOf Xo c y t ↔ Classifies Xo c t (jK R) y := Iff.rfl

theorem Classifies.pull {Xo : Moduli Dw l} {c : Coeff l} {T T' T'' : Scheme.{0}} {t : SAB H T} {g : T' ⟶ T}
    {y : T' ⟶ Xo.XF c} (h : Classifies Xo c t g y) (f : T'' ⟶ T') : Classifies Xo c t (f ≫ g) (f ≫ y) := by
  obtain ⟨t', ⟨m₁⟩, ⟨m₂⟩⟩ := h
  obtain ⟨t'', ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull f t'
  exact ⟨t'', GlobalTheory.TraitOrder.comp rfl m₁ n, GlobalTheory.TraitOrder.comp (Category.assoc _ _ _).symm m₂ n⟩

structure Fam (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] where

  b : c.F →+* R

  t : SAB H (Sp R)

  P : PELUnif (maximalIdeal R) t

  y : Sp (FractionRing R) ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = jK R ≫ spMap b
  gen : GlobalTheory.UPoinc.GenOf Xo c y t

structure MonoFam (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] extends Fam Xo c R where

  m : ℕ

  s : Fin m → R
  s_mem : ∀ i, s i ∈ maximalIdeal R

  δ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X
  cone : IsCone H.bar φ δ
  rank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q
  mono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i)

variable {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

abbrev Gens {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) : Type :=
  ∀ a b : Q.X, LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (a + b)).left, (Q.c a).left, (Q.c b).left, (Q.c 0).left]
    ![-1, 1, 1, -1])

def TauIn {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V)
    (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.P.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J


def lamUnit {B B₀ B' Z : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {π₁ : B' ⟶ B} {π₀ : B' ⟶ B₀}
    (w : LB.Iso (M.pull π₁) (M₀.pull π₀)) {X : Type} [AddCommGroup X] (x : X → (Z ⟶ B')) (a b : X) (z : Z)
    (J : (Z ⟶ B) → M.ι) (J₀ : (Z ⟶ B₀) → M₀.ι) : (Z.presheaf.stalk z)ˣ :=
  gw w (x (a + b)) z (J₀ (x (a + b) ≫ π₀)) (fun _ => J (x (a + b) ≫ π₁)) *
    (gw w (x a) z (J₀ (x a ≫ π₀)) (fun _ => J (x a ≫ π₁)))⁻¹ *
    (gw w (x b) z (J₀ (x b ≫ π₀)) (fun _ => J (x b ≫ π₁)))⁻¹ *
    gw w (x 0) z (J₀ (x 0 ≫ π₀)) (fun _ => J (x 0 ≫ π₁))

def SepAt {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) {m : ℕ} (s : Fin m → V)
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s i) = 0) ∧
  ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
    (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
    (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (α : Fin m → Kˣ),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧
    w.IsGen ∧
    (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) ∧
    ∀ a b τ₀, GlobalTheory.RigChart.IsUnitTau Q s gam a b τ₀ →
      ∃ τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]), τ₁.IsGen ∧
        ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val τ₀ (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (∏ i, α i ^ gam i a b)) * val τ₁ (spMap k₀.subtype) z J₀

abbrev DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  GlobalTheory.Poinc.Sep.DefOver k₀ P

def Sep (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (C : MonoFam Xo c φ V), GlobalTheory.Mum.Base V →
    ∀ ξ : Sp V ⟶ S, C.y ≫ j = jK V ≫ ξ →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) →
      SepAt C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ev k₀

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def OpenCls (C : MonoFam Xo c φ R) : Prop :=
  ∃ (yo : Sp (Localization.Away (∏ i, C.s i)) ⟶ Xo.XF c) (tO : SAB H (Sp (Localization.Away (∏ i, C.s i)))),
    Nonempty (SABMap tO C.t (spMap (algebraMap R (Localization.Away (∏ i, C.s i))))) ∧
    Nonempty (SABMap tO Xo.univ.t (yo ≫ pullback.fst _ _)) ∧
    ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, C.s i)),
      g ≫ spMap (algebraMap R (Localization.Away (∏ i, C.s i))) = jK R → g ≫ yo = C.y


def Inj (C : MonoFam Xo c φ R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R',
    Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ →
    ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ →
      κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁ = θ₂

def PointRigid (C : MonoFam Xo c φ R) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → SepAt C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ev k₀ →
    (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀

def IsTaut {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)) : Prop :=
  ∃ hm : C.m = m, (∀ i, C.s i = bdParam k m e (Fin.cast hm i)) ∧ OpenCls C ∧ Inj C ∧
    (GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ∧ PointRigid C ∧
      ((residue (ChartRing k m e)).comp C.b).EssFiniteType) ∧
    (∃ (N : ℕ) (s : Fin C.m ⊕ Fin N → ChartRing k m e)
      (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
      (∀ i, s (.inl i) = C.s i) ∧ (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) ∧ (∀ k, IsUnit (s (.inr k))) ∧
      TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X))) ∧
    (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra;
      ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim)

def UPre (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S)
    (a : Fin C.m → ℕ),
    IsTaut C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧
    (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i}

theorem Fam.rank_le [IsNoetherianRing R] (C : Fam Xo c R) :
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  haveI : CharZero R := C.b.charZero_iff C.b.injective |>.1 inferInstance
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let u : Sp K ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) K)
  have hu : u ≫ jK R = spMap f := (Spec.map_comp _ _).symm
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective ((u ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s)
  have hdet := (Xo.univ.geom K _ β₀.hom hβ₀.symm).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (u ≫ C.y ≫ pullback.fst _ _) τ N →
      Module.finrank (𝓞 E) C.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act u τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act C.t.act m₁.act u τ N).1 h₅
    rw [hu] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem level_pos (l : Geo.Tor.Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

theorem MonoFam.s_ne_zero (C : MonoFam Xo c φ R) (i : Fin C.m) : C.s i ≠ 0 := by
  intro h0
  have hy : ∃ y, C.δ i y y ≠ 0 := by
    by_contra hn
    push Not at hn
    refine C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => ?_)
    have := hn (a + b)
    simp only [map_add, LinearMap.add_apply, hn, (C.cone.mem i).1 b a] at this
    simp only [LinearMap.zero_apply]
    omega
  obtain ⟨y, hy⟩ := hy
  obtain ⟨u, n, hn, e⟩ := C.mono y
  have hni : n i ≠ 0 := fun h1 => by
    have := hn i
    simp only [h1, LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero, mul_eq_zero] at this
    exact this.elim (by exact_mod_cast (level_pos l).ne') hy
  exact GlobalTheory.PsiCoordLocal.ne_zero_of_coord e (by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0, zero_pow hni]), mul_zero])

theorem MonoFam.exists_tauIn (C : MonoFam Xo c φ R) :
    ∃ τ₀ : Gens C.P.D.toPre, TauIn C.P.D.toPre τ₀ C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  choose τ₀ h using GlobalTheory.UnitTau.exists_isUnitTau C.P.D.toPre C.s _ C.mono
    (fun i y z => by simp only [LinearMap.smul_apply, (C.cone.mem i).1 y z]) C.s_ne_zero
  exact ⟨τ₀, h⟩


theorem Fam.exists_monoFam [IsNoetherianRing R] (C : Fam Xo c R) (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) {u : R}
    (hu : u ∈ maximalIdeal R) {β : LinearMap.BilinForm ℤ C.P.D.toPre.X} (hβ : β ∈ balForms H.bar C.P.D.toPre.X)
    (h : IsMonomial C.P.D.toPre ![u] ![(l.M' : ℤ) • β]) : ∃ C' : MonoFam Xo c φ R, C'.toFam = C := by
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  have hM : (0 : ℤ) < l.M' := by exact_mod_cast level_pos l
  have h0 : ∀ y, 0 ≤ β y y := fun y => nonneg_of_mul_nonneg_right (h.nonneg 0 y) hM
  obtain ⟨m, δ, cf, hδ, hcf, hsum⟩ := GlobalTheory.ConeInterior.exists_pos_comb (hφ _ C.rank_le) hβ
    (toReal_mem_psdCone_of_nonneg E H _ β hβ h0)
  refine ⟨⟨C, m, fun i => u ^ cf i, fun i => Ideal.pow_mem_of_mem _ hu _ (hcf i), δ, hδ, C.rank_le, fun y => ?_⟩, rfl⟩
  obtain ⟨v, n, hn, hc⟩ := h y
  have ev : ∀ i, ∃ k : ℕ, ((l.M' : ℤ) • δ i) y y = 2 * k := fun i => by
    have h1 := apply_self_eq_two_mul ((balForms_eq_levelForms H C.P.D.toPre.X).le (hδ.mem i)) y
    have h2 := hδ.nonneg i y
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ δ i y (H.w0 • y) by omega)
    exact ⟨l.M' * k, by rw [LinearMap.smul_apply, LinearMap.smul_apply, h1, hk]; push_cast; simp; ring⟩
  choose k hk using ev
  have e : n 0 = ∑ i, cf i * k i := by
    have h1 : ((l.M' : ℤ) • β) y y = 2 * n 0 := hn 0
    have h2 : ((l.M' : ℤ) • β) y y = ∑ i, cf i * ((l.M' : ℤ) • δ i) y y := by
      simp only [hsum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, nsmul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hk] at h2
    have : (2 : ℤ) * n 0 = 2 * ((∑ i, cf i * k i : ℕ) : ℤ) := by
      rw [← h1, h2]; push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    omega
  refine ⟨v, k, hk, ?_⟩
  simpa only [Fin.prod_univ_one, Matrix.cons_val_zero, e, ← pow_mul, Finset.prod_pow_eq_pow_sum] using hc


section Tests

open GlobalTheory.RigChart GlobalTheory.RigChart.Model GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.InhTate

variable {V : Type} [CommRing V] [IsDomain V] {m : ℕ} {K : Type} [Field K]


theorem exists_val_eq (k₀ : Subfield K) {Y : Scheme.{0}} {M : LB Y} {I : Type} [Fintype I] {p : I → (Sp k₀ ⟶ Y)} {n : I → ℤ}
    (τ : LB.Gen (LB.LinComb M p n)) {z : Sp K} {J : (Sp K ⟶ Y) → M.ι} (hJ : Good M z J) :
    ∃ x : k₀ˣ, val τ (spMap k₀.subtype) z J = gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) := by
  have : Subsingleton (Sp k₀) := inferInstanceAs (Subsingleton (PrimeSpectrum k₀))
  have ht : LB.wchart M p (fun k => J (spMap k₀.subtype ≫ p k)) = ⊤ :=
    top_unique fun q _ => Subsingleton.elim (spMap k₀.subtype z) q ▸ hJ.mem p _
  obtain ⟨x, hx⟩ := unitOn_bijective.2 (res ht.ge (τ.s fun k => J (spMap k₀.subtype ≫ p k)))
  exact ⟨x, (gm_eq_of_top _ z ht _).trans (congrArg _ (hx ▸ pullTop_unitOn k₀.subtype x))⟩

theorem one_isGen₂ {W W' Y : Scheme.{0}} (f : Y ⟶ W) (g : Y ⟶ W') :
    LB.Gen.IsGen (⟨fun _ => 1⟩ : LB.Iso ((Inh.trivLB W).pull f) ((Inh.trivLB W').pull g)) := by
  intro i j
  have hg : (LB.div ((Inh.trivLB W').pull g) ((Inh.trivLB W).pull f)).g i j = 1 := by
    have h₁ := Inh.linComb_triv_g (fun _ : PUnit => f) (fun _ => 1) i.2 j.2
    have h₂ := Inh.linComb_triv_g (fun _ : PUnit => g) (fun _ => 1) i.1 j.1
    unfold LB.div
    dsimp only
    rw [h₁, h₂, map_one, map_one, inv_one, _root_.mul_one]
  rw [hg, _root_.one_mul]
  rfl

theorem exists_iso_pull_pull {B B₀ B' : Scheme.{0}} {M : LB B} (hM : M.IsLB) (β : B₀ ⟶ B) (π : B' ⟶ B₀) :
    ∃ w : LB.Iso (M.pull (π ≫ β)) ((M.pull β).pull π), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) (j k : PUnit → M.ι), β (π (f z)) ∈ M.U (j PUnit.unit) →
        β (π (f z)) ∈ M.U (k PUnit.unit) →
        gw w f z j k = gm (f ≫ π ≫ β) z _ (M.g (j PUnit.unit) (k PUnit.unit)) := by
  have le : ∀ p : (PUnit → PUnit → M.ι) × (PUnit → M.ι), ((M.pull β).pull π).U p.1 ⊓ (M.pull (π ≫ β)).U p.2 ≤
      (π ≫ β) ⁻¹ᵁ (M.U (p.1 PUnit.unit PUnit.unit) ⊓ M.U (p.2 PUnit.unit)) := fun p y hy =>
    ⟨(mem_pull (F := β)).1 ((mem_pull (F := π)).1 hy.1), (mem_pull (F := π ≫ β)).1 hy.2⟩
  let w : LB.Iso (M.pull (π ≫ β)) ((M.pull β).pull π) := ⟨fun p => res (le p) (pullU (π ≫ β) _ (M.g _ _))⟩
  have hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) (j k : PUnit → M.ι), β (π (f z)) ∈ M.U (j PUnit.unit) →
      β (π (f z)) ∈ M.U (k PUnit.unit) →
      gw w f z j k = gm (f ≫ π ≫ β) z _ (M.g (j PUnit.unit) (k PUnit.unit)) := fun Z f z j k hj hk =>
    (gm_res f z (le (fun _ => j, k)) ⟨mem_pull.2 (mem_pull.2 hj), mem_pull.2 hk⟩ _).trans
      (gm_pull f (π ≫ β) z (M.U (j PUnit.unit) ⊓ M.U (k PUnit.unit)) ⟨hj, hk⟩ _)
  refine ⟨w, (isGen_iff w).2 fun Z f z j j' k k' hj hj' hk hk' => ?_, hw⟩
  have a₁ := mem_pull.1 hj
  have a₂ := mem_pull.1 hj'
  have a₃ := mem_pull.1 hk
  have a₄ := mem_pull.1 hk'
  rw [hw Z f z j k a₁ a₃, hw Z f z j' k' a₂ a₄, gm_pull_g M β (f ≫ π) z j j' hj hj', gm_pull_g M (π ≫ β) f z k k' hk hk',
    Category.assoc, mul_right_comm, gm_cocycle hM (f ≫ π ≫ β) z a₁ a₂ a₄, ← gm_cocycle hM (f ≫ π ≫ β) z a₁ a₃ a₄,
    mul_inv_cancel_right]







end Tests

end GlobalTheory.UChart
end
end
