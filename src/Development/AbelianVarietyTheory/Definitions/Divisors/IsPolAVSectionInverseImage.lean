import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel

noncomputable section

namespace GlobalTheory.MBLow

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

def MuGe (h : HermFam K (Fin m → K)) (E : Submodule (𝓞 K) (Fin m → K)) (ν : ℝ) : Prop :=
  ∀ V : Submodule K (Fin m → K), ((m : ℝ) - Module.finrank K V) * ν ≤ deg h E - deg h (E ⊓ V.restrictScalars (𝓞 K))

end Lat

def IsOver {K : Type} [Field K] [NumberField K] (F : SemiFib K) {K'' : Type} [Field K''] [NumberField K''] [Algebra K K'']
    {P : Out.PolAV (Sp K'')} (ψ : P.A.left ⟶ F.P₀.A.left) {AA : Over (Sp (𝓞 K''))} [GrpObj AA]
    (φ : P.A.left ⟶ AA.left) : Prop :=
  IsPolFibre (algebraMap K K'') F.P₀ P ψ ∧ ∃ j : AA.left ⟶ F.G.left,
    IsGrpPullback AA F.G (spMap (algebraMap (𝓞 K) (𝓞 K''))) j ∧ φ ≫ j = ψ ≫ F.φ

end GlobalTheory.MBLow

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section Translates

variable {S : Scheme.{0}} (P : PolAV S)

def IsPolAVSectionInverseImage (T : Over S) (s : P.L.Sec) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) : Prop :=
  ∀ (i : P.L.ι) (h : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => i) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U i),
    t.f (fun _ => i) = ((snd T P.A).left.appLE _ _ h).hom (s.f i)

def OnT (T : Over S) (n : ℕ) (s : (lbPow P.L n).Sec) (t : LB.Sec (LPow P.A P.L (n : ℤ) T)) : Prop :=
  ∀ (i : P.L.ι) (h : (LPow P.A P.L (n : ℤ) T).U (fun _ => i) ≤ (snd T P.A).left ⁻¹ᵁ (lbPow P.L n).U (fun _ => i)),
    t.f (fun _ => i) = ((snd T P.A).left.appLE _ _ h).hom (s.f (fun _ => i))

def Tr (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {T : Over S} (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T))
    (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T) (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)),
    α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ t

def FinOrdT {k : ℤ} {T : Over S} (U : ThetaGrp P.A P.L k T) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ U.pt ^ n = 1 ∧ LB.Gen.Corr P.L _ _ _ _ (powGen P.A P.L k U n) (LB.oneGen P.L)

def ThJetT (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {B : Type} [CommRing B] (s : Sp B ⟶ S)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk s))) {I : Type} (pt : I → (Over.mk s ⟶ P.A)) {g : ℕ}
    (y : Fin g → (Sp (DualNumber B) ⟶ (Over.mk s ⊗ P.A).left)) (ϑ : I → B) (J : I → Fin g → B) : Prop :=
  ∃ (U : I → ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)) (t : I → LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)))
    (i₀ : P.L.ι) (c : Fin g → B),
    (∀ i, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr P ρ m th (U i) (t i)) ∧
    ⊤ ≤ (s ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
    ∀ i j, valR (y j) ((LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)).U fun _ => i₀) ((t i).f fun _ => i₀) =
      TrivSqZeroExt.inl (valR s ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ (m ^ 2)) *
        (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i))

end Translates

def epsLift {R : Type} [CommRing R] {A : Over (Sp R)} (v : epsR R ⟶ A) :
    Sp (DualNumber R) ⟶ (baseOver (Sp R) ⊗ A).left :=
  (lift (Over.homMk (epsR R).hom (by simp) : epsR R ⟶ baseOver (Sp R)) v).left

def ThJet {R : Type} [CommRing R] (x : KeyIn R) {g : ℕ} (hg : x.P.g = g) (m : ℕ) {I : Type}
    (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (ϑ : I → R) (J : I → Fin g → R) : Prop :=
  ∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧
    ThJetT x.P x.rig m (𝟙 (Sp R)) th pt (fun j => epsLift (x.v (j.cast hg.symm))) ϑ J

def Rule4 (κ : Rule) : Prop := Homog (fun _ => 1) κ ∧ Funct κ ∧ ThetaOne κ ∧ FamUnit κ

def KapF (κ : Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → Nonempty (C ≃+* ℂ) →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) →
      ‖c‖ ^ 8 * ‖algebraMap (FractionRing V) C (κ (FractionRing V) x : FractionRing V)‖ = 1

def Deform (κ : Rule) {C : Type} [NormedField C] [CharZero C] (e : C →+* ℂ) (x : KeyIn C) {g : ℕ} (hg : x.P.g = g) (m : ℕ)
    (ζ : Cˣ) (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) : Prop :=
  ∃ (Θ : (Fin (2 * g) → ZMod (m ^ 2)) → PowerSeries C) (Γ : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → PowerSeries C) (π : C) (b : ℝ),
    ‖π‖ < 1 ∧ (∀ a n, ‖PowerSeries.coeff n (Θ a)‖ ≤ b ∧ ∀ j, ‖PowerSeries.coeff n (Γ a j)‖ ≤ b) ∧
    ThJet x hg m (levelPoint lev hg) (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n)
      (fun a j => ∑' n, PowerSeries.coeff n (Γ a j) * π ^ n) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a, (Summable fun n => ‖e (PowerSeries.coeff n (Θ a)) * u ^ n‖) ∧
        ∀ j, Summable fun n => ‖e (PowerSeries.coeff n (Γ a j)) * u ^ n‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n)
          (fun a j => ∑' n, e (PowerSeries.coeff n (Γ a j)) * u ^ n) ∧ (κ ℂ x₀ : ℂ) = e k

def Transfer (κ : Rule) : Prop :=
  ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀,
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      (e : C →+* ℂ) (x : KeyIn C) (hg : x.P.g = g) (ζ : Cˣ) (lev : Out.Level x.P ((n ^ j) ^ 2) (unitOn ζ)) (k : C),
      Deform κ e x hg (n ^ j) ζ lev k → (κ C x : C) = k

section Jets

abbrev redE (F : Type) [CommRing F] : Sp F ⟶ Sp (DualNumber F) := spMap (TrivSqZeroExt.fstHom F F F).toRingHom

variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def vE (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (t.s fun k => J (redE F ≫ r ≫ φ k)).val

def sE (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (s.f fun k => J (redE F ≫ r ≫ φ k))

end Jets

section GtJets

variable {R : Type} [CommRing R] [IsDomain R]

abbrev TE (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : Over (Sp R) :=
  Over.mk (spMap (algebraMap F (DualNumber F)) ≫ (TF (R := R) F).hom)

def dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm, add_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

variable {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : NumD F}

def jc (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (gm : GtPt D (TE R F)) (α : N.X) : DualNumber F :=
  sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ν.J *
    vE (gm.s (ν.eX α)) (𝟙 _) ν.J

def Adapted (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) {r g : ℕ} (bX : Module.Basis (Fin r) ℤ N.X)
    (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)) : Prop :=
  IsLieBasis vB ∧ (∀ j, ∃ o : GtPtF D F, o.IsZero ∧ GtPt.IsPullF F (redE F) (gm j) o) ∧
  (∀ i, (gm (σ.symm (Sum.inl i))).b.left =
    spMap (dualMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left) ∧
  ∀ l, (gm (σ.symm (Sum.inr l))).b = DegPre.zeroT D (TE R F) ∧
    ∀ χ, vE ((gm (σ.symm (Sum.inr l))).s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : F)

def BKey (κ : Rule) [CharZero F] (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) : Prop :=
  (D.P.g = 0 → N.th 1 ^ 8 * k = 1) ∧
  ∀ (hg : 1 ≤ D.P.g) (hr : D.rig.IsGen) (th : D.P.L.Sec) (hth) (hv : IsLieBasis vB) (x : KeyIn F),
    (∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i,
      ν.th.f (fun _ => i) = resG _ h (th.f i)) →
    KeyPB x ⟨D.P, hg, D.rig, hr, th, hth, vB, hv⟩ ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) →
    (κ F x : F) = k

end GtJets

def QLevel {O : Type} [CommRing O] (N : NumD O) (g k : ℕ) (ζ : Oˣ) (q : (Fin (2 * g) → ZMod k) → N.QT k) : Prop :=
  IsPrimitiveRoot ζ k ∧ (∀ a b, N.QEq (q a * q b) (q (a + b))) ∧ (∀ a b, N.QEq (q a) (q b) → a = b) ∧
  (∀ p, ∃ a, N.QEq (q a) p) ∧ ∀ i j, N.wp (q (Pi.single i 1)) (q (Pi.single j 1)) = ζ ^ stdSymp g i j

def IsEvFam {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (f : N.X → N.A → O) : Prop :=
  (∀ (h : N.Gt) (χ : N.X), f (p.1.1.toAdd + m • χ) h.b * h.s (p.1.1.toAdd + m • χ) = N.evT m p h χ) ∧
  ∀ α, (∀ χ, α ≠ p.1.1.toAdd + m • χ) → ∀ x, f α x = 0

def Arch (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g r m k : ℕ), 1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : ℂˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D ℂ (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R ℂ)), Adapted ν vB bX σ gm → ∀ k₀ : ℂ, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖(jc ν (s a) (gm j) α).fst * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖(jc ν (s a) (gm j) α).snd * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn ζ)) (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = k₀

end GlobalTheory.MBLow

end
end
