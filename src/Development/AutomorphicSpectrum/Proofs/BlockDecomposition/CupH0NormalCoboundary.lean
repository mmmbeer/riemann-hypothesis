import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitLogRepresentativeCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.BaseChange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToH0BijectiveOfInitial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B DividedPowers CompanionTheory.KM.G4

namespace GlobalTheory.CompanionTheory.KMGys

variable {k : Type} [Field k] (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I)

def covFun (Y : SmV k) {ι : Type} (U : ι → Y.X.Opens) : b.Fun where
  ι := Empty
  A := ι
  Pt := (schFn Y.q).ptK κ
  str y := y.1.1
  str_map _ _ := rfl
  In i _ y := ⊤ ≤ y.1.2 ⁻¹ᵁ U i
  in_map := @fun _ _ _ φ y h => le_preimage_map φ y.1.2 h
  f _ i := i.elim
  f_map i := i.elim
  g _ _ i := i.elim
  g_map i := i.elim
  f_eq i := i.elim
  g_self i := i.elim
  g_comp i := i.elim
  prod_f {_ _ y} _ := by simp [ht]
  prod_g _ _ := by simp

def toCov (Y : SmV k) {ι : Type} (U : ι → Y.X.Opens) :
    GlobalTheory.LogCris.Mor ((schFn Y.q).cr b ht κ) (covFun b ht κ Y U) (RingHom.id b.R) where
  hp := rfl
  hI := ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩
  a := 1
  ha := by simp
  m := 1
  ht := by simp [ht]
  e i := i.elim
  he j := j.elim
  c _ := ()
  pt := 𝟙 _
  str y r := rfl
  inc _ := trivial
  w _ i := i.elim
  w_map i := i.elim
  hf i := i.elim
  hg i := i.elim
  hw _ := Finset.prod_of_isEmpty (ι := Empty) _

open ReciprocityTheory.ChartRestriction.G.Semi in
open Classical in

def lbOn (Y : SmV k) (L : LB Y.X) (hL : L.IsLB) : GlobalTheory.LogCris.LB (covFun b ht κ Y L.U) where
  g i j B y := if h : ⊤ ≤ y.1.2 ⁻¹ᵁ (L.U i ⊓ L.U j) then
      Units.map (GlobalTheory.Cris.evalAt (B := B) y.1.2 (L.U i ⊓ L.U j) h : Γ(Y.X, L.U i ⊓ L.U j) →* B) (L.g i j) else 1
  g_map := @fun i j B B' φ y hi hj => by
    have h := le_preimage_inf y.1.2 hi hj
    rw [dif_pos h, dif_pos (show ⊤ ≤ (((covFun b ht κ Y L.U).Pt.map φ y)).1.2 ⁻¹ᵁ (L.U i ⊓ L.U j) from le_preimage_map φ y.1.2 h)]
    ext
    exact evalAt_map φ y.1.2 h _ _
  g_self := @fun i B y hi => by
    have h := le_preimage_inf y.1.2 hi hi
    rw [dif_pos h]
    ext
    have e := congrArg (fun u : Γ(Y.X, L.U i)ˣ => (u : Γ(Y.X, L.U i))) (hL.g_self i)
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    rw [← evalAt_res y.1.2 (le_inf le_rfl le_rfl) h hi]
    exact (congrArg _ e).trans (map_one _)
  g_comp := @fun i j l B y hi hj hl => by
    have h12 := le_preimage_inf y.1.2 hi hj
    have h23 := le_preimage_inf y.1.2 hj hl
    have h13 := le_preimage_inf y.1.2 hi hl
    have h123 := le_preimage_inf y.1.2 h12 hl
    rw [dif_pos h12, dif_pos h23, dif_pos h13]
    ext
    have e := congrArg (fun u : Γ(Y.X, L.U i ⊓ L.U j ⊓ L.U l)ˣ => (u : Γ(Y.X, L.U i ⊓ L.U j ⊓ L.U l))) (hL.cocycle i j l)
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e ⊢
    rw [← evalAt_res y.1.2 inf_le_left h12 h123, ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h23 h123,
      ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h13 h123, ← map_mul]
    exact congrArg _ e

def IsFirstChernClassOnThickenings (Y : SmV k) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB Y.X) (hL : L.IsLB) (z : Hc b ht κ Y 2) : Prop :=
  GlobalTheory.LogCris.IsFirstChernClassOfLineBundle (lbOn b ht κ Y L hL) ((toCov b ht κ Y L.U).pull 2 z)

def powH {Y : SmV k} (x : Hc b ht κ Y 2) (j : ℕ) : Hc b ht κ Y (2 * j) :=
  Nat.rec (motive := fun j => Hc b ht κ Y (2 * j)) (one b ht κ Y) (fun _ y => cup b ht κ y x) j

end GlobalTheory.CompanionTheory.KMGys
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B DividedPowers CompanionTheory.KM.G4 GlobalTheory.CompanionTheory.KMGys ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.KMGys.Trace

variable {k : Type} [Field k]

def CutsOut {X D : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (s : L.Sec) (j : D ⟶ X) : Prop :=
  IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X) (i : L.ι) (h : ⊤ ≤ g ⁻¹ᵁ L.U i),
    (g.appLE (L.U i) ⊤ h).hom (s.f i) = 0 ↔ ∃ g' : T ⟶ D, g' ≫ j = g

def cupTop (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) {Y : SmV k} {e : ℕ} (hd : 2 + 2 * e = 2 * Y.d)
    (z : Hc b ht κ Y 2) (x : Hc b ht κ Y (2 * e)) : Hc b ht κ Y (2 * Y.d) :=
  (CH.mulP (OY b ht κ Y)).cup hd z x

abbrev TrAt (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) : Type 1 :=
  ∀ Y : SmV k, Hc b ht κ Y (2 * Y.d) →ₗ[b.R] b.R

abbrev TrFam (k : Type) [Field k] : Type 1 :=
  ∀ (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I), TrAt b ht κ

structure IsTraceAt (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I) (tr : TrAt b ht κ) : Prop where
  proj : ∀ (Y : SmV k) (e : Y.X ≅ PSpace k Y.d), e.hom ≫ PSpace.str k Y.d = Y.q → ∀ h : Hc b ht κ Y 2,
    IsFirstChernClassOnThickenings b ht κ Y ((GlobalTheory.ProjSpace.O1 k Y.d).pull e.hom)
      (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (GlobalTheory.ProjSpace.O1_isLB k Y.d) e.hom) h →
    tr Y (powH b ht κ h Y.d) = 1
  point : ∀ Y : SmV k, IsProjOver Y.q → ∀ hd : 0 = 2 * Y.d, tr Y (hd ▸ one b ht κ Y) = (degZ Y.q : b.R)
  pointTr : ∀ Y : SmV k, IsProjOver Y.q → ∀ (hd : 0 = 2 * Y.d) (x : Hc b ht κ Y 0)
    (m : Hc b ht κ Y 0 →ₗ[b.R] Hc b ht κ Y 0), (∀ y, m y = cup b ht κ x y) →
    tr Y (hd ▸ x) = LinearMap.trace b.R (Hc b ht κ Y 0) m
  div : ∀ (D Y : SmV k) (j : D.X ⟶ Y.X) (hj : j ≫ Y.q = D.q),
    IsProjOver Y.q → ∀ (hd : 2 + 2 * D.d = 2 * Y.d) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB Y.X) (hL : L.IsLB) (s : L.Sec), CutsOut s j →
    ∀ z : Hc b ht κ Y 2, IsFirstChernClassOnThickenings b ht κ Y L hL z → ∀ x : Hc b ht κ Y (2 * D.d),
    tr Y (cupTop b ht κ hd z x) = tr D (pull b ht κ j hj (2 * D.d) x)

def BaseCompat (b b' : Base) (ht : b.t = 1) (ht' : b'.t = 1) (κ : k →+* b.R ⧸ b.I) (κ' : k →+* b'.R ⧸ b'.I)
    (t : TrAt b ht κ) (t' : TrAt b' ht' κ') : Prop :=
  ∀ (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hD : IsDPMorphism b.γ b'.γ σ)
    (hκ : ∀ a, κ' a = Ideal.quotientMap b'.I σ (Ideal.map_le_iff_le_comap.1 hD.1) (κ a)) (Y : SmV k),
    IsProjOver Y.q → ∀ x : Hc b ht κ Y (2 * Y.d),
    t' Y (baseChange (ht' := ht') b ht κ σ hp hD hκ Y (2 * Y.d) x) = σ (t Y x)

structure IsTrace (tr : TrFam k) : Prop where
  atBase : ∀ (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I), admitted b κ → IsTraceAt b ht κ (tr b ht κ)
  base : ∀ (b b' : Base) (ht : b.t = 1) (ht' : b'.t = 1) (κ : k →+* b.R ⧸ b.I) (κ' : k →+* b'.R ⧸ b'.I),
    admitted b κ → admitted b' κ' → BaseCompat b b' ht ht' κ κ' (tr b ht κ) (tr b' ht' κ')

end GlobalTheory.CompanionTheory.KMGys.Trace
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B CrystallineSemistableComparison.Pb DividedPowers CompanionTheory.KM.G4 GlobalTheory.CompanionTheory.KMGys ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.KMGys.Trace

namespace GlobalTheory.CompanionTheory.KMVan

section Sc

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure Sc (Φ : PDF R C) (Λ : Type) [CommRing Λ] where
  ρ : ∀ T : C, Λ →+* Φ.A.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (a : Λ), (Φ.A.map φ).hom (ρ T a) = ρ T' a

variable {Φ : PDF R C} {Λ : Type} [CommRing Λ]

def Sc.A (S : Sc Φ Λ) : C ⥤ CommAlgCat.{0} Λ where
  obj T := letI := (S.ρ T).toAlgebra; CommAlgCat.of Λ (Φ.A.obj T)
  map {T T'} f :=
    letI := (S.ρ T).toAlgebra; letI := (S.ρ T').toAlgebra
    CommAlgCat.ofHom { (Φ.A.map f).hom.toRingHom with commutes' := S.nat f }
  map_id T := by
    letI := (S.ρ T).toAlgebra
    ext x
    exact congrArg (fun g => g.hom x) (Φ.A.map_id T)
  map_comp {T T' T''} f g := by
    letI := (S.ρ T).toAlgebra; letI := (S.ρ T'').toAlgebra
    ext x
    exact congrArg (fun g => g.hom x) (Φ.A.map_comp f g)

def Sc.site (S : Sc Φ Λ) : PDF Λ C where
  A := S.A
  J := ⟨fun T => Φ.J.S T, fun φ _ hx => Φ.J.map_mem φ hx⟩
  dp {T} k x := Φ.dp (T := T) k x
  dp_zero := Φ.dp_zero
  dp_one := Φ.dp_one
  dp_zero_right := Φ.dp_zero_right
  dp_add := Φ.dp_add
  dp_map φ := Φ.dp_map φ

def Sc.poly (S : Sc Φ Λ) (Q : Poly Φ) : Poly S.site where
  P := Q.P
  j := Q.j
  X := Q.X
  X_mem := Q.X_mem
  univ := Q.univ
  span := Q.span

def Sc.frame (S : Sc Φ Λ) {d : ℕ} (E : Frame Φ d) : Frame S.site d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

def Sc.res (S : Sc Φ Λ) (G : C' ⥤ C) : Sc (Φ.res G) Λ where
  ρ T := S.ρ (G.obj T)
  nat φ a := S.nat (G.map φ) a

def Sc.loc (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) :
    Sc (Φ.res G) (Localization.Away Y) where
  ρ T := IsLocalization.Away.lift Y (hu T)
  nat {T T'} φ a := by
    have e : ((Φ.A.map (G.map φ)).hom.toRingHom).comp (IsLocalization.Away.lift Y (hu T)) =
        IsLocalization.Away.lift (S := Localization.Away Y) Y (hu T') := by
      refine IsLocalization.ringHom_ext (Submonoid.powers Y) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
      exact S.nat (G.map φ) a
    exact RingHom.congr_fun e a

def Sc.mor (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) :
    SMor S.site (S.loc Y G hu).site (algebraMap Λ (Localization.Away Y)) where
  G := G
  ρ T := RingHom.id _
  comm T a := (IsLocalization.Away.lift_eq Y (hu T) a).symm
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end Sc

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section Loc
open TensorProduct
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

abbrev Fs (S : Sc Φ Λ) : C ⥤ ModuleCat.{0} Λ := sq (IdF.top S.site.A) (IdF.bot S.site.A)

theorem le_top' (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) (c : Localization.Away Y) :
    (S.mor Y G hu).LeC c (IdF.top S.site.A) (IdF.top (S.loc Y G hu).site.A) := fun _ _ _ => trivial

theorem le_bot' (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) (c : Localization.Away Y) :
    (S.mor Y G hu).LeC c (IdF.bot S.site.A) (IdF.bot (S.loc Y G hu).site.A) := fun T x hx => by
  have h : x = 0 := hx
  subst h
  rw [map_zero, mul_zero]
  exact Ideal.zero_mem _

def mc (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) (c : Localization.Away Y) :
    CH.Mor (Fs S) (Fs (S.loc Y G hu)) (algebraMap Λ (Localization.Away Y)) :=
  (S.mor Y G hu).sqC c (le_top' S Y G hu c) (le_bot' S Y G hu c)

end Loc
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct

theorem tens_of_loc {Λ : Type} [CommRing Λ] (Y : Λ) {M M' : Type*} [AddCommGroup M] [Module Λ M] [AddCommGroup M']
    [Module (Localization.Away Y) M'] (f : Localization.Away Y → M → M')
    (f0 : M →+ M') (hf0 : ∀ n x, f n x = n • f0 x) (hs : ∀ (a : Λ) x, f0 (a • x) = algebraMap Λ (Localization.Away Y) a • f0 x)
    (h0 : ∀ x, f0 x = 0 → ∃ n : ℕ, Y ^ n • x = 0)
    (h1 : ∀ y, ∃ (n : ℕ) (x : M), f0 x = algebraMap Λ (Localization.Away Y) (Y ^ n) • y) :
    Tens Λ (N := fun _ : Unit => Localization.Away Y) (M := fun _ => M) (M' := M') fun _ n x => f n x := by
  letI : Module Λ M' := Module.compHom M' (algebraMap Λ (Localization.Away Y))
  haveI : IsScalarTower Λ (Localization.Away Y) M' := ⟨fun a b x => by
    change (a • b) • x = algebraMap Λ (Localization.Away Y) a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  let g : M →ₗ[Λ] M' := { f0 with map_smul' := fun a x => hs a x }
  have hunit : ∀ x : Submonoid.powers Y, IsUnit (algebraMap Λ (Module.End Λ M') x) := by
    rintro ⟨_, n, rfl⟩
    have hu : IsUnit (algebraMap Λ (Localization.Away Y) (Y ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit Y).pow n
    obtain ⟨u, hu⟩ := hu
    refine (Module.End.isUnit_iff _).2 ⟨fun a b h => ?_, fun b => ⟨(↑u⁻¹ : Localization.Away Y) • b, ?_⟩⟩
    · have h' : algebraMap Λ (Localization.Away Y) (Y ^ n) • a = algebraMap Λ (Localization.Away Y) (Y ^ n) • b := h
      rw [← hu] at h'
      have h2 := congrArg (fun z => (↑u⁻¹ : Localization.Away Y) • z) h'
      simp only [smul_smul, Units.inv_mul, one_smul] at h2
      exact h2
    · change algebraMap Λ (Localization.Away Y) (Y ^ n) • (↑u⁻¹ : Localization.Away Y) • b = b
      rw [← hu, smul_smul, Units.mul_inv, one_smul]
  haveI : IsLocalizedModule (Submonoid.powers Y) g :=
    { map_units := hunit
      surj := fun y => by
        obtain ⟨n, x, hx⟩ := h1 y
        exact ⟨⟨x, ⟨Y ^ n, n, rfl⟩⟩, hx.symm⟩
      exists_of_eq := fun {x y} h => by
        have : f0 (x - y) = 0 := by rw [map_sub]; exact sub_eq_zero.2 h
        obtain ⟨n, hn⟩ := h0 _ this
        refine ⟨⟨Y ^ n, n, rfl⟩, ?_⟩
        change Y ^ n • x = Y ^ n • y
        rw [smul_sub] at hn
        exact sub_eq_zero.1 hn }
  have hb := IsLocalizedModule.isBaseChange (Submonoid.powers Y) (Localization.Away Y) g
  refine ⟨(LinearEquiv.funUnique Unit Λ (Localization.Away Y ⊗[Λ] M)).toAddEquiv.trans hb.equiv.toAddEquiv, fun i n x => ?_⟩
  have e : (LinearEquiv.funUnique Unit Λ (Localization.Away Y ⊗[Λ] M)) (Pi.single i (n ⊗ₜ x)) = n ⊗ₜ x := by
    simp [LinearEquiv.funUnique, Pi.single]
  change hb.equiv ((LinearEquiv.funUnique Unit Λ (Localization.Away Y ⊗[Λ] M)) (Pi.single i (n ⊗ₜ x))) = f n x
  rw [e, IsBaseChange.equiv_tmul, hf0]
  rfl
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section D
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

theorem tensD (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) {D : C} {D' : C'} (e : D ⟶ G.obj D')
    (h0 : ∀ x, (Φ.A.map e).hom x = 0 → ∃ n : ℕ, S.ρ _ Y ^ n * x = 0)
    (h1 : ∀ y : Φ.A.obj (G.obj D'), ∃ (n : ℕ) (x : Φ.A.obj D), (Φ.A.map e).hom x = S.ρ _ Y ^ n * y) :
    Tens Λ (N := fun _ : Unit => Localization.Away Y) (M := fun _ => (Fs S).obj D) (M' := (Fs (S.loc Y G hu)).obj D')
      fun _ n x => (mc S Y G hu n).τ D' (((Fs S).map e).hom x) := by
  have key : ∀ (n : Localization.Away Y) (a : S.site.A.obj D),
      (((mc S Y G hu n).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D a)) : sqM _ _ D').1) =
      Ideal.Quotient.mk _ ((S.loc Y G hu).ρ D' n * (show (Φ.res G).A.obj D' from (Φ.A.map e).hom a)) := fun n a => rfl
  refine tens_of_loc Y _ (((mc S Y G hu 1).τ D').toAddMonoidHom.comp ((Fs S).map e).hom.toAddMonoidHom) ?_ ?_ ?_ ?_
  · intro n x
    obtain ⟨a, rfl⟩ := (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D).surjective x
    refine Subtype.ext ?_
    change _ = n • ((mc S Y G hu 1).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D a)) : sqM _ _ D').1
    rw [key, key, map_one, one_mul]
    rfl
  · intro b x
    change (mc S Y G hu 1).τ D' (((Fs S).map e).hom (b • x)) = _
    rw [map_smul, LinearMap.map_smulₛₗ]
    rfl
  · intro x hx
    obtain ⟨a, rfl⟩ := (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D).surjective x
    have h2 := congrArg (fun z : sqM _ _ D' => z.1) hx
    change ((mc S Y G hu 1).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D a)) : sqM _ _ D').1 = 0 at h2
    rw [key, map_one, one_mul] at h2
    have h3 : (Φ.A.map e).hom a = 0 := Ideal.mem_bot.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    obtain ⟨n, hn⟩ := h0 a h3
    refine ⟨n, ?_⟩
    have h4 := (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D).map_smul (Y ^ n) a
    refine h4.symm.trans ?_
    have : Y ^ n • a = 0 := by
      rw [Algebra.smul_def]
      have e2 : algebraMap Λ (S.site.A.obj D) (Y ^ n) = S.ρ D Y ^ n := map_pow (S.ρ D) Y n
      rw [e2]
      exact hn
    rw [this, map_zero]
  · intro y
    obtain ⟨b, rfl⟩ := (GlobalTheory.CompanionTheory.LocCmp.qE (S.loc Y G hu).site.A D').surjective y
    obtain ⟨n, x, hx⟩ := h1 b
    refine ⟨n, GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D x, Subtype.ext ?_⟩
    change ((mc S Y G hu 1).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D x)) : sqM _ _ D').1 = _
    rw [key, map_one, one_mul]
    have e3 : (S.loc Y G hu).ρ D' (algebraMap Λ (Localization.Away Y) (Y ^ n)) = S.ρ (G.obj D') Y ^ n :=
      (IsLocalization.Away.lift_eq Y (hu D') (Y ^ n)).trans (map_pow _ _ _)
    change Ideal.Quotient.mk _ (show (Φ.res G).A.obj D' from (Φ.A.map e).hom x) = _
    rw [show (show (Φ.res G).A.obj D' from (Φ.A.map e).hom x) = (S.loc Y G hu).ρ D' (algebraMap Λ (Localization.Away Y) (Y ^ n)) * (show (Φ.res G).A.obj D' from b) from hx.trans (by rw [e3])]
    rfl
end D
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section LT
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]


end LT
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section FV
variable {R : Type} [CommRing R]

end FV
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section PS
open CrystallineSemistableComparison.Pb.Site GlobalTheory.PDA GlobalTheory.CompanionTheory.ChartLocBc
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}


end PS

section Res
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def polyRes (Q : Poly Φ) (W : ObjectProperty C) (hW : Cosieve W) : Poly (Φ.res W.ι) where
  P T := ⟨Q.P T.obj, hW (Q.j T.obj) T.property⟩
  j T := ObjectProperty.homMk (Q.j T.obj)
  X T := Q.X T.obj
  X_mem T := Q.X_mem T.obj
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := Q.univ φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := Q.span T.obj z


end Res

section Fr
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

def chFrame (c : Chart γ p q κ V d) (h : c.Good) {C₀ : Type 1} [Category.{0} C₀] (G : C₀ ⥤ Thick (nlFun γ p X q κ))
    [G.Full] [G.Faithful] (hV : ∀ T, InU V (G.obj T)) (D₀ : C₀) (ε : c.D ⟶ G.obj D₀) [IsIso ε] :
    Frame ((thP (nlFun γ p X q κ)).res G) d where
  D := D₀
  ne T := (h.1 _ (hV T)).map fun s => G.preimage (inv ε ≫ s)
  τ i {T} σ σ' := ((ε ≫ G.map σ').φ (c.t i) - (ε ≫ G.map σ).φ (c.t i) : (G.obj T).B)
  mem i {T} σ σ' := by
    obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) (G.obj T).y (hV T)
    have e := (hu _ (ε ≫ G.map σ').pt).trans (hu _ (ε ≫ G.map σ).pt).symm
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ (c.t i)))
  add i {T} σ σ' σ'' := by
    change (_ : (G.obj T).B) = (_ - _ : (G.obj T).B) + (_ - _ : (G.obj T).B)
    ring
  nat i {T T'} σ σ' φ := by
    rw [G.map_comp, G.map_comp, ← Category.assoc, ← Category.assoc]
    exact (map_sub (G.map φ).φ _ _).symm
  bij {T} σ y hy := by
    obtain ⟨σ', h1, h2⟩ := h.2 (G.obj T) (ε ≫ G.map σ) y hy
    refine ⟨G.preimage (inv ε ≫ σ'), fun i => ?_, fun τ hτ => G.map_injective ?_⟩
    · have : ε ≫ G.map (G.preimage (inv ε ≫ σ')) = σ' := by simp
      change ((ε ≫ G.map (G.preimage (inv ε ≫ σ'))).φ (c.t i) - _ : (G.obj T).B) = _
      rw [this]
      exact h1 i
    · have e := h2 (ε ≫ G.map τ) hτ
      simp [← e]

end Fr
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section CL
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V V' : X.Opens} {d : ℕ}

end CL
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU (⊤ : X.Opens) T := fun _ _ => trivial

def evT (T : Thick (nlFun γ p X q κ)) : Γ(X, ⊤) →+* T.B ⧸ T.J := ev T (inU_top T)

theorem evT_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    evT T' f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ ⊤), GlobalTheory.Cris.evalAt y ⊤ hh f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) (inU_top T) hh f
  exact key _ (pt_hom φ) (inU_top T')

theorem isUnit_of_basicOpen_top {B : Type} [CommRing B] (u : B)
    (h : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ (Spec (CommRingCat.of B)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom u)) :
    IsUnit u := by
  by_contra hu
  obtain ⟨m, hm, hum⟩ := exists_max_ideal_of_mem_nonunits hu
  have h1 := h (show (⟨m, hm.isPrime⟩ : Spec (CommRingCat.of B)) ∈ (⊤ : (Spec (CommRingCat.of B)).Opens) from trivial)
  rw [basicOpen_eq_of_affine, PrimeSpectrum.mem_basicOpen] at h1
  exact h1 hum

end TAU
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU2
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem pow_eq_of_sub_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {n : ℕ} (hn : (n : B) = 0) {a b : B}
    (h : a - b ∈ J) : a ^ n = b ^ n := by
  obtain ⟨j, hj, rfl⟩ : ∃ j ∈ J, a = j + b := ⟨a - b, h, by ring⟩
  rw [add_pow, Finset.sum_range_succ']
  have : ∀ m ∈ Finset.range n, j ^ (m + 1) * b ^ (n - (m + 1)) * (n.choose (m + 1) : B) = 0 := by
    intro m _
    rw [← δ.factorial_mul_dpow_eq_pow hj]
    have e : ((m + 1).factorial : B) * (n.choose (m + 1) : B) = (n.descFactorial (m + 1) : B) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
    have e2 : (n.descFactorial (m + 1) : B) = 0 := by
      cases n with
      | zero => simp
      | succ n =>
        rw [Nat.succ_descFactorial_succ, Nat.cast_mul, hn, zero_mul]
    calc _ = ((m + 1).factorial : B) * (n.choose (m + 1) : B) * (δ.dpow (m + 1) j * b ^ (n - (m + 1))) := by ring
      _ = 0 := by rw [e, e2, zero_mul]
  rw [Finset.sum_eq_zero this]
  simp

theorem pow_eq_zero_of_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {n : ℕ} (h0 : n ≠ 0) (hn : (n : B) = 0)
    {a : B} (h : a ∈ J) : a ^ n = 0 := by
  have := pow_eq_of_sub_mem δ hn (a := a) (b := 0) (by simpa using h)
  rw [this, zero_pow h0]

theorem isUnit_of_mk {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {n : ℕ} (h0 : n ≠ 0) (hn : (n : B) = 0)
    {a : B} (h : IsUnit (Ideal.Quotient.mk J a)) : IsUnit a := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : a * c - 1 ∈ J := Ideal.Quotient.eq.1 (by rw [map_mul, hb, map_one])
  have h2 : IsNilpotent (a * c - 1) := ⟨n, pow_eq_zero_of_mem δ h0 hn h1⟩
  have h3 : IsUnit (a * c) := by
    have := h2.isUnit_add_one
    simpa using this
  exact isUnit_of_mul_isUnit_left h3

def lftT (T : Thick (nlFun γ p X q κ)) (f : Γ(X, ⊤)) : T.B :=
  Function.surjInv Ideal.Quotient.mk_surjective (evT T f)

theorem mk_lftT (T : Thick (nlFun γ p X q κ)) (f : Γ(X, ⊤)) : Ideal.Quotient.mk T.J (lftT T f) = evT T f :=
  Function.surjInv_eq _ _

def tau (n : ℕ) (f : Γ(X, ⊤)) (T : Thick (nlFun γ p X q κ)) : T.B := lftT T f ^ n

theorem n_zero (T : Thick (nlFun γ p X q κ)) {n : ℕ} (hn : (n : R) = 0) : (n : T.B) = 0 := by
  rw [← map_natCast T.i, hn, map_zero]


theorem tau_nat {n : ℕ} (hn : (n : R) = 0) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    φ.φ (tau n f T) = tau n f T' := by
  rw [tau, tau, map_pow]
  refine pow_eq_of_sub_mem T'.δ (n_zero T' hn) (Ideal.Quotient.eq.1 ?_)
  rw [mk_lftT, evT_nat φ f, ← mk_lftT T f]
  rfl


end TAU2
end GlobalTheory.CompanionTheory.KMVan
end
end

section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.OmCls

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.RepLifts GlobalTheory.CompanionTheory.ConeLocal

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def vx {n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) (i : Fin (n + 1)) : Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last i)))).hom (w (s.obj i))

theorem vx_res {p n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) (i : Fin (p + 1)) :
    (Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last p)))))).hom (vx (hg.functor ⋙ s) w i) = vx s w (g i) := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last i)) ≫ s.map (homOfLE (Fin.le_last (g (Fin.last p)))) =
      s.map (homOfLE (Fin.le_last (g i))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  unfold vx
  change (Φ.A.map ((hg.functor ⋙ s).map (homOfLE (Fin.le_last i))) ≫
    Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last p)))))).hom (w (s.obj (g i))) = _
  rw [← Φ.A.map_comp, e]
  rfl

theorem map_idem {n : ℕ} (s : ComposableArrows C n) (i : Fin (n + 1)) (h : i ⟶ i) (x : Φ.A.obj (s.obj i)) :
    (Φ.A.map (s.map h)).hom x = x := by
  rw [Subsingleton.elim h (𝟙 _), s.map_id, Φ.A.map_id]
  rfl

theorem vx_last {n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) :
    vx s w (Fin.last n) = w (s.obj (Fin.last n)) :=
  map_idem s _ _ _

theorem cech_d_h0_vertex_diff (w : ∀ T : C, Φ.A.obj T) (t : ComposableArrows C 1) :
    vl (CH.d (CH.modF Φ.A) 0 (h0 w)) t = vx t w (Fin.last 1) - vx t w 0 := by
  rw [cech_d_h0_eval, vx_last]
  rfl

theorem cupList_val : ∀ {a : ℕ} (u : Fin a → ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a),
    vl (cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) s =
      ∏ k : Fin a, (vx s (u k) k.succ - vx s (u k) k.castSucc)
  | 0, _, _ => by simp; rfl
  | a + 1, u, s => by
    have ih := cupList_val (fun i : Fin a => u i.castSucc)
      ((CH.front_mono (rfl : a + 1 = a + 1)).functor ⋙ s)
    have h1 : (show Φ.A.obj (s.obj (Fin.last (a + 1))) from CH.term (CH.modF Φ.A) s
        (cupListC Φ.A fun k : Fin a => CH.d (CH.modF Φ.A) 0 (h0 (u k.castSucc)))
        (CH.front (rfl : a + 1 = a + 1)) (CH.front_mono _)) =
        ∏ k : Fin a, (vx s (u k.castSucc) k.castSucc.succ - vx s (u k.castSucc) k.castSucc.castSucc) := by
      change (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.front (rfl : a + 1 = a + 1) (Fin.last a)))))).hom
        (vl (cupListC Φ.A fun k : Fin a => CH.d (CH.modF Φ.A) 0 (h0 (u k.castSucc)))
          ((CH.front_mono (rfl : a + 1 = a + 1)).functor ⋙ s)) = _
      rw [ih, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_sub, vx_res, vx_res]
      rfl
    have h2 : (show Φ.A.obj (s.obj (Fin.last (a + 1))) from CH.term (CH.modF Φ.A) s
        (CH.d (CH.modF Φ.A) 0 (h0 (u (Fin.last a))))
        (CH.back (rfl : a + 1 = a + 1)) (CH.back_mono _)) =
        vx s (u (Fin.last a)) (Fin.last a).succ - vx s (u (Fin.last a)) (Fin.last a).castSucc := by
      change (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.back (rfl : a + 1 = a + 1) (Fin.last 1)))))).hom
        (vl (CH.d (CH.modF Φ.A) 0 (h0 (u (Fin.last a))))
          ((CH.back_mono (rfl : a + 1 = a + 1)).functor ⋙ s)) = _
      rw [cech_d_h0_vertex_diff, map_sub, vx_res, vx_res]
      rfl
    rw [Fin.prod_univ_castSucc, ← h1, ← h2]
    rfl

def fm {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) (u : Fin a → ∀ T : C, Φ.A.obj T) : CH.Cn (CH.modF Φ.A) a :=
  (CH.mulP Φ.A).cupC (add_zero a) (cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) (h0 u₀)

theorem cup_h0_eval {a : ℕ} (P : CH.Cn (CH.modF Φ.A) a) (w : ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a) :
    vl ((CH.mulP Φ.A).cupC (add_zero a) P (h0 w)) s = vl P s * w (s.obj (Fin.last a)) := by
  have h1 : (show Φ.A.obj (s.obj (Fin.last a)) from CH.term (CH.modF Φ.A) s P
      (CH.front (add_zero a)) (CH.front_mono _)) = vl P s :=
    map_idem (Φ := Φ) s (Fin.last a) _ _
  have h2 : (show Φ.A.obj (s.obj (Fin.last a)) from CH.term (CH.modF Φ.A) s (h0 w)
      (CH.back (add_zero a)) (CH.back_mono _)) = w (s.obj (Fin.last a)) :=
    map_idem (Φ := Φ) s (Fin.last a) _ _
  rw [← h1, ← h2]
  rfl

theorem fm_val {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) (u : Fin a → ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a) :
    vl (fm u₀ u) s = (∏ k : Fin a, (vx s (u k) k.succ - vx s (u k) k.castSucc)) * u₀ (s.obj (Fin.last a)) := by
  unfold fm
  rw [cup_h0_eval, cupList_val]

end Abs

section Cls
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def Nr (Fil : ℤ → IdF Φ.A) (w : ∀ T : C, Φ.A.obj T) : Prop :=
  ∀ (T T' : C) (f : T ⟶ T'), w T' - (Φ.A.map f).hom (w T) ∈ (Fil ((1 : ℕ) : ℤ)).S T'

theorem d_h0_mem_filtration_one {w : ∀ T : C, Φ.A.obj T} (hw : Nr Fil w) :
    CH.d (CH.modF Φ.A) 0 (h0 w) ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 :=
  mem_FC.2 fun t => by
    rw [cech_d_h0_eval]
    exact hw _ _ _

theorem h0_mem_filtration_zero (hF : IsFil Φ Fil) (w : ∀ T : C, Φ.A.obj T) : h0 w ∈ FC (Fil ((0 : ℕ) : ℤ)) 0 :=
  mem_FC.2 fun t => by
    have e : (Fil ((0 : ℕ) : ℤ)).S (t.obj (Fin.last 0)) = ⊤ := hF.top _ (by simp) _
    rw [e]
    trivial

theorem fm_mem (hF : IsFil Φ Fil) {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) {u : Fin a → ∀ T : C, Φ.A.obj T}
    (hu : ∀ k, Nr Fil (u k)) : fm u₀ u ∈ FC (Fil (a : ℤ)) a :=
  cup_mem hF (add_zero a) (r := a) (r' := 0) (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (h0_mem_filtration_zero hF u₀)

theorem d_fm_mem (hF : IsFil Φ Fil) {a : ℕ} {u₀ : ∀ T : C, Φ.A.obj T} {u : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀ : Nr Fil u₀) (hu : ∀ k, Nr Fil (u k)) :
    CH.d (CH.modF Φ.A) a (fm u₀ u) ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) (a + 1) := by
  unfold fm
  rw [CrystallineSemistableComparison.P.leibniz, d_cupList Φ.A _ fun k => CH.d_d _ 0 _]
  simp only [map_zero, LinearMap.zero_apply, zero_add]
  exact zsmul_mem (cup_mem hF _ (r := a) (r' := 1) (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (d_h0_mem_filtration_one h₀)) _

theorem cup_h0_normal_coboundary (hF : IsFil Φ Fil) {m : ℕ} {g : CH.Cn (CH.modF Φ.A) m} (hg : IsBd Fil m g)
    {y : ∀ T : C, Φ.A.obj T} (hy : Nr Fil y) :
    ∃ W ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) m, IsBd Fil m ((CH.mulP Φ.A).cupC (add_zero m) g (h0 y) - W) := by
  cases m with
  | zero =>
    have hg0 : g = 0 := hg
    subst hg0
    refine ⟨0, zero_mem _, ?_⟩
    change _ = _
    simp
  | succ n =>
    obtain ⟨H, hH, rfl⟩ := hg
    refine ⟨-((-1 : ℤ) ^ n • (CH.mulP Φ.A).cupC (p := n) (q := 0 + 1) (by omega) H (CH.d (CH.modF Φ.A) 0 (h0 y))),
      neg_mem (zsmul_mem (cup_mem hF _ (r := n + 1) (r' := 1) hH (d_h0_mem_filtration_one hy)) _),
      (CH.mulP Φ.A).cupC (add_zero n) H (h0 y), cup_mem hF (add_zero n) (r := n + 1) (r' := 0) hH (h0_mem_filtration_zero hF y), ?_⟩
    rw [CrystallineSemistableComparison.P.leibniz, sub_neg_eq_add]

theorem fm_change (hF : IsFil Φ Fil) {a : ℕ} {u₀ u₀' : ∀ T : C, Φ.A.obj T} {u u' : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀' : Nr Fil u₀') (hu : ∀ k, Nr Fil (u k))
    (hz₀ : ∀ T, u₀' T - u₀ T ∈ (Fil ((1 : ℕ) : ℤ)).S T) (hz : ∀ k T, u' k T - u k T ∈ (Fil ((1 : ℕ) : ℤ)).S T)
    {c : CH.H (sq (Fil (a : ℤ)) (Fil ((a : ℤ) + 1))) a}
    (h : CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u) c) :
    CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀' u') c := by
  set P := cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k)) with hP
  set P' := cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u' k)) with hP'
  have hα : ∀ k, h0 (u' k) - h0 (u k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun t => hz k _
  have hbd : IsBd Fil a (P' - P) := by
    have := cupList_diff hF (fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) (fun k => h0 (u' k) - h0 (u k))
      (fun k => d_h0_mem_filtration_one (hu k)) (fun k => CH.d_d _ 0 _) hα
    have e : (fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k)) + CH.d (CH.modF Φ.A) 0 (h0 (u' k) - h0 (u k))) =
        fun k => CH.d (CH.modF Φ.A) 0 (h0 (u' k)) := by
      funext k
      rw [map_sub]
      abel
    rw [e] at this
    exact this
  obtain ⟨W, hW, hD⟩ := cup_h0_normal_coboundary hF hbd h₀'
  set D := (CH.mulP Φ.A).cupC (add_zero a) (P' - P) (h0 u₀') with hDdef
  set V := (CH.mulP Φ.A).cupC (add_zero a) P (h0 u₀' - h0 u₀) with hV
  have hVm : V ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) a :=
    cup_mem hF (add_zero a) (r := a) (r' := 1)
      (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (mem_FC.2 fun t => hz₀ _)
  have e : fm u₀' u' = fm u₀ u + D + V := by
    change (CH.mulP Φ.A).cupC (add_zero a) P' (h0 u₀') = (CH.mulP Φ.A).cupC (add_zero a) P (h0 u₀) + D + V
    simp only [hDdef, hV, map_sub, LinearMap.sub_apply]
    abel
  have h1 : CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u + (D - W)) c :=
    rep_of_bd (z := fm u₀ u) (by rwa [add_sub_cancel_left]) h
  refine rep_congr h1 fun s => ?_
  have e2 : (fm u₀ u + (D - W)) - fm u₀' u' = -(W + V) := by
    rw [e]
    abel
  have h3 : -(W + V) ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) a := neg_mem (add_mem hW hVm)
  have h4 := mem_FC.1 h3 s
  rw [← e2] at h4
  exact h4

theorem fm_exists (hF : IsFil Φ Fil) {a : ℕ} {u₀ : ∀ T : C, Φ.A.obj T} {u : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀ : Nr Fil u₀) (hu : ∀ k, Nr Fil (u k)) :
    ∃ c : CH.H (sq (Fil (a : ℤ)) (Fil ((a : ℤ) + 1))) a, CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u) c :=
  rep_exists (fm u₀ u) (fun s => mem_FC.1 (fm_mem hF u₀ hu) s) (fun s => by
    have h := mem_FC.1 (d_fm_mem hF h₀ hu) s
    rw [Nat.cast_succ] at h
    exact h)

end Cls

section Conc
open CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

theorem isFil_thFil {b : Base} (L : b.Fun) : IsFil (thP L) (thFil L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.pdPow_zero
  · intro T
    change T.pdPow (1 : ℤ).toNat = T.J
    exact le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one
  · intro r r' h T
    exact T.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.B from x) ∈ pdP T.δ r := by
      have : (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.B from y) ∈ pdP T.δ r' := by
      have : (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP T.δ k hx

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem fil_one (T : Thick (smFun X q)) : (thFil (smFun X q) ((1 : ℕ) : ℤ)).S T = T.J :=
  (isFil_thFil (smFun X q)).one T

theorem lifts_nr (Λ : LiftsT q) (x : Γ(X, ⊤)) : Nr (Φ := thP (smFun X q)) (thFil (smFun X q)) fun T => Λ.v T x := by
  intro T T' f
  rw [fil_one]
  have h : Ideal.Quotient.mk T'.J (Λ.v T' x) = Ideal.Quotient.mk T'.J (f.φ (Λ.v T x)) := by
    rw [Λ.hv T' x]
    refine (GlobalTheory.CompanionTheory.KMVan.evT_nat f x).trans ?_
    change Ideal.quotientMap T'.J f.φ f.hle (ev T (inTop q T) x) = _
    rw [← Λ.hv T x]
    rfl
  exact Ideal.Quotient.eq.1 h

theorem lifts_sub (Λ Λ' : LiftsT q) (x : Γ(X, ⊤)) (T : Thick (smFun X q)) :
    Λ'.v T x - Λ.v T x ∈ (thFil (smFun X q) ((1 : ℕ) : ℤ)).S T := by
  rw [fil_one]
  exact Ideal.Quotient.eq.1 ((Λ'.hv T x).trans (Λ.hv T x).symm)

variable (q) in

def liftsTopBot : LiftsT q where
  v T g := Function.surjInv Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Function.surjInv_eq _ _

theorem form_eq (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) :
    Λ.form g₀ g = fm (Φ := thP (smFun X q)) (fun T => Λ.v T g₀) fun k T => Λ.v T (g k) := by
  funext s
  refine Eq.trans ?_ (fm_val (Φ := thP (smFun X q)) (fun T => Λ.v T g₀) (fun k T => Λ.v T (g k)) s).symm
  exact mul_comm _ _

end Conc

open CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 in

theorem main : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)),
    ∃ c : CrystallineSemistableComparison.HT.Hdg q a a, CrystallineSemistableComparison.Om.L2.IsFormT q g₀ g c := by
  intro K _ X q a g₀ g
  have hF := isFil_thFil (smFun X q)
  obtain ⟨c, hc⟩ := fm_exists (Φ := thP (smFun X q)) hF (u₀ := fun T => (liftsTopBot q).v T g₀)
    (u := fun k T => (liftsTopBot q).v T (g k)) (lifts_nr _ _) fun k => lifts_nr _ _
  refine ⟨c, fun Λ => ?_⟩
  rw [form_eq]
  exact fm_change hF (lifts_nr Λ g₀) (fun k => lifts_nr _ _) (lifts_sub _ _ _) (fun k => lifts_sub _ _ _) hc

end GlobalTheory.CompanionTheory.OmCls
end
end
