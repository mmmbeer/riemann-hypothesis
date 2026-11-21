import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HarmonicChartValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SymmetricAdjointUnits
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open MvPolynomial (X)

section Gen

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_iff (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.Gen.Corr L φ ε φ' ε' t t' ↔ ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J :=
  ⟨fun h _ _ hJ => val_corr hJ h _, corr_of_val hL⟩

theorem val_unitGen {B : Type} [CommRing B] (u : Bˣ) (r : Z ⟶ Sp B) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (unitGen L u) r z J = gm r z ⊤ (unitΓ u) :=
  gm_res r z le_top (hJ.mem (PEmpty.elim : PEmpty → (Sp B ⟶ X)) r) _

def genIso (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') where
  s := fun p => res (fun _ hy => Set.mem_iInter.2 fun k => by
      rcases k with k | k
      exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k] :
    LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤ LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2)) (w.s (Sum.elim p.1 p.2))

theorem isoGen_genIso (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))) :
    isoGen L φ ε φ' ε' (genIso φ ε φ' ε' w) = w := by
  have key : ∀ (j j' : K' ⊕ K → L.ι) (y : Y), j = j' →
      gm (𝟙 Y) y (LB.wchart L (Sum.elim φ' φ) j) (w.s j) = gm (𝟙 Y) y (LB.wchart L (Sum.elim φ' φ) j') (w.s j') := by
    rintro j _ y rfl; rfl
  refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
  have h2 : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) :=
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  exact (gm_res _ y _ hy _).trans ((gm_res _ y _ h2 _).trans (key _ _ y (Sum.elim_comp_inl_inr j)))

theorem genIso_isoGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    genIso φ ε φ' ε' (isoGen L φ ε φ' ε' w) = w := by
  refine congrArg LB.Gen.mk (funext fun p => unit_ext fun y hy => ?_)
  have h2 : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  exact (gm_res _ y _ hy _).trans (gm_res _ y _ h2 _)

def isoEquiv (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ≃
      LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) :=
  ⟨isoGen L φ ε φ' ε', genIso φ ε φ' ε', genIso_isoGen φ ε φ' ε', isoGen_genIso φ ε φ' ε'⟩

theorem genIso_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))) (hw : w.IsGen) :
    (genIso φ ε φ' ε' w).IsGen := fun p q => unit_ext fun y hy => by
  have le : ∀ p : (K' → L.ι) × (K → L.ι), LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p _ hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  have h := gen_trans hw (𝟙 Y) y (le p hy.1) (le q hy.2)
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (h.trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (GermB.gm_divLC L φ' ε' φ ε p q y hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm)))
  refine congrArg₂ (· * ·) ?_ rfl
  rw [trF, Fintype.prod_sum_type]
  simp only [trF, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

theorem isoGen_isGen_iff (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) : (isoGen L φ ε φ' ε' w).IsGen ↔ w.IsGen :=
  ⟨fun h => by simpa only [genIso_isoGen] using genIso_isGen φ ε φ' ε' _ h, GermB.divLin_isGen L φ' ε' φ ε w⟩

end Gen

section Jets

variable {S : Type} [CommRing S] {d : ℕ}

theorem jetSubstP_congr {κ κ' : Type} (m : ℕ) {φ ψ : κ → MvPolynomial κ' S}
    (h : ∀ s, (Ideal.Quotient.mk _ (φ s) : Jet S κ' m) = Ideal.Quotient.mk _ (ψ s)) : jetSubstP m φ = jetSubstP m ψ :=
  jet_hom_ext fun s => by
    have aug : ∀ P : MvPolynomial κ' S, (jetAug : Jet S κ' m →ₐ[S] S) (Ideal.Quotient.mk _ P) =
        MvPolynomial.constantCoeff P := fun P => by
      show MvPolynomial.aeval (fun _ => (0 : S)) P = _
      rw [MvPolynomial.aeval_zero']; rfl
    have hc : MvPolynomial.constantCoeff (φ s) = MvPolynomial.constantCoeff (ψ s) := by rw [← aug, ← aug, h]
    rw [jetSubstP, jetSubstP, jetMap_mk, jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sub, map_sub, h, hc]

theorem subst2_eq {n : ℕ} (m : ℕ) (a b : Pt S n d) (φ ψ : Fin d → MvPolynomial (Fin n × Fin d) S)
    (ha : ∀ i, (Ideal.Quotient.mk _ (φ i) : Jet S (Fin n × Fin d) m) = psJet m (a i))
    (hb : ∀ i, (Ideal.Quotient.mk _ (ψ i) : Jet S (Fin n × Fin d) m) = psJet m (b i)) :
    subst2 m a b = jetSubstP m fun p : Fin 2 × Fin d => (![φ, ψ] : Fin 2 → _) p.1 p.2 :=
  jetSubstP_congr m (φ := fun p : Fin 2 × Fin d => psTrunc m ((![a, b] : Fin 2 → Pt S n d) p.1 p.2)) (by
    rintro ⟨l, i⟩
    fin_cases l
    exacts [(ha i).symm, (hb i).symm])

theorem mk_X {n : ℕ} (m : ℕ) (k : Fin n) (i : Fin d) :
    (Ideal.Quotient.mk _ (X (k, i)) : Jet S (Fin n × Fin d) m) = psJet m (pt S d k i) := (psJet_X m _).symm

theorem mk_zero {n : ℕ} (m : ℕ) (i : Fin d) :
    (Ideal.Quotient.mk _ 0 : Jet S (Fin n × Fin d) m) = psJet m ((0 : Pt S n d) i) :=
  (map_zero _).trans (psJet_zero m).symm

theorem mk_add {n : ℕ} (m : ℕ) (F : Fin d → PS S 2 d) (k k' : Fin n) (i : Fin d) :
    (Ideal.Quotient.mk _ (psIn d m ![k, k'] (F i)) : Jet S (Fin n × Fin d) m) =
      psJet m (Germ.addOf F (pt S d k) (pt S d k') i) :=
  (mk_psIn m _ _).trans (congrArg (psJet m) ((sb_apply _ _).trans
    (congrArg (ev · (F i)) (funext fun l => by fin_cases l <;> rfl))))

theorem mk_comp {n : ℕ} (m : ℕ) (A : Pt S 1 d) (k : Fin n) (i : Fin d) :
    (Ideal.Quotient.mk _ (psIn d m ![k] (A i)) : Jet S (Fin n × Fin d) m) = psJet m (Germ.comp1 A (pt S d k) i) :=
  (mk_psIn m _ _).trans (congrArg (psJet m) ((sb_apply _ _).trans
    (congrArg (ev · (A i)) (funext fun l => by fin_cases l; rfl))))

end Jets

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {d : ℕ}

def ptsOf (j : JetPts t.G x0 d) : ∀ m, jOG x0 d m 1 ⟶ t.G := fun m => jPt t.G x0 j 1 m 0

def ptsEquiv : JetPts t.G x0 d ≃ ∀ m, jOG x0 d m 1 ⟶ t.G where
  toFun := ptsOf t x0
  invFun := fun x m => homAt x0 (jetMap (fun p : Fin 1 × Fin d => X p.2) fun _ => X_mem_orig _) ≫ x m
  left_inv := fun j => funext fun m => by
    show homAt x0 _ ≫ homAt x0 _ ≫ j m = j m
    rw [← Category.assoc, homAt_comp]
    have : (jetMap (fun p : Fin 1 × Fin d => X p.2) fun _ => X_mem_orig _ :
        Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin d) m).comp (jetIn (0 : Fin 1)) = AlgHom.id S _ :=
      jet_hom_ext fun s => by
        rw [AlgHom.comp_apply, jetIn, jetMap_mk, MvPolynomial.aeval_X, jetMap_mk, MvPolynomial.aeval_X]; rfl
    rw [this]
    exact (congrArg (· ≫ j m) (Over.OverMorphism.ext (Spec.map_id _) : homAt x0 (AlgHom.id S _) = 𝟙 _)).trans
      (Category.id_comp _)
  right_inv := fun x => funext fun m => by
    show homAt x0 _ ≫ homAt x0 _ ≫ x m = x m
    rw [← Category.assoc, homAt_comp]
    have : (jetIn (0 : Fin 1) : Jet S (Fin d) m →ₐ[S] _).comp
        (jetMap (fun p : Fin 1 × Fin d => X p.2) fun _ => X_mem_orig _) = AlgHom.id S _ :=
      jet_hom_ext fun s => by
        obtain ⟨k, s⟩ := s
        obtain rfl := Subsingleton.elim k 0
        rw [AlgHom.comp_apply, jetIn, jetMap_mk, MvPolynomial.aeval_X, jetMap_mk, MvPolynomial.aeval_X]; rfl
    rw [this]
    exact (congrArg (· ≫ x m) (Over.OverMorphism.ext (Spec.map_id _) : homAt x0 (AlgHom.id S _) = 𝟙 _)).trans
      (Category.id_comp _)

theorem jptG_ptsOf (j : JetPts t.G x0 d) {n : ℕ} (m : ℕ) (k : Fin n) :
    jptG t x0 d (ptsOf t x0 j) m k = jPt t.G x0 j n m k := by
  show homAt x0 _ ≫ homAt x0 _ ≫ j m = homAt x0 _ ≫ j m
  rw [← Category.assoc, homAt_comp]
  refine congrArg (fun g => homAt x0 g ≫ j m) (jet_hom_ext fun s => ?_)
  rw [AlgHom.comp_apply, jetIn, jetIn, jetCopy, jetMap_mk, MvPolynomial.aeval_X, jetMap_mk, MvPolynomial.aeval_X,
    jetMap_mk, MvPolynomial.aeval_X]

theorem pair_eq (j : JetPts t.G x0 d) (m : ℕ) : jPt t.G x0 j 2 m =
    ![jptG t x0 d (ptsOf t x0 j) m (0 : Fin 2), jptG t x0 d (ptsOf t x0 j) m (1 : Fin 2)] :=
  funext fun k => by fin_cases k <;> exact (jptG_ptsOf t x0 j m _).symm

def castGen {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) :
    LB.Gen (cubeLB t.G p t.PP.L) ≃ LB.Gen (cubeLB t.G q t.PP.L) :=
  Equiv.cast (congrArg (fun p => LB.Gen (cubeLB t.G p t.PP.L)) h)

theorem castGen_isGen {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) (g : LB.Gen (cubeLB t.G p t.PP.L)) :
    (castGen t h g).IsGen ↔ g.IsGen := by subst h; rfl

theorem val_castGen {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) (g : LB.Gen (cubeLB t.G p t.PP.L))
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (L := t.PP.L) (φ := cφG t q) (ε := cε 2) (castGen t h g) r z J =
      val (L := t.PP.L) (φ := lamφ t.G p) (ε := lamε) g r z J := by subst h; rfl

attribute [irreducible] castGen

def frEquiv (j : JetPts t.G x0 d) : FrameFam t.G x0 t.PP.L j ≃ ∀ m, FrTyG t x0 d (ptsOf t x0 j) m where
  toFun := fun e m => castGen t (pair_eq t x0 j m) (e m)
  invFun := fun e m => (castGen t (pair_eq t x0 j m)).symm (e m)
  left_inv := fun e => funext fun m => (castGen t (pair_eq t x0 j m)).symm_apply_apply (e m)
  right_inv := fun e => funext fun m => (castGen t (pair_eq t x0 j m)).apply_symm_apply (e m)

theorem frEquiv_apply (j : JetPts t.G x0 d) (e : FrameFam t.G x0 t.PP.L j) (m : ℕ) :
    frEquiv t x0 j e m = castGen t (pair_eq t x0 j m) (e m) := rfl

variable {t x0} {j : JetPts t.G x0 d} (e : FrameFam t.G x0 t.PP.L j)

theorem val_frEquiv (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x0 d m 2).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (L := t.PP.L) (φ := cφG t ![jptG t x0 d (ptsOf t x0 j) m (0 : Fin 2), jptG t x0 d (ptsOf t x0 j) m (1 : Fin 2)])
      (ε := cε 2) (frEquiv t x0 j e m) r z J =
      val (L := t.PP.L) (φ := lamφ t.G (jPt t.G x0 j 2 m)) (ε := lamε) (e m) r z J := by
  rw [frEquiv_apply]
  exact val_castGen t (pair_eq t x0 j m) (e m) r z J

theorem val_frAt {n : ℕ} (m : ℕ) (a b : Pt S n d) (φ ψ : Fin d → MvPolynomial (Fin n × Fin d) S)
    (ha : ∀ i, (Ideal.Quotient.mk _ (φ i) : Jet S (Fin n × Fin d) m) = psJet m (a i))
    (hb : ∀ i, (Ideal.Quotient.mk _ (ψ i) : Jet S (Fin n × Fin d) m) = psJet m (b i))
    {Z : Scheme.{0}} (r : Z ⟶ (jOG x0 d m n).left) {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (peG t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) m ![φ, ψ]) r z J = val (frAt e m a b) r z J := by
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [subst2_eq m a b φ ψ ha hb]
  exact val_frEquiv e m _ z J

theorem val_scale' {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)


theorem gen_iff : (∀ m, (e m).IsGen) ↔ ∀ m, (frEquiv t x0 j e m).IsGen :=
  forall_congr' fun m => by rw [frEquiv_apply]; exact (castGen_isGen t (pair_eq t x0 j m) (e m)).symm

theorem isFrame_iff : IndefiniteRowSideFullHecke.RigidAdjointFrameLaws.IsFrame e ↔ (∀ m, (frEquiv t x0 j e m).IsGen) ∧
    FrTrunc t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) ∧ FrAxes t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) := by
  have hL := t.PP.isLB
  refine and_congr (gen_iff e) (and_congr (forall_congr' fun m => ?_) ?_)
  · refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
    exact Eq.congr ((val_pull hJ _ _ _).trans ((val_pull hJ _ _ _).trans (val_frEquiv e (m + 1) _ y J)).symm)
      (val_frEquiv e m _ y J).symm
  · refine forall_and.symm.trans (forall_congr' fun m => and_congr ?_ ?_)
    · refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
      exact Eq.congr (val_frAt e m _ _ _ _ (mk_zero m) (mk_X m 0) _ hJ).symm rfl
    · refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
      exact Eq.congr (val_frAt e m _ _ _ _ (mk_X m 0) (mk_zero m) _ hJ).symm rfl

section Clauses

variable (t x0 d) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (e' : ∀ m, FrTyG t x0 d x m)

def Ph1Clause (F : Fin d → PS S 2 d) (ph1 : PS S 3 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e' m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))

def Ph2Clause (F : Fin d → PS S 2 d) (ph2 : PS S 3 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))

def SyClause (sy : PS S 2 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e' m)
      (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))

abbrev AdTy (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

def AdClause (act : 𝓞 E → Pt S 1 d) (a : 𝓞 E) (wL : AdTy t a) (ad : PS S 2 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m ad ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.mulGen t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
        (peG t x0 d x e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ u)
        (peG t x0 d x e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

def AdRigid (a : 𝓞 E) (wL : AdTy t a) : Prop :=
  LB.Gen.Corr t.PP.L _ _ (Y := t.G.left) _ _
      (LB.pullGen t.PP.L _ _ wL (lift (𝟙 t.G) (1 : t.G ⟶ t.G)).left) (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ (Y := t.G.left) _ _
      (LB.pullGen t.PP.L _ _ wL (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L)

set_option maxHeartbeats 1000000 in

theorem isFrameG_iff (F : Fin d → PS S 2 d) (act : 𝓞 E → Pt S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d) : IsFrameG t x0 d x F act ph1 ph2 sy ad e' ↔
      (∀ m, (e' m).IsGen) ∧ Ph1Clause t x0 d x e' F ph1 ∧ Ph2Clause t x0 d x e' F ph2 ∧ SyClause t x0 d x e' sy ∧
        ∀ a, ∃ wL : AdTy t a, wL.IsGen ∧ AdClause t x0 d x e' act a wL (ad a) :=
  ⟨fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

end Clauses




theorem sym_iff (sy : PS S 2 d) : SymIs e sy ↔ SyClause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) sy := by
  have hL := t.PP.isLB
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
  refine (Eq.congr rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_unitGen u _ hJ) rfl))).trans
    (Iff.trans ?_ (Eq.congr (val_frEquiv e m _ y J) ((val_scale' _ _ _ hJ).trans (congrArg₂ (· * ·)
      ((congrArg _ (map_inv (Units.map (toΓ _).toMonoidHom) u)).trans (map_inv _ _))
      (val_frAt e m _ _ _ _ (mk_X m 1) (mk_X m 0) _ hJ)))).symm)
  exact eq_comm.trans eq_inv_mul_iff_mul_eq.symm

def adEquiv (a : 𝓞 E) : LB.Iso (cubeLB t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] t.PP.L)
    (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] t.PP.L) ≃ AdTy t a :=
  isoEquiv (L := t.PP.L) (lamφ t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) lamε
    (lamφ t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) lamε

theorem adjVia_iff (A : 𝓞 E → Pt S 1 d) (a : 𝓞 E)
    (w : LB.Iso (cubeLB t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] t.PP.L)
      (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] t.PP.L)) (ad : PS S 2 d) :
    AdjVia e w (A a) (A (H.bar a)) ad ↔
      AdClause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) A a (adEquiv a w) ad := by
  have hL := t.PP.isLB
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
  refine Eq.congr ((val_mul hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      (val_frAt e m _ _ _ _ (mk_comp m (A a) 0) (mk_X m 1) _ hJ))).symm))
    (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_unitGen u _ hJ) rfl)).trans ((val_scale' _ _ _ hJ).trans
      (congrArg₂ (· * ·) rfl (val_frAt e m _ _ _ _ (mk_X m 0) (mk_comp m (A (H.bar a)) 1) _ hJ))).symm)
  refine congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_) rfl
  rw [jptG_ptsOf, jptG_ptsOf]
  rfl

theorem isRigAdj_iff (a : 𝓞 E) (w : LB.Iso (cubeLB t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] t.PP.L)
      (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] t.PP.L)) :
    IsRigAdj t.G t.PP.L (t.act.act a) (t.act.act (H.bar a)) w ↔ (adEquiv a w).IsGen ∧ AdRigid t a (adEquiv a w) :=
  and_congr (isoGen_isGen_iff (L := t.PP.L) (lamφ t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) lamε
    (lamφ t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) lamε w).symm Iff.rfl

theorem adj_iff (A : 𝓞 E → Pt S 1 d) (a : 𝓞 E) (ad : PS S 2 d) :
    AdjIs e (t.act.act a) (t.act.act (H.bar a)) (A a) (A (H.bar a)) ad ↔ ∃ wL : AdTy t a, (wL.IsGen ∧ AdRigid t a wL) ∧
      AdClause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) A a wL ad :=
  (adEquiv a).exists_congr fun w => and_congr (isRigAdj_iff a w) (adjVia_iff e A a w ad)



section Rigid

variable (t)

theorem prod_ad (a : 𝓞 E) {T : Over X0} (p q : T ⟶ t.G) (U : Type) [CommGroup U] (h : (T.left ⟶ t.G.left) → U) :
    ∏ i, h ((lift p q).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) ^ Sum.elim (cε 2) (fun I => -cε 2 I) i =
    h (p * (q ≫ t.act.act (H.bar a))).left * (h p.left)⁻¹ * (h (q ≫ t.act.act (H.bar a)).left)⁻¹ *
      ((h ((p ≫ t.act.act a) * q).left)⁻¹ * h (p ≫ t.act.act a).left * h q.left) := by
  have e₁ := prod_cube₂ (fst t.G t.G) (snd t.G t.G ≫ t.act.act (H.bar a)) fun r => h ((lift p q).left ≫ r)
  have e₂ := prod_neg _ _ (prod_cube₂ (fst t.G t.G ≫ t.act.act a) (snd t.G t.G) fun r => h ((lift p q).left ≫ r))
  rw [Fintype.prod_sum_type]
  refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


variable {t} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {e' : ∀ m, FrTyG t x0 d x m} {G : FGLaw S d} {A : Germ.OAct (𝓞 E) G}
  (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1)
include hz





end Rigid





end GlobalTheory.FrameCompare
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCompatOfGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)

theorem exists_sec_ne_zero {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] [IsProper G.hom] {L : LB G.left} (hL : L.IsLB)
    (hA : RelAmple G L) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (q : (Over.mk x0 ⊗ G).left) :
    ∃ k : ℕ, 0 < k ∧ ∃ F : LB.Sec (LPow G L k (Over.mk x0)), q ∈ nonzeroLocus F := by
  let π := (snd (Over.mk x0) G).left
  let f : (Over.mk x0 ⊗ G).left ⟶ Sp S := (fst (Over.mk x0) G).left
  have hp : IsPullback π f G.hom x0 := (IsPullback.of_hasPullback x0 G.hom).flip
  obtain ⟨N, hN, M, s, hcov, -⟩ := AmpleBaseChange.relAmple_of_isPullback hL hA hp ⊤ (isAffineOpen_top _)
  obtain ⟨h, hh⟩ : ∃ h : (Over.mk x0 ⊗ G).left ⟶ (f ⁻¹ᵁ ⊤).toScheme, h ≫ (f ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hy : ∀ y, (f ⁻¹ᵁ ⊤).ι (h y) = y := fun y => congrArg (fun g => g y) hh
  have le : ∀ j : Fin 1 → L.ι, (LPow G L N (Over.mk x0)).U j ≤
      h ⁻¹ᵁ (powOver (Over.mk f) (L.pull π) ⊤ N).U (fun _ _ => j 0) := fun j y hj =>
    Set.mem_iInter.2 fun _ => mem_pull.2 (by
      show π ((f ⁻¹ᵁ ⊤).ι (h y)) ∈ L.U (j 0)
      rw [hy]; exact Set.mem_iInter.1 hj 0)
  let a : ChartPull (LPow G L N (Over.mk x0)) (powOver (Over.mk f) (L.pull π) ⊤ N) h :=
    { idx := fun j _ _ => j 0
      le := le
      g := fun y j j' hj hj' => by
        refine (gm_linComb L (fun _ : Fin 1 => π) (fun _ => (N : ℤ)) (𝟙 _) y j j' hj hj').trans
          (Eq.trans ?_ (gm_linComb (L.pull π) (fun _ : Fin N => (f ⁻¹ᵁ ⊤).ι) (fun _ => 1) h y _ _
            (le j hj) (le j' hj')).symm)
        rw [Fin.prod_univ_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_one, zpow_natCast, hh]
        exact congrArg (· ^ N) (gm_pull_g L π (𝟙 _) y (fun _ => j 0) (fun _ => j' 0)
          (mem_pull.2 (Set.mem_iInter.1 hj 0)) (mem_pull.2 (Set.mem_iInter.1 hj' 0))).symm }
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show h q ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  refine ⟨N, hN, chartSec a (s i), (nonzeroLocus_chartSec a (s i) fun y _ _ => ?_).ge hi⟩
  obtain ⟨i, hi⟩ := exists_chart hL (π y)
  exact ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩

theorem val_stalk {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans (gm_val (κ ≫ r) w _ h _).symm))

theorem eq_one_of_pow {R : Type} [CommRing R] {r : R} {k : ℕ} (hk : IsUnit (k : R)) (hn : IsNilpotent (r - 1))
    (h : r ^ k = 1) : r = 1 := by
  have h1 : r - 1 ∣ (∑ i ∈ Finset.range k, r ^ i) - k := by
    have : (∑ i ∈ Finset.range k, r ^ i) - k = ∑ i ∈ Finset.range k, (r ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow r 1 i
  obtain ⟨c, hc⟩ := h1
  have hu : IsUnit (∑ i ∈ Finset.range k, r ^ i) := by
    rw [sub_eq_iff_eq_add.1 hc]
    exact ((Commute.all _ _).isNilpotent_mul_right hn).isUnit_add_right_of_commute hk (Commute.all _ _)
  have := geom_sum_mul r k
  rw [h, sub_self] at this
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d n : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}


variable (x0 d) in

abbrev tr (m n : ℕ) : jOG x0 d m n ⟶ jOG x0 d (m + 1) n :=
  homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m)






def cstHom {V : Type} [CommRing V] (y : Sp V) : V →+* (Sp V).presheaf.stalk y :=
  ((Sp V).presheaf.germ ⊤ y trivial).hom.comp (toΓ V)

theorem cst_eq {V : Type} [CommRing V] (y : Sp V) (a : V) : cst (𝟙 _) y a = cstHom y a := gs_eq (𝟙 _) y ⊤ trivial _


variable {G : FGLaw S d} {A : Germ.OAct (𝓞 E) G} {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)}
  {uvec : κ → Fin d → S} {e : ∀ m, FrTyG t x0 d x m} {ph1 ph2 : PS S 3 d} {sy : PS S 2 d} {ad : 𝓞 E → PS S 2 d}


end GlobalTheory.FrameCompatOfGerms
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NablaPinCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames GlobalTheory.IndefiniteRowSideFullHecke.HarmonicChartValues GlobalTheory.GermSectionCompare
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {j : JetPts t.G x0 d}


theorem powFrame_isGen {T : Over X0} (z : T ⟶ t.G)
    (e : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame t.G t.PP.L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl


def zeroSec (t : SAB H X0) (k : ℤ) (T : Over X0) : LB.Sec (LPow t.G t.PP.L k T) := ⟨fun _ => 0, fun i j => by simp⟩




end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem starRing_eq (st : StarRing (𝓞 E)) (h : ∀ a : 𝓞 E, star a = H.bar a) : st = H.starRing := by
  obtain @⟨@⟨@⟨⟨s⟩, _⟩, _⟩, _⟩ := st
  obtain rfl : s = fun a => H.bar a := funext h
  rfl

section Chart

variable {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S}

variable (y) in

abbrev BarChart : Type := @ChartAt E _ _ _ H Dw l Xo c H.starRing S _ _ (ratAlg c S) y

abbrev Compat (C : BarChart y) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  FrTruncC y C

variable {d : ℕ} {j : JetPts Xo.univ.t.G y.x d} {e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j} {B : FBar H S d}
  {cf : Lt1 Dw → Fin d → S} {h : Germ.PS S 2 d} {eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j}



variable (j e B cf h eL) in

def SameData (C : BarChart y) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  ∃ wP hc hf hp hg hr, C = ⟨d, B, cf, chartEquiv _ y.x j, frameEquiv _ y.x j e, wP, h, hc, hf, hp, hg, hr⟩ ∧
    ∀ m, (eL m).IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL m)
      (eLG Xo.univ.t y.x d (chartEquiv _ y.x j) B.A.act (frameEquiv _ y.x j e) wP m)



def ComputesNat (C : BarChart y) (v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  (∀ (k : ℕ) (F : SecAt y k), ∃ f, Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
    ∀ (k : ℕ) (F : SecAt y k) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
      Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∀ α : Lt1 Dw →₀ ℕ, v k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)




end Chart

section Pin

variable (Xo c)

def IsNabCompat [StarRing (𝓞 E)] (nab : NabV Xo c) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) ∧
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S),
    ∃ C : ChartAt Xo c y, FrTruncC y C ∧
      (∀ (k : ℕ) (F : SecAt y k), ∃ f, Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
      ∀ (k : ℕ) (F : SecAt y k) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
          ∀ α : Lt1 Dw →₀ ℕ, nab y k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)

variable {Xo c}


def AgreeNat (nab nab' : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) (F : SecAt y k) (α : Lt1 Dw →₀ ℕ),
    nab y k F α = nab' y k F α







end Pin

end GlobalTheory.NablaPinCompare
end
end
